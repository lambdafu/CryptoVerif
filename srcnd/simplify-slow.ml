open Types

(* Store the difference of probabilities coming from the elimination
   of collisions *)

let proba = ref Zero

let add_proba p =
  if !proba == Zero then proba := p else proba := Add(!proba, p)

(* Apply reduction rules defined by statements to term t *)

let reduced = ref false

let rec apply_red t (redl,redr) =
  try
    Terms.match_term redl t;
    let t' = Terms.copy_term redr in
    Terms.cleanup();
    reduced := true;
    t'
  with Terms.NoMatch ->
    Terms.cleanup();
    match t.t_desc with
      FunApp(f,l) ->
	{ t_desc = FunApp(f, List.map (fun t' -> apply_red t' (redl, redr)) l);
	  t_type = t.t_type;
	  t_occ = t.t_occ }
    | _ -> t

let apply_statement t (vl,t_state) =
  match t_state.t_desc with
    FunApp(f, [t1;t2]) when f == Settings.f_equal ->
      apply_red t (t1,t2)
  | _ -> apply_red t (t_state, Terms.make_true())

let rec apply_all_red t = function
    [] -> t
  | (a::l) ->
      let t' = apply_statement t a in
      if !reduced then t' else apply_all_red t l

let rec apply_reds t =
  reduced := false;
  let t' = apply_all_red t (!Transform.statements) in
  if !reduced then 
    apply_reds t' 
  else
    t

(* Applying a substitution that maps x[M1,...,Mn] to M' *)

let rec match_term2 t t' = 
  match (t.t_desc,t'.t_desc) with
    Var (v,[]), _ when List.for_all (function
	{ definition = DProcess(Repl _) } -> true 
      | _ -> false) v.def -> 
          (* Check that types match *)
	  if not (Terms.is_subtype t'.t_type v.btype) then
	    raise Terms.NoMatch;
	  begin
	    match v.link with
	      NoLink -> Terms.link v (TLink t')
	    | TLink t -> 
		if not (Terms.equal_terms t t') then raise Terms.NoMatch 
	    | _ -> Parsing_helper.internal_error "unexpected link in match_term"
	  end
  | FunApp(f,l), FunApp(f',l') when f == f' ->
      List.iter2 match_term2 l l'
  | Var(b,l),Var(b',l') when b == b' ->
      List.iter2 match_term2 l l'
  | (TestE _ | FindE _ | LetE _), _ ->
      Parsing_helper.internal_error "If, find, and let should not occur in match_term"
  | _,_ -> raise Terms.NoMatch

let rec apply_subst t (redl,redr) =
  try
    match_term2 redl t;
    let t' = Terms.copy_term redr in
    Terms.cleanup();
    reduced := true;
    t'
  with Terms.NoMatch ->
    Terms.cleanup();
    match t.t_desc with
      FunApp(f,l) ->
	{ t_desc = FunApp(f, List.map (fun t' -> apply_subst t' (redl, redr)) l);
	  t_type = t.t_type;
	  t_occ = t.t_occ }
    | _ -> t

let rec apply_all_subst t = function
    [] -> t
  | (a::l) ->
      let t' = apply_subst t a in
      if !reduced then t' else apply_all_subst t l

let rec apply_subst subst t =
  reduced := false;
  let t' = apply_all_subst t subst in
  if !reduced then 
    apply_subst subst t' 
  else
    t

(* Display facts; for debugging *)

let display_facts (subst, subst2, facts) =
  List.iter (fun (b,t) -> 
    Display.display_binder b;
    print_string " -> ";
    Display.display_term [] t;
    print_newline()) subst;
  List.iter (fun (t,t') -> 
    Display.display_term [] t;
    print_string " -> ";
    Display.display_term [] t';
    print_newline()) subst2;
  List.iter (fun t -> Display.display_term [] t; print_newline()) facts


(* Add a fact to a set of true facts, and simplify it *)

exception Contradiction

let is_true t =
  match t.t_desc with
    FunApp(f,[]) when f == Settings.c_true -> true
  | _ -> false

let is_false t =
  match t.t_desc with
    FunApp(f,[]) when f == Settings.c_false -> true
  | _ -> false

let rec add_fact_list ((subst, subst2, facts) as simp_facts) = function
    [] -> simp_facts
  | (fact''::rest_facts) ->
  match fact''.t_desc with
    FunApp(f,[t1;t2]) when f == Settings.f_and ->
      add_fact_list simp_facts (t1::t2::rest_facts)
  | FunApp(f, [t1;t2]) when f == Settings.f_equal && Terms.equal_terms t1 t2 ->
      add_fact_list simp_facts rest_facts
  | FunApp(f, [t1;t2]) when f == Settings.f_diff && Terms.equal_terms t1 t2 ->
      raise Contradiction
  | FunApp(f, [{t_desc = Var(b,l)};t2]) when f == Settings.f_equal &&
    (not (Terms.refers_to b t2)) && 
    (List.for_all2 Terms.equal_terms l b.args_at_creation) &&
    (not (Terms.is_restr b)) ->
      subst_simplify simp_facts (b,t2) rest_facts
  | FunApp(f, [t2;{t_desc = Var(b,l)}]) when f == Settings.f_equal &&
    (not (Terms.refers_to b t2)) && 
    (List.for_all2 Terms.equal_terms l b.args_at_creation) &&
    (not (Terms.is_restr b)) ->
      subst_simplify simp_facts (b,t2) rest_facts
  | FunApp(f, [({t_desc = Var(b,l)} as t1);t2]) when f == Settings.f_equal &&
    (not (Terms.refers_to b t2)) && 
    (not (Terms.is_restr b)) ->
      subst_simplify2 simp_facts (t1,t2) rest_facts
  | FunApp(f, [t2;({t_desc = Var(b,l)} as t1)]) when f == Settings.f_equal &&
    (not (Terms.refers_to b t2)) && 
    (not (Terms.is_restr b)) ->
      subst_simplify2 simp_facts (t1,t2) rest_facts
  | FunApp(f,[{ t_desc = FunApp(f1,l1) }; { t_desc = FunApp(f2,l2) }]) when
    f == Settings.f_equal &&
    f1.f_cat == Tuple && f2.f_cat == Tuple && f1 != f2 -> 
      raise Contradiction
  | FunApp(f,[{ t_desc = FunApp(f1,l1) }; { t_desc = FunApp(f2,l2) }]) when
    f == Settings.f_diff && 
    f1.f_cat == Tuple && f2.f_cat == Tuple && f1 != f2 -> 
      add_fact_list simp_facts rest_facts
  | FunApp(f,[{ t_desc = FunApp(f1,l1) }; { t_desc = FunApp(f2,l2) }]) when
    f == Settings.f_equal && f1.f_cat == Tuple && f1 == f2 -> 
      add_fact_list simp_facts ((List.map2 Terms.make_equal l1 l2) @ rest_facts)
  | FunApp(f,[{ t_desc = Var(b1,l1) }; {t_desc = Var(b2,l2)}]) when
    f == Settings.f_equal && (Terms.is_restr b1) &&
    Terms.is_large b1.btype && b1 == b2 ->
      (* TO DO add_proba (Div(Cst 1, Card b1.btype)); * number applications *)
      add_fact_list simp_facts ((List.map2 Terms.make_equal l1 l2) @ rest_facts)
  | FunApp(f,[{ t_desc = Var(b1,l1) }; {t_desc = Var(b2,l2)}]) when
    f == Settings.f_equal && (Terms.is_restr b1) && (Terms.is_restr b2) &&
    (Terms.is_large b1.btype || Terms.is_large b2.btype) &&
    b1 != b2 ->
      raise Contradiction
      (* TO DO add probability *)
  | FunApp(f,[{ t_desc = Var(b1,l1) }; {t_desc = Var(b2,l2)}]) when
    f == Settings.f_diff && (Terms.is_restr b1) && (Terms.is_restr b2) &&
    (Terms.is_large b1.btype || Terms.is_large b2.btype) &&
    b1 != b2 ->
      add_fact_list simp_facts rest_facts
      (* TO DO add probability *)
  | FunApp(f,[{ t_desc = FunApp(f1,[]) }; { t_desc = FunApp(f2,[]) }]) when
    f == Settings.f_equal && f1 != f2 && (!Settings.diff_constants) ->
      raise Contradiction
	(* Different constants are different *)
  | FunApp(f,[{ t_desc = FunApp(f1,[]) }; { t_desc = FunApp(f2,[]) }]) when
    f == Settings.f_diff && f1 != f2 && (!Settings.diff_constants) ->
      add_fact_list simp_facts rest_facts
	(* Different constants are different *)
  | _ -> 
      if is_false fact'' then raise Contradiction else
      if is_true fact'' then add_fact_list simp_facts rest_facts else
      add_fact_list (subst, subst2, fact''::facts) rest_facts

and subst_simplify (subst, subst2, facts) link rest_facts =
  let subst' = List.map (fun (b,t) -> (b,apply_reds(Terms.subst2 [link] t))) subst in
  let subst2' = List.map (fun (t,t') -> (t,apply_reds(Terms.subst2 [link] t'))) subst2 in
  let facts' = List.map (fun t -> apply_reds(Terms.subst2 [link] t)) (facts @ rest_facts) in
  add_fact_list (link :: subst',subst2',[]) facts'

and subst_simplify2 (subst, subst2, facts) link rest_facts =
  let subst' = List.map (fun (b,t) -> (b,apply_reds(apply_subst [link] t))) subst in
  let subst2' = List.map (fun (t,t') -> (t,apply_reds(apply_subst [link] t'))) subst2 in
  let facts' = List.map (fun t -> apply_reds(apply_subst [link] t)) (facts @ rest_facts) in
  simplif_add_list (subst',link :: subst2',[]) facts'

and simplif_add ((subst, subst2, facts) as simp_facts) fact =
  let fact' = apply_reds (apply_subst subst2 (Terms.subst2 subst fact)) in
  add_fact_list simp_facts [fact']

and simplif_add_list ((subst, subst2, facts) as simp_facts) facts =
  let facts' = List.map (fun fact -> apply_reds (apply_subst subst2 (Terms.subst2 subst fact))) facts in
  add_fact_list simp_facts facts'

(* Simplify a term knowing some true facts *)

let make_or t1 t2 =
  if (is_true t1) || (is_true t2) then Terms.make_true() else
  if is_false t1 then t2 else
  if is_false t2 then t1 else
  Terms.make_or t1 t2

let rec get_or t =
  match t.t_desc with
    FunApp(f, [t1;t2]) when f == Settings.f_or ->
      (get_or t1) @ (get_or t2)
  | _ -> [t]

let rec make_and1 a = function
    [] -> Parsing_helper.internal_error "make_and1 empty"
  | [b] -> Terms.make_and b a
  | (b::l2) -> Terms.make_or (Terms.make_and a b) (make_and1 a l2)

let rec make_and2 l1 = function
    [] -> Parsing_helper.internal_error "make_and2 empty"
  | [a] -> make_and1 a l1
  | (a::l2) -> Terms.make_or (make_and1 a l1) (make_and2 l1 l2)


let make_and t1 t2 =
  if (is_false t1) || (is_false t2) then Terms.make_false() else
  if is_true t1 then t2 else
  if is_true t2 then t1 else
  (* If t1 or t2 is "or", distribute *)
  make_and2 (get_or t1) (get_or t2)

let rec make_and_list = function
    [] -> Terms.make_true()
  | [a] -> a
  | (a::l) -> make_and a (make_and_list l)

let rec make_or_list = function
    [] -> Terms.make_false()
  | [a] -> a
  | (a::l) -> make_or a (make_or_list l)

let rec simplify_term_rec t' = 
  match t'.t_desc with
    FunApp(f, [t1;t2]) when f == Settings.f_and ->
      make_and (simplify_term_rec t1) (simplify_term_rec t2)
  | FunApp(f, [t1;t2]) when f == Settings.f_or ->
      make_or (simplify_term_rec t1) (simplify_term_rec t2)
  | FunApp(f, [t1;t2]) when f == Settings.f_equal && Terms.equal_terms t1 t2 ->
      Terms.make_true()
  | FunApp(f, [t1;t2]) when f == Settings.f_diff && Terms.equal_terms t1 t2 ->
      Terms.make_false()
  | FunApp(f,[{ t_desc = FunApp(f1,l1) }; { t_desc = FunApp(f2,l2) }]) when
    f == Settings.f_equal &&
    f1.f_cat == Tuple && f2.f_cat == Tuple && f1 != f2 -> 
      Terms.make_false()
  | FunApp(f,[{ t_desc = FunApp(f1,l1) }; { t_desc = FunApp(f2,l2) }]) when
    f == Settings.f_diff &&
    f1.f_cat == Tuple && f2.f_cat == Tuple && f1 != f2 -> 
      Terms.make_true()
  | FunApp(f,[{ t_desc = FunApp(f1,l1) }; { t_desc = FunApp(f2,l2) }]) when
    f == Settings.f_equal && f1.f_cat == Tuple && f1 == f2 -> 
      make_and_list (List.map2 (fun t1 t2 -> simplify_term_rec (Terms.make_equal t1 t2)) l1 l2)
  | FunApp(f,[{ t_desc = FunApp(f1,l1) }; { t_desc = FunApp(f2,l2) }]) when
    f == Settings.f_diff && f1.f_cat == Tuple && f1 == f2 -> 
      make_or_list (List.map2 (fun t1 t2 -> simplify_term_rec (Terms.make_diff t1 t2)) l1 l2)
  | FunApp(f,[{ t_desc = Var(b1,l1) }; {t_desc = Var(b2,l2)}]) when
    f == Settings.f_equal && (Terms.is_restr b1) &&
    Terms.is_large b1.btype && b1 == b2 ->
      (* TO DO add_proba (Div(Cst 1, Card b1.btype)); * number applications *)
      make_and_list (List.map2 (fun t1 t2 -> simplify_term_rec (Terms.make_equal t1 t2)) l1 l2)
  | FunApp(f,[{ t_desc = Var(b1,l1) }; {t_desc = Var(b2,l2)}]) when
    f == Settings.f_diff && (Terms.is_restr b1) &&
    Terms.is_large b1.btype && b1 == b2 ->
      (* TO DO add_proba (Div(Cst 1, Card b1.btype)); * number applications *)
      make_or_list (List.map2 (fun t1 t2 -> simplify_term_rec (Terms.make_diff t1 t2)) l1 l2)
  | FunApp(f,[{ t_desc = Var(b1,l1) }; {t_desc = Var(b2,l2)}]) when
    f == Settings.f_equal && (Terms.is_restr b1) && (Terms.is_restr b2) &&
    (Terms.is_large b1.btype || Terms.is_large b2.btype) &&
    b1 != b2 ->
      Terms.make_false()
      (* TO DO add probability *)
  | FunApp(f,[{ t_desc = Var(b1,l1) }; {t_desc = Var(b2,l2)}]) when
    f == Settings.f_diff && (Terms.is_restr b1) && (Terms.is_restr b2) &&
    (Terms.is_large b1.btype || Terms.is_large b2.btype) &&
    b1 != b2 ->
      Terms.make_true()
      (* TO DO add probability *)
  | FunApp(f,[{ t_desc = FunApp(f1,[]) }; { t_desc = FunApp(f2,[]) }]) when
    f == Settings.f_equal && f1 != f2 && (!Settings.diff_constants) ->
      Terms.make_false()
	(* Different constants are different *)
  | FunApp(f,[{ t_desc = FunApp(f1,[]) }; { t_desc = FunApp(f2,[]) }]) when
    f == Settings.f_diff && f1 != f2 && (!Settings.diff_constants) ->
      Terms.make_true()
	(* Different constants are different *)
  | _ -> t'

let simplify_term ((subst, subst2, facts) as simp_facts) t = 
  let t' = apply_subst subst2 (Terms.subst2 subst t) in
  let t'' = apply_reds t' in
  let t''' = 
    if t''.t_type == Settings.t_bool then
      begin
	try
	  ignore(add_fact_list simp_facts [t'']);
	  try
	    ignore(add_fact_list simp_facts [Terms.make_not t'']);
	    simplify_term_rec t''
	  with Contradiction ->
	    Terms.make_true()
	with Contradiction ->
	  Terms.make_false()
      end
    else
      t''
  in
  if !Settings.minimal_simplifications then
    begin
      if is_true t''' || is_false t''' || not (Terms.equal_terms t' t''') then
	begin
	  if not (is_true t || is_false t) then Transform.changed := true;
	  t'''
	end
      else
	(* The change is not really useful, don't do it *)
	t
    end
  else
    begin
      if not (Terms.equal_terms t t''') then Transform.changed := true;
      t'''
    end

(* facts_from_defined def_list: 
       for each (b,l) in def_list,
       look for definitions n of binders b,
       substitute l for b.args_at_creation in n.true_facts_at_def and
       add these facts to the returned list 
       substitute l for b.args_at_creation in n.def_vars_at_def and
       continue recursively with these definitions 
       If there are several definitions of b, take the intersection
       of lists of facts/defined vars. ("or" would be more precise
       but difficult to implement) 
       Do not reconsider an already seen pair (b,l), to avoid loops.*)

let rec intersect eqtest l = function
    [] -> []
  | (a'::l') -> 
      let l'' = intersect eqtest l' l in
      if List.exists (eqtest a') l then 
	a'::l'' 
      else
	l''

let rec intersect_list eqtest = function
    [] -> raise Contradiction
  | [a] -> a
  | (a::l) -> intersect eqtest a (intersect_list eqtest l)

let rec add_facts fact_accu seen_refs (b,l) =
  if not (List.exists (Terms.equal_binderref (b,l)) (!seen_refs)) then
    begin
      seen_refs := (b,l) :: (!seen_refs);
      let true_facts_at_def = intersect_list Terms.equal_terms (List.map (fun n -> n.true_facts_at_def) b.def) in
      let def_vars_at_def = intersect_list (==) (List.map (fun n -> n.def_vars_at_def) b.def) in
      (* b.args_at_creation -> l *)
      let true_facts_at_def = List.map (Terms.subst (List.map Terms.binder_from_term b.args_at_creation) l) true_facts_at_def in
      let def_vars_at_def = List.map (fun (b',l') ->
	(b', List.map (Terms.subst (List.map Terms.binder_from_term b.args_at_creation) l) l')) def_vars_at_def 
      in
      (* add facts *)
      List.iter (fun f -> 
	if not (List.memq f (!fact_accu)) then
	  fact_accu := f :: (!fact_accu)) true_facts_at_def;
      (* recursive call *)
      List.iter (fun br ->
	add_facts fact_accu seen_refs br) def_vars_at_def
    end
      
let facts_from_defined def_list =
  let fact_accu = ref [] in
  let seen_refs = ref [] in
  List.iter (add_facts fact_accu seen_refs) def_list;
  !fact_accu

(* Simplify pattern *)

let rec simplify_pat true_facts = function
    (PatVar b) as pat -> pat
  | PatTuple l -> PatTuple (List.map (simplify_pat true_facts) l)
  | PatEqual t -> PatEqual (simplify_term true_facts t)

(* NOTE: simplify_cterm is simply simplify_term when 
   TestE/FindE/LetE are forbidden *)
let rec simplify_cterm true_facts t =
  match t.t_desc with
    TestE(t1, t2, t3) ->
      begin
      let t1' = simplify_term true_facts t1 in
      try
	let t3' = simplify_cterm (simplif_add true_facts (Terms.make_not t1')) t3 in
	simplify_if t.t_type true_facts t2 t3' t1'
      with Contradiction ->
	Transform.changed := true;
	simplify_cterm true_facts t2
      end
  | FindE(bl, def_list, t1, t2, t3) ->
      begin
	let t3' = simplify_cterm true_facts t3 in
	try
	  let true_facts' = simplif_add_list true_facts (facts_from_defined def_list) in
	  let t1' = simplify_cterm true_facts' t1 in
	  simplify_find t.t_type bl def_list true_facts' t2 t3' t1'
	with Contradiction ->
	  Transform.changed := true;
	  t3'
      end
  | LetE(pat, t1, t2, topt) ->
      let t1' = simplify_term true_facts t1 in
      let topt' = match topt with
	None -> None 
      |	Some t3 -> Some (simplify_cterm true_facts t3) 
      in
      simplify_let t.t_type true_facts t2 topt' t1' pat
  | _ -> simplify_term true_facts t

and simplify_if ty true_facts ptrue pfalse t' =
  match t'.t_desc with
    FunApp(f, []) when f == Settings.c_false -> 
      Transform.changed := true;
      pfalse
  | FunApp(f, []) when f == Settings.c_true -> 
      Transform.changed := true;
      simplify_cterm true_facts ptrue
  | FunApp(f, [t1; t2]) when f == Settings.f_or ->
      Transform.changed := true;
      simplify_if ty true_facts ptrue (simplify_if ty true_facts ptrue pfalse t2) t1
  | _ -> 
      try
	{ t_desc = TestE(t', simplify_cterm (simplif_add true_facts t') ptrue, pfalse);
	  t_type = ty;
	  t_occ = Terms.new_occ() }
      with Contradiction ->
	Transform.changed := true;
	pfalse

and simplify_find ty bl def_list true_facts ptrue pfalse t' =
  match t'.t_desc with
    FunApp(f, []) when f == Settings.c_false -> 
      Transform.changed := true;
      pfalse
  | FunApp(f, [t1; t2]) when f == Settings.f_or ->
      Transform.changed := true;
      simplify_find ty bl def_list true_facts ptrue (simplify_find ty bl def_list true_facts ptrue pfalse t2) t1
  | _ -> 
      try
	{ t_desc = FindE(bl, def_list, t', simplify_cterm (simplif_add true_facts t') ptrue, pfalse);
	  t_type = ty;
	  t_occ = Terms.new_occ() }
      with Contradiction ->
	Transform.changed := true;
	pfalse

and simplify_let ty true_facts ptrue pfalse t' = function
    (PatVar b) as pat -> 
      if pfalse != None then Transform.changed := true;
      { t_desc = LetE(pat, t', simplify_cterm (simplif_add true_facts (Terms.make_equal 
	           (Terms.term_from_binder b) t')) ptrue, None);
	t_type = ty;
	t_occ = Terms.new_occ() }
  | PatEqual t ->
      Transform.changed := true;
      simplify_cterm true_facts { t_desc = TestE(Terms.make_equal t t', ptrue,
 						 match pfalse with
						   None -> Parsing_helper.internal_error "Missing else part of let"
						 | Some tfalse -> tfalse);
				  t_type = ty;
				  t_occ = Terms.new_occ() }
  | (PatTuple l) as pat ->
      begin
	try 
	  let res = simplify_cterm true_facts 
	      (Terms.put_lets (Terms.make_let_term ty) l (Terms.split_term (List.length l) t') ptrue pfalse)
	  in
	  Transform.changed := true;
	  res
	with 
	  Not_found -> 
	    { t_desc = LetE(pat, t', simplify_cterm true_facts ptrue, pfalse);
	      t_type = ty;
	      t_occ = Terms.new_occ() }
	| Terms.Impossible -> 
	    Transform.changed := true;
	    match pfalse with
	      None -> Parsing_helper.internal_error "Missing else part of let"
	    | Some tfalse -> tfalse
      end

let rec simplify_process true_facts = function
    Nil -> Nil
  | Par(p1,p2) -> Par(simplify_process true_facts p1,
		      simplify_process true_facts p2)
  | Restr(b,p) -> Restr(b, simplify_process true_facts p)
  | Repl(b,p) -> Repl(b, simplify_process true_facts p)
  | Test(t, p1, p2) ->
      begin
      let t' = simplify_term true_facts t in
      try
	let p2' = simplify_process (simplif_add true_facts (Terms.make_not t')) p2 in
	simplify_if true_facts p1 p2' t'
      with Contradiction ->
	Transform.changed := true;
	simplify_process true_facts p1
      end
  | Find(bl, def_list, t, p1, p2) ->
      begin
	let p2' = simplify_process true_facts p2 in
	try
	  let true_facts' = simplif_add_list true_facts (facts_from_defined def_list) in
	  let t' = simplify_cterm true_facts' t in
	  simplify_find bl def_list true_facts' p1 p2' t'
	with Contradiction ->
	  Transform.changed := true;
	  p2'
      end
  | Let(pat, t, p1, p2) ->
      let t' = simplify_term true_facts t in
      let p2' = simplify_process true_facts p2 in
      simplify_let true_facts p1 p2' t' pat
  | Input(t, pat, p) ->
      Input(simplify_term true_facts t, simplify_pat true_facts pat, 
	    simplify_process true_facts p)
  | Output(t1,t2,p) ->
      Output(simplify_term true_facts t1, simplify_term true_facts t2,
	     simplify_process true_facts p)


and simplify_if true_facts ptrue pfalse t' =
  match t'.t_desc with
    FunApp(f, []) when f == Settings.c_false -> 
      Transform.changed := true;
      pfalse
  | FunApp(f, []) when f == Settings.c_true -> 
      Transform.changed := true;
      simplify_process true_facts ptrue
  | FunApp(f, [t1; t2]) when f == Settings.f_or ->
      Transform.changed := true;
      simplify_if true_facts ptrue (simplify_if true_facts ptrue pfalse t2) t1
  | _ -> 
      try
	Test(t', simplify_process (simplif_add true_facts t') ptrue, pfalse)
      with Contradiction ->
	Transform.changed := true;
	pfalse

and simplify_find bl def_list true_facts ptrue pfalse t' =
  match t'.t_desc with
    FunApp(f, []) when f == Settings.c_false -> 
      Transform.changed := true;
      pfalse
  | FunApp(f, [t1; t2]) when f == Settings.f_or ->
      Transform.changed := true;
      simplify_find bl def_list true_facts ptrue (simplify_find bl def_list true_facts ptrue pfalse t2) t1
  | _ -> 
      try
	Find(bl, def_list, t', simplify_process (simplif_add true_facts t') ptrue, pfalse)
      with Contradiction ->
	Transform.changed := true;
	pfalse

and simplify_let true_facts ptrue pfalse t' = function
    (PatVar b) as pat -> 
      if pfalse != Nil then Transform.changed := true;
      Let(pat, t', simplify_process (simplif_add true_facts (Terms.make_equal 
	(Terms.term_from_binder b) t')) ptrue, Nil)
  | PatEqual t ->
      Transform.changed := true;
      simplify_process true_facts (Test(Terms.make_equal t t', ptrue, pfalse))
  | (PatTuple l) as pat ->
      begin
	try 
	  let res = simplify_process true_facts 
	      (Terms.put_lets Terms.make_let_proc l (Terms.split_term (List.length l) t') ptrue pfalse)
	  in
	  Transform.changed := true;
	  res
	with 
	  Not_found -> 
	    Let(pat, t', simplify_process true_facts ptrue, pfalse)
	| Terms.Impossible -> 
	    Transform.changed := true;
	    pfalse
      end

let rec simplify_main1 iter process =
  let tmp_changed = !Transform.changed in
  Transform.changed := false;
  Terms.build_def_process process;
  let p' = simplify_process ([],[],[]) process in
  let res = 
    if (!Transform.changed) && (iter != 0) then 
      simplify_main1 (iter-1) p'
    else
      p'
  in
  Transform.changed := (!Transform.changed) || tmp_changed;
  res

let simplify_main process =
  proba := Zero;
  (simplify_main1 (!Settings.max_iter_simplif) process, !proba)
