open Types

(* Lexicographic path ordering *)

type symbol = 
    SVar of binder
  | SFun of funsymb 

let order = ref ([]: (symbol * symbol) list)

let eq_symb s1 s2 = match (s1, s2) with
  SVar b1, SVar b2 -> b1 == b2
| SFun f1, SFun f2 -> f1 == f2
| _ -> false
    

let rec check_no_path f f' = 
  (not (eq_symb f f')) && 
  (List.for_all (fun (f2,f2') -> 
    if eq_symb f f2 then check_no_path f2' f' else true) (!order))

let check_no_path f f' =
  let catf = match f with
    SFun g -> if fst g.f_type = [] then 2 else 3
  | SVar b -> if Terms.is_repl b then 0 else if Terms.is_restr b then 1 else 4
  in
  let catf' = match f' with
    SFun g -> if fst g.f_type = [] then 2 else 3
  | SVar b -> if Terms.is_repl b then 0 else if Terms.is_restr b then 1 else 4
  in
  if catf = catf' then
    check_no_path f f' 
  else
    catf < catf'

(* comparison for terms in user-defined rewrite rules *)

let rec greater_lpo t1 t2 = match (t1.t_desc,t2.t_desc) with
  (Var(v1,[]), _) -> false
| (_, Var(v2,[])) -> Terms.refers_to v2 t1
| (FunApp(f1,l1), FunApp(f2,l2)) ->
    (List.exists (fun t1' -> greater_lpo t1' t2) l1) ||
    ((f1 != f2) && (not (check_no_path (SFun f1) (SFun f2))) && 
     (List.for_all (greater_lpo t1) l2)) ||
    ((f1 == f2) && (List.for_all (greater_lpo t1) l2) &&
     (greater_lpo_lex l1 l2))
| _ -> Parsing_helper.internal_error "if/let/find/array ref in greater_lpo"

and greater_lpo_lex l1 l2 = match (l1,l2) with
  ([], []) -> false
| (t1::l1',t2::l2') ->
    (greater_lpo t1 t2) ||
    ((Terms.equal_terms t1 t2) && (greater_lpo_lex l1' l2'))
| _ -> Parsing_helper.internal_error "Different length in greater_lpo_lex"


(* Comparison for terms in rewrite rules that come from the process
   No variables in them. *)

let get_symb_args t = match t.t_desc with
  Var(b,l) -> ((SVar b),l)
| FunApp(f,l) -> ((SFun f),l)
| _ -> Parsing_helper.internal_error "if/let/find in get_symb_args"

let rec greater_lpo_cl t1 t2 = 
  let (f1,l1) = get_symb_args t1 in
  let (f2,l2) = get_symb_args t2 in
  (List.exists (fun t1' -> greater_lpo_cl t1' t2) l1) ||
  ((f1 != f2) && (not (check_no_path f1 f2)) && 
   (List.for_all (greater_lpo_cl t1) l2)) ||
   ((f1 == f2) && (List.for_all (greater_lpo_cl t1) l2) &&
    (greater_lpo_lex_cl l1 l2))

and greater_lpo_lex_cl l1 l2 = match (l1,l2) with
  ([], []) -> false
| (t1::l1',t2::l2') ->
    (greater_lpo_cl t1 t2) ||
    ((Terms.equal_terms t1 t2) && (greater_lpo_lex_cl l1' l2'))
| _ -> Parsing_helper.internal_error "Different length in greater_lpo_lex_cl"

let orient1 t1 t2 =
  if greater_lpo_cl t1 t2 then 1 else 
  if greater_lpo_cl t2 t1 then -1 else 0 

(* Choose the ordering of symbols (variables and function symbols) 
   - replication indexes are the smallest
   - next, variables defined by restrictions
   - next, function symbols, ordered as far as possible 
   by orienting user-defined rules from left to right
   - next, other variables. Variables defined by let are greater than
   the variables they depend on.
*)

let set_order s1 s2 =
  if check_no_path s2 s1 then
    order := (s1,s2) :: (!order)

(* Orienting user-defined rewrite rules from left to right *)

let rec occurs_f f t =
  match t.t_desc with
    Var(b,l) -> List.exists (occurs_f f) l
  | FunApp(f',l) -> (f' == f) || (List.exists (occurs_f f) l)
  | _ -> false

let rec add_order t1 t2 = match t1.t_desc, t2.t_desc with
    (FunApp(f1,l1), FunApp(f2,l2)) when f1 == f2 ->
      List.iter (fun t1 -> add_order t1 t2) l1;
      List.iter2 (fun t1 t2 -> add_order t1 t2) l1 l2
  | (FunApp(f1,l1), _) when occurs_f f1 t2 ->
      List.iter (fun t1 -> add_order t1 t2) l1
  | (FunApp(f1,l1), _) ->
      let rec find_fun_symb accu t = match t.t_desc with
	  Var _ -> accu
	| FunApp(f2,l2) -> 
	    let accu' = if List.memq f2 accu then accu else f2::accu in
	    List.fold_left find_fun_symb accu' l2
	| _ -> accu
      in
      let new_symbols = find_fun_symb [] t2 in
      List.iter (fun f2 -> set_order (SFun f1) (SFun f2)) new_symbols
  | _ -> ()


let order_statement (vl, t_state) =
  match t_state.t_desc with
    FunApp(f, [t1;t2]) when f.f_cat == Equal ->
      add_order t1 t2
  | _ -> ()

let order_coll (restr, forall, t1, proba, t2) =
  add_order t1 t2

(* Order variables according to game *)

let rec find_var accu t = match t.t_desc with
  Var(b,l) -> if not (List.memq b (!accu)) then accu := b :: (!accu);
    List.iter (find_var accu) l
| FunApp(f,l) -> List.iter (find_var accu) l
| _ -> Parsing_helper.internal_error "if/let/find in find_var"

let set_order_terms t1 t2 =
  let accu1 = ref [] in
  find_var accu1 t1;
  let accu2 = ref [] in
  find_var accu2 t2;
  List.iter (fun b1 ->
    List.iter (fun b2 -> set_order (SVar b1) (SVar b2)) (!accu2)) (!accu1)

let rec let_order t = function
  PatVar b -> 
    let accu = ref [] in
    find_var accu t;
    List.iter (fun b' -> set_order (SVar b) (SVar b')) (!accu)
| PatTuple(f,l) -> 
    List.iter (let_order t) l
| PatEqual t -> () 

let rec set_order_process = function
    Nil -> ()
  | Par(p1,p2) -> set_order_process p1; set_order_process p2
  | Repl(b,p) -> set_order_process p
  | Input(_,_,p) -> set_order_oprocess p

and set_order_oprocess = function
    Yield -> ()
  | Restr(b,p) -> set_order_oprocess p
  | Test(t,p1,p2) -> set_order_oprocess p1; set_order_oprocess p2
  | Find(l,p,_) ->
      List.iter (fun (_,_,t,p1) -> set_order_oprocess p1) l;
      set_order_oprocess p
  | Output(_,_,p) -> set_order_process p
  | Let(pat, t, p1,p2) -> 
      let_order t pat;
      set_order_oprocess p1;
      set_order_oprocess p2

let def_order p = 
  order := [];
  List.iter order_statement (!Transform.statements);
  List.iter order_coll (!Transform.collisions);
  set_order_process p

(* Store the difference of probabilities coming from the elimination
   of collisions *)

let proba = ref Zero

let add_proba p =
  if !proba == Zero then proba := p else proba := Add(!proba, p)

(* On demand substitutions 

let try_no_var (subst, facts) t =
   when t is FunApp(_), return t itself.
   when t is Var(_), try applying substitutions until t becomes FunApp(_)
   if impossible, return t itself.

   It may be necessary to apply subtitutions to strict subterms of t
   in order to be able to apply another substitution to t itself.

   Apply on demand substitution when 
   - a matching for a reduction rule meets a variable when
   it expects a function symbol
   - unification called when we have an inequality meets a 
   different variable on both sides 
   - we have a variable in a boolean formula (x && ...), ...
   - equality between a variable and a variable or a tuple
   - let (...) = x[...] substitute x

Substitutions map variables x[...] to some term.

Difficulty = avoid loops; when should I stop applying substitutions
to avoid cycles? Do not reapply the same subtitution in a term
that comes from its image term, perhaps after transformation.
The difficulty is to follow what the term becomes during these
transformations.
Possible transformations are:
   - applying another substitution
   - applying a reduction rule, which does not change variables.
So keep a mapping (occ, M -> M') of forbidden substitutions,
and update it when applying a substitution. If this substitution
transforms N into N', and occ is in N then add (occ', M -> M')
for each occ' occurrence of a variable in N'.

*)


(* Applying a substitution that maps x[M1,...,Mn] to M' *)

let reduced_subst = ref false

let rec apply_subst1 t (redl,redr) =
  match t.t_desc with
    FunApp(f,l) -> t
  | _ ->
      if Terms.equal_terms t redl then 
	begin
	  reduced_subst := true;
	  redr
	end
      else
    match t.t_desc with
      Var(b,l) ->
	{ t_desc = Var(b, List.map (fun t' -> apply_subst1 t' (redl, redr)) l);
	  t_type = t.t_type;
	  t_occ = t.t_occ }
    | _ -> t
(*    match t.t_desc with
      FunApp(f,l) ->
	{ t_desc = FunApp(f, List.map (fun t' -> apply_subst1 t' (redl, redr)) l);
	  t_type = t.t_type;
	  t_occ = t.t_occ }
    | _ -> t*)

let rec apply_all_subst t = function
    [] -> t
  | (a::l) ->
      let t' = apply_subst1 t a in
      if !reduced_subst then t' else apply_all_subst t l

let rec try_no_var ((subst2, _) as simp_facts) t =
  match t.t_desc with
    FunApp(f,l) -> t
  | Var(b,l) -> 
      reduced_subst := false;
      let t' = apply_all_subst t subst2 in
      if !reduced_subst then 
	try_no_var simp_facts t' 
      else
	t
  | TestE _ | FindE _ | LetE _ -> 
      Parsing_helper.internal_error "If, find, and let should not occur in try_no_var"

(* Unification *)

let rec unify_terms simp_facts t t' =
  match t.t_desc,t'.t_desc with
    ((TestE _ | FindE _ | LetE _), _)
  | (_, (TestE _ | FindE _ | LetE _)) ->
      Parsing_helper.internal_error "If, find, and let should not occur in unify_terms"
  | (Var(b,l), Var(b',l')) when Terms.equal_terms t t' -> () 
  | _ ->
      let t1 = try_no_var simp_facts t in
      let t1' = try_no_var simp_facts t' in
      match (t1.t_desc, t1'.t_desc) with
	Var(b,l), Var(b',l') -> if not (Terms.equal_terms t1 t1') then raise Terms.NoMatch
      |	FunApp(f,l), FunApp(f',l') when f == f' ->
	  List.iter2 (unify_terms simp_facts) l l'
      |	_ -> raise Terms.NoMatch


(* Apply reduction rules defined by statements to term t *)

let rec match_term simp_facts restr t t' = 
  match t.t_desc with
    Var (v,[]) -> 
    (* Check that types match *)
      if t'.t_type != v.btype then
	raise Terms.NoMatch;
      begin
	match v.link with
	  NoLink -> 
	    if List.memq v restr then
	      (* t' must be a variable created by a restriction *)
	      begin
		if not (t'.t_type == v.btype) then
		  raise Terms.NoMatch;
		match t'.t_desc with
		  Var(b,l) when Terms.is_restr b -> ()
		| _ -> raise Terms.NoMatch
	      end;
	    Terms.link v (TLink t')
	| TLink t -> 
	    unify_terms simp_facts t t'
	| _ -> Parsing_helper.internal_error "unexpected link in match_term"
      end
  | FunApp(f,l) ->
      begin
	match (try_no_var simp_facts t').t_desc with
	  FunApp(f',l') when f == f' ->
	    List.iter2 (match_term simp_facts restr) l l'
	| _ -> raise Terms.NoMatch
      end
  | Var _ | TestE _ | FindE _ | LetE _ ->
      Parsing_helper.internal_error "Var with arguments, If, find, and let should not occur in match_term"

let reduced = ref false

let rec apply_not_red simp_facts t =
  match t.t_desc with
    FunApp(fnot, [t']) when fnot == Settings.f_not ->
      begin
      let t' = try_no_var simp_facts t' in
      match t'.t_desc with
	FunApp(feq, [t1;t2]) when feq.f_cat == Equal ->
	  reduced := true;
	  Terms.make_diff t1 t2
      |	FunApp(fdiff, [t1;t2]) when fdiff.f_cat == Diff ->
	  reduced := true;
	  Terms.make_equal t1 t2
      |	_ -> Terms.make_not (apply_not_red simp_facts t')
      end
  | FunApp(f,l) ->
    { t_desc = FunApp(f, List.map (apply_not_red simp_facts) l);
      t_type = t.t_type;
      t_occ = t.t_occ }
  | _ -> t

let rec apply_red simp_facts t (restr,redl,redr) =
  match t.t_desc with
    FunApp(f,l) ->
      begin
	try
	  match_term simp_facts restr redl t;
	  let t' = Terms.copy_term redr in
	  Terms.cleanup();
	  reduced := true;
	  t'
	with Terms.NoMatch ->
	  Terms.cleanup();
	  { t_desc = FunApp(f, List.map (fun t' -> apply_red simp_facts t' (restr, redl, redr)) l);
	    t_type = t.t_type;
	    t_occ = t.t_occ }
      end
  | _ -> t

let apply_statement simp_facts t (vl,t_state) =
  match t_state.t_desc with
    FunApp(f, [t1;t2]) when f.f_cat == Equal ->
      apply_red simp_facts t ([],t1,t2)
  | FunApp(f, [t1;t2]) when f.f_cat == Diff ->
      apply_red simp_facts (apply_red simp_facts (apply_red simp_facts (apply_red simp_facts t 
	([],t_state, Terms.make_true())) 
        ([],Terms.make_diff t2 t1, Terms.make_true()))
	([],Terms.make_equal t1 t2, Terms.make_false()))
	([],Terms.make_equal t2 t1, Terms.make_false())
  | _ -> apply_red simp_facts t ([],t_state, Terms.make_true())

let rec apply_all_red simp_facts t = function
    [] -> 
      let t' = apply_not_red simp_facts t in
      if !reduced then t' else t
  | (a::l) ->
      let t' = apply_statement simp_facts t a in
      if !reduced then t' else apply_all_red simp_facts t l

let apply_collision simp_facts t (restr, forall, t1, proba, t2) =
  (* TO DO add proba when reducing *)
  apply_red simp_facts t (restr,t1,t2)

let rec apply_all_coll simp_facts t = function
    [] -> t
  | (a::l) ->
      let t' = apply_collision simp_facts t a in
      if !reduced then t' else apply_all_coll simp_facts t l

let apply_statements_and_collisions simp_facts t =
  let t' = apply_all_red simp_facts t (!Transform.statements) in
  if !reduced then t' else
  apply_all_coll simp_facts t (!Transform.collisions) 

let rec apply_reds simp_facts t =
  reduced := false;
  let t' = apply_statements_and_collisions simp_facts t in
  if !reduced then 
    apply_reds simp_facts t' 
  else
    t

(* Display facts; for debugging *)

let display_facts (subst2, facts) =
  List.iter (fun (t,t') -> 
    Display.display_term [] t;
    print_string " -> ";
    Display.display_term [] t';
    print_newline()) subst2;
  List.iter (fun t -> Display.display_term [] t; print_newline()) facts


(* Add a fact to a set of true facts, and simplify it *)

exception Contradiction

let is_tuple t =
  match t.t_desc with
    FunApp(f, _) when (f.f_options land Settings.fopt_COMPOS) != 0 -> true
  | _ -> false

let is_pat_tuple = function
    PatTuple (f,_) -> true
  | _ -> false

let is_ok_subst2 (t1,t2) =
  match t1.t_desc with
    Var(b,l) -> (not (Terms.refers_to b t2))
  | _ -> false

(*
let refers_to_var b0 t =
  match t.t_desc with
    Var(b,l) -> (b == b0) || (List.exists (Terms.refers_to b0) l)
  | FunApp(f,l) -> false
  | TestE _ | FindE _ | LetE _ ->
      Parsing_helper.internal_error "If, find, and let should not occur in refers_to_var"
*)
let refers_to_var b0 t = 
  match t.t_desc with
    FunApp(f,_) when (f.f_options land Settings.fopt_DECOMPOS) != 0 -> true
  | _ -> Terms.refers_to b0 t

let rec orient t1 t2 = 
  match t1.t_desc, t2.t_desc with
    (Var(b,l), _) when
    (not (refers_to_var b t2)) && 
    (not (Terms.is_restr b)) -> true
  | (Var(b1,l1), Var(b2,l2)) when
    (b1 == b2) && (List.for_all2 orient l1 l2) -> true
  | _ -> false
  
let put_order orient_v t1 t2 =
  if orient_v != 0 then orient_v else
  begin
    if orient t1 t2 then 
      begin
	set_order_terms t1 t2;
	orient1 t1 t2
      end
    else if orient t2 t1 then
      begin
	set_order_terms t2 t1;
	orient1 t1 t2
      end
    else 
      0
  end
  

(* Small specialized prover for showing that 
    t = t{b0'/b0} implies b0 = b0' *)

let rec add_fact b0 b0' fact =
  match fact.t_desc with
    FunApp(f,[t1;t2]) when f.f_cat == Equal ->
      begin
      match (t1.t_desc, t2.t_desc) with
      	Var(b1,l1), Var(b2,l2) when (b1 == b0 && b2 == b0') || (b1 == b0' && b2 == b0) -> 
          (* TO DO add probability *)
	  raise Contradiction
      | (FunApp(f1,l1), FunApp(f2,l2)) when
	(f1.f_options land Settings.fopt_COMPOS) != 0 && f1 == f2 -> 
	  List.iter (simplif_add b0 b0') (List.map2 Terms.make_equal l1 l2)
      | _ -> ()
      end
  | FunApp(f,[t1;t2]) when f == Settings.f_and ->
      add_fact b0 b0' t1; add_fact b0 b0' t2
  | _ -> ()

and simplif_add b0 b0' fact =
  let fact' = apply_reds ([],[]) fact in
  add_fact b0 b0' fact' 

(* Find all variables that depend on a certain variable, provided
   these variables are not output (raises BadDep when some
   of these variables may be output)

   When tests depend on these variables, they must always yield
   the same result up to a negligible probability.
 *)

let whole_game = ref Nil

exception BadDep

let rec depends b0 t = 
  match t.t_desc with
    Var (b,l) -> 
      (b == b0) || (List.exists (depends b0) l)
  | FunApp(f,l) -> List.exists (depends b0) l
  | TestE(t1,t2,t3) -> 
      (depends b0 t2) || (depends b0 t3)
  | FindE(l0,t3,_) -> 
      (List.exists (fun (bl,def_list,t1,t2) ->
	depends b0 t2) l0) || 
      (depends b0 t3)
  | LetE(pat, t1, t2, topt) ->
      (depends b0 t2) ||
      (match topt with
	None -> false
      |	Some t3 -> depends b0 t3)


(* find_compos b t returns true when t = t{b'/b} implies b = b' with 
   overwhelming probability *)
let rec subst assql t =
  { t_desc = 
    begin
      match t.t_desc with
	Var(b,l) -> Var((try List.assq b (!assql) with Not_found ->
	  let r = Terms.new_binder b in
	  assql := (b,r)::(!assql);
	  r), List.map (subst assql) l)
      | FunApp(f,l) -> FunApp(f, List.map (subst assql) l)
      |	_ -> Parsing_helper.internal_error "If, find, and let should not occur in subst"
    end;
    t_type = t.t_type;
    t_occ = Terms.new_occ() }

let rec find_compos b t =
  match t.t_desc with
    Var(b',l) when b == b' -> true
  | FunApp(f,l) when (f.f_options land Settings.fopt_COMPOS) != 0 ->
      List.exists (find_compos b) l
  | _ ->
  let b' = Terms.new_binder b in
  let t' = subst (ref [(b, b')]) t in
  let f1 = Terms.make_equal t t' in
  try
    let _ = simplif_add b b' f1 in
    false
  with Contradiction -> 
    true
  (* A simpler version, that does not take into account collision statements 
let rec find_compos b t =
  match t.t_desc with
    Var(b',l) when (b' == b) && (not (List.exists (depends b) l)) -> true
  | FunApp(f,l) when (f.f_options land Settings.fopt_COMPOS) != 0 ->
      List.exists (find_compos b) l
  | _ -> false*)




let rec almost_indep_test seen_list t =
  match t.t_desc with
    FunApp(f,[t1;t2]) when (f == Settings.f_and) || (f == Settings.f_or) ->
      almost_indep_test seen_list t1;
      almost_indep_test seen_list t2
  | FunApp(f,[t1]) when (f == Settings.f_not) ->
      almost_indep_test seen_list t1
(* Be careful: do not use or-patterns with when: 
   If both patterns of the or succeed but the when clause fails for the 
   first one and succeeds for the second one, Caml considers that the
   match fails.
*)
  | FunApp(f,[t1;t2]) 
    when ((f.f_cat == Equal) || (f.f_cat == Diff)) && 
    (List.exists (fun b -> find_compos b t1) (!seen_list)) ->
      if List.exists (fun b -> depends b t2) (!seen_list) then
	raise BadDep
  | FunApp(f,[t2;t1]) 
    when ((f.f_cat == Equal) || (f.f_cat == Diff)) && 
    (List.exists (fun b -> find_compos b t1) (!seen_list)) ->
      if List.exists (fun b -> depends b t2) (!seen_list) then
	raise BadDep
  | _ -> if List.exists (fun b -> depends b t) (!seen_list) then 
	raise BadDep

let rec check_depend_term seen_list b0 t = 
  match t.t_desc with
    Var (b,l) -> 
      List.iter (check_depend_term seen_list b0) l
  | FunApp(f,l) -> List.iter (check_depend_term seen_list b0) l
  | TestE(t1,t2,t3) ->
      almost_indep_test seen_list t1;
      check_depend_term seen_list b0 t1;
      check_depend_term seen_list b0 t2;
      check_depend_term seen_list b0 t3
  | FindE(l0,t3,_) -> 
      List.iter (fun (bl,def_list,t1,t2) ->
	List.iter (fun (b, l) -> 
	  if List.exists (depends b0) l then raise BadDep;
	  List.iter (check_depend_term seen_list b0) l) def_list;
        almost_indep_test seen_list t1;
	check_depend_term seen_list b0 t1;
	check_depend_term seen_list b0 t2) l0;
      check_depend_term seen_list b0 t3
  | LetE(pat, t1, t2, topt) ->
      if depends b0 t1 then
	begin
	  if not (find_compos b0 t1) then raise BadDep;
	  check_depend_assign seen_list pat
	end;
      check_depend_pat seen_list b0 pat;
      check_depend_term seen_list b0 t1;
      check_depend_term seen_list b0 t2;
      match topt with
	None -> ()
      |	Some t3 -> check_depend_term seen_list b0 t3

and check_depend_assign seen_list pat =
  match pat with
    PatVar b ->
      if not (List.memq b (!seen_list)) then
	begin
	  seen_list := b :: (!seen_list);
	  check_depend_process seen_list b (!whole_game)
	end
  | _ -> raise BadDep

and check_depend_pat seen_list b0 = function
    PatVar b -> ()
  | PatTuple (f,l) -> List.iter (check_depend_pat seen_list b0) l
  | PatEqual t -> 
      if depends b0 t then 
	raise BadDep;
      check_depend_term seen_list b0 t

and check_depend_process seen_list b0 = function
    Nil -> ()
  | Par(p1,p2) -> 
      check_depend_process seen_list b0 p1;
      check_depend_process seen_list b0 p2
  | Repl(b,p) -> check_depend_process seen_list b0 p
  | Input((c,tl),pat,p) -> 
      if List.exists (depends b0) tl then raise BadDep;
      List.iter (check_depend_term seen_list b0) tl;
      check_depend_pat seen_list b0 pat;
      check_depend_oprocess seen_list b0 p

and check_depend_oprocess seen_list b0 = function
    Yield -> ()
  | Restr(b,p) -> check_depend_oprocess seen_list b0 p
  | Test(t,p1,p2) -> 
      almost_indep_test seen_list t;
      check_depend_term seen_list b0 t;
      check_depend_oprocess seen_list b0 p1;
      check_depend_oprocess seen_list b0 p2
  | Find(l0,p2,_) ->
      List.iter (fun (bl,def_list,t,p1) ->
	List.iter (fun (b, l) -> 
	  if List.exists (depends b0) l then raise BadDep;
	  List.iter (check_depend_term seen_list b0) l) def_list;
        almost_indep_test seen_list t;
	check_depend_term seen_list b0 t;
        check_depend_oprocess seen_list b0 p1) l0;
      check_depend_oprocess seen_list b0 p2
  | Output((c,tl),t2,p) ->
      if (List.exists (depends b0) tl) || (depends b0 t2) then raise BadDep;
      List.iter (check_depend_term seen_list b0) tl;
      check_depend_term seen_list b0 t2;
      check_depend_process seen_list b0 p
  | Let(pat,t,p1,p2) ->
      if depends b0 t then
	begin
	  if not (find_compos b0 t) then raise BadDep;
	  check_depend_assign seen_list pat
	end;
      check_depend_pat seen_list b0 pat;
      check_depend_term seen_list b0 t;
      check_depend_oprocess seen_list b0 p1;
      check_depend_oprocess seen_list b0 p2

let check_all_deps b0 =
  let seen_vars = ref [b0] in
  check_depend_process seen_vars b0 (!whole_game);
  !seen_vars

(* Memoizing version of check_all_deps *)

let success_check_all_deps = ref [] 
let failure_check_all_deps = ref []

let check_all_deps b0 =
  try 
    List.assq b0 (!success_check_all_deps)
  with Not_found -> 
    if List.memq b0 (!failure_check_all_deps) then raise BadDep
    else
      try 
	let res = check_all_deps b0 in
	success_check_all_deps := (b0, res) :: (!success_check_all_deps);
	res
      with BadDep ->
	failure_check_all_deps := b0 :: (!failure_check_all_deps);
	raise BadDep



let rec fully_defined simp_facts t =
  let t = try_no_var simp_facts t in  (* Risk of non-termination? *)
  match t.t_desc with
    FunApp(f,l) -> List.for_all (fully_defined simp_facts) l
  | Var(b,l) -> Terms.is_restr b
  | _ -> false

(* A try that does not work, for block ciphers

let check_no_dep simp_facts b0 t =
  let rec check_dep ty t =
    ((not (Terms.refers_to b0 t)) && (fully_defined simp_facts t)) ||
    (
    let t = try_no_var simp_facts t in
    match t.t_desc with
      FunApp(f, l) when (f.f_options land Settings.fopt_COMPOS) != 0 ->
	(Terms.is_subtype t.t_type ty) &&
	(List.exists (fun t' ->
	  Terms.is_large t'.t_type && check_dep t'.t_type t) l)
    | _ -> 
	false
	  )
  in
  (check_dep b0.btype t) || 
  (try 
    let vlist = check_all_deps b0 in
    let rec check_dep2 ty t =
      (not (List.exists (fun b -> Terms.refers_to b t) vlist)) ||
      (
      let t = try_no_var simp_facts t in
      match t.t_desc with
	FunApp(f, l) when (f.f_options land Settings.fopt_COMPOS) != 0 ->
	  (Terms.is_subtype t.t_type ty) &&
	  (List.exists (fun t' ->
	    Terms.is_large t'.t_type && check_dep2 t'.t_type t) l)
      | _ -> 
	  false
	    )
    in
    check_dep2 b0.btype t
  with BadDep ->
    false)
*)

let rec try_no_var_rec simp_facts t =
  let t' = try_no_var simp_facts t in(* Risk of non-termination? *)
  match t'.t_desc with
    FunApp(f,l) -> 
      { t_desc = FunApp(f, List.map (try_no_var_rec simp_facts) l);
	t_occ = t'.t_occ;
	t_type = t'.t_type }
  | _ -> t'

let rec dependency_collision_rec simp_facts t1 t2 t =
  match t.t_desc with
    Var(b,l) when (Terms.is_restr b) && (Terms.is_large b.btype) && (find_compos b t1) ->
      ((not (Terms.refers_to b t2)) && (fully_defined simp_facts t2)) ||
      (try 
	let vlist = check_all_deps b in
	not (List.exists (fun b' -> Terms.refers_to b' t2) vlist)
      with BadDep ->
	false)
  | FunApp(f,l) ->
      List.exists (dependency_collision_rec simp_facts t1 t2) l
  | _ -> false

let dependency_collision simp_facts t1 t2 = 
  let t1' = try_no_var_rec simp_facts t1 in
  dependency_collision_rec simp_facts t1' t2 t1'

let rec add_fact ((subst2, facts) as simp_facts) fact =
  let fact' = try_no_var simp_facts fact in
  match fact'.t_desc with
    FunApp(f,[t1;t2]) when f.f_cat == Equal ->
      let t1' = try_no_var simp_facts t1 in
      let t2' = try_no_var simp_facts t2 in
      if Terms.equal_terms t1' t2' then simp_facts else
      let orient_v = orient1 t1' t2' in
      begin
      match (t1'.t_desc, t2'.t_desc) with
	(Var(b,l), _) when (orient_v = 1) &&
	(not (refers_to_var b t2')) && 
	(List.for_all2 Terms.equal_terms l b.args_at_creation) &&
	(not (Terms.is_restr b)) ->
	  subst_simplify2 simp_facts (t1',t2')
      | (_, Var(b,l)) when (orient_v = -1) &&
	(not (refers_to_var b t1')) && 
	(List.for_all2 Terms.equal_terms l b.args_at_creation) &&
	(not (Terms.is_restr b)) ->
	  subst_simplify2 simp_facts (t2',t1')
      | (FunApp(f1,l1), FunApp(f2,l2)) when
	f1.f_cat == Tuple && f2.f_cat == Tuple && f1 != f2 -> 
	  raise Contradiction
      | (FunApp(f1,l1), FunApp(f2,l2)) when
	(f1.f_options land Settings.fopt_COMPOS) != 0 && f1 == f2 -> 
	  simplif_add_list simp_facts (List.map2 Terms.make_equal l1 l2)
      | (Var(b1,l1), Var(b2,l2)) when
	(Terms.is_restr b1) &&
	Terms.is_large b1.btype && b1 == b2 ->
          (* TO DO add_proba (Div(Cst 1, Card b1.btype)); * number applications *)
	  simplif_add_list simp_facts (List.map2 Terms.make_equal l1 l2)
      | (Var(b1,l1), Var(b2,l2)) when
	(Terms.is_restr b1) && (Terms.is_restr b2) &&
	(Terms.is_large b1.btype || Terms.is_large b2.btype) &&
	b1 != b2 ->
	  raise Contradiction
          (* TO DO add probability *)
      | (_,_) when (!Settings.redo_dependency_collision) && (dependency_collision simp_facts t1' t2') ->
	  raise Contradiction
          (* TO DO add probability *)
      | (_,_) when (!Settings.redo_dependency_collision) && (dependency_collision simp_facts t2' t1') ->
	  raise Contradiction
          (* TO DO add probability *)
      | (FunApp(f1,[]), FunApp(f2,[]) ) when
	f1 != f2 && (!Settings.diff_constants) ->
	  raise Contradiction
	  (* Different constants are different *)
      | _ -> 
	  let orient_v = put_order orient_v t1' t2' in
	  if orient_v = 1 then 
	    subst_simplify2 simp_facts (t1',t2')
	  else if orient_v = -1 then
	    subst_simplify2 simp_facts (t2',t1')
	  else
	    (subst2, fact'::facts)
      end
  | FunApp(f,[t1;t2]) when f == Settings.f_and ->
      simplif_add (add_fact simp_facts t1) t2
  | FunApp(f,[t1;t2]) when f.f_cat == Diff ->
      let t1' = try_no_var simp_facts t1 in
      let t2' = try_no_var simp_facts t2 in
      begin
      try
	unify_terms simp_facts t1' t2';
	raise Contradiction
      with Terms.NoMatch ->
	match (t1'.t_desc, t2'.t_desc) with
	  (FunApp(f1,l1), FunApp(f2,l2)) when
	  f1.f_cat == Tuple && f2.f_cat == Tuple && f1 != f2 -> 
	    simp_facts
	| (Var(b1,l1), Var(b2,l2)) when
	  (Terms.is_restr b1) && (Terms.is_restr b2) &&
	  (Terms.is_large b1.btype || Terms.is_large b2.btype) &&
	  b1 != b2 ->
	    simp_facts
            (* TO DO add probability *)
	| (_,_) when (!Settings.redo_dependency_collision) && (dependency_collision simp_facts t1' t2') ->
	    simp_facts
            (* TO DO add probability *)
	| (_,_) when (!Settings.redo_dependency_collision) && (dependency_collision simp_facts t2' t1') ->
	    simp_facts
            (* TO DO add probability *)
	| (FunApp(f1,[]), FunApp(f2,[])) when
	  f1 != f2 && (!Settings.diff_constants) ->
	    simp_facts
	    (* Different constants are different *)
	| _ -> (subst2, fact'::facts)
      end
  | _ -> 
      if Terms.is_false fact' then raise Contradiction else
      if Terms.is_true fact' then simp_facts else
      (subst2, fact'::facts)

(* OLD VERSION faster on some examples, but more likely not to terminate

and subst_simplify2 (subst, subst2, facts) link =
  let subst' = List.map (fun (b,t) -> (b,apply_reds(apply_subst [link] t))) subst in
  let subst2' = List.map (fun (t,t') -> (apply_reds(apply_subst [link] t),apply_reds(apply_subst [link] t'))) subst2 in
  let (subst2'', not_subst2) = List.partition is_ok_subst2 subst2' in
  let not_subst2_facts = List.map (fun (t,t') -> Terms.make_equal t t') not_subst2 in
  simplif_add_list (subst',link :: subst2'',[]) (not_subst2_facts @ facts)

*)

and subst_simplify2 (subst2, facts) link =
  let subst2'' = ref [] in
  let not_subst2_facts = ref [] in
  List.iter (fun (t,t') ->
    reduced_subst := false;
    let t1 = apply_subst1 t link in
    let t1' = apply_subst1 t' link in
    if !reduced_subst then
      not_subst2_facts := (Terms.make_equal t1 t1') :: (!not_subst2_facts)
    else
      subst2'' := (t,t') :: (!subst2'')
    ) subst2;
  simplif_add_list (link :: (!subst2''),[]) ((!not_subst2_facts) @ facts)

and simplif_add ((subst2, facts) as simp_facts) fact =
  let fact' = apply_reds simp_facts fact in
  add_fact simp_facts fact'

and simplif_add_list simp_facts = function
    [] -> simp_facts
  | (a::l) -> simplif_add_list (simplif_add simp_facts a) l

(* Put a term in the form or (and (...)) *)

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

let make_and_distr t1 t2 =
  if (Terms.is_false t1) || (Terms.is_false t2) then Terms.make_false() else
  if Terms.is_true t1 then t2 else
  if Terms.is_true t2 then t1 else
  (* If t1 or t2 is "or", distribute *)
  make_and2 (get_or t1) (get_or t2)

let rec or_and_form t =
  match t.t_desc with
    FunApp(f, [t1;t2]) when f == Settings.f_and ->
      make_and_distr (or_and_form t1) (or_and_form t2)
  | FunApp(f, [t1;t2]) when f == Settings.f_or ->
      Terms.make_or (or_and_form t1) (or_and_form t2)
  | _ -> t

(* Simplify a term knowing some true facts *)

let rec simplify_term_rec simp_facts t =
  let t' = try_no_var simp_facts t in
  match t'.t_desc with
    FunApp(f, [t1;t2]) when f == Settings.f_and ->
      Terms.make_and (simplify_term_rec simp_facts t1) (simplify_term_rec simp_facts t2)
  | FunApp(f, [t1;t2]) when f == Settings.f_or ->
      Terms.make_or (simplify_term_rec simp_facts t1) (simplify_term_rec simp_facts t2)
  | FunApp(f, [t1;t2]) when f.f_cat == Equal ->
      let t1' = try_no_var simp_facts t1 in
      let t2' = try_no_var simp_facts t2 in
      if Terms.equal_terms t1' t2' then Terms.make_true() else
      begin
	match t1'.t_desc, t2'.t_desc with
	  (FunApp(f1,l1), FunApp(f2,l2)) when
	  f1.f_cat == Tuple && f2.f_cat == Tuple && f1 != f2 -> 
	    Terms.make_false()
	| (FunApp(f1,l1), FunApp(f2,l2)) when
	  (f1.f_options land Settings.fopt_COMPOS) != 0 && f1 == f2 -> 
	    Terms.make_and_list (List.map2 (fun t1 t2 -> simplify_term_rec simp_facts (Terms.make_equal t1 t2)) l1 l2)
	| (Var(b1,l1), Var(b2,l2)) when
	  (Terms.is_restr b1) &&
	  Terms.is_large b1.btype && b1 == b2 ->
          (* TO DO add_proba (Div(Cst 1, Card b1.btype)); * number applications *)
	    Terms.make_and_list (List.map2 (fun t1 t2 -> simplify_term_rec simp_facts (Terms.make_equal t1 t2)) l1 l2)
	| (Var(b1,l1), Var(b2,l2)) when
	  (Terms.is_restr b1) && (Terms.is_restr b2) &&
	  (Terms.is_large b1.btype || Terms.is_large b2.btype) &&
	  b1 != b2 ->
	    Terms.make_false()
          (* TO DO add probability *)
	| (_,_) when dependency_collision simp_facts t1' t2' ->
	    Terms.make_false()
          (* TO DO add probability *)
	| (_,_) when dependency_collision simp_facts t2' t1' ->
	    Terms.make_false()
          (* TO DO add probability *)
	| (FunApp(f1,[]), FunApp(f2,[])) when
	  f1 != f2 && (!Settings.diff_constants) ->
	    Terms.make_false()
	(* Different constants are different *)
	| _ -> t
      end
  | FunApp(f, [t1;t2]) when f.f_cat == Diff ->
      let t1' = try_no_var simp_facts t1 in
      let t2' = try_no_var simp_facts t2 in
      if Terms.equal_terms t1' t2' then Terms.make_false() else
      begin
	match t1'.t_desc, t2'.t_desc with
	  (FunApp(f1,l1), FunApp(f2,l2)) when
	  f1.f_cat == Tuple && f2.f_cat == Tuple && f1 != f2 -> 
	    Terms.make_true()
	| (FunApp(f1,l1), FunApp(f2,l2)) when
	  (f1.f_options land Settings.fopt_COMPOS) != 0 && f1 == f2 -> 
	    Terms.make_or_list (List.map2 (fun t1 t2 -> simplify_term_rec simp_facts (Terms.make_diff t1 t2)) l1 l2)
	| (Var(b1,l1), Var(b2,l2)) when
	  (Terms.is_restr b1) &&
	  Terms.is_large b1.btype && b1 == b2 ->
      (* TO DO add_proba (Div(Cst 1, Card b1.btype)); * number applications *)
	    Terms.make_or_list (List.map2 (fun t1 t2 -> simplify_term_rec simp_facts (Terms.make_diff t1 t2)) l1 l2)
	| (Var(b1,l1), Var(b2,l2)) when
	  (Terms.is_restr b1) && (Terms.is_restr b2) &&
	  (Terms.is_large b1.btype || Terms.is_large b2.btype) &&
	  b1 != b2 ->
	    Terms.make_true()
            (* TO DO add probability *)
	| (_,_) when dependency_collision simp_facts t1' t2' ->
	    Terms.make_true()
            (* TO DO add probability *)
	| (_,_) when dependency_collision simp_facts t2' t1' ->
	    Terms.make_true()
            (* TO DO add probability *)
	| (FunApp(f1,[]), FunApp(f2,[])) when
	  f1 != f2 && (!Settings.diff_constants) ->
	    Terms.make_true()
	    (* Different constants are different *)
	| _ -> t
      end
  | _ -> t

let simplify_term keep_tuple ((subst2, facts) as simp_facts) t = 
  let t' = 
    if keep_tuple then 
      try_no_var simp_facts t 
    else
      t
  in
  let t'' = apply_reds simp_facts t' in
  let t''' = 
    if t''.t_type == Settings.t_bool then
      simplify_term_rec simp_facts t''
    else
      t''
  in
  if !Settings.minimal_simplifications then
    begin
      if Terms.is_true t''' || Terms.is_false t''' || (not (Terms.equal_terms t' t''')) ||
         (keep_tuple && is_tuple t''' && not (is_tuple t)) then
	begin
	  if not (Terms.is_true t || Terms.is_false t) then Transform.changed := true;
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
(*
let simplify_term k s t =
  print_string "Simplifying "; Display.display_term [] t;
  print_string " knowing\n";
  display_facts s; 
  print_newline();
  let res = simplify_term k s t in
  print_string "Simplify done "; Display.display_term [] res;
  print_newline();
  res
*)
(* Simplify pattern *)

let rec simplify_pat true_facts = function
    (PatVar b) as pat -> pat
  | PatTuple (f,l) -> PatTuple (f,List.map (simplify_pat true_facts) l)
  | PatEqual t -> PatEqual (simplify_term false true_facts t)

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
      let l'' = intersect eqtest l l' in
      if List.exists (eqtest a') l then 
	a'::l'' 
      else
	l''

let rec intersect_list eqtest = function
    [] -> raise Contradiction
  | [a] -> a
  | (a::l) -> intersect eqtest a (intersect_list eqtest l)

let rec check_non_nested seen_fsymb seen_binders t =
  match t.t_desc with
    Var(b,l) ->
      (not (List.memq b seen_binders)) &&
      (List.for_all (check_non_nested seen_fsymb (b::seen_binders)) l)
  | FunApp(f,l) ->
      (not (List.memq f seen_fsymb)) &&
      (List.for_all (check_non_nested (f::seen_fsymb) seen_binders) l)
  | _ -> Parsing_helper.internal_error "If, find, let should have been expanded"

let rec add_facts fact_accu seen_refs (b,l) =
  if (List.for_all (check_non_nested [] [b]) l) &&
    (not (List.exists (Terms.equal_binderref (b,l)) (!seen_refs))) then
    begin
      seen_refs := (b,l) :: (!seen_refs);
      let true_facts_at_def = intersect_list Terms.equal_terms (List.map (fun n -> n.true_facts_at_def) b.def) in
      let def_vars_at_def = intersect_list Terms.equal_binderref (List.map (fun n -> n.def_vars_at_def) b.def) in
      let bindex = List.map Terms.binder_from_term b.args_at_creation in
      (* add facts *)
      List.iter (fun f -> 
        (* b.args_at_creation -> l *)
	let f = Terms.subst bindex l f in
	if not (List.memq f (!fact_accu)) then
	  fact_accu := f :: (!fact_accu)) true_facts_at_def;
      (* recursive call *)
      List.iter (fun (b',l') ->
        (* b.args_at_creation -> l *)
	add_facts fact_accu seen_refs (b', List.map (Terms.subst bindex l) l')
	  ) def_vars_at_def
    end
      
let facts_from_defined def_list =
  let fact_accu = ref [] in
  let seen_refs = ref [] in
  List.iter (add_facts fact_accu seen_refs) def_list;
  !fact_accu

(* Reduce the definition list of a find, taking into account already
   defined variables *)

let rec close_node accu n =
  List.iter (fun b' ->
    accu := ((b',b'.args_at_creation))::(!accu)
      ) n.binders;
  if n.above_node != n then
    close_node accu n.above_node

let get_def_vars_above n =
  let accu = ref [] in
  close_node accu n; 
  !accu

let reduced_def_list def_node_opt def_list =
  match def_node_opt with
    Some def_node ->
      let def_vars = get_def_vars_above def_node in 
      List.filter (fun br -> not (List.exists (Terms.equal_binderref br) def_vars)) def_list
  | None -> def_list

(* More precise solution, but must not be used to remove elements
of def_list, just to test whether all elements of def_list are defined,
in which case for a "find ... defined(def_list) && M", if M is true,
the else branch can be removed. -- Useful to remove the "else" branches
generated by applying the security of a Diffie-Hellman key agreement,
for example. 
Removing useful elements of def_list breaks the code of SSArename *)

let rec add_def_vars def_vars_accu seen_refs (b,l) =
  if (List.for_all (check_non_nested [] [b]) l) &&
    (not (List.exists (Terms.equal_binderref (b,l)) (!seen_refs))) then
    begin
      seen_refs := (b,l) :: (!seen_refs);
      let def_vars_above_def = intersect_list Terms.equal_binderref (List.map get_def_vars_above b.def) in
      let def_vars_at_def = intersect_list Terms.equal_binderref (List.map (fun n -> n.def_vars_at_def) b.def) in
      (* b.args_at_creation -> l *)
      let def_vars_above_def = (b,l)::(List.map (fun (b',l') ->
	(b', List.map (Terms.subst (List.map Terms.binder_from_term b.args_at_creation) l) l')) def_vars_above_def)
      in
      let def_vars_at_def = List.map (fun (b',l') ->
	(b', List.map (Terms.subst (List.map Terms.binder_from_term b.args_at_creation) l) l')) def_vars_at_def 
      in
      (* add facts *)
      List.iter (fun br -> 
	if not (List.exists (Terms.equal_binderref br) (!def_vars_accu)) then
	  def_vars_accu := br :: (!def_vars_accu)) def_vars_above_def;
      (* recursive call *)
      List.iter (add_def_vars def_vars_accu seen_refs) def_vars_at_def
    end

let get_def_vars_at n =
  let def_vars_accu = ref (get_def_vars_above n) in
  let seen_refs = ref [] in
  List.iter (add_def_vars def_vars_accu seen_refs) n.def_vars_at_def;
  !def_vars_accu

let is_already_defined_def_list def_node_opt def_list =
  match def_node_opt with
    Some def_node ->
      let def_vars = get_def_vars_at def_node in 
      List.for_all (fun br -> List.exists (Terms.equal_binderref br) def_vars) def_list
  | None -> def_list == []

let rec simplify_process true_facts = function
    Nil -> Nil
  | Par(p1,p2) -> Par(simplify_process true_facts p1,
		      simplify_process true_facts p2)
  | Repl(b,p) -> Repl(b, simplify_process true_facts p)
  | Input((c,tl), pat, p) ->
      Input((c, List.map (simplify_term false true_facts) tl), 
	    simplify_pat true_facts pat, 
	    simplify_oprocess true_facts p)


and simplify_oprocess true_facts = function
    Yield -> Yield
  | Restr(b,p) -> Restr(b, simplify_oprocess true_facts p)
  | Test(t, p1, p2) ->
      begin
      let t' = simplify_term false true_facts t in
      let t_or_and = or_and_form t' in
      try
	let p2' = simplify_oprocess (simplif_add true_facts (Terms.make_not t')) p2 in
	simplify_if true_facts p1 p2' t_or_and
      with Contradiction ->
	Transform.changed := true;
	simplify_oprocess true_facts p1
      end
  | Find(l0, p2, def_node_opt) ->
      begin
      match l0 with
	[([],def_list,t1,p1)] when reduced_def_list (!def_node_opt) def_list = [] -> 
	  Transform.changed := true;
	  simplify_oprocess true_facts (Test(t1,p1,p2))
      |	_ -> 
      let always_then = ref false in
      let p2' = simplify_oprocess true_facts p2 in
      let rec simplify_findl = function
	  [] -> []
	| ((bl, def_list, t, p1)::l) ->
	    let l' = simplify_findl l in
	    try
	      let true_facts' = simplif_add_list true_facts (facts_from_defined def_list) in
	      let def_list' = reduced_def_list (!def_node_opt) def_list in
	      let t' = simplify_term false true_facts' t in
	      if is_already_defined_def_list (!def_node_opt) def_list' then
		begin
		  try
		    ignore(simplif_add true_facts (Terms.make_not t'))
		  with Contradiction -> 
		    always_then := true
		end;
	      let tf' = simplif_add true_facts' t' in
	      (bl, def_list', t', simplify_oprocess tf' p1) :: l'
	      (*let t_or_and = or_and_form t' in
	      simplify_find true_facts' l' bl def_list' t_or_and p1 *)
	    with Contradiction ->
	      Transform.changed := true;
	      l'
      in
      let l0' = simplify_findl l0 in
      if l0' == [] then
	begin
	  Transform.changed := true;
	  p2'
	end
      else if !always_then then
	Find(l0',Yield, ref None)
      else
	Find(l0', p2', ref None)
      end
  | Let(pat, t, p1, p2) ->
      let t' = simplify_term (is_pat_tuple pat) true_facts t in
      let p2' = simplify_oprocess true_facts p2 in
      simplify_let true_facts p1 p2' t' pat
  | Output((c,tl),t2,p) ->
      Output((c, List.map (simplify_term false true_facts) tl), 
	     simplify_term false true_facts t2,
	     simplify_process true_facts p)


and simplify_if true_facts ptrue pfalse t' =
  match t'.t_desc with
    FunApp(f, []) when f == Settings.c_false -> 
      Transform.changed := true;
      pfalse
  | FunApp(f, []) when f == Settings.c_true -> 
      Transform.changed := true;
      simplify_oprocess true_facts ptrue
  | FunApp(f, [t1; t2]) when f == Settings.f_or ->
      Transform.changed := true;
      simplify_if true_facts ptrue (simplify_if true_facts ptrue pfalse t2) t1
  | _ -> 
      try
	let ptrue' =  simplify_oprocess (simplif_add true_facts t') ptrue in
	if (ptrue' == Yield) && (pfalse == Yield) then 
	  begin
	    Transform.changed := true;
	    Yield
	  end
	else
	  Test(t', ptrue', pfalse)
      with Contradiction ->
	Transform.changed := true;
	pfalse

(*
and simplify_find true_facts accu bl def_list t' ptrue = 
  match t'.t_desc with
    FunApp(f, []) when f == Settings.c_false -> 
      Transform.changed := true;
      accu
  | FunApp(f, [t1; t2]) when f == Settings.f_or ->
      Transform.changed := true;
      simplify_find true_facts (simplify_find true_facts accu bl def_list t2 ptrue) bl def_list t1 ptrue
  | _ -> 
      try
	let tf' = simplif_add true_facts t' in
	(bl, def_list, t', simplify_oprocess tf' ptrue) :: accu
      with Contradiction ->
	Transform.changed := true;
	accu
*)

and simplify_let true_facts ptrue pfalse t' = function
    (PatVar b) as pat -> 
      if pfalse != Yield then Transform.changed := true;
      Let(pat, t', simplify_oprocess (simplif_add true_facts (Terms.make_equal 
	(Terms.term_from_binder b) t')) ptrue, Yield)
  | PatEqual t ->
      Transform.changed := true;
      simplify_oprocess true_facts (Test(Terms.make_equal t t', ptrue, pfalse))
  | (PatTuple (f,l)) as pat ->
      begin
	try 
	  let res = simplify_oprocess true_facts 
	      (Terms.put_lets Terms.make_let_proc l (Terms.split_term f t') ptrue pfalse)
	  in
	  Transform.changed := true;
	  res
	with 
	  Not_found -> 
	    begin
	      try
		Let(pat, t', simplify_oprocess (simplif_add true_facts (Terms.make_equal 
		      (Terms.term_from_pat pat) t')) ptrue, pfalse)
	      with Contradiction ->
		Transform.changed := true;
		pfalse
	    end
	| Terms.Impossible -> 
	    Transform.changed := true;
	    pfalse
      end

let rec simplify_main1 iter process =
  let tmp_changed = !Transform.changed in
  Transform.changed := false;
  Terms.build_def_process process;
  def_order process;
  let p' = simplify_process ([],[]) process in
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
  whole_game := process;
  success_check_all_deps := [];
  failure_check_all_deps := [];
  (simplify_main1 (!Settings.max_iter_simplif) process, !proba)


(* Show that elements of the array b at different indexes are always
   different (up to negligible probability).
   This is useful for showing semantic security of a key.
 *)


let make_indexes b =
  List.map (fun t -> 
    let v = Terms.new_binder (Terms.binder_from_term t) in
    let rec def_node = { above_node = def_node; binders = [];
			 true_facts_at_def = []; def_vars_at_def = []; 
			 definition = DNone }
    in
    v.def <- [{ above_node = def_node; binders = [v];
		true_facts_at_def = []; def_vars_at_def = []; 
		definition = DNone }];
    Terms.term_from_binder v) b.args_at_creation

let collect_facts accu (def,bindex,index) =
  let fact_accu = ref accu in
  let seen_refs = ref [] in
  (* add facts *)
  List.iter (fun f -> 
    let f = Terms.subst bindex index f in
    if not (List.memq f (!fact_accu)) then
      fact_accu := f :: (!fact_accu)) def.true_facts_at_def;
  (* recursive call *)
  List.iter (fun (b',l') ->
    add_facts fact_accu seen_refs (b', List.map (Terms.subst bindex index) l')
      ) def.def_vars_at_def;
  (* Result *)
  !fact_accu

let check_distinct b process =
  Terms.build_def_process process;
  def_order process;
  let index1 = make_indexes b in
  let index2 = make_indexes b in
  let diff_index = Terms.make_or_list (List.map2 Terms.make_diff index1 index2) in
  let bindex = List.map Terms.binder_from_term b.args_at_creation in
  let d1withfacts = List.map (fun d -> d,collect_facts [] (d,bindex,index1)) b.def in
  let d2withfacts = List.map (fun d -> d,collect_facts [] (d,bindex,index2)) b.def in
  List.for_all (fun (d1,d1facts) ->
    List.for_all (fun (d2,d2facts) ->
      match d1.definition, d2.definition with
	DProcess (Restr _), DProcess (Restr _) -> true
      | DProcess (Restr _), 
	    (DProcess (Let(PatVar _,{ t_desc = Var(b',l) },_,_))
	    |DTerm { t_desc = LetE(PatVar _, { t_desc = Var(b',l) },_,_) }) ->
		if not (Terms.is_restr b') then
		  Parsing_helper.internal_error "restriction should be checked when testing secrecy";
		(b != b') || 
		(
		try
		  let eq_b = Terms.make_and_list 
		      (List.map2 Terms.make_equal index1 (List.map (Terms.subst bindex index2) l))
		  in
		  let facts1 = diff_index :: eq_b :: d1facts @ d2facts in
		  let facts = simplif_add_list ([],[]) facts1 in
		  false
		with Contradiction -> true
		    )
      |	(DProcess (Let(PatVar _,{ t_desc = Var(b',l) },_,_))
        |DTerm { t_desc = LetE(PatVar _, { t_desc = Var(b',l) },_,_) }), DProcess (Restr _) ->
	  true (* The symmetric case will be checked by the previous pattern *)
      |	(DProcess (Let(PatVar _,{ t_desc = Var(b1',l1) },_,_))
        |DTerm { t_desc = LetE(PatVar _, { t_desc = Var(b1',l1) },_,_) }),
	  (DProcess (Let(PatVar _,{ t_desc = Var(b2',l2) },_,_))
          |DTerm { t_desc = LetE(PatVar _, { t_desc = Var(b2',l2) },_,_) }) ->
		if not ((Terms.is_restr b1') && (Terms.is_restr b2')) then
		  Parsing_helper.internal_error "restriction should be checked when testing secrecy";
		(b1' != b2') || 
		(
		try
		  let eq_b = Terms.make_and_list 
		      (List.map2 Terms.make_equal 
			 (List.map (Terms.subst bindex index1) l1) 
			 (List.map (Terms.subst bindex index2) l2))
		  in
		  let facts1 = diff_index :: eq_b :: d1facts @ d2facts in
		  let facts = simplif_add_list ([],[]) facts1 in
		  false
		with Contradiction -> true
		    )
      | _ -> 
	  Parsing_helper.internal_error "definition cases should be checked when testing secrecy"
	  ) d2withfacts
      ) d1withfacts



        (*
        print_string "Facts for check_distinct 1:\n";
        List.iter (fun t -> Display.display_term [] t; print_newline()) facts1;

        print_string "Facts for check_distinct 2:\n";
        display_facts facts;
        *)
