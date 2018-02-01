open Types
open Parsing_helper

let allow_array_ref = ref false

let cur_branch_var_list = ref []
    (* List of pairs (variable in current branch, variable in else branch)
       for variables with array references, a single definition, and
       a different name in different branches *)

let all_branches_var_list = ref []
    (* All lists cur_branch_var_list for the various branches *)

let var_not_needed = ref []
    (* Variables that must not be needed in the final game *)

let has_array_ref b =
  Terms.has_array_ref_non_exclude b || Transform.occurs_in_queries b

let merge_var next_f map b b' =
  if b == b' then
    next_f map
  else if b.btype != b'.btype then
    false
  else if (not (has_array_ref b)) && (not (has_array_ref b')) then
    next_f ((b,b')::map)
  else if (!allow_array_ref) && (has_array_ref b) && (has_array_ref b') && (b.count_def == 1) && (b'.count_def == 1) then
    (* TO DO if allow_array_ref is false and the rest is true, I could advise 
       MergeBranches(...). Or better: do not check allow_array_ref here;
       in the end of equal.../can_merge... check whether cur_branch_var_list
       is empty. If yes, succeed. If no, fail with advise MergeBranches(...).
       Difficulty: the occurrence of the branches to merge may be
       unusable (not unique)... *)
    begin
      cur_branch_var_list := (b,b') :: (!cur_branch_var_list);
      next_f ((b,b')::map)
    end
  else 
    false

let rec merge_var_list next_f map bl bl' =
  match bl,bl' with
    [], [] -> next_f map
  | [], _ | _, [] -> false
  | (b::bl, b'::bl') ->
      merge_var (fun map' -> merge_var_list next_f map' bl bl') map b b'
      

let eq_oblig = ref []

let equal_terms_ren map t t' = 
  if t.t_type != t'.t_type then false else
  let mapped_t = Terms.subst3 (List.map (fun (b,b') -> (b, Terms.term_from_binder b')) map) t in
  (* We test the equality of processes by first testing that
     they have the same structure, and collecting all needed 
     equalities of terms in eq_oblig. When the processes have
     the same structure, we will later verify that the terms are
     indeed equal. This is because testing equality of terms
     is more costly. *)
  eq_oblig := (mapped_t, t') :: (!eq_oblig);
  true


let eq_binderref map br br' = 
  equal_terms_ren map (Terms.term_from_binderref br) (Terms.term_from_binderref br')
  
let eq_deflist map dl dl' = 
  Terms.equal_lists (eq_binderref map) dl dl'
(* TO DO because equalities are collected and tested later, "List.exists"
does not play its role and always takes the first element of the list, which
is not what we want. For now, I use a stronger test that requires the elements
of dl and dl' to be in the same order.
  (List.for_all (fun br' -> List.exists (fun br -> eq_binderref map br br') dl) dl') &&
  (List.for_all (fun br -> List.exists (fun br' -> eq_binderref map br br') dl') dl) 
*)

let eq_otheruses map o o' =
  match o, o' with
    None, None -> true
  | Some { args = l; res = r }, Some { args = l'; res = r' } ->
      (eq_deflist map l l') && (eq_binderref map r r')
  | _ -> false

let rec equal_pat_ren map map_ref pat pat' =
  match pat, pat' with
    PatVar b, PatVar b' ->
      merge_var (fun map' -> map_ref := map'; true) (!map_ref) b b'
  | PatTuple(f,l), PatTuple(f',l') ->
      (f == f') && (List.for_all2 (equal_pat_ren map map_ref) l l')
  | PatEqual t, PatEqual t' -> 
      equal_terms_ren map t t' 
  | _ -> false

let rec equal_find_cond map t t' =
  match t.t_desc, t'.t_desc with
    (Var _ | FunApp _), (Var _ | FunApp _) -> equal_terms_ren map t t'
  | TestE(t1,t2,t3), TestE(t1',t2',t3') ->
      (equal_terms_ren map t1 t1') &&
      (equal_find_cond map t2 t2') &&
      (equal_find_cond map t3 t3')
  | FindE(l0,t3,find_info), FindE(l0',t3',find_info') ->
      (equal_find_cond map t3 t3') && (List.length l0 == List.length l0') &&
      (find_info = find_info') (* TO DO change this test if find_info structure becomes richer *) &&
      (List.for_all2 (fun (bl, def_list, otheruses, t, t1)
	  (bl', def_list', otheruses', t', t1') ->
	    merge_var_list (fun map' -> 
	      (eq_deflist map' def_list def_list') &&
	      (eq_otheruses map' otheruses otheruses') &&
	      (equal_find_cond map' t t') &&
	      (equal_find_cond map' t1 t1')) map bl bl'
	      ) l0 l0')
  | LetE(pat,t1,t2,topt),LetE(pat',t1',t2',topt') ->
      (equal_terms_ren map t1 t1') &&
      (match topt, topt' with
	None, None -> true
      |	Some t3, Some t3' -> equal_find_cond map t3 t3'
      |	_ -> false) &&
      (let map_ref = ref map in
      let eq_pat = equal_pat_ren map map_ref pat pat' in
      eq_pat && (equal_find_cond (!map_ref) t2 t2'))
  | ResE(b,t), ResE(b',t') ->
      merge_var (fun map' -> equal_find_cond map' t t') map b b'
  | EventE _, EventE _ ->
      Parsing_helper.internal_error "Event should have been expanded"
  | _ -> false

let rec equal_process map p p' =
  match p.i_desc, p'.i_desc with
    Nil, Nil -> true
  | Par(p1,p2), Par(p1',p2') -> 
      (equal_process map p1 p1') && (equal_process map p2 p2')
  | Repl(b,p), Repl(b',p') -> 
      if b == b' then
	equal_process map p p'
      else
	(b.btype == b'.btype) && (equal_process ((b,b')::map) p p')
  | Input((c,tl), pat, p), Input((c',tl'), pat', p') ->
      (c == c') && 
      (Terms.equal_lists (equal_terms_ren map) tl tl') &&
      (let map_ref = ref map in
      let eq_pat = equal_pat_ren map map_ref pat pat' in
      eq_pat && (equal_oprocess (!map_ref) p p'))
  | _ -> false

and equal_oprocess map p p' =
  match p.p_desc, p'.p_desc with
    Yield, Yield -> true
  | Restr(b,p), Restr(b',p') ->
      merge_var (fun map' -> equal_oprocess map' p p') map b b'
  | Test(t,p1,p2), Test(t',p1',p2') ->
      (equal_terms_ren map t t') &&
      (equal_oprocess map p1 p1') &&
      (equal_oprocess map p2 p2')
  | Let(pat, t, p1, p2), Let(pat', t', p1', p2') ->
      (equal_terms_ren map t t') &&
      (equal_oprocess map p2 p2') &&
      (let map_ref = ref map in
      let eq_pat = equal_pat_ren map map_ref pat pat' in
       eq_pat && (equal_oprocess (!map_ref) p1 p1'))
  | Output((c,tl),t2,p), Output((c',tl'),t2',p') ->
      (c == c') && 
      (Terms.equal_lists (equal_terms_ren map) tl tl') &&
      (equal_terms_ren map t2 t2') &&
      (equal_process map p p')
  | EventP(t,p), EventP(t',p') ->
      (equal_terms_ren map t t') &&
      (equal_oprocess map p p')
  | Find(l,p, find_info), Find(l',p', find_info') ->
      (equal_oprocess map p p') && (List.length l == List.length l') &&
      (find_info = find_info') (* TO DO change this test if find_info structure becomes richer *) &&
      (List.for_all2 (fun 
	(bl, def_list, otheruses, t, p1)
	  (bl', def_list', otheruses', t', p1') ->
	    merge_var_list (fun map' -> 
	      (eq_deflist map' def_list def_list') &&
	      (eq_otheruses map' otheruses otheruses') &&
	      (equal_find_cond map' t t') &&
	      (equal_oprocess map' p1 p1')) map bl bl'
	      ) l l')
  | _ -> false


(* For simplification of terms *)

(* Applying a substitution *)

let reduced_subst = ref false

let rec apply_subst1 t tsubst =
     match tsubst.t_desc with
       FunApp(f,[redl;redr]) when f.f_cat == Equal || f.f_cat == LetEqual ->
         begin
           if Terms.equal_terms t redl then 
	     begin
	       reduced_subst := true;
	       redr
	     end
           else
             match t.t_desc with
               Var(b,l) ->
	         Terms.build_term2 t (Var(b, List.map (fun t' -> apply_subst1 t' tsubst) l))
             | FunApp(f,l) when f.f_cat != LetEqual ->
	         Terms.build_term2 t (FunApp(f, List.map (fun t' -> apply_subst1 t' tsubst) l))
             | _ -> t
         end
     | _ -> Parsing_helper.internal_error "substitutions should be Equal or LetEqual terms"

let rec apply_all_subst t = function
    [] -> t
  | (a::l) ->
      let t' = apply_subst1 t a in
      if !reduced_subst then t' else apply_all_subst t l

let rec reduce ((subst2, _, _) as simp_facts) t =
  reduced_subst := false;
  let t' = apply_all_subst t subst2 in
  if !reduced_subst then 
    reduce simp_facts t' 
  else
    t

(* simp_equal_terms tests equality between t and t', modulo rewrite rules in 
   simp_facts. Returns true when equal, false otherwise.  *)

let simp_equal_terms simp_facts t t' =
  let t = reduce simp_facts t in
  let t' = reduce simp_facts t' in
  Terms.equal_terms t t'

(* Apply reduction rules defined by statements to term t *)

let rec match_term next_f restr t t' = 
  match t.t_desc with
    Var (v,[]) -> 
    (* Check that types match *)
      if t'.t_type != v.btype then
	raise NoMatch;
      begin
	match v.link with
	  NoLink -> 
	    if List.memq v restr then
	      (* t' must be a variable created by a restriction *)
	      begin
		if not (t'.t_type == v.btype) then
		  raise NoMatch;
		match t'.t_desc with
		  Var(b,l) when Terms.is_restr b -> ()
		| _ -> raise NoMatch
	      end;
	    Terms.link v (TLink t')
	| TLink t -> 
	    if not (Terms.equal_terms t t') then raise NoMatch
      end;
      next_f()
  | FunApp(f,[t1;t2]) when f.f_options land Settings.fopt_COMMUT != 0 ->
      (* Commutative function symbols *)
      begin
	match t'.t_desc with
	  FunApp(f',[t1';t2']) when f == f' ->
            begin
              try
                Terms.auto_cleanup (fun () ->
	          match_term (fun () -> match_term next_f restr t2 t2') restr t1 t1')
              with NoMatch ->
                match_term (fun () -> match_term next_f restr t2 t1') restr t1 t2'
            end
	| _ -> raise NoMatch
      end
  | FunApp(f,l) ->
      begin
	match t'.t_desc with
	  FunApp(f',l') when f == f' ->
	    match_term_list next_f restr l l'
	| _ -> raise NoMatch
      end
  | Var _ | TestE _ | FindE _ | LetE _ | ResE _ | EventE _ ->
      Parsing_helper.internal_error "Var with arguments, if, find, let, and new should not occur in match_term"

and match_term_list next_f restr l l' = 
  match l,l' with
    [],[] -> next_f()
  | a::l,a'::l' ->
      match_term (fun () -> match_term_list next_f restr l l') 
	restr a a'
  | _ -> Parsing_helper.internal_error "Different lengths in match_term_list"

let reduced = ref false

(* apply_not_red implements reduction rules 
     not (x = y) -> x != y
     not (x != y) -> x = y
     x = x -> true
     x != x -> false
(These rules cannot be stored in file default, because there are several
functions for = and for !=, one for each type.)
*)

let rec apply_not_red t =
  match t.t_desc with
    FunApp(fnot, [t']) when fnot == Settings.f_not ->
      begin
      match t'.t_desc with
	FunApp(feq, [t1;t2]) when feq.f_cat == Equal ->
	  reduced := true;
	  Terms.make_diff t1 t2
      |	FunApp(fdiff, [t1;t2]) when fdiff.f_cat == Diff ->
	  reduced := true;
	  Terms.make_equal t1 t2
      |	_ -> Terms.make_not (apply_not_red t')
      end
  | FunApp(f,[t1;t2]) when f.f_cat == Equal && (Terms.equal_terms t1 t2) ->
      reduced := true;
      Terms.make_true()
  | FunApp(f,[t1;t2]) when f.f_cat == Diff && (Terms.equal_terms t1 t2) ->
      reduced := true;
      Terms.make_false()
  | FunApp(f,[t1;t2]) when f == Settings.f_and ->
      Terms.make_and (apply_not_red t1) (apply_not_red t2)
  | FunApp(f,[t1;t2]) when f == Settings.f_or ->
      Terms.make_or (apply_not_red t1) (apply_not_red t2)
  | FunApp(f,l) ->
      Terms.build_term2 t (FunApp(f, List.map apply_not_red l))
  | _ -> t

let rec apply_red t (restr,proba,redl,redr) =
  match t.t_desc with
    FunApp(f,l) ->
      begin
	try
	  match_term (fun () -> 
	    let t' = Terms.copy_term redr in
	    if proba != Zero then
	      begin
              (* Instead of storing the term t, I store the term obtained 
                 after the applications of try_no_var in match_term,
                 obtained by (Terms.copy_term redl) *)
		Proba.add_proba_red (Terms.copy_term redl) t' proba (List.map (fun restr1 ->
		  match restr1.link with
		    TLink trestr -> (restr1,trestr)
		  | _ -> Parsing_helper.internal_error "unexpected link in apply_red") restr)
	      end;
	    Terms.cleanup();
	    reduced := true;
	    t'
	      ) restr redl t
	with NoMatch ->
	  Terms.cleanup();
	  Terms.build_term2 t (FunApp(f, List.map (fun t' -> apply_red t' (restr, proba, redl, redr)) l))
      end
  | _ -> t

let apply_statement t (vl,t_state) =
  match t_state.t_desc with
    FunApp(f, [t1;t2]) when f.f_cat == Equal ->
      apply_red t ([],Zero,t1,t2)
  | FunApp(f, [t1;t2]) when f.f_cat == Diff ->
      apply_red (apply_red t 
	([],Zero,t_state, Terms.make_true())) 
	([],Zero,Terms.make_equal t1 t2, Terms.make_false())
  | _ -> apply_red t ([],Zero,t_state, Terms.make_true())

let rec apply_all_red t = function
    [] -> 
      let t' = apply_not_red t in
      if !reduced then t' else t
  | (a::l) ->
      let t' = apply_statement t a in
      if !reduced then t' else apply_all_red t l

let apply_collision t (restr, forall, t1, proba, t2) =
  apply_red t (restr,proba,t1,t2)

let rec apply_all_coll t = function
    [] -> t
  | (a::l) ->
      let t' = apply_collision t a in
      if !reduced then t' else apply_all_coll t l

let apply_statements_and_collisions t =
  let t' = apply_all_red t (!Transform.statements) in
  if !reduced then t' else
  apply_all_coll t (!Transform.collisions) 

let rec apply_reds simp_facts t =
  let t = reduce simp_facts t in
  reduced := false;
  let t' = apply_statements_and_collisions t in
  if !reduced then 
    apply_reds simp_facts t' 
  else
    t

let rec orient t1 t2 = 
  match t1.t_desc, t2.t_desc with
    (Var(b,l), _) when
    (not (match t2.t_desc with
            FunApp(f,_) when (f.f_options land Settings.fopt_DECOMPOS) != 0 -> true
          | _ -> Terms.refers_to b t2)) && 
    (not (Terms.is_restr b)) -> true
  | (Var(b1,l1), Var(b2,l2)) when
    (b1 == b2) && (List.for_all2 orient l1 l2) -> true
  | (FunApp(f1,l1), FunApp(f2,l2)) when
    (f1 == f2) && (List.for_all2 orient l1 l2) -> true
  | _ -> false
    
let rec add_fact ((subst2, facts, elsefind) as simp_facts) fact =
  (* print_string "Adding "; Display.display_term [] fact; print_newline(); *)
  match fact.t_desc with
    FunApp(f,[t1;t2]) when f.f_cat == LetEqual ->
      begin
	match t1.t_desc with
	  Var(b,l) -> 
	    let t1' = Terms.build_term2 t1 (Var(b, List.map (reduce simp_facts) l))
	    in
	    let t2' = reduce simp_facts t2 in
	    let rec try_red_t1 = function
		[] -> (* Could not reduce t1' *)
		  subst_simplify2 simp_facts (Terms.make_let_equal t1' t2')
	      | { t_desc = FunApp(f'',[t1'';t2''])}::l when f''.f_cat == LetEqual ->
		  if Terms.equal_terms t1'' t1' then 
		    simplif_add simp_facts (Terms.make_equal t2' t2'')
		  else
		    try_red_t1 l
	      | _::l -> try_red_t1 l
	    in
	    try_red_t1 subst2
	| _ -> 
	    Parsing_helper.internal_error "LetEqual terms should have a variable in the left-hand side"
      end
  | FunApp(f,[t1;t2]) when f.f_cat == Equal ->
      begin
      match (t1.t_desc, t2.t_desc) with
        (FunApp(f1,l1), FunApp(f2,l2)) when
	f1.f_cat == Tuple && f2.f_cat == Tuple && f1 != f2 -> 
	  raise Contradiction
      | (FunApp(f1,l1), FunApp(f2,l2)) when
	(f1.f_options land Settings.fopt_COMPOS) != 0 && f1 == f2 -> 
	  simplif_add_list simp_facts (List.map2 Terms.make_equal l1 l2)
      | (Var(b1,l1), Var(b2,l2)) when
	(Terms.is_restr b1) &&
	(Proba.is_large_term t1 || Proba.is_large_term t2) && b1 == b2 ->
	  Proba.add_elim_collisions b1 b1;
          (* add_proba (Div(Cst 1, Card b1.btype)); * number applications *)
	  simplif_add_list simp_facts (List.map2 Terms.make_equal l1 l2)
      | (Var(b1,l1), Var(b2,l2)) when
	(Terms.is_restr b1) && (Terms.is_restr b2) &&
	(Proba.is_large_term t1 || Proba.is_large_term t2) &&
	b1 != b2 ->
	  Proba.add_elim_collisions b1 b2;
	  raise Contradiction
(*      | (_,_) when simp_facts t1 t2 ->
	  raise Contradiction*)
      | (FunApp(f1,[]), FunApp(f2,[]) ) when
	f1 != f2 && (!Settings.diff_constants) ->
	  raise Contradiction
	  (* Different constants are different *)
      | (_, _) when orient t1 t2 ->
	  subst_simplify2 simp_facts (Terms.make_equal t1 t2)
      | (_, _) when orient t2 t1 -> 
	  subst_simplify2 simp_facts (Terms.make_equal t2 t1)
      | _ -> (subst2, fact::facts, elsefind)
      end
  | FunApp(f,[t1;t2]) when f == Settings.f_and ->
      simplif_add (add_fact simp_facts t1) t2
  | _ -> 
      if Terms.is_false fact then raise Contradiction else
      if Terms.is_true fact then simp_facts else
      (subst2, fact::facts, elsefind)

and subst_simplify2 (subst2, facts, elsefind) link =
  let subst2'' = ref [] in
  let not_subst2_facts = ref [] in
  List.iter (fun t0 ->
    match t0.t_desc with
      FunApp(f, [t;t']) when f.f_cat == Equal || f.f_cat == LetEqual ->
	(* When f.f_cat == LetEqual, t itself cannot be reduced by link,
	   since otherwise the left-hand side of link is t, and this
           term should have been reduced into t' by t0 before.
	   However, subterms of t may be reduced by link.
	   
	   When f.f_cat == LetEqual and we reduce only t' (not t),
	   we might directly add 
	   Terms.make_let_equal t (try_no_var simp_facts t1') to subst2''
	   However, it is not clear what "simp_facts" should really be...
         *)
	let (t1, t1', reduced) = 
	  match t'.t_desc with
	    Var _ ->
	      reduced_subst := false;
	      let t1 = apply_subst1 t link in
	      let t1' = apply_subst1 t' link in
	      (t1,t1',!reduced_subst)
	  | FunApp _ ->
	      reduced_subst := false;
	      let t1 = apply_subst1 t link in
	      let red = !reduced_subst in
	      (* Applying reductions here slows down simplification *)
	      reduced := false;
	      let t1' = apply_statements_and_collisions (reduce (link :: (!subst2''), facts, elsefind) t') in
	      (t1, t1', red || (!reduced) || (!reduced_subst))
	  | _ -> Parsing_helper.internal_error "If/let/find/new not allowed in subst_simplify2"
	in
	if reduced then
	  not_subst2_facts := Terms.build_term_type Settings.t_bool (FunApp(f,[t1; t1']))
	     :: (!not_subst2_facts)
	else
	  subst2'' := t0 :: (!subst2'')
    | _ -> Parsing_helper.internal_error "substitutions should be Equal or LetEqual terms"
    ) subst2;
  simplif_add_list (link :: (!subst2''),[], elsefind) ((!not_subst2_facts) @ facts)

and simplif_add ((subst2, facts, elsefind) as simp_facts) fact =
(*  print_string "simplif_add "; Display.display_term [] fact; 
  print_string " knowing\n"; display_facts simp_facts; print_newline();*)
  let fact' = apply_reds simp_facts fact in
  add_fact simp_facts fact'

and simplif_add_list simp_facts = function
    [] -> simp_facts
  | (a::l) -> simplif_add_list (simplif_add simp_facts a) l


let equal_oprocess true_facts p p' =
  eq_oblig := [];
  let r = equal_oprocess [] p p' in
  if not r then
    begin
      eq_oblig := [];
      false
    end
  else
    begin
      try 
	let (subst, facts, elsefind) = true_facts in
	let true_facts' = simplif_add_list (subst, [], []) facts in
	let r = List.for_all (fun (t,t') -> simp_equal_terms true_facts' t t') (!eq_oblig) in
	eq_oblig := [];
	r
      with Contradiction ->
	(* A contradiction is discovered when adding the facts in true_facts.
	   This means that the current program point is in fact not reachable.
           This may happen because the addition procedure is not exactly the same
           as that used in the rest of simplification, so it may discover some
           new information, but it should be extremely rare. For simplicity, 
	   we ignore the information that the current program point is unreachable. *)
	false
    end
      
let equal_term_with_find true_facts t t' =
  eq_oblig := [];
  let r = equal_find_cond [] t t' in
  if not r then
    begin
      eq_oblig := [];
      false
    end
  else
    begin
      try 
	let (subst, facts, elsefind) = true_facts in
	let true_facts' = simplif_add_list (subst, [], []) facts in
	let r = List.for_all (fun (t,t') -> simp_equal_terms true_facts' t t') (!eq_oblig) in
	eq_oblig := [];
	r
      with Contradiction ->
	(* A contradiction is discovered when adding the facts in true_facts.
	   This means that the current program point is in fact not reachable.
           This may happen because the addition procedure is not exactly the same
           as that used in the rest of simplification, so it may discover some
           new information, but it should be extremely rare. For simplicity, 
	   we ignore the information that the current program point is unreachable. *)
	false
    end

let needed_vars vars = List.exists has_array_ref vars

let get_in_scope fact_info =
  match fact_info with
    Some(_,_,n) -> Terms.add_def_vars_node [] n
  | None -> Parsing_helper.internal_error "facts should have been set"

let can_merge_all_branches_findE above_t true_facts l0 t3 =
  let in_scope = get_in_scope above_t.t_facts in
  List.iter (fun (bl, def_list, otheruses, t1, t2) ->
    Terms.exclude_array_ref_def_list (bl @ in_scope) def_list;
    Terms.exclude_array_ref_term (bl @ in_scope) t1) l0;
  let r = List.for_all (fun (bl, def_list, otheruses, t1, t2) ->
    (equal_term_with_find true_facts t2 t3) &&
    (not (needed_vars bl))) l0
  in
  Terms.cleanup_exclude_array_ref();
  r

let can_merge_one_branch_findE above_t true_facts (bl, def_list, otheruses, t1, t2) t3 =
  let in_scope = get_in_scope above_t.t_facts in
  Terms.exclude_array_ref_def_list (bl @ in_scope) def_list;
  Terms.exclude_array_ref_term (bl @ in_scope) t1;
  let r = 
    (equal_term_with_find true_facts t2 t3) &&
    (not (needed_vars bl))
  in
  Terms.cleanup_exclude_array_ref();
  r

let can_merge_all_branches_find above_p true_facts l0 p3 =
  let in_scope = get_in_scope above_p.p_facts in
  List.iter (fun (bl, def_list, otheruses, t1, p2) ->
    Terms.exclude_array_ref_def_list (bl @ in_scope) def_list;
    Terms.exclude_array_ref_term (bl @ in_scope) t1) l0;
  let r = List.for_all (fun (bl, def_list, otheruses, t1, p2) ->
    (equal_oprocess true_facts p2 p3) &&
    (not (needed_vars bl))) l0
  in
  Terms.cleanup_exclude_array_ref();
  r

let can_merge_one_branch_find above_p true_facts (bl, def_list, otheruses, t1, p2) p3 =
  let in_scope = get_in_scope above_p.p_facts in
  Terms.exclude_array_ref_def_list (bl @ in_scope) def_list;
  Terms.exclude_array_ref_term (bl @ in_scope) t1;
  let r = 
    (equal_oprocess true_facts p2 p3) &&
    (not (needed_vars bl))
  in
  Terms.cleanup_exclude_array_ref();
  r


(* Transformation MergeBranches with merging of array references *)

type state_ty =
    MergeToDo of int * Parsing_helper.extent * merge_set
  | MergeDone of int * Parsing_helper.extent

exception Failed

let rec merge_find_cond count t =
  match !count with
    MergeToDo(occ, ext_o, m_set) when occ == t.t_occ ->
      count := MergeDone(occ, ext_o);
      begin
	match t.t_desc with
	  ResE _ | EventE _ | Var _ | FunApp _ ->
	    raise (Error("Occurrence " ^ (string_of_int occ) ^ " corresponds to an instruction that cannot be merged.", ext_o))
	| TestE(t1,t2,t3) ->
	    if m_set != AllBranches then
	      raise (Error("This occurrence corresponds to an if, one always merges all branches, so no need to indicate a branch to merge.", ext_o));
	    let true_facts = Facts.get_facts_at t.t_facts in
	    let simp_facts = Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) true_facts in
	    if equal_term_with_find simp_facts t2 t3 then
	      begin
		all_branches_var_list := (!cur_branch_var_list) :: (!all_branches_var_list);
		cur_branch_var_list := [];
		t3
	      end
	    else
	      raise Failed
	| LetE(pat,t1,t2,topt) ->
	    if m_set != AllBranches then
	      raise (Error("This occurrence corresponds to a let, one always merges all branches, so no need to indicate a branch to merge.", ext_o));
	    begin
	      match topt with
		None -> raise (Error("To be able to merge branches, a let should have an else branch", ext_o))
	      |	Some t3 ->
		  let true_facts = Facts.get_facts_at t.t_facts in
		  let simp_facts = Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) true_facts in
		  if equal_term_with_find simp_facts t2 t3 then
		    begin
		      all_branches_var_list := (!cur_branch_var_list) :: (!all_branches_var_list);
		      cur_branch_var_list := [];
		      t3
		    end
		  else
		    raise Failed
	    end
	| FindE(l0,t3, find_info) ->
	    let true_facts = Facts.get_facts_at t.t_facts in
	    let simp_facts = Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) true_facts in
	    let in_scope = get_in_scope t.t_facts in
	    match m_set with
	      AllBranches ->
		List.iter (fun (bl, def_list, otheruses, t1, t2) ->
		  Terms.exclude_array_ref_def_list (bl @ in_scope) def_list;
		  Terms.exclude_array_ref_term (bl @ in_scope) t1) l0;
		let r = List.for_all (fun (bl, def_list, otheruses, t1, t2) ->
		  let r1 = equal_term_with_find simp_facts t2 t3 in
		  all_branches_var_list := (!cur_branch_var_list) :: (!all_branches_var_list);
		  cur_branch_var_list := [];
		  var_not_needed := bl @ (!var_not_needed);		  
		  r1
		    ) l0
		in
		if r then 
		  t3
		else
		  raise Failed
	    | OneBranch(occ_b, ext_b) ->
		if find_info != Unique then
		  raise (Error("To be able to merge a single branch of find with the else branch, the find must be marked [unique]" , ext_o));
		let l0' = List.filter (fun (bl, def_list, otheruses, t1, t2) ->
		  if t2.t_occ != occ_b then true else
		  begin
		    Terms.exclude_array_ref_def_list (bl @ in_scope) def_list;
		    Terms.exclude_array_ref_term (bl @ in_scope) t1;
		    let r = equal_term_with_find simp_facts t2 t3 in
		    all_branches_var_list := (!cur_branch_var_list) :: (!all_branches_var_list);
		    cur_branch_var_list := [];
		    var_not_needed := bl @ (!var_not_needed);		  
		    not r
		  end
		    ) l0
		in
		if List.length l0' == List.length l0 then
		  raise (Error("Branch to merge not found", ext_b));
		if List.length l0' < List.length l0-1 then
		  raise (Error("Branch to merge ambiguous", ext_b));
		Terms.build_term2 t (FindE(l0',t3,find_info))
      end
  | MergeDone(occ, ext_o) when occ == t.t_occ ->
      raise (Error("Occurrence " ^ (string_of_int occ) ^ " ambiguous. You should use the command show_game occ to determine the desired occurrence.", ext_o))
  | _ ->
  match t.t_desc with
    ResE(b,p) ->
      Terms.build_term2 t (ResE(b, merge_find_cond count p))
  | EventE _ ->
      Parsing_helper.internal_error "event should not occur as term"
  | TestE(t1,t2,t3) ->
      let t2' = merge_find_cond count t2 in
      let t3' = merge_find_cond count t3 in
      Terms.build_term2 t (TestE(t1,t2',t3'))
  | LetE(pat,t1,t2,topt) ->
      let t2' = merge_find_cond count t2 in
      let topt' = 
	match topt with
	  None -> None
	| Some t3 -> Some (merge_find_cond count t3)
      in
      Terms.build_term2 t (LetE(pat,t1,t2',topt'))
  | FindE(l0,t3, find_info) ->
      let t3' = merge_find_cond count t3 in
      let l0' = List.map (fun (bl, def_list, otheruses, t, p) ->
	let p' = merge_find_cond count p in
	let t' = merge_find_cond count t in
	(bl, def_list, otheruses, t', p')
	  ) l0 
      in
      Terms.build_term2 t (FindE(l0',t3',find_info))
  | Var _ | FunApp _ -> t 

let rec merge_i count p =
  let p_desc' =
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) ->
      Par(merge_i count p1,
	  merge_i count p2)
  | Repl(b,p) ->
      Repl(b, merge_i count p)
  | Input((c,tl),pat, p) ->
      let p' = merge_o count p in
      Input((c,tl),pat,p')
  in
  Terms.iproc_from_desc2 p p_desc'

and merge_o count p =
  match !count with
    MergeToDo(occ, ext_o, m_set) when occ == p.p_occ ->
      count := MergeDone(occ, ext_o);
      begin
	match p.p_desc with
	  Yield | Restr _ | EventP _ | Output _ ->
	    raise (Error("Occurrence " ^ (string_of_int occ) ^ " corresponds to an instruction that cannot be merged.", ext_o))
	| Test(t,p1,p2) ->
	    if m_set != AllBranches then
	      raise (Error("This occurrence corresponds to an if, one always merges all branches, so no need to indicate a branch to merge.", ext_o));
	    let true_facts = Facts.get_facts_at p.p_facts in
	    let simp_facts = Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) true_facts in
	    if equal_oprocess simp_facts p1 p2 then
	      begin
		all_branches_var_list := (!cur_branch_var_list) :: (!all_branches_var_list);
		cur_branch_var_list := [];
		p2
	      end
	    else
	      raise Failed
	| Let(pat,t,p1,p2) ->
	    if m_set != AllBranches then
	      raise (Error("This occurrence corresponds to a let, one always merges all branches, so no need to indicate a branch to merge.", ext_o));
	    let true_facts = Facts.get_facts_at p.p_facts in
	    let simp_facts = Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) true_facts in
	    if equal_oprocess simp_facts p1 p2 then
	      begin
		all_branches_var_list := (!cur_branch_var_list) :: (!all_branches_var_list);
		cur_branch_var_list := [];
		p2
	      end
	    else
	      raise Failed
	| Find(l0,p3,find_info) ->
	    let true_facts = Facts.get_facts_at p.p_facts in
	    let simp_facts = Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) true_facts in
	    let in_scope = get_in_scope p.p_facts in
	    match m_set with
	      AllBranches ->
		List.iter (fun (bl, def_list, otheruses, t1, p2) ->
		  Terms.exclude_array_ref_def_list (bl @ in_scope) def_list;
		  Terms.exclude_array_ref_term (bl @ in_scope) t1) l0;
		let r = List.for_all (fun (bl, def_list, otheruses, t1, p2) ->
		  let r1 = equal_oprocess simp_facts p2 p3 in
		  all_branches_var_list := (!cur_branch_var_list) :: (!all_branches_var_list);
		  cur_branch_var_list := [];
		  var_not_needed := bl @ (!var_not_needed);
		  r1
		    ) l0
		in
		if r then 
		  p3
		else
		  raise Failed
	    | OneBranch(occ_b, ext_b) ->
		if find_info != Unique then
		  raise (Error("To be able to merge a single branch of find with the else branch, the find must be marked [unique]" , ext_o));
		let l0' = List.filter (fun (bl, def_list, otheruses, t1, p2) ->
		  if p2.p_occ != occ_b then true else
		  begin
		    Terms.exclude_array_ref_def_list (bl @ in_scope) def_list;
		    Terms.exclude_array_ref_term (bl @ in_scope) t1;
		    let r = equal_oprocess simp_facts p2 p3 in
		    all_branches_var_list := (!cur_branch_var_list) :: (!all_branches_var_list);
		    cur_branch_var_list := [];
		    var_not_needed := bl @ (!var_not_needed);
		    not r
		  end
		    ) l0
		in
		if List.length l0' == List.length l0 then
		  raise (Error("Branch to merge not found", ext_b));
		if List.length l0' < List.length l0-1 then
		  raise (Error("Branch to merge ambiguous", ext_b));
		Terms.oproc_from_desc2 p (Find(l0',p3,find_info))
      end
  | MergeDone(occ, ext_o) when occ == p.p_occ ->
      raise (Error("Occurrence " ^ (string_of_int occ) ^ " ambiguous. You should use the command show_game occ to determine the desired occurrence.", ext_o))
  | _ ->
  let p_desc' =
    match p.p_desc with
      Yield -> Yield
    | Restr(b,p) ->
	Restr(b, merge_o count p)
    | Test(t,p1,p2) ->
	let p1' = merge_o count p1 in
	let p2' = merge_o count p2 in
	Test(t,p1',p2')
    | EventP(t,p) ->
	let p' = merge_o count p in
	EventP(t,p')
    | Let(pat,t,p1,p2) ->
	let p1' = merge_o count p1 in
	let p2' = merge_o count p2 in
	Let(pat,t,p1',p2')
    | Find(l0,p3,find_info) ->
	let p3' = merge_o count p3 in
	let l0' = List.map (fun (bl, def_list, otheruses, t, p) ->
	  let p' = merge_o count p in
	  let t' = merge_find_cond count t in
	  (bl, def_list, otheruses, t', p')
	  ) l0 
	in
	Find(l0',p3',find_info)
    | Output((c,tl),t,p) ->
	let p' = merge_i count p in
	Output((c,tl),t,p')
  in
  Terms.oproc_from_desc2 p p_desc'



let merge simplify_internal_info occ ext m_set g =
  Terms.array_ref_process g.proc;
  Terms.build_def_process None g.proc;
  Proba.reset [] simplify_internal_info g;
  allow_array_ref := true;
  cur_branch_var_list := [];
  all_branches_var_list := [];
  var_not_needed := [];
  let count = ref (MergeToDo(occ, ext, m_set)) in
  try
    let p' = merge_i count g.proc in
    begin
      match !count with
	MergeDone _ -> ()
      |	MergeToDo _ ->
	  raise (Error("Occurrence " ^ (string_of_int occ) ^ " not found. You should use the command show_game occ to determine the desired occurrence.", ext))
    end;
    if not (List.for_all (fun one_branch_var_list -> one_branch_var_list == []) (!all_branches_var_list)) then
      raise (Error("Need to merge arrays, not implemented yet.", ext));
    if needed_vars (!var_not_needed) then
      raise Failed;
    Transform.changed := true;
    let proba = Proba.final_add_proba [] in
    Terms.cleanup_exclude_array_ref();
    allow_array_ref := false;
    cur_branch_var_list := [];
    all_branches_var_list := [];
    var_not_needed := [];
    ({ proc = p'; game_number = -1 }, proba, Proba.final_internal_info(), None)
  with 
    Failed ->
      Terms.cleanup_exclude_array_ref();
      allow_array_ref := false;
      cur_branch_var_list := [];
      all_branches_var_list := [];
      var_not_needed := [];
      raise (Error("Merging of branches failed.", ext))
  | Error(mess,ext) ->
      Terms.cleanup_exclude_array_ref();
      allow_array_ref := false;
      cur_branch_var_list := [];
      all_branches_var_list := [];
      var_not_needed := [];
      raise (Error(mess,ext))
