open Types

let binder_list = ref []

let transfos_done = ref ([]: (binder * (term * term) list ref) list)
    (* For each binder [b], the list of replacements t1 -> t2 that
       have been done by using that binder *)

let rec find_map f = function
    [] -> None
  | a::l ->
      match f a with
      | (Some x) as res -> res
      | None -> find_map f l

let rec get_val = function
    [] -> None
  | (a::l) ->
      let a_val = 
	match a.definition with
	| DProcess { p_desc = Let(PatVar _, t, _, _) } 
	| DTerm { t_desc = LetE(PatVar _, t, _, _) } -> t
	| _ -> raise Not_found
      in
      match get_val l with
      | None -> Some a_val
      | Some l_val -> if Terms.equal_terms a_val l_val then Some l_val else raise Not_found

	    
let replace t cur_array (b,l) =
  if List.memq b (!binder_list) then
    let defs = List.filter (fun n ->
      (* NOTE We could require that [n.definition_success] be executed *before* [t], but it
	 does not seem to help much in practice *)
      Incompatible.both_pp (l,n.definition_success) (List.map Terms.term_from_repl_index cur_array, DTerm t) 
	) b.def
    in
    try
      match get_val defs with
      | None -> None
      | Some t' -> (* b = t' *)
	  let t'' = Terms.subst b.args_at_creation l t' in (* b[l] = t'' *)
	  if Terms.equal_terms t t'' then
	    let t2 = Terms.build_term t (Var(b,l)) in
	    (* We replace [t] with [t2 = b[l]] *)
	    begin
	      try
		let l_b = List.assq b (!transfos_done) in
		l_b := (t, t2) :: (!l_b)
	      with Not_found ->
		transfos_done := (b, ref [t, t2]) :: (!transfos_done)
	    end;
	    Some t2
	  else
	    None
    with Not_found ->
      if (List.length defs > 1) &&
	(List.exists (fun n ->
	  match n.definition with
	  | DProcess { p_desc = Let(PatVar _, t, _, _) } 
	  | DTerm { t_desc = LetE(PatVar _, t, _, _) } -> true
	  | _ -> false) defs) then
	Settings.advise := (SArenaming b) :: (!Settings.advise);
      None
  else
    None

let replace_all t cur_array defined_vars =
  match t.t_desc with
  | FunApp _ ->
      if Terms.check_simple_term t then
	find_map (replace t cur_array) defined_vars
      else
	None
  | _ -> None

(* NOTE Variables defined locally in a subterm cannot be used
   in other terms evaluated later without a "defined" condition
   that requires their definition.
   To avoid having to add such defined conditions potentially
   everywhere in the game, we do not consider them as being
   defined in the following terms. That should not have a major
   impact on the power of this command in practice. *)
	
let rec use_var_t cur_array defined_vars t =
  match replace_all t cur_array defined_vars with
  | Some t' -> t'
  | None ->
      match t.t_desc with
      | Var(b,l) ->
	  let l' = List.map (use_var_t cur_array defined_vars) l in
	  Terms.build_term t (Var(b, l'))
      | FunApp(f,l) ->
	  let l' = List.map (use_var_t cur_array defined_vars) l in
	  Terms.build_term t (FunApp(f, l'))
      | ReplIndex _ | EventAbortE _ -> t
      | ResE(b,p) ->
	  let defined_vars' = (Terms.binderref_from_binder b) :: defined_vars in
	  let p' = use_var_t cur_array defined_vars' p in
	  Terms.build_term t (ResE(b,p'))
      | EventE(t1,p) ->
	  let t1' = use_var_t cur_array defined_vars t1 in
	  let p' = use_var_t cur_array defined_vars p in
	  Terms.build_term t (EventE(t1',p'))
      | GetE _ | InsertE _ ->
	  Parsing_helper.internal_error "get, insert should not occur as term"
      | TestE(t1,t2,t3) ->
	  let t1' = use_var_t cur_array defined_vars t1 in
	  let t2' = use_var_t cur_array defined_vars t2 in
	  let t3' = use_var_t cur_array defined_vars t3 in
	  Terms.build_term t (TestE(t1',t2',t3'))
      | LetE(pat,t1,t2,topt) ->
	  let t1' = use_var_t cur_array defined_vars t1 in
	  let pat' = use_var_pat cur_array defined_vars pat in
	  let def_pat = Terms.vars_from_pat [] pat in
	  let defined_vars_in = (List.map Terms.binderref_from_binder def_pat) @ defined_vars in
	  let t2' = use_var_t cur_array defined_vars_in t2 in
	  let topt' =
	    match topt with
	    | None -> None
	    | Some t3 ->
		Some(use_var_t cur_array defined_vars t3)
	  in
	  Terms.build_term t (LetE(pat',t1',t2',topt'))
      | FindE(l0,t3, find_info) ->
	  let t3' = use_var_t cur_array defined_vars t3 in
	  let l0' = List.fold_right (fun (bl, def_list, tc, p) laccu ->
	    try 
	      let vars = List.map fst bl in
	      let repl_indices = List.map snd bl in
	      let newly_defined = Facts.def_vars_from_defined (Facts.get_initial_history (DTerm t)) def_list  in
	      let tc' = use_var_t (repl_indices @ cur_array) (Terms.union_binderref newly_defined defined_vars) tc in
	      let vars_terms = List.map Terms.term_from_binder vars in
	      let defined_vars_then =
		Terms.union_binderref (List.map Terms.binderref_from_binder vars) 
		  (Terms.union_binderref (Terms.subst_def_list repl_indices vars_terms newly_defined) 
		     defined_vars)
	      in
	      let p' = use_var_t cur_array defined_vars_then p in
	      let br' = Facts.update_def_list_term defined_vars newly_defined bl def_list tc' p' in
	      br' :: laccu
	    with Contradiction ->
	      (* variables in [def_list] cannot be defined *)
	      laccu
		) l0 []
	  in
	  Terms.build_term t (FindE(l0',t3', find_info))

and use_var_pat cur_array defined_vars = function
  | PatVar b -> PatVar b
  | PatTuple(f,l) ->
      let l' = List.map (use_var_pat cur_array defined_vars) l in
      PatTuple(f,l')
  | PatEqual t ->
      let t' = use_var_t cur_array defined_vars t in
      PatEqual t'

let rec use_var_i cur_array defined_vars p =
  match p.i_desc with
  | Nil -> p
  | Par(p1, p2) ->
      Terms.iproc_from_desc_loc p
	(Par(use_var_i cur_array defined_vars p1,
	     use_var_i cur_array defined_vars p2))
  | Repl(b,p1) ->
      Terms.iproc_from_desc_loc p
	(Repl(b, use_var_i (b::cur_array) defined_vars p1))
  | Input((c,tl),pat,p1) ->
      let tl' = List.map (use_var_t cur_array defined_vars) tl in
      let pat' = use_var_pat cur_array defined_vars pat in 
      let def_pat = Terms.vars_from_pat [] pat in
      let defined_vars' = (List.map Terms.binderref_from_binder def_pat) @ defined_vars in
      Terms.iproc_from_desc_loc p
	(Input((c, tl'), pat',
	       use_var_o cur_array defined_vars' p1))
    
and use_var_o cur_array defined_vars p =
  match p.p_desc with
  | Yield | EventAbort _ -> p
  | Restr(b,p1) ->
      let defined_vars' = (Terms.binderref_from_binder b) :: defined_vars in
      Terms.oproc_from_desc_loc p
	(Restr(b, use_var_o cur_array defined_vars' p1))
  | Test(t,p1,p2) ->
      Terms.oproc_from_desc_loc p
	(Test(use_var_t cur_array defined_vars t,
	      use_var_o cur_array defined_vars p1,
	      use_var_o cur_array defined_vars p2))
  | EventP(t,p1) ->
      Terms.oproc_from_desc_loc p
	(EventP(use_var_t cur_array defined_vars t,
		use_var_o cur_array defined_vars p1))
  | Let(pat, t, p1, p2) ->
      let t' = use_var_t cur_array defined_vars t in
      let pat' = use_var_pat cur_array defined_vars pat in
      let def_pat = Terms.vars_from_pat [] pat in
      let defined_vars_in = (List.map Terms.binderref_from_binder def_pat) @ defined_vars in
      let p1' = use_var_o cur_array defined_vars_in p1 in
      let p2' = use_var_o cur_array defined_vars p2 in
      Terms.oproc_from_desc_loc p (Let(pat', t', p1', p2'))
  | Find(l0,p3,find_info) ->
      let p3' = use_var_o cur_array defined_vars p3 in
      let l0' = List.fold_right (fun (bl, def_list, tc, p1) laccu ->
	try 
	  let vars = List.map fst bl in
	  let repl_indices = List.map snd bl in
	  let newly_defined = Facts.def_vars_from_defined (Facts.get_initial_history (DProcess p)) def_list  in
	  let tc' = use_var_t (repl_indices @ cur_array) (Terms.union_binderref newly_defined defined_vars) tc in
	  let vars_terms = List.map Terms.term_from_binder vars in
	  let defined_vars_then =
	    Terms.union_binderref (List.map Terms.binderref_from_binder vars) 
	      (Terms.union_binderref (Terms.subst_def_list repl_indices vars_terms newly_defined) 
		 defined_vars)
	  in
	  let p1' = use_var_o cur_array defined_vars_then p1 in
	  let br' = Facts.update_def_list_process defined_vars newly_defined bl def_list tc' p1' in
	  br' :: laccu
	with Contradiction ->
	  (* variables in [def_list] cannot be defined *)
	  laccu
	    ) l0 []
      in
      Terms.oproc_from_desc_loc p (Find(l0', p3', find_info))
  | Output((c,tl),t,p1) ->
      Terms.oproc_from_desc_loc p
	(Output((c, List.map (use_var_t cur_array defined_vars) tl),
		use_var_t cur_array defined_vars t,
		use_var_i cur_array defined_vars p1))
  | Get _ | Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

let use_variable l g =
  binder_list := l;
  transfos_done := [];
  Improved_def.improved_def_game None true g;
  let g_proc = Terms.get_process g in
  let p' = use_var_i [] [] g_proc in
  Improved_def.empty_improved_def_game true g;
  if !transfos_done != [] then
    Settings.changed := true;
  let transfos_done' = 
    List.map (fun (b, l_ref) -> 
      DUseVariable(b, !l_ref)
	) (!transfos_done) 
  in
  transfos_done := [];
  binder_list := [];
  (Terms.build_transformed_game p' g, [], transfos_done')


