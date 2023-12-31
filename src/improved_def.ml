open Types

(* Infer more facts *)

let add_elsefind2 fact_accu def_vars l =
  List.fold_left (fun accu (_,(_,efl)) ->
    List.fold_left (fun accu (bl, def_list, t1) ->
      if bl == [] && def_list == [] then
	(Terms.make_not t1)::accu
      else
	let true_facts_ref = ref accu in
	Facts.always_true_def_list_t true_facts_ref t1 ([], [], []) bl def_vars def_list;
	(!true_facts_ref)
	  ) accu efl
      ) fact_accu l

let convert_elsefind2 accu def_vars elsefind =
  let true_facts_ref = ref accu in
  List.iter (fun (bl, def_list, t1) ->
    Facts.always_true_def_list_t true_facts_ref t1 ([],[],[]) bl def_vars def_list
      ) elsefind;
  (!true_facts_ref)

let get_node = function
    None -> Parsing_helper.internal_error "t/i/p_facts should have been set"
  | Some(_,_,_,_,_,_,n) ->
      n

let rec infer_facts_t true_facts t =
  begin
    match t.t_facts with
      None -> Parsing_helper.internal_error "t_facts should have been set"
    | Some (cur_array, true_facts_old, elsefind, def_vars, fut_true_facts, future_binders, n) ->
	t.t_facts <- Some(cur_array, true_facts, elsefind, def_vars, fut_true_facts, future_binders, n)
  end;
  match t.t_desc with
    Var(_,l) | FunApp(_,l) -> List.iter (infer_facts_t true_facts) l
  | ReplIndex _ -> ()
  | _ -> Parsing_helper.internal_error "if/let/find/new should have been expanded in infer_facts_t"

let rec infer_facts_pat true_facts = function
    PatVar _ -> ()
  | PatTuple(_,l) -> List.iter (infer_facts_pat true_facts) l
  | PatEqual t -> infer_facts_t true_facts t

let improved_def_game event_accu compatible_needed g =
  
let rec infer_facts_fc cur_array true_facts t =
  match t.t_facts with
    None -> Parsing_helper.internal_error "t_facts should have been set"
  | Some (cur_array, true_facts_old, elsefind, def_vars, fut_true_facts, future_binders, n) ->
      t.t_facts <- Some(cur_array, true_facts, elsefind, def_vars, fut_true_facts, future_binders, n);
      match t.t_desc with
	Var(_,l) | FunApp(_,l) -> List.iter (infer_facts_t true_facts) l
      | ReplIndex _ -> ()
      |	TestE(t1,t2,t3) ->
	  infer_facts_t true_facts t1;
	  let true_facts' = t1 :: true_facts in
	  let true_facts'' = (Terms.make_not t1) :: true_facts in
	  infer_facts_fc cur_array true_facts' t2;
	  infer_facts_fc cur_array true_facts'' t3
      |	FindE(l0,t3,find_info) ->
	  begin
	    match event_accu, find_info with
	    | Some accu, UniqueToProve f ->
		accu := (Terms.event_term t.t_occ f cur_array, DTerm t) :: (!accu)
	    | _ -> ()
	  end;
	  let l0_with_info = Info_from_term.add_info_find (Some g) g.expanded l0 in
	  begin
	  try 
	    let (pps, def_vars, find_node) = Facts.get_def_vars_at (DTerm t) in
	    let true_facts_t3 = add_elsefind2 true_facts def_vars l0_with_info in
	    infer_facts_fc cur_array true_facts_t3 t3;
	    let cur_array_term = List.map Terms.term_from_repl_index cur_array in
	    List.iter (fun ((bl,def_list,t1,t2), (info_then, info_else)) ->
	      let vars = List.map fst bl in
	      let repl_indices = List.map snd bl in
	      let cur_array_cond = repl_indices @ cur_array in
	      let vars_terms = List.map Terms.term_from_binder vars in
  	      infer_facts_fc cur_array_cond true_facts t1;
              let (sure_facts_t1, sure_def_list_t1, _) = info_then in
	      let sure_facts_t1 = List.map (Terms.subst repl_indices vars_terms) sure_facts_t1 in
	      
	      (* The "elsefind" facts inferred from [t1] have 
		 already been taken into account in the first collection of facts.
		 I do not take them into account again here. *)
	      let true_facts' = List.rev_append sure_facts_t1 true_facts in
	    (* Infer new facts *)	    
	      try
		let def_list' = Terms.subst_def_list repl_indices vars_terms (List.rev_append sure_def_list_t1 (Facts.reduced_def_list t.t_facts def_list)) in
		let (pps_init_and_cond, def_vars_cond) = Facts.def_vars_from_defined pps def_vars find_node def_list' in
		let true_facts' = Incompatible.ppl_before_pp_facts true_facts' (DTerm t2, cur_array_term) pps_init_and_cond in
		let true_facts' = Incompatible.both_ppl_facts true_facts' pps pps_init_and_cond in
		let true_facts' = convert_elsefind2 true_facts' (def_vars_cond @ def_vars) elsefind in
		let node = get_node t2.t_facts in
		node.true_facts_at_def <- true_facts';
		infer_facts_fc cur_array true_facts' t2
	      with Contradiction -> 
		(* The branch is in fact unreachable; simplification will remove it
		   I could say that "false" holds at this point, but I don't think
		   it is worth continuing in that branch, since it will be easily removed. *)
		()
		) l0_with_info
	  with Contradiction ->
	    (* The find is in fact unreachable; simplification will remove it *)
	    ()
	  end
      |	LetE(pat,t1,t2,topt) ->
	  infer_facts_t true_facts t1;
	  infer_facts_pat true_facts pat;
	  let new_fact = 
	    (match pat with PatVar _ -> Terms.make_let_equal | _ -> Terms.make_equal) 
	      (Terms.term_from_pat pat) t1 
	  in
	  let true_facts' = new_fact :: true_facts in
	  let node = get_node t2.t_facts in
	  node.true_facts_at_def <- true_facts';
	  infer_facts_fc cur_array true_facts' t2;
	  begin
	    match topt with
	      None -> ()
	    | Some t3 -> 
		let true_facts' = 
		  try
		    (Terms.make_for_all_diff (Terms.gen_term_from_pat pat) t1) :: true_facts
		  with Terms.NonLinearPattern -> true_facts
		in
		infer_facts_fc cur_array true_facts' t3
	  end
      |	ResE(b,t1) ->
	  let node = get_node t.t_facts in
	  node.true_facts_at_def <- true_facts;
	  infer_facts_fc cur_array true_facts t1
      | EventAbortE f ->
	  begin
	    match event_accu with
	      None -> ()
	    | Some accu -> 
		accu := (Terms.event_term t.t_occ f cur_array, DTerm t) :: (!accu)
	  end
       | EventE _ | GetE _ | InsertE _ -> 
	  Parsing_helper.internal_error "get, insert, event should have been expanded in infer_facts_fc"

in

let rec infer_facts_i cur_array true_facts p' =
  (* print_string "infer_facts_i occ "; print_int p'.i_occ; print_newline(); *)
  begin
    match p'.i_facts with
      None -> Parsing_helper.internal_error "i_facts should have been set"
    | Some (cur_array, true_facts_old, elsefind, def_vars, fut_true_facts, future_binders, n) ->
	p'.i_facts <- Some(cur_array, true_facts, elsefind, def_vars, fut_true_facts, future_binders, n)
  end;
  match p'.i_desc with
    Nil -> ()
  | Par(p1,p2) -> 
      infer_facts_i cur_array true_facts p1;
      infer_facts_i cur_array true_facts p2
  | Repl(b,p) ->
      let node = get_node p.i_facts in
      node.true_facts_at_def <- true_facts;      
      infer_facts_i (b::cur_array) true_facts p
  | Input((c,tl),pat,p) ->
      List.iter (infer_facts_t true_facts) tl;
      infer_facts_pat true_facts pat;
      let node = get_node p.p_facts in
      node.true_facts_at_def <- true_facts;
      infer_facts_o cur_array true_facts p 

and infer_facts_o cur_array true_facts p' =
  (* print_string "infer_facts_o occ "; print_int p'.p_occ; print_newline(); *)
  match p'.p_facts with
    None -> Parsing_helper.internal_error "p_facts should have been set"
  | Some (cur_array, true_facts_old, elsefind, def_vars, fut_true_facts, future_binders, n) ->
      p'.p_facts <- Some(cur_array, true_facts, elsefind, def_vars, fut_true_facts, future_binders, n);
      match p'.p_desc with
	Yield -> ()
      |	EventAbort f ->
	  begin
	    match event_accu with
	      None -> ()
	    | Some accu -> 
		accu := (Terms.event_term p'.p_occ f cur_array, DProcess p') :: (!accu)
	  end
      |	Restr(b,p) ->
	  let node = get_node p.p_facts in
	  node.true_facts_at_def <- true_facts;
	  infer_facts_o cur_array true_facts p
      |	Test(t,p1,p2) ->
	  infer_facts_t true_facts t;
	  let true_facts' = t :: true_facts in
	  let true_facts'' = (Terms.make_not t) :: true_facts in
	  infer_facts_o cur_array true_facts' p1;
	  infer_facts_o cur_array true_facts'' p2
      |	Find(l0,p2,find_info) ->
	  begin
	    match event_accu, find_info with
	    | Some accu, UniqueToProve f  -> 
		accu := (Terms.event_term p'.p_occ f cur_array, DProcess p') :: (!accu)
	    | _ -> ()
	  end;
	  let l0_with_info = Info_from_term.add_info_find (Some g) g.expanded l0 in
	  begin
	  try 
	    let (pps, def_vars, find_node) = Facts.get_def_vars_at (DProcess p') in
	    let true_facts_p2 = add_elsefind2 true_facts def_vars l0_with_info in
	    infer_facts_o cur_array true_facts_p2 p2;
	    let cur_array_term = List.map Terms.term_from_repl_index cur_array in
	    List.iter (fun ((bl,def_list,t,p1), (info_then, info_else)) ->
	      let vars = List.map fst bl in
	      let repl_indices = List.map snd bl in
	      let cur_array_cond = repl_indices @ cur_array in
	      let vars_terms = List.map Terms.term_from_binder vars in
 	      infer_facts_fc cur_array_cond true_facts t;
              let (sure_facts_t, sure_def_list_t, _) = info_then in
	      let sure_facts_t = List.map (Terms.subst repl_indices vars_terms) sure_facts_t in
	      let sure_def_list_t = Terms.subst_def_list repl_indices vars_terms sure_def_list_t in
	      (* The "elsefind" facts inferred from [t] have 
		 already been taken into account in the first collection of facts.
		 I do not take them into account again here. *)
	      let true_facts' = List.rev_append sure_facts_t true_facts in
	    (* Infer new facts *)
	      try
		let def_list' = Terms.subst_def_list repl_indices vars_terms (List.rev_append sure_def_list_t (Facts.reduced_def_list p'.p_facts def_list)) in
		let (pps_init_and_cond, def_vars_cond) = Facts.def_vars_from_defined pps def_vars find_node def_list' in
		let true_facts' = Incompatible.ppl_before_pp_facts true_facts' (DProcess p1, cur_array_term) pps_init_and_cond in
		let true_facts' = Incompatible.both_ppl_facts true_facts' pps pps_init_and_cond in
		let true_facts' = convert_elsefind2 true_facts' (def_vars_cond @ def_vars) elsefind in
		let node = get_node p1.p_facts in
		node.true_facts_at_def <- true_facts';
		infer_facts_o cur_array true_facts' p1
	      with Contradiction -> 
		(* The branch is in fact unreachable; simplification will remove it
		   I could say that "false" holds at this point, but I don't think
		   it is worth continuing in that branch, since it will be easily removed. *)
		()
		  ) l0_with_info
	  with Contradiction ->
	    (* The find is in fact unreachable; simplification will remove it *)
	    ()
	  end
      |	Output((c,tl),t',p) ->
	  List.iter (infer_facts_t true_facts) tl;
	  infer_facts_t true_facts t';
	  infer_facts_i cur_array true_facts p
      |	Let(pat,t,p1,p2) ->
	  infer_facts_t true_facts t;
	  infer_facts_pat true_facts pat;
	  let new_fact = 
	    (match pat with PatVar _ -> Terms.make_let_equal | _ -> Terms.make_equal) 
	      (Terms.term_from_pat pat) t 
	  in
	  let true_facts' = new_fact :: true_facts in
	  let node = get_node p1.p_facts in
	  node.true_facts_at_def <- true_facts';
	  infer_facts_o cur_array true_facts' p1;
	  begin
	    match pat, p2.p_desc with
	      PatVar _, Yield -> ()
	    | _ -> 
		let true_facts' = 
		  try
		    (Terms.make_for_all_diff (Terms.gen_term_from_pat pat) t) :: true_facts
		  with Terms.NonLinearPattern -> true_facts
		in
		infer_facts_o cur_array true_facts' p2
	  end
      |	EventP(t,p) ->
	  begin
	    match event_accu with
	      None -> ()
	    | Some accu -> accu := (t, DProcess p') :: (!accu)
	  end;
	  infer_facts_t true_facts t;
	  infer_facts_o cur_array (t::true_facts) p
      | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

in
let p = Terms.get_process g in
(* [infer_facts_i] does not support non-expanded games,
   so we fall back to the basic version when the game is 
   not expanded. *)
if (!Settings.improved_fact_collection) && g.expanded then
  begin
    Def.build_def_process (Some g) None p;
    Incompatible.build_compatible_defs p;
    infer_facts_i [] [] p
  end
else
  begin
    Def.build_def_process (Some g) event_accu p;
    if compatible_needed then
      Incompatible.build_compatible_defs p
  end

    
let empty_improved_def_game compatible_needed g =
  let p = Terms.get_process g in
  Def.empty_def_process p;
  if compatible_needed ||
     ((!Settings.improved_fact_collection) && g.expanded)  then
    Incompatible.empty_comp_process p

