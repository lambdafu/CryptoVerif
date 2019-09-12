open Types

(* Infer more facts *)

let add_elsefind2 fact_accu def_vars l =
  List.fold_left (fun accu ((bl, def_list, t1,_):'a findbranch) ->
    (* When the condition t1 contains if/let/find/new, we simply ignore it when adding elsefind facts. *)
    match (bl, def_list, t1.t_desc) with
      [],[],(Var _ | FunApp _) -> (Terms.make_not t1)::accu
    | _,[],_ -> accu
    | _,_,(Var _ | FunApp _) -> 
	let bl' = List.map snd bl in
	let true_facts_ref = ref accu in
	Simplify1.always_true_def_list_t true_facts_ref t1 ([], [], []) bl' def_vars def_list;
	(!true_facts_ref)
    | _ -> accu
	  ) fact_accu l

let convert_elsefind2 accu def_vars elsefind =
  let true_facts_ref = ref accu in
  List.iter (fun (bl, def_list, t1) ->
    Simplify1.always_true_def_list_t true_facts_ref t1 ([],[],[]) bl def_vars def_list
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
      |	FindE(l0,t3,_) ->
	  begin
	  try 
	    let def_vars = Facts.get_def_vars_at (DTerm t) in
	    let true_facts_t3 = add_elsefind2 true_facts def_vars l0 in
	    infer_facts_fc cur_array true_facts_t3 t3;
	    let find_node = Facts.get_initial_history (DTerm t) in 
	    List.iter (fun (bl,def_list,t1,t2) ->
	      let vars = List.map fst bl in
	      let repl_indices = List.map snd bl in
	      let cur_array_cond = repl_indices @ cur_array in
	      let vars_terms = List.map Terms.term_from_binder vars in
  	      infer_facts_fc cur_array_cond true_facts t1;
	      let t1' = Terms.subst repl_indices vars_terms t1 in
              let (sure_facts_t1, sure_def_list_t1, _) = Terms.def_vars_and_facts_from_term t1' in
	      (* The "elsefind" facts inferred from [t1'] have 
		 already been taken into account in the first collection of facts.
		 I do not take them into account again here. *)
	      let true_facts' = List.rev_append sure_facts_t1 true_facts in
	    (* Infer new facts *)	    
	      try
		let def_list' = Facts.reduced_def_list t.t_facts def_list in
		let def_vars_cond = Facts.def_vars_from_defined find_node def_list' in
		let def_vars_accu = List.rev_append sure_def_list_t1
		    (Terms.subst_def_list repl_indices vars_terms def_vars_cond) in
		let cur_array_term = List.map Terms.term_from_repl_index cur_array in
		let true_facts' = Terms.def_list_at_pp_facts true_facts' (DTerm t2) cur_array_term def_vars_accu in
		let true_facts' = Terms.both_def_list_facts true_facts' def_vars def_vars_accu in
		let true_facts' = convert_elsefind2 true_facts' (def_vars_accu @ def_vars) elsefind in
		let node = get_node t2.t_facts in
		node.true_facts_at_def <- true_facts';
		infer_facts_fc cur_array true_facts' t2
	      with Contradiction -> 
		(* The branch is in fact unreachable; simplification will remove it
		   I could say that "false" holds at this point, but I don't think
		   it is worth continuing in that branch, since it will be easily removed. *)
		()
		) l0
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
      |	ResE _ | EventAbortE _ | EventE _ | GetE _ | InsertE _ -> 
	  Parsing_helper.internal_error "new, get, insert, event, event_abort should have been expanded in infer_facts_fc"

let improved_def_process event_accu compatible_needed p =
  
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
		let idx = Terms.build_term_type Settings.t_bitstring (FunApp(Settings.get_tuple_fun [], [])) in
		let t = Terms.build_term_type Settings.t_bool (FunApp(f, [idx])) in
		accu := (t, DProcess p') :: (!accu)
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
      |	Find(l0,p2,_) ->
	  begin
	  try 
	    let def_vars = Facts.get_def_vars_at (DProcess p') in
	    let true_facts_p2 = add_elsefind2 true_facts def_vars l0 in
	    infer_facts_o cur_array true_facts_p2 p2;
	    let find_node = Facts.get_initial_history (DProcess p') in 
	    List.iter (fun (bl,def_list,t,p1) ->
	      let vars = List.map fst bl in
	      let repl_indices = List.map snd bl in
	      let cur_array_cond = repl_indices @ cur_array in
	      let vars_terms = List.map Terms.term_from_binder vars in
 	      infer_facts_fc cur_array_cond true_facts t;
	      let t' = Terms.subst repl_indices vars_terms t in
              let (sure_facts_t, sure_def_list_t, _) = Terms.def_vars_and_facts_from_term t' in
	      (* The "elsefind" facts inferred from [t1'] have 
		 already been taken into account in the first collection of facts.
		 I do not take them into account again here. *)
	      let true_facts' = List.rev_append sure_facts_t true_facts in
	    (* Infer new facts *)
	      try
		let def_list' = Facts.reduced_def_list p'.p_facts def_list in
		let def_vars_cond = Facts.def_vars_from_defined find_node def_list' in
		let def_vars_accu = List.rev_append sure_def_list_t
		    (Terms.subst_def_list repl_indices vars_terms def_vars_cond) in
		let cur_array_term = List.map Terms.term_from_repl_index cur_array in
		let true_facts' = Terms.def_list_at_pp_facts true_facts' (DProcess p1) cur_array_term def_vars_accu in
		let true_facts' = Terms.both_def_list_facts true_facts' def_vars def_vars_accu in
		let true_facts' = convert_elsefind2 true_facts' (def_vars_accu @ def_vars) elsefind in
		let node = get_node p1.p_facts in
		node.true_facts_at_def <- true_facts';
		infer_facts_o cur_array true_facts' p1
	      with Contradiction -> 
		(* The branch is in fact unreachable; simplification will remove it
		   I could say that "false" holds at this point, but I don't think
		   it is worth continuing in that branch, since it will be easily removed. *)
		()
		  ) l0
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
if !Settings.improved_fact_collection then
  begin
    Terms.build_def_process None p;
    Terms.build_compatible_defs p;
    infer_facts_i [] [] p
  end
else
  begin
    Terms.build_def_process event_accu p;
    if compatible_needed then
      Terms.build_compatible_defs p
  end

let empty_improved_def_process compatible_needed p =
  Terms.empty_def_process p;
  if compatible_needed || (!Settings.improved_fact_collection)  then
    Terms.empty_comp_process p

