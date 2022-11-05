open Types

(* [above_input_node n] returns the first node corresponding to
   an input above [n]. *)

let rec above_input_node n =
  match n.definition with
  | DInputProcess _ -> n
  | _ ->
      match n.above_node with
      | None -> Parsing_helper.internal_error "reached beginning of program without seeing an input"
      | Some n' -> above_input_node n'
    
(* get_elsefind_facts *)

(* Reasoning that depends on assumptions on the order of definition
   of variables. *)

	    (* Dependency analysis that takes into account assumption on the
   definition order

   dep_info = (list of array ref defined later; list of array ref defined before)
 *)

(* Dependency analysis taking into account the order of definition of the variables. 
   Here dep_info is a list of array ref defined after and a list of array ref defined before *)

let dependency_anal_order_hyp cur_array dep_info =
  let (defl_after, defl_before) = dep_info in
  let depinfo =
    { args_at_creation_only = false;
      dep = [];
      other_variables = true;
      nodep = defl_before }
  in
  let get_dep_info br =
    if Terms.mem_binderref br defl_after then
      (* The variables in [defl_before] do not depend on [br],
         since [br] is in [defl_after], so defined after the
         variables in [defl_before] *)
      depinfo
    else
      Facts.nodepinfo
  in
  let get_dep_info_for_indep (b,l) =
    (* reconstruct the initial list: indices may have been
       replaced with fresh replication indices to make them independent *)
    let linit = List.map (Terms.copy_term Terms.Links_RI) l in
    get_dep_info (b,linit)
  in
  let collision_test simp_facts t1 t2 =
    let t1' = Terms.try_no_var_rec simp_facts t1 in
    let t2' = Terms.try_no_var_rec simp_facts t2 in
    if !Settings.debug_elsefind_facts then
      begin
	print_string "dependency_anal_order_hyp: ";
	Display.display_term t1; print_string ", ";
	Display.display_term t2; print_newline ();
	print_string "simplified t1,t2=";
	Display.display_term t1'; print_string ", ";
	Display.display_term t2'; print_newline ();
      end;
    let res =
      Depanal.try_two_directions (Depanal.dependency_collision_rec cur_array simp_facts get_dep_info) t1' t2'
    in
    if !Settings.debug_elsefind_facts then
      begin
	match res with
	| None ->
	    print_string "Result: failed";
	    print_newline()
	| Some t ->
	    print_string "Result: success ";
	    Display.display_term t;
	    print_newline ()
      end;
    res
  in
  if !Settings.proba_zero then
    (Facts.default_indep_test get_dep_info_for_indep, Facts.no_collision_test)
  else
    (Facts.default_indep_test get_dep_info_for_indep, collision_test)
      
(* this function returns the list of all the binderref that are defined before the node `node' after transformation through the rename_br transformation, and stops if it encounters a binder from stop_binders or if the node is stop_node *)

let rec add_vars_until_binder_or_node node stop_binders stop_node acc =
  match node.above_node with
  | None -> 
      if !Settings.debug_elsefind_facts then
        begin
          print_string "Bug ?";
          print_newline ()
        end;
      acc
  | Some n -> 
      if node == stop_node then
	begin
	  if !Settings.debug_elsefind_facts then
            begin
              print_string "Elsefind_fact add_vars stopped at input_node";
              print_newline ()
            end;
	  acc
	end
      else if List.exists (fun b -> List.mem b node.binders) stop_binders then
	begin
          if !Settings.debug_elsefind_facts then
            begin
              print_string "Elsefind_fact add_vars stopped because var b or br found";
              print_newline ()
            end;
          acc
	end
      else
	add_vars_until_binder_or_node n stop_binders stop_node (node.binders @ acc)
  

(* this function is used as the final function for match_among_list *)
let final_next3 bl def_list t result () =
  Terms.ri_auto_cleanup (fun () ->
    let t' = Terms.copy_term Terms.Links_RI t in
    let def_list' = Terms.copy_def_list Terms.Links_RI def_list in
    result := (def_list', t')::(!result));
  (* Backtrack *)
  raise NoMatch

let final_next4 bl def_list t fact_accu () =
  Terms.ri_auto_cleanup (fun () ->
    let t' = Terms.copy_term Terms.Links_RI t in
    fact_accu := (Terms.make_not t')::(!fact_accu));
  (* Backtrack *)
  raise NoMatch

(* [get_fact_of_elsefind_fact] collects terms that are true, where
   - the variable b[tl] is known to be defined at the current program point (due to some defined condition of find)
   - the variable b is defined in the else branch of a find, so that 
     [elsefind_fact = (bl,def_list,t1)], which means [forall bl, not (defined(def_list) && t1)] 
     holds just before the definition of b
   - [cur_array] contains the current replication indices
   - [def_vars] are variables known to be defined at the current program point.
   - [simp_facts] are facts known to be true at the current program point.

   - [term_accu] stores the proved terms
   - [g] is the current game

   [get_fact_of_elsefind_fact] uses the following reasoning:
   * we substitute tl for b.args_at_creation in the [elsefind_fact], and choose the variables bl such that
   the elements of def_list are defined at the current program point.
   * then, we know that not (defined(def_list) && t1) holds just before the definition of b[tl].
   * if the elements of def_list are defined before b[tl], we obtain not(t1).
   * otherwise, we try to show that, if an element of def_list is defined after b[tl], then
   t1 leads to a contradiction.
   * if this succeeds, we can conclude that not(t1) holds in all cases.
*)

let defined_after b b1 =
  List.for_all (fun n -> List.memq b1 (Terms.add_def_vars_node [] n)) b.def

let rec add_latest ((b,tl) as br) elsefind = function
    [] -> [(br,elsefind)]
  | ((b', tl') as br',elsefind')::l ->
      if (Terms.equal_elsefind_facts elsefind elsefind') && (Terms.equal_term_lists tl tl') then
	if defined_after b b' then
	  (br,elsefind)::l
	else
	  (br',elsefind')::l
      else
	(br',elsefind')::(add_latest br elsefind l)

let rec collect_eff = function
    [] -> []
  | br::l ->
      let last_effl = collect_eff l in
      let new_effl = 
	try 
          Terms.intersect_list Terms.equal_elsefind_facts (List.map (fun n -> n.elsefind_facts_at_def) (fst br).def)
	with Contradiction -> []
      in
      List.fold_right (add_latest br) new_effl last_effl

let get_fact_of_elsefind_fact term_accu g cur_array def_vars simp_facts (b,tl) ((bl,def_list,t1) as elsefind_fact) =
  if !Settings.debug_elsefind_facts then
    begin
      print_string "-----------------\n";
      print_string "Variables known to be currently defined: ";
      Display.display_def_list def_vars;
      print_newline();
      print_string "Variable known to be defined in an else branch of find: ";
      Display.display_var b tl;
      print_newline ();
      print_string "Elsefind_fact (before renaming): ";
      Display.display_elsefind elsefind_fact
    end;

  (* decompose def_list into subterms: all *subterms* of def_list must
     be defined before the find so that we can conclude not(t1) from
     the elsefind fact. *)
  let def_list_subterms = ref [] in
  List.iter (Terms.close_def_subterm def_list_subterms) def_list;
  let def_list = !def_list_subterms in

  (* transform the elsefind fact such that the variable (b,b.args_at_creation) 
     for the original fact corresponds to our variable (b,tl):
     substitute b.args_at_creation with tl. *)
  let b_index = b.args_at_creation in
  let (bl, def_list, t1) = Terms.subst_else_find b_index tl (bl, def_list, t1) in

  (* Variables defined before or at the same time as (b,tl) *)
  let def_vars_before = 
    try
      let (_, def_vars) = Facts.def_vars_from_defined [] [] None [Terms.binderref_from_binder b] in
      Terms.subst_def_list b_index tl def_vars
    with Contradiction -> 
      (* Contradiction may be raised when b can in fact not be defined. *)
      []
  in
  if !Settings.debug_elsefind_facts then
    begin
      print_string "Elsefind_fact_vars_before:\n";
      Display.display_list Display.display_term (List.map Terms.term_from_binderref def_vars_before);
      print_newline ()
    end;
  
  let vars_at_b = List.concat (List.map (fun n -> n.binders) b.def) in
  (* Variables defined strictly before (b,tl) *)  
  let def_vars_strictly_before = Terms.setminus_binderref def_vars_before (List.map (fun b' -> (b',tl)) vars_at_b) in
  
  (* Optimization: if br1 and br2=(b2,tl2) are in def_list and
     br2 defined strictly before (b,tl) implies that
     br1 defined strictly before (b,tl), then we can remove br1 from def_list,
     since knowing that br2 is defined strictly before (b,tl) is enough to apply the elsefind fact. 
     This optimization does not seem to affect much the speed of the system. *)
  let def_list = Terms.setminus_binderref def_list def_vars_strictly_before in
  let rec filter_def_list already_seen = function
    | [] -> List.rev already_seen
    | ((b2,tl2)::l) ->
	let before_br2 = 
	  try
	    let (_, def_vars) = Facts.def_vars_from_defined [] [] None [Terms.binderref_from_binder b2] in
            Terms.subst_def_list b2.args_at_creation tl2 def_vars
	  with Contradiction -> 
	    (* Contradiction may be raised when b2 can in fact not be defined. *)
	    []	
	in
	(* When br2 = (b2,tl2) is defined strictly before (b,tl), 
	   the variables in [strictly_before_b_tl] are also defined strictly before (b,tl).
	   We can then remove them from [def_list]. *)
	let strictly_before_b_tl =
	  if not (List.exists (fun b2_n -> List.exists (fun b_n ->
	    (b2_n != b_n) && (Facts.is_reachable_same_block b2_n b_n)
	      ) b.def) b2.def) then
	    (* When br2 = (b2,tl2) is defined strictly before (b,tl), 
               the block that defines (b2,tl2) has been entirely executed before defining (b,tl) *)
	    let same_block_after_b2 =
	      try 
		(Terms.intersect_list (==)  (List.map (fun n -> n.binders @ n.future_binders) b2.def))
	      with Contradiction ->
		(* Happens when b2 is never defined *)
		[]
	    in
	    (List.map (fun b' -> (b', tl2)) same_block_after_b2) @ before_br2
	  else
	    before_br2
	in
	let already_seen' = Terms.setminus_binderref already_seen strictly_before_b_tl in
	let l' = Terms.setminus_binderref l strictly_before_b_tl in
	filter_def_list ((b2,tl2)::already_seen') l'
  in
  let def_list = filter_def_list [] def_list in

  if !Settings.debug_elsefind_facts then
    begin
      print_string "Elsefind_fact (after renaming): ";
      Display.display_elsefind (bl,def_list,t1)
    end;

  (* We have [elsefind_fact = (bl,def_list,t1)], which means [forall bl, not (defined(def_list) && t1)].
     We collect in variable [result] the pairs (def_list', t') instances of (def_list, t1) such that
     the elements of [def_list'] are defined at the current program point. (They are in [def_vars].) *)
  let result = ref [] in
  begin
    try 
      Facts.match_among_list (final_next3 bl def_list t1 result) simp_facts bl def_vars def_list
    with NoMatch -> ()
  end;
    
  List.iter (fun (def_list',t') ->

    let proba_state = Depanal.get_current_state() in
    if !Settings.debug_elsefind_facts then
      begin
        print_string "Elsefind_fact_try:\n";
        Display.display_term t';
        print_newline ();
        print_string "And the def_list':\n";
        Display.display_list Display.display_term (List.map Terms.term_from_binderref def_list');
        print_newline ()
      end;

    (* If \forall br \in def_list', br is defined strictly before (b,tl), 
       then it is defined before the find that gives the elsefind_fact, and 
       so (not t') is true, since the "else" branch of that find has been taken.
       In the other case, we must prove that \forall br \in def_list', 
       if br is defined after or at (b,tl), t' => Contradiction. *)

    (* [additional_disjuncts] stores additional disjuncts: 
       we actually prove (!additional_disjuncts) || (not t') *)
    let additional_disjuncts = ref [] in
    
    if (
      List.for_all (fun br ->
        (* Let us suppose that br has been defined after or at (b,tl) *)
        if !Settings.debug_elsefind_facts then
          begin
            print_string "Let's assume that ";
	    Display.display_term (Terms.term_from_binderref br);
	    print_string " is defined after or simultaneously ";
	    Display.display_term (Terms.term_from_binderref (b,tl));
            print_newline ()
          end;

	  (* If the variable of br is defined at the definition of b, 
                * if the indices of br are the same as those of b[tl]
                  or [Settings.else_find_additional_disjunct] is false, then we
	          remove the variables defined at the same time as (b,tl) and br
	          from def_vars_before. (We are not sure that they are defined before br.)
                * otherwise, we assume that the indices of br are different from
                  those of b[tl], that is, [not((snd br) = tl)], to make sure that all variables in 
                  def_vars_before are defined before br.
                  Hence, we actually prove [not((snd br) = tl) => not(t')],
                  that is, [((snd br) = tl) || not(t')], so we 
                  add [(snd br) = tl] to [additional_disjuncts].
                  [assumed_distinct_block] is true when we make this assumption.
	     [br_future_or_at_b] contains [(b,tl)] as well as all binderrefs in 
	     [def_vars_before] that are defined after [(b,tl)]. *)
	let (def_vars_before, assumed_distinct_block, br_future_or_at_b) = 
	  if List.memq (fst br) vars_at_b then
            if (List.for_all2 Terms.equal_terms (snd br) tl) ||
            (not (!Settings.else_find_additional_disjunct))
            then
	      (def_vars_strictly_before, false, [(b,tl)])
            else
              begin
                let disjunct = Terms.make_and_list (List.map2 Terms.make_equal (snd br) tl) in
                additional_disjuncts := disjunct::(!additional_disjuncts);
                if !Settings.debug_elsefind_facts then
                  begin
                    print_string "We assume that not(";
                    Display.display_term disjunct;
                    print_string ") so that ";
	            Display.display_term (Terms.term_from_binderref br);
	            print_string " is defined strictly after the input...output block defining ";
	            Display.display_term (Terms.term_from_binderref (b,tl));
                    print_newline ()
                  end;
		(* Add variables defined in the same block as (b,tl) to def_vars_before *)
		let future_or_at_b =
		  try
		    Terms.intersect_list (==) (List.map (fun n -> n.binders @ n.future_binders) b.def)
		  with Contradiction ->
		    (* Happens when b is never defined *)
		    []
		in
		let br_future_or_at_b = List.map (fun b' -> (b', tl)) future_or_at_b in
                (br_future_or_at_b @ def_vars_before, true, br_future_or_at_b)
              end
	  else
	    (def_vars_before, false, [(b,tl)])
	in

	if !Settings.debug_elsefind_facts then
	  begin
            print_string "Elsefind_fact_vars_before extended:\n";
            Display.display_list Display.display_term (List.map Terms.term_from_binderref def_vars_before);
            print_newline ()
	  end;

	(* Under the assumption that br has been defined after or at (b,tl),
	   all variables in def_vars_before are defined strictly before br.
	   If br is in def_vars_before, that's a contradiction, so the assumption 
	   that br is defined after or at the same time as (b,tl) never holds. 
	   (due to the modification of def_vars_before above, br is never defined
	   at the same time as (b,tl) when it is in def_vars_before) *)
	(Terms.mem_binderref br def_vars_before) || (
        let order_assumptions = [br,(b,tl)] in
        List.for_all (fun n -> (* for each definition def_node of br *)
          try
            (* The elements of future_vars are defined after those of def_vars_before. 
	       Compute variables that are defined 
	       - after (b,tl) if not assumed_distinct_block,
	       - after the end of the block that defines (b,tl) if assumed_distinct_block. *)
            let future_binders =
              if assumed_distinct_block then
                (* We assumed that the indices of br are different from those of b[tl]
                   and br is defined after b[l], so all variables from the input point before br
                   to the definition of br and variables certainly defined after the definition of br
                   are defined after the end of the block that defines b[tl] *)
                add_vars_until_binder_or_node n [] (above_input_node n) n.future_binders
              else
		(* We compute variables defined after (b,tl).
		   Add to the future variables of br the variables defined between the previous input 
		   point and the definition of br and after another definition of (b,_) *)
                add_vars_until_binder_or_node n [b] (above_input_node n) n.future_binders
            in
	    let future_vars = Terms.subst_def_list (fst br).args_at_creation (snd br) (List.map Terms.binderref_from_binder future_binders) in

	      (* Variables in [def_vars] are known to be defined.
                 If they cannot be defined before or at the same time as a binderref in [br_future_or_at_b], 
		 or they cannot be defined before or at the same time as a binderref already in [future_vars], then they
	         are certainly defined after [def_vars_before], so we can add them
	         to [future_vars] *)
	    let future_vars = 
	      List.fold_left (fun future_vars br' ->
		if (not (List.exists (Incompatible.may_def_before br') br_future_or_at_b &&
			 List.for_all (Incompatible.may_def_before br') future_vars)) &&
		  (not (Terms.mem_binderref br' future_vars)) 
		then
		  br' :: future_vars
		else
		  future_vars) future_vars def_vars
	    in

            if !Settings.debug_elsefind_facts then
              begin
                print_string "Elsefind_fact_future_vars:\n";
                Display.display_list Display.display_term (List.map Terms.term_from_binderref future_vars);
                print_newline ()
              end;

	      (* Elements of future_vars are defined after those of def_vars_before;
	         If they are in def_vars_before, that's a contradiction *)
	    if List.exists (fun future_br -> Terms.mem_binderref future_br def_vars_before) future_vars then
	      raise Contradiction;
	    
	    (* Elements of future_vars are defined after those of def_vars_before.
	       Therefore, the elements of def_vars_before are independent of the elements of future_vars
	       that are randomly chosen. *)
            let dep_info = (future_vars, List.map Terms.term_from_binderref def_vars_before) in
     
            if !Settings.debug_elsefind_facts then
              begin
                print_string "--Args to dependency_collision:\n";
                print_string "Cur_array=";
                Display.display_list Display.display_repl_index cur_array;
                print_string "\nOrder assumptions=";
                Display.display_list (fun (br,br') -> 
		  print_string "(";
                  Display.display_list Display.display_term (List.map Terms.term_from_binderref [br;br']); 
		  print_string ")"
		    ) order_assumptions;
                print_string "\nDepinfo=previous lists";
                print_string "\nFacts=\n";
                Display.display_facts simp_facts;
                print_string "\nt'=";
                Display.display_term t';
                print_string "\n--End of args"; print_newline ();
                Settings.debug_simplif_add_facts := true;
              end;
           
	    (* Get additional facts using again elsefind facts.
	       If an elsefind fact (bl, def_list, t1) holds at the
	       definition of b'[tl'] in future_vars, that is,
	       at the definition of b'[tl'], we have
	       forall bl, not (defined(def_list) && t1)
	       and furthermore all elements of def_list are in 
	       def_vars_before, so all elements of def_list are defined
	       at the definition of b[tl], so a fortiori at the
	       definition of b'[tl'], then we have not(t1). *)

            let (subst, facts, _) = simp_facts in
	    let fact_accu = ref [] in
	    let elsefind_facts = collect_eff future_vars in
	    List.iter (fun ((b',tl'), (bl, def_list, t1)) ->
	      (* The "elsefind" fact (bl, def_list, t1) holds
		 at the definition of b', and I know that b'[tl'] is defined *)

	      (* Rename indices b'.args_at_creation -> tl' *)
	      let def_list = Terms.subst_def_list b'.args_at_creation tl' def_list in
	      let t1 = Terms.subst b'.args_at_creation tl' t1 in

              (* We add to [fact_accu] the facts [not t'] where the pairs 
		 (def_list', t') are instances of (def_list, t1) such that
		 the elements of [def_list'] are defined at the definition of b[tl]. 
		 (They are in [def_vars_before].) *)
	      begin
		try 
		  Facts.match_among_list (final_next4 bl def_list t1 fact_accu) simp_facts bl def_vars_before def_list
		with NoMatch -> ()
	      end
		) elsefind_facts;

              (* Note: we re-add the facts that are already in simp_facts, 
                 because the dependency information can allow further 
                 simplifications on them as well. 
		 We add [t'] last, so that we can already exploit 
		 the values of variables known previously when using
		 the dependency analysis on [t']. *)
	    let dep_anal = dependency_anal_order_hyp cur_array dep_info in
            let simp_facts1 = Facts.simplif_add_list dep_anal ([],[],[]) subst in
	    let simp_facts2 = Facts.simplif_add_list dep_anal simp_facts1 facts in
	    let simp_facts3 = Facts.simplif_add_list dep_anal simp_facts2 (!fact_accu) in
	    let _ = Facts.simplif_add dep_anal simp_facts3 t' in
            if !Settings.debug_elsefind_facts then
              begin
                Settings.debug_simplif_add_facts := false;
                print_string "Failed to obtain a contradiction.";
                print_newline ()
              end;
            false
          with Contradiction -> 
            if !Settings.debug_elsefind_facts then
              begin
                Settings.debug_simplif_add_facts := false;
                print_string "Obtained a contradiction.";
                print_newline ()
              end;
            true
              ) (fst br).def
	  )
          ) def_list'; 
      )
    then
      begin
        (* The term (not t') is true, add it *)
        let t = Terms.make_or_list ((Terms.make_not t')::(!additional_disjuncts)) in
        term_accu := t :: (!term_accu);
        if !Settings.debug_elsefind_facts then
	  begin
	    print_string "Found a usable term: ";
	    Display.display_term t;
	    print_newline ()
	  end
      end
    else
      begin
	(* Nothing inferred, restore the old probability state.
	   The collisions that we eliminated were useless in the end. *)
	Depanal.restore_state proba_state;
        if !Settings.debug_elsefind_facts then
          begin
            print_string "Found no usable terms.";
            print_newline ()
          end
      end
	) (!result)


let get_facts_of_elsefind_facts g cur_array simp_facts def_vars =
  if !Settings.debug_elsefind_facts then
    begin
      print_string "__________________\n";
      print_string "Elsefind begin\n";
      print_newline ()
    end; 
(*  print_string "Defined variables original:\n";
  Display.display_def_list_lines def_vars; *)
  let def_vars_tmp = ref [] in
  List.iter (fun (b,l) ->
    let br' = (b, List.map (Terms.try_no_var simp_facts) l) in
    Terms.add_binderref br' def_vars_tmp) def_vars;
  let def_vars = !def_vars_tmp in
(*  print_string "Defined variables simplified:\n";
  Display.display_def_list_lines def_vars; *)
  let term_accu = ref [] in
  let effl = collect_eff def_vars in
  List.iter (fun (br, eff) -> get_fact_of_elsefind_fact term_accu g cur_array def_vars simp_facts br eff) effl;
  if !Settings.debug_elsefind_facts then
    begin
      print_string "__________________\n";
      print_string "Elsefind summary: these terms are true:\n";
      Display.display_list Display.display_term (!term_accu);
      print_newline ()
    end;
  !term_accu


