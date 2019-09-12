open Types

(* Priorities for orienting equalities into rewrite rules *)
let current_max_priority = ref 0
let priority_list = ref []

let rec match_term2 next_f simp_facts bl t t' =
  match t.t_desc with
    ReplIndex(v) when (List.memq v bl) ->
      begin
	if t'.t_type != v.ri_type then
	  raise NoMatch;
	match v.ri_link with
	  NoLink -> Terms.ri_link v (TLink t')
	| TLink t -> if not (Terms.simp_equal_terms simp_facts true t t') then raise NoMatch
      end;
      next_f ()
  | ReplIndex(v) ->
      begin
	match t'.t_desc with
	  ReplIndex(v') when v == v' -> next_f()
	| _ -> if not (Terms.simp_equal_terms simp_facts true t t') then raise NoMatch else next_f()
      end
  | Var(v,l) ->
      begin
	match t'.t_desc with
	  Var(v',l') when v == v' ->
	    match_term_list2 next_f simp_facts bl l l'
	| _ -> if not (Terms.simp_equal_terms simp_facts true t t') then raise NoMatch else next_f()
      end
  | FunApp _ ->
      Parsing_helper.internal_error "Function symbol in Simplify1.match_term2. Should never occur since it is used to match binderrefs only"
  | _ -> Parsing_helper.internal_error "If, find, let, and new should not occur in match_term2"

and match_term_list2 next_f simp_facts bl l l' = 
  match l,l' with
    [],[] -> next_f()
  | a::l,a'::l' ->
      match_term2 (fun () -> match_term_list2 next_f simp_facts bl l l') 
	simp_facts bl a a'
  | _ -> Parsing_helper.internal_error "Different lengths in match_term_list2"


let match_binderref2 next_f simp_facts bl (b,l) (b',l') =
  if b != b' then raise NoMatch;
  match_term_list2 next_f simp_facts bl l l'

let rec match_among next_match simp_facts bl br = function
    [] -> raise NoMatch
  | (br1::brl) ->
      try 
	Terms.ri_auto_cleanup (fun () ->
	  match_binderref2 next_match simp_facts bl br br1)
      with NoMatch ->
	match_among next_match simp_facts bl br brl

let rec match_among_list next_match simp_facts bl def_vars = function
    [] -> next_match()
  | (br1::brl) ->
      match_among (fun () -> 
	match_among_list next_match simp_facts bl def_vars brl) 
	simp_facts bl br1 def_vars
  

(* Test if a branch of find always succeeds *)

exception SuccessBranch of (binder * repl_index * term) list * (binder * repl_index) list

let final_next2 dep_info bl true_facts t1 () =
  let bl' = List.map snd bl in
  let t1' = Terms.copy_term Terms.Links_RI t1 in
  (* Cleanup links, with possibility to restore *)
  let tmp_list = List.map (fun b -> b.ri_link) bl' in
  List.iter (fun b -> b.ri_link <- NoLink) bl';
  (* Raise Contradiction when t1 implied *)
  begin
    try 
      Terms.ri_auto_cleanup (fun () -> 
	ignore (Facts.simplif_add dep_info true_facts (Terms.make_not t1')))
    with Contradiction ->
      (* For the value of bl computed in the links, t1 is true;
	 furthermore match_among_list has checked that all variables
	 in def_list are defined, so this branch of find succeeds *)
      (* print_string "Proved ";
         Display.display_term t1';
         print_newline();*)
      let subst = ref [] in
      let keep_bl = ref [] in
      List.iter2 (fun (b,b') l -> 
	match l with
	  TLink b_im -> subst := (b,b',b_im) :: (!subst)
	| NoLink -> keep_bl := (b,b') :: (!keep_bl)) bl tmp_list;
      raise (SuccessBranch(!subst, !keep_bl))
  end;
  (* Restore links *)
  List.iter2 (fun b l -> b.ri_link <- l) bl' tmp_list;
  (* Backtrack *)
  raise NoMatch

(* Raises SuccessBranch when the branch is proved to succeed for some
   value of the indices. These values are stored in the argument of SuccessBranch *)

let branch_succeeds ((bl, def_list, t1, _): 'b findbranch) dep_info true_facts def_vars =
  let bl'' = List.map snd bl in
  try
    match_among_list (final_next2 dep_info bl true_facts t1) true_facts bl'' def_vars def_list
  with NoMatch -> ()

(* Treatment of elsefind facts *)

let final_next true_facts t () =
  let t' = Terms.copy_term Terms.Links_RI t in
  true_facts := (Terms.make_not t')::(!true_facts);
  (* Backtrack *)
  raise NoMatch

let always_true_def_list_t true_facts t simp_facts bl def_vars def_list =
  try
    match_among_list (final_next true_facts t) simp_facts bl def_vars def_list
  with NoMatch -> ()

let rec add_elsefind dep_info def_vars ((subst, facts, elsefind) as simp_facts) = function
    [] -> simp_facts
  | (((bl, def_list, t1,_):'a findbranch)::l) -> 
      (* When the condition t1 contains if/let/find/new, we simply ignore it when adding elsefind facts. *)
      let simp_facts' = 
	match (bl, def_list, t1.t_desc) with
	  [],[],(Var _ | FunApp _) -> Facts.simplif_add dep_info simp_facts (Terms.make_not t1)
	| _,[],_ -> simp_facts
	| _,_,(Var _ | FunApp _) -> 
	    let bl' = List.map snd bl in
	    let true_facts_ref = ref [] in
	    let simp_facts = (subst, facts, (bl', def_list, t1)::elsefind) in
	    always_true_def_list_t true_facts_ref t1 simp_facts bl' def_vars def_list;
	    Facts.simplif_add_list dep_info simp_facts (!true_facts_ref)
	| _ -> simp_facts
      in
      add_elsefind dep_info def_vars simp_facts' l

let update_elsefind_with_def bl (subst, facts, elsefind) =
  (subst, facts, List.map (Terms.update_elsefind_with_def bl) elsefind)

let convert_elsefind dep_info def_vars ((_, _, elsefind) as simp_facts) =
  let true_facts_ref = ref [] in
  List.iter (fun (bl, def_list, t1) ->
    always_true_def_list_t true_facts_ref t1 simp_facts bl def_vars def_list
    ) elsefind;
  (* print_string "Convert_elsefind: found\n";
  List.iter (fun t -> Display.display_term t; print_newline()) (!true_facts_ref);
  print_newline(); *)
  Facts.simplif_add_list dep_info simp_facts (!true_facts_ref)


(* Reasoning that depends on assumptions on the order of definition
   of variables. *)

	    (* Dependency analysis that takes into account assumption on the
   definition order

   dep_info = (list of array ref defined later; list of array ref defined before)
 *)

let rec dependency_collision_rec2bis cur_array simp_facts order_assumptions ((defl_after, defl_before) as dep_info) t1 t2 t =
  match t.t_desc with
    Var(b,l) when (Terms.is_restr b) && (Terms.mem_binderref (b,l) defl_after) && (Proba.is_large_term t) ->
      begin
        if (!Settings.debug_elsefind_facts) then
          begin
            print_string "t t1 t2="; 
	    Display.display_term t;print_string ", "; 
	    Display.display_term t1;print_string ", ";
	    Display.display_term t2;
          end;

	let depinfo =
	  { args_at_creation_only = false;
	    dep = [];
	    other_variables = true;
	    nodep = defl_before }
	in
        let t' = Depanal.remove_dep_array_index (b,depinfo) t in
        let l_after' = 
	  match t'.t_desc with
	    Var (_,l_after') -> l_after'
	  | _ -> Parsing_helper.internal_error "t' must be a variable in dependency_collision_rec2bis"
	in
        if (!Settings.debug_elsefind_facts) then
          begin
            Display.display_term t;print_string " is restriction.";
	    print_newline ();
          end;
	let t1' = Depanal.remove_dep_array_index (b,depinfo) t1 in
        if (!Settings.debug_elsefind_facts) then
          begin
            print_string "remove_dep_array_index t1=";
	    Display.display_term t1';print_newline ()
          end;
	match Depanal.extract_from_status t1' (Depanal.find_compos (b, depinfo) (Some l_after') t1') with
	| Some(probaf, t1'', _) -> 
	    begin
	    try 
              if (!Settings.debug_elsefind_facts) then
                begin
                  print_string "FindCompos ok";print_newline ()
                end;
	      let (t2', dep_types, indep_types) = Depanal.is_indep simp_facts (b, depinfo) t2 in
	      (* add probability, if small enough. returns true if proba small enough, false otherwise *)
	      Depanal.add_term_collisions (cur_array, Facts.true_facts_from_simp_facts simp_facts, order_assumptions, Terms.make_true()) t1'' t2' b (Some l_after') (probaf, dep_types, t2.t_type, indep_types)
	    with Not_found -> false
	    end
	| None -> false
      end 
  | FunApp(f,l) ->
      List.exists (dependency_collision_rec2bis cur_array simp_facts order_assumptions dep_info t1 t2) l
  | _ -> false

(* Dependency analysis taking into account the order of definition of the variables. 
   Here dep_info is a list of array ref defined after and a list of array ref defined before *)

let dependency_anal_order_hyp cur_array order_assumptions dep_info =
  let indep_test simp_facts t (b,l) =
    let (defl_after, defl_before) = dep_info in
    let depinfo =
      { args_at_creation_only = false;
	dep = [];
	other_variables = true;
	nodep = defl_before }
    in
    (* reconstruct the initial list: indices may have been
       replaced with fresh replication indices to make them independent *)
    let linit = List.map (Terms.copy_term Terms.Links_RI) l in
    if Terms.mem_binderref (b,linit) defl_after then
      Facts.default_indep_test depinfo simp_facts t (b,l)
    else
      None
  in
  let collision_test simp_facts t1 t2 =
    let t1' = Terms.try_no_var_rec simp_facts t1 in
    let t2' = Terms.try_no_var_rec simp_facts t2 in
    if (!Settings.debug_elsefind_facts) then
      begin
	print_string "dependency_anal_order_hyp: ";
	Display.display_term t1; print_string ", ";
	Display.display_term t2; print_newline ();
	print_string "simplified t1,t2=";
	Display.display_term t1'; print_string ", ";
	Display.display_term t2'; print_newline ();
      end;
    let b =   
      (dependency_collision_rec2bis cur_array simp_facts order_assumptions dep_info t1' t2' t1') ||
      (dependency_collision_rec2bis cur_array simp_facts order_assumptions dep_info t2' t1' t2')
    in
    if (!Settings.debug_elsefind_facts) then
      begin
	print_string (if b then "Result: true" else "Result: false");
	print_newline ()
      end;
    if b then Some (Terms.make_false()) else None
  in
  (indep_test, collision_test)

(* [is_in_bl bl t] returns true when the term [t] is equal to some
   variable in the list [bl] *)

let is_in_bl bl t =
  match t.t_desc with
    Var(b,l) ->
      (List.memq b bl) && (Terms.is_args_at_creation b l)
  | _ -> false

(* [above_input_node n] returns the first node corresponding to
   an input above [n]. *)

let rec above_input_node n =
  if n.above_node == n then
    Parsing_helper.internal_error "reached beginning of program without seeing an input";
  match n.definition with
    DInputProcess _ -> n
  | _ -> above_input_node n.above_node
    
(* get_elsefind_facts *)

(* this function returns the list of all the binderref that are defined before the node `node' after transformation through the rename_br transformation, and stops if it encounters a binder from stop_binders or if the node is stop_node *)

let rec add_vars_until_binder_or_node node stop_binders stop_node acc =
  if (node == node.above_node) then
    (
      if (!Settings.debug_elsefind_facts) then
        begin
          print_string "Bug ?";
          print_newline ()
        end;
      acc
    )
  else
  if (node == stop_node) then
    (
      if (!Settings.debug_elsefind_facts) then
        begin
          print_string "Elsefind_fact add_vars stopped at input_node";
          print_newline ()
        end;
      acc
    )
  else if (List.exists (fun b -> List.mem b node.binders) stop_binders) then
      (
        if (!Settings.debug_elsefind_facts) then
          begin
            print_string "Elsefind_fact add_vars stopped because var b or br found";
            print_newline ()
          end;
        acc
      )
  else
    (add_vars_until_binder_or_node node.above_node stop_binders stop_node (node.binders @ acc))
  

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
  if (!Settings.debug_elsefind_facts) then
    begin
      print_string "-----------------\n";
      print_string "Variables known to be currently defined: ";
      Display.display_list (fun (b,tl) -> Display.display_var b tl) def_vars;
      print_newline();
      print_string "Variable known to be defined in an else branch of find: ";
      Display.display_var b tl;
      print_newline ();
      print_string "Elsefind_fact (before renaming): ";
      Facts.display_elsefind elsefind_fact
    end;

  (* decompose def_list into subterms: all *subterms* of def_list must
     be defined before the find so that we can conclude not(t1) from
     the elsefind fact. *)
  let def_list_subterms = ref [] in
  List.iter (Terms.close_def_subterm def_list_subterms) def_list;
  let def_list = !def_list_subterms in

  (* Optimization: if we know that an element br1 is defined before br2 = (b2,tl2) in deflist', 
     we can remove br1. Indeed, assuming that br2 is defined before (b,tl) implies that
     br1 is defined before (b,tl), so that is enough to apply the elsefind fact. 
     This optimization does not seem to affect much the speed of the system. *)
  let rec filter_def_list already_seen = function
      [] -> List.rev already_seen
    | ((b2,tl2)::l) ->
	let before_br2 = 
	  try 
            Terms.subst_def_list b2.args_at_creation tl2 (Facts.def_vars_from_defined None [Terms.binderref_from_binder b2])
	  with Contradiction -> 
	    (* Contradiction may be raised when b2 can in fact not be defined. *)
	    []	
	in
	let already_seen' = Terms.setminus_binderref already_seen before_br2 in
	let l' = Terms.setminus_binderref l before_br2 in
	filter_def_list ((b2,tl2)::already_seen') l'
  in
  let def_list = filter_def_list [] def_list in

  (* transform the elsefind fact such that the variable (b,b.args_at_creation) 
     for the original fact corresponds to our variable (b,tl):
     substitute b.args_at_creation with tl. *)
  let b_index = b.args_at_creation in
  let (bl, def_list, t1) = Terms.subst_else_find b_index tl (bl, def_list, t1) in

  if (!Settings.debug_elsefind_facts) then
    begin
      print_string "Elsefind_fact (after renaming): ";
      Facts.display_elsefind (bl,def_list,t1)
    end;

  (* We have [elsefind_fact = (bl,def_list,t1)], which means [forall bl, not (defined(def_list) && t1)].
     We collect in variable [result] the pairs (def_list', t') instances of (def_list, t1) such that
     the elements of [def_list'] are defined at the current program point. (They are in [def_vars].) *)
  let result = ref [] in
  begin
    try 
      match_among_list (final_next3 bl def_list t1 result) simp_facts bl def_vars def_list
    with NoMatch -> ()
  end;
    
  List.iter (fun (def_list',t') ->
      if (!Settings.debug_elsefind_facts) then
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

    (* Variables defined before or at the same time as (b,tl) *)
    let def_vars_before = 
      try 
        Terms.subst_def_list b_index tl (Facts.def_vars_from_defined None [Terms.binderref_from_binder b])
      with Contradiction -> 
	(* Contradiction may be raised when b can in fact not be defined. *)
	[]
    in

    (* [additional_disjuncts] stores additional disjuncts: 
       we actually prove (!additional_disjuncts) || (not t') *)
    let additional_disjuncts = ref [] in
    
      if (!Settings.debug_elsefind_facts) then
        begin
          print_string "Elsefind_fact_vars_before:\n";
          Display.display_list Display.display_term (List.map Terms.term_from_binderref def_vars_before);
          print_newline ()
        end;
      if (
        List.for_all (fun br ->
          (* Let us suppose that br has been defined after or at (b,tl) *)
          if (!Settings.debug_elsefind_facts) then
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
                  [assumed_distinct_block] is true when we make this assumption. *)
	  let vars_at_b = List.concat (List.map (fun n -> n.binders) b.def) in
	  let (def_vars_before, assumed_distinct_block) = 
	    if List.memq (fst br) vars_at_b then
              if (List.for_all2 Terms.equal_terms (snd br) tl) ||
                   (not (!Settings.else_find_additional_disjunct))
              then
	        (Terms.setminus_binderref def_vars_before (List.map (fun b' -> (b', tl)) vars_at_b), false)
              else
                begin
                  let disjunct = Terms.make_and_list (List.map2 Terms.make_equal (snd br) tl) in
                  additional_disjuncts := disjunct::(!additional_disjuncts);
                  if (!Settings.debug_elsefind_facts) then
                    begin
                      print_string "We assume that not(";
                      Display.display_term disjunct;
                      print_string ") so that ";
	              Display.display_term (Terms.term_from_binderref br);
	              print_string " is defined strictly after ";
	              Display.display_term (Terms.term_from_binderref (b,tl));
                      print_newline ()
                    end;
                  (def_vars_before, true)
                end
	    else
	      (def_vars_before, false)
	  in

	  (* If br is in def_vars_before, br is defined before (b,tl), so the assumption 
	     that br is defined after (b,tl) never holds. 
	     (due to the modification of def_vars_before above, br is never defined
	     at the same time as (b,tl) when it is in def_vars_before) *)
	  (Terms.mem_binderref br def_vars_before) || (
          let order_assumptions = [br,(b,tl)] in
          List.for_all (fun n -> (* for each definition def_node of br *)
            try
                (* Compute variables that are defined after (b,tl):
		   add to the future variables of br the variables defined between the previous input 
		   point and the definition of br and after another definition of (b,_). *)
              let future_binders =
                if assumed_distinct_block then
                  (* we assumed that the indices of br are different from those of b[tl]
                     and br is defined after b[l], so all variables from the input point before br
                     to the definition of br and variables certainly defined after the definition of br
                     are defined after b[tl] *)
                  add_vars_until_binder_or_node n [] (above_input_node n) n.future_binders
                else
                  add_vars_until_binder_or_node n [b] (above_input_node n) n.future_binders
              in
	      let future_vars = Terms.subst_def_list (fst br).args_at_creation (snd br) (List.map Terms.binderref_from_binder future_binders) in

	      (* Variables in [def_vars] are known to be defined.
                 If they cannot be defined before or at the same time as [(b,tl)] or a binderref 
		 already in [future_vars], then they
	         are certainly defined after [(b,tl)], so we can add them
	         to [future_vars] *)
	      let future_vars = 
		List.fold_left (fun future_vars br' ->
		  if (not (Terms.may_def_before br' (b,tl) &&
			   List.for_all (Terms.may_def_before br') future_vars)) &&
		     (not (Terms.mem_binderref br' future_vars)) 
		  then
		    br' :: future_vars
		  else
		    future_vars) future_vars def_vars
	      in

              if (!Settings.debug_elsefind_facts) then
                begin
                  print_string "Elsefind_fact_future_vars:\n";
                  Display.display_list Display.display_term (List.map Terms.term_from_binderref future_vars);
                  print_newline ()
                end;

	      (* Elements of future_vars are defined after those of def_vars_before;
	         If they are in def_vars_before, that's a contradiction *)
	      if List.exists (fun future_br -> Terms.mem_binderref future_br def_vars_before) future_vars then
		raise Contradiction;

	      (* Since br is defined after (b,tl), all elements of future_vars are defined after (b,tl).
		 The elements of def_vars_before are defined before (b,tl), so before the elements
		 of future_vars. 
		 Therefore, the elements of def_vars_before are independent of the elements of future_vars
		 that are randomly chosen. *)
              let dep_info = (future_vars, List.map Terms.term_from_binderref def_vars_before) in
     
                if (!Settings.debug_elsefind_facts) then
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
                    Facts.display_facts simp_facts;
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

		(* Rename indices b'.args_at_creation -> tl *)
		let def_list = Terms.subst_def_list b'.args_at_creation tl' def_list in
		let t1 = Terms.subst b'.args_at_creation tl' t1 in

                (* We add to [fact_accu] the facts [not t'] where the pairs 
		   (def_list', t') are instances of (def_list, t1) such that
		   the elements of [def_list'] are defined at the definition of b[tl]. 
		   (They are in [def_vars_before].) *)
		begin
		  try 
		    match_among_list (final_next4 bl def_list t1 fact_accu) simp_facts bl def_vars_before def_list
		  with NoMatch -> ()
		end;
		  ) elsefind_facts;

              (* Note: we re-add the facts that are already in simp_facts, 
                 because the dependency information can allow further 
                 simplifications on them as well. 
		 We add [t'] last, so that we can already exploit 
		 the values of variables known previously when using
		 the dependency analysis on [t']. *)
	      let dep_anal = dependency_anal_order_hyp cur_array order_assumptions dep_info in
              let simp_facts1 = Facts.simplif_add_list dep_anal ([],[],[]) subst in
	      let simp_facts2 = Facts.simplif_add_list dep_anal simp_facts1 facts in
	      let simp_facts3 = Facts.simplif_add_list dep_anal simp_facts2 (!fact_accu) in
	      let _ = Facts.simplif_add dep_anal simp_facts3 t' in
                if (!Settings.debug_elsefind_facts) then
                  begin
                    Settings.debug_simplif_add_facts := false;
                    print_string "Failed to obtain a contradiction.";
                    print_newline ()
                  end;
                false
            with Contradiction -> 
              if (!Settings.debug_elsefind_facts) then
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
          if (!Settings.debug_elsefind_facts) then
	    begin
	      print_string "Found a usable term: ";
	      Display.display_term t;
	      print_newline ()
	    end
        end
      else
        begin
          if (!Settings.debug_elsefind_facts) then
            begin
              print_string "Found no usable terms.";
              print_newline ()
            end
	end
	  ) (!result)


let get_facts_of_elsefind_facts g cur_array simp_facts def_vars =
  if (!Settings.debug_elsefind_facts) then
    begin
      print_string "__________________\n";
      print_string "Elsefind begin\n";
      print_newline ()
    end; 
(*  print_string "Defined variables original:\n";
  List.iter (fun (b,l) -> Display.display_var b l; print_newline()) def_vars; *)
  let def_vars_tmp = ref [] in
  List.iter (fun (b,l) ->
    let br' = (b, List.map (Terms.try_no_var simp_facts) l) in
    Terms.add_binderref br' def_vars_tmp) def_vars;
  let def_vars = !def_vars_tmp in
(*  print_string "Defined variables simplified:\n";
  List.iter (fun (b,l) -> Display.display_var b l; print_newline()) def_vars; *)
  let term_accu = ref [] in
  let effl = collect_eff def_vars in
  List.iter (fun (br, eff) -> get_fact_of_elsefind_fact term_accu g cur_array def_vars simp_facts br eff) effl;
  if (!Settings.debug_elsefind_facts) then
    begin
      print_string "__________________\n";
      print_string "Elsefind summary: these terms are true:\n";
      Display.display_list Display.display_term (!term_accu);
      print_newline ()
    end;
  (!term_accu)


    
(* [needed_vars vars] returns true when some variables in [vars]
   have array accesses or are used in queries. That is, we must keep
   them even if they are not used in their scope. *)
	
let needed_vars vars q = List.exists (fun b -> Terms.has_array_ref_q b q) vars

let needed_vars_in_pat pat q =
  needed_vars (Terms.vars_from_pat [] pat) q

(* Add lets *)

let rec add_let p = function
    [] -> p
  | ((b, b_im)::l) ->
      Terms.oproc_from_desc (Let(PatVar b, b_im, add_let p l, Terms.oproc_from_desc Yield))

let rec add_let_term p = function
    [] -> p
  | ((b, b_im)::l) ->
      Terms.build_term_type p.t_type (LetE(PatVar b, b_im, add_let_term p l, None))

(* [not_found_repl_index_t ri t] returns either
   [None] when [t] does not contain any replication index of [ri]
   or [Some def_list] where [def_list] is a list of the largest variable
   references in [t] that do not contain indices in [ri] *)

let rec not_found_repl_index_l ri = function
    [] -> None
  | (a::l) ->
      let r1 = not_found_repl_index_l ri l in
      let r2 = not_found_repl_index_t ri a in
      match r1, r2 with
	None, None -> None
      |	Some (def_list1), Some(def_list2) -> Some (def_list1 @ def_list2)
      |	None, Some(def_list2) -> 
	  let accu = ref def_list2 in
	  List.iter (Terms.get_deflist_subterms accu) l;
	  Some(!accu)
      |	Some(def_list1), None ->
	  let accu = ref def_list1 in
	  Terms.get_deflist_subterms accu a;
	  Some(!accu)

and not_found_repl_index_t ri t =
  match t.t_desc with
    Var(_,l) | FunApp(_,l) -> not_found_repl_index_l ri l
  | ReplIndex i -> 
      if List.memq i ri then Some [] else None
  | _ -> Parsing_helper.internal_error "This term should not occur in def_list, in Transf_simplify.not_found_repl_index_t"
      
(* [not_found_repl_index_br accu ri def_list] adds to [accu]
   the largest sub-array-references in [def_list] that do not contain 
   replication indices in [ri]. *)

let not_found_repl_index_br accu ri (b,l) =
  match not_found_repl_index_l ri l with
    Some(def_list) -> List.iter (fun br -> Terms.add_binderref br accu) def_list
  | None -> Terms.add_binderref (b,l) accu 

(* [filter_deflist_indices bl def_list] removes from [def_list] all
   elements that refer to replication indices in [bl].
   Used when we know that the indices in [bl] are in fact not used. *)

let filter_deflist_indices bl def_list =
  let ri = List.map snd bl in
  let accu = ref [] in
  List.iter (not_found_repl_index_br accu ri) def_list;
  !accu
  
(* [is_unique l0' find_info] returns Unique when a [find] is unique,
   that is, at runtime, there is always a single possible branch 
   and a single possible value of the indices:
   either it is marked [Unique] in the [find_info],
   or it has a single branch with no index.
   [l0'] contains the branches of the considered [find]. *)

let is_unique l0' find_info =
  match l0' with
    [([],_,_,_)] -> Unique
  | _ ->
      match find_info with
      | UniqueToProve -> Nothing
      | _ -> find_info

(* [infer_unique g cur_array simp_facts def_vars dep_info current_history l0' find_info]
   tries to prove that there is single possible choice in the find with
   branches [l0'], and if so it returns the modified [find_info] equal to
   [Unique]. It also returns a boolean set to true when a real change has been made.

   [g] is the current game
   [cur_array] the current replication indices
   [simp_facts] the facts known to hold at the current program point
   [def_vars] the variables known to be defined
   [dep_info] is a dependency analysis
   [current_history] is the known history at the find, at which [def_list]
   is tested (may be returned by [Facts.get_initial_history]) *)

let prove_unique g cur_array simp_facts def_vars dep_info node l0' =
  let unique_branch (bl, def_list1, t1, _) =
    let repl_index1 = List.map snd bl in
    let repl_index1_term = List.map Terms.term_from_repl_index repl_index1 in
    let repl_index2 = List.map Terms.new_repl_index repl_index1 in
    let repl_index2_term = List.map Terms.term_from_repl_index repl_index2 in
    let def_list2 = Terms.subst_def_list repl_index1 repl_index2_term def_list1 in
    let t2 = Terms.subst repl_index1 repl_index2_term t1 in
    try 
      let def_vars1 = Facts.def_vars_from_defined node def_list1 in
      let facts_def_list1 = Facts.facts_from_defined node def_list1 in
      let def_vars2 = Facts.def_vars_from_defined node def_list2 in
      let facts_def_list2 = Facts.facts_from_defined node def_list2 in
      let def_vars = Terms.union_binderref (Terms.union_binderref def_vars def_vars1) def_vars2 in
      let diff_ri1_ri2 = Terms.make_or_list (List.map2 Terms.make_diff repl_index1_term repl_index2_term) in
      let simp_facts = Facts.simplif_add_list dep_info simp_facts (diff_ri1_ri2 :: t2 :: t1 :: facts_def_list1 @ facts_def_list2) in
      let new_facts = get_facts_of_elsefind_facts g cur_array simp_facts def_vars in
      let _ = Facts.simplif_add_list dep_info simp_facts new_facts in
      false
    with Contradiction -> true
  in
  let incompatible_branch (bl1, def_list1, t1, _) (bl2, def_list2_orig, t2_orig, _) =
    let repl_index2_orig = List.map snd bl2 in
    let repl_index2 = List.map Terms.new_repl_index repl_index2_orig in
    let repl_index2_term = List.map Terms.term_from_repl_index repl_index2 in
    let def_list2 = Terms.subst_def_list repl_index2_orig repl_index2_term def_list2_orig in
    let t2 = Terms.subst repl_index2_orig repl_index2_term t2_orig in
    try 
      let def_vars1 = Facts.def_vars_from_defined node def_list1 in
      let facts_def_list1 = Facts.facts_from_defined node def_list1 in
      let def_vars2 = Facts.def_vars_from_defined node def_list2 in
      let facts_def_list2 = Facts.facts_from_defined node def_list2 in
      let def_vars = Terms.union_binderref (Terms.union_binderref def_vars def_vars1) def_vars2 in
      let simp_facts = Facts.simplif_add_list dep_info simp_facts (t2 :: t1 :: facts_def_list1 @ facts_def_list2) in
      let new_facts = get_facts_of_elsefind_facts g cur_array simp_facts def_vars in
      let _ = Facts.simplif_add_list dep_info simp_facts new_facts in
      false
    with Contradiction -> true
  in
  (List.for_all unique_branch l0') &&
  (let rec incompatible_branches = function
    | [] | [_] -> true
    | branch1 :: rest -> 
        (List.for_all (incompatible_branch branch1) rest) &&
        (incompatible_branches rest)
  in
  incompatible_branches l0')

let infer_unique g cur_array simp_facts def_vars dep_info node l0' find_info =
  if not (!Settings.infer_unique) then
    (is_unique l0' find_info, false)
  else
    match is_unique l0' find_info with
    | Unique -> (Unique, false)
    | UniqueToProve
    | Nothing ->
       if prove_unique g cur_array simp_facts def_vars dep_info node l0' then
         (Unique, true)
       else
         (Nothing, false)
         
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
	always_true_def_list_t true_facts_ref t1 ([], [], []) bl' def_vars def_list;
	(!true_facts_ref)
    | _ -> accu
	  ) fact_accu l

let convert_elsefind2 accu def_vars elsefind =
  let true_facts_ref = ref accu in
  List.iter (fun (bl, def_list, t1) ->
    always_true_def_list_t true_facts_ref t1 ([],[],[]) bl def_vars def_list
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

