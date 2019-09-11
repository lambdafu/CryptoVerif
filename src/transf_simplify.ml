open Types
open Simplify1

let whole_game = ref Terms.empty_game

let current_pass_transfos = ref []

let known_when_adv_wins = ref (None : known_when_adv_wins option)
    
(* Priorities for orienting equalities into rewrite rules *)
let current_max_priority = Simplify1.current_max_priority
let priority_list = Simplify1.priority_list

let proba_state_at_beginning_iteration = ref (([],[]), [])
let failure_check_all_deps = ref []

(* Initialization of probability counting *)  

let reset coll_elim g =
  whole_game := g;
  (* Remove the advice found in Transf_globaldepanal in previous iterations. 
     If advice is still useful, we will find it again at the next iteration. *)
  Transf_globaldepanal.advise := [];
  proba_state_at_beginning_iteration := (Proba.get_current_state(), !term_collisions);
  failure_check_all_deps := [];
  current_max_priority := 0;
  List.iter (fun b -> b.priority <- 0) (!priority_list);
  priority_list := [];
  Simplify1.reset coll_elim g

let final_reset g_proc =
  current_pass_transfos := [];
  Terms.cleanup_array_ref();
  Simplify1.empty_improved_def_process true g_proc;
  whole_game := Terms.empty_game;
  List.iter (fun b -> b.priority <- 0) (!priority_list);
  priority_list := [];
  failure_check_all_deps := [];
  known_when_adv_wins := None;
  proba_state_at_beginning_iteration := (([],[]), [])

(* Dependency analysis
   When M1 characterizes a part of x of a large type T
   and M2 does not depend on x, then M1 = M2 fails up to
   negligible probability.
   The module FindCompos defines "characterize"
   The modules Transf_globaldepanal and DepAnal2 perform dependency analyses
   Function dependency_collision concludes *)

module DepAnal2 :
sig
(* Local dependency analysis: take into account the freshness
   of the random number b to determine precisely which expressions depend on b
   for expressions defined before the first output that follows the choice
   of b *)

  type dep_info 
  type elem_dep_info = unit Types.depinfo
  (* The dependency information [dep_info] contains a list of
     [(b, depinfo)] that associates to each variable [b]
     its dependency information [depinfo] of type [elem_dep_info]. 
     See type ['a depinfo] in types.ml for an explanation of this type. *)

  (* [init] is the empty dependency information *)
  val init : dep_info


  (* [update_dep_info] and [update_dep_infoo] update the dependency information
     inside processes.

     [update_dep_info cur_array dep_info true_facts p] returns the dependency information
     valid at the immediate subprocesses of [p] when [p] is an input process. The dependency
     information is the same for all subprocesses of [p], and is actually equal to the
     dependency information for [p] itself.

     [update_dep_infoo cur_array dep_info true_facts p] returns a simplified version [p']
     of process [p] (using the dependency information), as well as the dependency information
     valid at the immediate subprocesses of [p'] when [p] is an output process. There is
     one dependency information for each immediate subprocess of [p'] (e.g. 2 for "if",
     one for the "then" branch and one for the "else" branch; one for each branch of "find",
     and so on).

     [cur_array] is the list of current replication indices.
     [dep_info] is the dependency information valid at [p].
     [true_facts] are facts that are known to hold at [p]. *)
  val update_dep_info : repl_index list -> dep_info -> simp_facts -> inputprocess -> dep_info
  val update_dep_infoo : repl_index list -> dep_info -> simp_facts -> process -> process * dep_info list 

  (* [get_dep_info dep_info b] extracts from [dep_info] the
     dependency information of the variable [b]. *)
  val get_dep_info : dep_info -> binder -> elem_dep_info

  (* find_compos_glob (b,depinfo) t   returns Some ty when
     t characterizes a part of b of type ty, knowing the dependency
     information given in depinfo. Otherwise, returns None. *)
  val find_compos_glob : binder * elem_dep_info -> term -> (probaf * term * term list option) option

end
= 
struct

  type elem_dep_info = unit Types.depinfo
  type dep_info = (binder * elem_dep_info) list

  let init = []

  let depends = FindCompos.depends
    
  let is_indep = FindCompos.is_indep
    
  let find_compos ((b,_) as bdepinfo) t =
    let t' = FindCompos.remove_dep_array_index bdepinfo t in
    let st = FindCompos.find_compos bdepinfo (Some (List.map Terms.term_from_repl_index b.args_at_creation)) t' in
    (st, FindCompos.extract_from_status t' st)

  exception Else
    	 
(* check_assign2 is called when the assigned term does not depend on b
   Return None when both branches may be taken and
          Some(charac_type, t') when only the else branch of the let
          may be taken. t' is the term with which the collision is
          eliminated and charac_type is the type of the part of t'
          characterized by the value of t' *)
let rec check_assign2 bdepinfo = function
    PatVar _ ->
      None
  | PatTuple(f,l) ->
      begin
        match check_assign2_list bdepinfo l with
	  None -> None
	| Some(probaf, l') ->
	    Some(probaf, Terms.build_term_type (snd f.f_type) (FunApp(f,l')))
      end
  | PatEqual t ->
      match find_compos bdepinfo t with
	_, Some (probaf, t', _) when Proba.is_large_term t ->
	  Some (probaf, t')
      |	_ ->
	  None

and check_assign2_list bdepinfo = function
    [] -> None
  | (a::l) ->
      match check_assign2 bdepinfo a with
	None -> 
	  begin
	    match check_assign2_list bdepinfo l with
	      None -> None
	    | Some(probaf, l') -> Some(probaf, (Facts.any_term_pat a)::l')
	  end
      |	Some(probaf, a') -> Some(probaf, a'::(List.map Facts.any_term_pat l))
      
let rec depends_pat bdepinfo = function
    PatVar _ ->
      false
  | PatTuple(f,l) ->
      List.exists (depends_pat bdepinfo) l
  | PatEqual t ->
      depends bdepinfo t

let rec simplify_term cur_array dep_info true_facts t =
  match t.t_desc with
    FunApp(f,[t1;t2]) when f == Settings.f_and ->
      (* We simplify t2 knowing t1 and t1 knowing t2, by swapping the "and"
         after the simplification of t2 *)
      begin
	try
	  let true_facts2 = Facts.simplif_add Facts.no_dependency_anal true_facts t1 in
	  let t2' = simplify_term cur_array dep_info true_facts2 t2 in
	  let true_facts1 = Facts.simplif_add Facts.no_dependency_anal true_facts t2' in
	  Terms.make_and (simplify_term cur_array dep_info true_facts1 t1)  t2'
	with Contradiction ->
	  Terms.make_false()
      end
  | FunApp(f,[t1;t2]) when f == Settings.f_or ->
      (* We simplify t2 knowing (not t1) and t1 knowing (not t2), 
	 by swapping the "or" after the simplification of t2 *)
      begin
	try
	  let true_facts2 = Facts.simplif_add Facts.no_dependency_anal true_facts (Terms.make_not t1) in
	  let t2' = simplify_term cur_array dep_info true_facts2 t2 in
	  let true_facts1 = Facts.simplif_add Facts.no_dependency_anal true_facts (Terms.make_not t2') in
	  Terms.make_or (simplify_term cur_array dep_info true_facts1 t1) t2' 
	with Contradiction ->
	  Terms.make_true()
      end
  | FunApp(f,[t1]) when f == Settings.f_not ->
      let t' = simplify_term cur_array dep_info true_facts t1 in
      if Terms.is_false t' then Terms.make_true() else
      if Terms.is_true t' then Terms.make_false() else
      Terms.make_not t'
  | FunApp(f,[t1;t2]) 
    when ((f.f_cat == Equal) || (f.f_cat == Diff)) && (Proba.is_large_term t1 || Proba.is_large_term t2) ->
      begin
	let rec try_dep_info = function
	    [] -> t
	  | ((b, _) as bdepinfo)::restl ->
	      match find_compos bdepinfo t1 with
		_, Some(probaf, t1'',_) ->
		  begin
		    try 
		      let (t2', dep_types, indep_types) = is_indep true_facts bdepinfo t2 in
                      (* add probability; if too large to eliminate collisions, raise Not_found *)
		      if not (add_term_collisions (cur_array, true_facts_from_simp_facts true_facts, [], Terms.make_true()) t1'' t2' b (Some (List.map Terms.term_from_repl_index b.args_at_creation)) (probaf, dep_types, t2.t_type, indep_types)) then raise Not_found;
		      if (f.f_cat == Diff) then Terms.make_true() else Terms.make_false()
		    with Not_found ->
		      try_dep_info restl
		  end
	      | _, None -> 
		  match find_compos bdepinfo t2 with
		  _, Some(probaf, t2'',_) ->
		    begin
		      try 
			let (t1', dep_types, indep_types) = is_indep true_facts bdepinfo t1 in
                        (* add probability; if too large to eliminate collisions, raise Not_found *)
			if not (add_term_collisions (cur_array, true_facts_from_simp_facts true_facts, [], Terms.make_true()) t2'' t1' b (Some (List.map Terms.term_from_repl_index b.args_at_creation)) (probaf, dep_types, t1.t_type, indep_types)) then raise Not_found;
			if (f.f_cat == Diff) then Terms.make_true() else Terms.make_false()
		      with Not_found ->
			try_dep_info restl
		    end
		| _, None ->
		    try_dep_info restl
	in
	try_dep_info dep_info
      end
  | _ -> t

(* Takes a dep_info as input and returns the new dep_info for the subprocesses
   of the input process p *)

let update_dep_info cur_array dep_info true_facts p = dep_info

(* Takes a dep_info as input and returns a simplified process and
   the list of new dep_info's for the subprocesses *)

let rec update_dep_infoo cur_array dep_info true_facts p' =
  let pp = DProcess p' in
  match p'.p_desc with
    Yield -> (Terms.oproc_from_desc2 p' Yield, [])
  | EventAbort f -> (Terms.oproc_from_desc2 p' (EventAbort f), [])
  | Restr(b,p) ->
      let b_term = Terms.term_from_binder b in
      let dep_info' = List.map (fun (b', depinfo) -> (b', { depinfo with nodep = b_term::depinfo.nodep })) dep_info in
      if Proba.is_large b.btype then
	try 
	  let def_vars = Facts.get_def_vars_at (DProcess p') in
	  (Terms.oproc_from_desc (Restr(b,p)), 
	   [(b, { args_at_creation_only = true;
		  dep = [b, (Decompos(Some(List.map Terms.term_from_repl_index b.args_at_creation)), None, ())];
		  other_variables = false;
		  nodep = List.map Terms.term_from_binderref def_vars }) :: dep_info' ])
	with Contradiction ->
	  (* The current program point is unreachable, because it requires the definition
	     of a variable that is never defined *)
	  (Terms.oproc_from_desc2 p' Yield, [])
      else
	(Terms.oproc_from_desc2 p' (Restr(b,p)), [dep_info'])
  | Test(t,p1,p2) ->
      let t' = simplify_term cur_array dep_info true_facts t in
      if Terms.is_true t' then
	begin
	  Settings.changed := true;
	  current_pass_transfos := (STestTrue(pp)) :: (!current_pass_transfos);
	  update_dep_infoo cur_array dep_info true_facts p1
	end
      else if Terms.is_false t' then
	begin
	  Settings.changed := true;
	  current_pass_transfos := (STestFalse(pp)) :: (!current_pass_transfos);
	  update_dep_infoo cur_array dep_info true_facts p2
	end
      else
	let r = List.map (function ((b, depinfo) as bdepinfo) ->
	  if depends bdepinfo t' then
	    (b, { depinfo with other_variables = true })
	  else
	    bdepinfo) dep_info
	in
	if not (Terms.equal_terms t t') then 
	  begin
	    Settings.changed := true;
	    current_pass_transfos := (SReplaceTerm(t,t')) :: (!current_pass_transfos);
	  end;
	(Terms.oproc_from_desc2 p' (Test(t',p1,p2)), [r])
  | Find(l0,p2,find_info) ->
       let always_then = ref false in
       let rec simplify_find = function
          [] -> []
        | (bl, def_list, t, p1)::l ->
            let l' = simplify_find l in
	    let bl'' = List.map snd bl in
            let t' = simplify_term (bl'' @ cur_array) dep_info true_facts t
            in
            if Terms.is_false t' then 
	      begin
		Settings.changed := true;
		current_pass_transfos := (SFindBranchRemoved(pp, (bl, def_list, t, DProcess p1))) :: (!current_pass_transfos);
		l'
	      end 
	    else 
	      begin
		if Terms.is_true t' && def_list == [] then always_then := true;
		if not (Terms.equal_terms t t') then Settings.changed := true;
		(bl, def_list, t', p1)::l'
	      end
       in
       let l0' = simplify_find l0 in
       begin
	 match l0' with
	   [] -> 
	     Settings.changed := true;
             update_dep_infoo cur_array dep_info true_facts p2
	 | [([],[],t, p1)] when Terms.is_true t ->
	     Settings.changed := true;
	     current_pass_transfos := (SFindElseRemoved(pp)) :: (!current_pass_transfos);
	     update_dep_infoo cur_array dep_info true_facts p1
	 | _ ->
         (* For each b in dep_info.in_progress, does the branch taken
            depend on b? *)
         let dep_b = List.map (fun bdepinfo ->
	   let tmp_bad_dep = ref false in
	   let check_br (b, l) = 
	     if List.exists (depends bdepinfo) l then tmp_bad_dep := true
	   in
	   List.iter (fun (bl, def_list, t, p1) ->
	     List.iter check_br def_list;
	     if depends bdepinfo t then tmp_bad_dep := true;
		  ) l0';
           !tmp_bad_dep) dep_info 
	 in

         (* Dependence info for the "then" branches *)
         let dep_info_branches = List.fold_right (fun (bl, def_list, _, _) accu ->
	   let this_branch_node = Facts.get_initial_history (DProcess p') in
	   (* Variables that are certainly defined before the find do not depend on b *)
	   let nodep_add_cond = List.map Terms.term_from_binderref 
	     (try
	       Facts.def_vars_from_defined this_branch_node def_list
	     with Contradiction -> 
	       (* For simplicity, I ignore when a variable can in fact not be defined. 
		  I could remove that branch of the find to be more precise *)
	       def_list)
	       (* I add variables by closing recursively variables
	          that must be defined *)
	   in
	   (* nodep_add_then is the same as nodep_add_cond, except that
	      the replication indices of find are replaced with the corresponding variables. *)
	   let nodep_add_then = List.map (Terms.subst (List.map snd bl) 
	       (List.map (fun (b,_) -> Terms.term_from_binder b) bl)) nodep_add_cond 
	   in
	   (* Dependence info for the condition *)
	   let dep_info_cond = 
	     List.map (fun ((b, depinfo) as bdepinfo) ->
	       (b, { depinfo with nodep = (List.filter (fun t -> not (depends bdepinfo t)) nodep_add_cond) @ depinfo.nodep})
		 ) dep_info
	   in
	   (* Dependence info for the then branch.
	      The replication indices of find are replaced with the corresponding variables. *)
	   let dep_info_then = 
	     List.map2 (fun dep1 ((b, depinfo) as bdepinfo) ->
	       if dep1 then
		 (b, { depinfo with other_variables = true })
	       else
		 (b, { depinfo with nodep = (List.filter (fun t -> not (depends bdepinfo t)) nodep_add_then) @ depinfo.nodep })
		   ) dep_b dep_info
	   in
	   dep_info_cond :: dep_info_then :: accu
             ) l0' []
	 in
         (* Dependence info for the else branch *)
	 let dep_info_else = List.map2 
	     (fun dep1 ((b, depinfo) as bdepinfo) ->
	       if dep1 then
		 (b, { depinfo with other_variables = true })
	       else
		 bdepinfo) dep_b dep_info
	 in
         (Terms.oproc_from_desc2 p' (Find(l0',(if !always_then then Terms.oproc_from_desc Yield else p2), find_info)), dep_info_else :: dep_info_branches)
       end
  | Let(pat, t, p1, p2) ->
      begin
        match pat with
          PatVar b' -> 
            let dep_info' = 
              List.map (fun ((b, depinfo) as bdepinfo) ->
		if depends bdepinfo t then
                  match FindCompos.find_compos bdepinfo (Some (List.map Terms.term_from_repl_index b.args_at_creation)) t with
		  | Any ->
		      if depinfo.other_variables then
			bdepinfo
		      else
			(b, { depinfo with dep = (b', (Any,None,())) :: depinfo.dep })
		  | st ->
		      (b, { depinfo with dep = (b, (st,None,())) :: depinfo.dep })
		else
		  (b, { depinfo with nodep = (Terms.term_from_binder b')::depinfo.nodep })
                 ) dep_info 
            in
	    if p2.p_desc != Yield then 
	      begin
		Settings.changed := true;
		current_pass_transfos := (SLetElseRemoved(pp)) :: (!current_pass_transfos);
	      end;
            (Terms.oproc_from_desc2 p' (Let(pat, t, p1, Terms.oproc_from_desc Yield)), [dep_info'])
        | _ -> 
            let bl = Terms.vars_from_pat [] pat in
            let bl_terms = List.map Terms.term_from_binder bl in
	    try        
	      (* status is true when the chosen branch may depend on b *)
              let status ((b, _) as bdepinfo) =
		match find_compos bdepinfo t with
		| _, Some (probaf, t'',_) ->
		    let (t2', dep_types, indep_types) = FindCompos.is_indep_pat true_facts bdepinfo pat in
		    if add_term_collisions (cur_array, true_facts_from_simp_facts true_facts, [], Terms.make_true()) 
			t'' t2' b (Some (List.map Terms.term_from_repl_index b.args_at_creation))
			(probaf, dep_types, t.t_type, indep_types) then raise Else;
		    true
		| _, None ->
		    begin
		      match check_assign2 bdepinfo pat with
		      | None -> ()
		      |	Some(probaf, t1') ->
			  let (t2', dep_types, indep_types) = is_indep true_facts bdepinfo t in
			  (* Add probability *)
			  if add_term_collisions (cur_array, true_facts_from_simp_facts true_facts, [], Terms.make_true()) t1' t2' b (Some (List.map Terms.term_from_repl_index b.args_at_creation)) (probaf, dep_types, t.t_type, indep_types) then
			    raise Else
		    end;
		    (depends bdepinfo t) || (depends_pat bdepinfo pat)
	      in
	      (* dependency information for the "in" and "else" branches *)
	      let dep_info' = List.map (fun ((b, depinfo) as bdepinfo) ->
		if status bdepinfo then
		  let bdepinfo' = (b, { depinfo with other_variables = true }) in
		  (bdepinfo', bdepinfo')
		else
		  (b, { depinfo with nodep = bl_terms @ depinfo.nodep }), bdepinfo
		    ) dep_info
	      in
	      let dep_info1, dep_info2 = List.split dep_info' in
              (Terms.oproc_from_desc2 p' (Let(pat, t, p1, p2)), [dep_info1; dep_info2])
	    with Else ->         
	      Settings.changed := true;
	      current_pass_transfos := (SLetRemoved(pp)) :: (!current_pass_transfos);	      
	      update_dep_infoo cur_array dep_info true_facts p2
      end
  | Output _ ->
      (p', [List.map (fun (b, depinfo) -> (b, { depinfo with other_variables = true })) dep_info])
  | EventP _ ->
      (p', [dep_info])
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

  let get_dep_info dep_info b =
    try 
      List.assq b dep_info
    with Not_found ->
      Facts.nodepinfo (* Not found *)

  let find_compos_glob ((b, _) as b_depinfo) t =
    let t' = FindCompos.remove_dep_array_index b_depinfo t in
    FindCompos.extract_from_status t' (FindCompos.find_compos b_depinfo (Some (List.map Terms.term_from_repl_index b.args_at_creation)) t') 

end (* Module DepAnal2 *)

(* The exception [Restart(b,g)] is raised by [dependency_collision_rec1]
   when simplification should be restarted on the game [g] 
   obtained by a successful global dependency analysis 
   on binder [b]. *) 
exception Restart of binder * game

(* The functions [dependency_collision_rec1], [dependency_collision_rec2],
   and [dependency_collision_rec3] have similar interfaces.
   They all aim to simplify [t1 = t2] by eliminating collisions
   using dependency analyses.
   [dependency_collision_rec1] uses the global dependency analysis 
   (module [Transf_globaldepanal]).
   [dependency_collision_rec2] uses the local dependency analysis
   (module [DepAnal2]).
   [dependency_collision_rec3] just uses that randomly chosen values
   do not depend on other variables.
   Basically, the collision is eliminated when [t1] characterizes
   a large part of a random variable [b] and [t2] does not depend 
   on [b]. 
   [t] is a subterm of [t1] that contains the variable [b].
   (Initially, it is [t1], and recursive calls are made until [t] is 
   just a variable.)

   They return [None] when they fail, and [Some t'] when they
   succeed in simplifying [t1=t2] into [t'], except [dependency_collision_rec1]
   which raises exception [Restart] so that the simplification
   is restarted on the game after dependency analysis.

   [cur_array] is the list of current replication indices.
   [true_facts] is a list of facts that are known to hold.
   For [dependency_collision_rec2], [depinfo] contains the local
   dependency information. *)

let rec dependency_collision_rec1 cur_array simp_facts t1 t2 t =
  match t.t_desc with
    Var(b,l) when (Terms.is_restr b) && (Proba.is_large_term t) && (not (Terms.refers_to b t2)) ->
      begin
	match FindCompos.find_compos (b,Facts.nodepinfo) (Some l) t1 with
	| Any -> None
	| _ -> 
	    if List.memq b (!failure_check_all_deps) then None else
	    begin
	      print_string "Doing global dependency analysis on ";
	      Display.display_binder b;
	      print_string " inside simplify... "; flush stdout;
	      let current_proba_state = Proba.get_current_state() in
	      let current_term_collisions = !term_collisions in
	      match Transf_globaldepanal.check_all_deps b (!proba_state_at_beginning_iteration) (!whole_game) with
		None -> 
		  (* global dependency analysis failed *)
		  print_string "No change"; print_newline();
		  Proba.restore_state current_proba_state;
		  term_collisions := current_term_collisions;
		  failure_check_all_deps := b :: (!failure_check_all_deps);
		  None
	      | Some(res_game) ->
		  (* global dependency analysis succeeded. 
                     Restart simplification from the result of global dep anal *)
		  print_string "Done. Restarting simplify"; print_newline();
		  Settings.changed := true;
		  raise (Restart(b, res_game))
	    end
      end
  | FunApp(f,l) ->
      Terms.find_some (dependency_collision_rec1 cur_array simp_facts t1 t2) l
  | _ -> None

let rec dependency_collision_rec2 cur_array simp_facts dep_info t1 t2 t =
  match t.t_desc with
    Var(b,l) when (Terms.is_restr b) && (Proba.is_large_term t) && (Terms.is_args_at_creation b l) ->
      begin
	 let depinfo = DepAnal2.get_dep_info dep_info b in
	 match DepAnal2.find_compos_glob (b,depinfo) t1 with
	   None -> None
	 | Some(probaf, t1'',_) ->
	    try 
	      let collect_bargs = ref [] in
	      let collect_bargs_sc = ref [] in
	      let (t2', t2_eq, dep_types, indep_types) = Facts.is_indep simp_facts (b,l,depinfo,collect_bargs,collect_bargs_sc) t2 in
	      (* We eliminate collisions because t1 characterizes b[l] and t2 does not depend on b[l],
                 In case b occurs in t2, we reason as follows:
                    1/ When the indices of b in t2 are all different from l, t2 does not depend on b[l].
                       We eliminate collisions under that additional condition, hence the equality 
                       t1 = t2 is false in this case.
                       We collect in collect_bargs the indices l_i of b in t2. Hence the additional
                       condition is &&_(l_i in collect_bargs) l <> l_i. This condition is added
                       as side_condition below.
                    2/ Therefore, we can replace t1 = t2 with 
	               (t1 = t2) && (||_(l_i in collect_bargs) l = l_i),
	               which we rewrite
                       ||_(l_i in collect_bargs) (l = l_i && t1 = t2 { l/l_i }) 
		 *)
	      let side_condition = 
		Terms.make_and_list (List.map (fun l' ->
		  Terms.make_or_list (List.map2 Terms.make_diff l l')
		    ) (!collect_bargs_sc))
	      in
	      (* add probability; returns true if small enough to eliminate collisions, false otherwise. *)
	      if add_term_collisions (cur_array, true_facts_from_simp_facts simp_facts, [], side_condition) t1'' t2' b (Some (List.map Terms.term_from_repl_index b.args_at_creation)) (probaf, dep_types, t2.t_type, indep_types) then
		Some (Terms.make_or_list (List.map (fun l' ->   
		  let t2'' = Terms.replace l' l t2_eq in
		    Terms.make_and (Terms.make_and_list (List.map2 Terms.make_equal l l')) (Terms.make_equal t1 t2'')
		    ) (!collect_bargs)))
              else
                None
	    with Not_found -> None
      end 
  | FunApp(f,l) ->
      Terms.find_some (dependency_collision_rec2 cur_array simp_facts dep_info t1 t2) l
  | _ -> None


(* [dependency_anal cur_array dep_info = (indep_test, collision_test)]
[collision_test simp_facts t1 t2] simplifies [t1 = t2] using dependency 
analysis.
It returns
- [Some t'] when it simplified [t1 = t2] into [t'];
- [None] when it could not simplify [t1 = t2]. 
[cur_array] is the list of current replication indices at [t1 = t2].
[dep_info] is the local dependency information (for module DepAnal2).
[simp_facts] contains facts that are known to hold.

[indep_test t (b,l] 
returns [Some (t', side_condition)] when [t'] is a term obtained from [t] 
by replacing array indices that depend on [b[l]] with fresh indices.
[t'] does not depend on [b[l]] when [side_condition] is true.
Returns [None] if that is not possible.
*)

let dependency_anal cur_array dep_info = 
  let indep_test simp_facts t (b,l) =
    let bdepinfo =
      if Terms.is_args_at_creation b l then
	DepAnal2.get_dep_info dep_info b
      else
	Facts.nodepinfo
    in
    Facts.default_indep_test bdepinfo simp_facts t (b,l)
  in
  let collision_test simp_facts t1 t2 = 
    let t1' = try_no_var_rec simp_facts t1 in
    let t2' = try_no_var_rec simp_facts t2 in
    match try_two_directions (dependency_collision_rec2 cur_array simp_facts dep_info) t1' t2' with
      (Some _) as x -> x
    | None ->
	Facts.reset_repl_index_list();
	match try_two_directions (dependency_collision_rec3 cur_array simp_facts) t1' t2' with
	  (Some _) as x -> x
	| None ->
	    try_two_directions (dependency_collision_rec1 cur_array simp_facts) t1' t2'
  in
  (indep_test, collision_test)
		
(* [contradicts_known_when_adv_wins] returns [true] when the information
   given as argument contradicts the fact that the adversary wins,
   as summarized in [known_when_adv_wins] *)

let contradicts_known_when_adv_wins (cur_array, pp) simp_facts =
  match !known_when_adv_wins with
  | None -> false
  | Some l ->
      (* We assume that the adversary wins after executing the current
         program point [pp] with indices [cur_array], and we try to obtain
	 a contradiction. The contradiction is obtained at the point at
	 which the adversary wins. *)
      let dep_anal = dependency_anal cur_array DepAnal2.init
         (* We cannot exploit information from DepAnal2 at the current program point because 
	    it may no longer be true at the point at which the adversary wins. *)
      in
      let nsimpfacts = true_facts_from_simp_facts simp_facts in 
      let def_list = Facts.get_def_vars_at pp in
      let cur_array_t = List.map Terms.term_from_repl_index cur_array in
      List.for_all (fun (all_indices', pp_list', simp_facts', def_list') ->
	try 
	  let facts1 = List.fold_left (fun accu pp' ->
	    Terms.both_pp_add_fact accu (cur_array_t, pp) pp') nsimpfacts pp_list'
	  in
	  let facts2 = Terms.both_def_list_facts facts1 def_list def_list' in
	  let facts3 = Terms.def_list_pp facts2 (pp, cur_array_t) def_list' in
	  let simp_facts3 = Facts.simplif_add_list dep_anal simp_facts' facts3 in
	  let simp_facts4 = Simplify1.convert_elsefind dep_anal (def_list @ def_list') simp_facts3 in
	  if !Settings.elsefind_facts_in_success_simplify then
	    let facts5 = Simplify1.get_facts_of_elsefind_facts (!whole_game) (cur_array @ all_indices') simp_facts4 (def_list @ def_list') in
	    let _ = Facts.simplif_add_list dep_anal simp_facts4 facts5 in 
	    false
	  else
	    false
	with Contradiction ->
	  true
	) l

let is_adv_loses p =
  match p.p_desc with
  | EventAbort f -> f == Settings.e_adv_loses
  | _ -> false
	
(* Note on the elimination of collisions in find conditions:
   The find indices are replaced with fresh replication indices,
   so that we correctly take into account that
   the condition of find is executed for every value of the indices. *)

(* Simplify a term knowing some true facts *)

let simplify_term cur_array dep_info keep_tuple simp_facts t = 
  let t' = 
    if keep_tuple then 
      Terms.try_no_var simp_facts t 
    else
      t
  in
  let t'' = Facts.simplify_term (dependency_anal cur_array dep_info) simp_facts t' in
  if !Settings.minimal_simplifications then
    begin
      if Terms.is_true t'' || Terms.is_false t'' || (not (Terms.synt_equal_terms t' t'')) ||
         (keep_tuple && Terms.is_tuple t'' && not (Terms.is_tuple t)) then
	begin
	  if not (Terms.is_true t || Terms.is_false t) then 
	    begin
	      Settings.changed := true;
	      current_pass_transfos := (SReplaceTerm(t,t'')) :: (!current_pass_transfos)
	    end;
	  t''
	end
      else
	(* The change is not really useful, don't do it *)
	t
    end
  else
    begin
      if not (Terms.synt_equal_terms t t'') then 
	begin
	  Settings.changed := true;
	  current_pass_transfos := (SReplaceTerm(t,t'')) :: (!current_pass_transfos)
	end;
      t''
    end

(*
let simplify_term cur_array dep_info k s t =
  let res = simplify_term cur_array dep_info k s t in
  if not (Terms.synt_equal_terms t res) then
    begin
      print_string "Simplifying "; Display.display_term t;
      print_string " knowing\n";
      Facts.display_facts s; 
      print_string "Simplify done "; Display.display_term res;
      print_newline();
      print_newline()
    end;
  res
*)

let rec get_tuple cur_array dep_info simp_facts t =
  if Terms.is_tuple t then t else
  let t' = Terms.try_no_var simp_facts t in
  if Terms.is_tuple t' then t' else
  let t'' = Facts.simplify_term (dependency_anal cur_array dep_info) simp_facts t' in
  if Terms.is_tuple t'' then t'' else
  match t''.t_desc with
    Var _ when (not (Terms.synt_equal_terms t' t'')) ->
      get_tuple cur_array dep_info simp_facts t''
  | _ -> t

(* Simplify pattern *)

let rec simplify_pat cur_array dep_info true_facts = function
    (PatVar b) as pat -> pat
  | PatTuple (f,l) -> PatTuple (f,List.map (simplify_pat cur_array dep_info true_facts) l)
  | PatEqual t -> PatEqual (simplify_term cur_array dep_info false true_facts t)

(* If a find condition is not a basic term (without if/let/find/new),
   I should not apply it to a function, because it breaks the 
   invariant that if/let/find/new are at the root of find conditions.

   Another option would be to expand the obtained term by
   Transf_expand.final_pseudo_expand.
 *)

exception CannotExpand

let make_and_find_cond t t' =
  match t.t_desc, t'.t_desc with
    (Var _ | FunApp _), (Var _ | FunApp _) -> Terms.make_and t t'
  | _ -> raise CannotExpand


(* [has_array_access b t] returns true when [b] has an array reference
   in [t] with indexes different from the indexes at creation *)

let rec has_array_access b t =
  match t.t_desc with
    Var(b',l) -> 
      ((b == b') && not (Terms.is_args_at_creation b l)) ||
      (List.exists (has_array_access b) l)
  | ReplIndex _ -> false
  | FunApp(f,l) ->
      List.exists (has_array_access b) l
  | ResE(b',t) -> has_array_access b t
  | TestE(t1,t2,t3) -> 
      (has_array_access b t1) || (has_array_access b t2) || (has_array_access b t3)
  | FindE(l0,t3,_) ->
      (List.exists (fun (bl,def_list,t1,t2) ->
	(List.exists (has_array_access_br b) def_list) ||
	(has_array_access b t1) || (has_array_access b t2)
	) l0) || (has_array_access b t3)
  | LetE(pat,t1,t2,topt) ->
      (has_array_access_pat b pat) ||
      (has_array_access b t1) || 
      (has_array_access b t2) || 
      (match topt with
	None -> false
      |	Some t3 -> has_array_access b t3)
  | EventAbortE _ | EventE _ | GetE _ | InsertE _ ->
     Parsing_helper.internal_error "Event, event_abort, get, insert should have been expanded"

and has_array_access_br b (b',l) =
  ((b == b') && not (Terms.is_args_at_creation b l)) ||
  (List.exists (has_array_access b) l)

and has_array_access_pat b = function
    PatVar _ -> false
  | PatTuple(_,l) -> List.exists (has_array_access_pat b) l
  | PatEqual t -> has_array_access b t

(* Collect array accesses to variables in [bl] that occur in [def_list].
   Store them in [accu]. *)

let rec collect_array_accesses_br accu bl (b,l) =
  if (List.memq b bl) && (not (Terms.is_args_at_creation b l)) then
    Terms.add_binderref (b,l) accu;
  List.iter (collect_array_accesses_t accu bl) l

and collect_array_accesses_t accu bl t =
  match t.t_desc with
    Var(b,l) -> collect_array_accesses_br accu bl (b,l)
  | ReplIndex _ -> ()
  | FunApp(f,l) -> List.iter (collect_array_accesses_t accu bl) l
  | _ -> Parsing_helper.internal_error "If/let/find/new should not occur in def_list"

let collect_array_accesses accu bl def_list =
  List.iter (collect_array_accesses_br accu bl) def_list

(* size of an array access *)

let rec size t =
  match t.t_desc with
    ReplIndex _ -> 1
  | Var(_,l) | FunApp(_,l) -> 1 + size_list l
  | _ -> Parsing_helper.internal_error "If/let/find/new should not occur in def_list"

and size_list = function
    [] -> 0
  | (a::l) -> size a + size_list l

let rec size_br (b,l) = size_list l

(* sort list in increasing size order *)

let sort_fun br1 br2 = size_br br1 - size_br br2

(* Helper functions for expanding find in find branch 

   make_and_find_cond requires that the find condition is a basic term
   Var/FunApp, so I do not need to rewrite that term to update args_at_creation
   of variables defined inside it. (There are no such variables.) *)

let rec generate_branches_rec ((bl, _, _, _) as ext_branch) (bl3, def_list3, t3, p4) = function
    [] -> (* no array accesses to variables in bl in def_list3 *)
      (* Replace references to variables in bl with the corresponding 
	 replication indices in def_list3/t3 (because def_list3/t3 occurred 
	 in the "then" branch before transformation, and occur in the 
	 condition after transformation). *)
      let bl_rev_subst = List.map (fun (b,b') -> (b, Terms.term_from_repl_index b')) bl in
      let def_list3' = Terms.subst_def_list3 bl_rev_subst def_list3 in
      let t3' = Terms.subst3 bl_rev_subst t3 in
      [(bl3, def_list3', t3', p4)]
  | ((b, l) as br)::rest ->
      let branches_rest = generate_branches_rec ext_branch (bl3, def_list3, t3, p4) rest in
      (* Case the array access to br is in fact done with the current replication
	 indices => I replace br with the corresponding replication index *)
      let subst = Terms.OneSubstArgs(br, Terms.term_from_repl_index (List.assq b bl)) in
      (List.map (fun (bl', def_list', t', p') -> 
	(bl', Terms.copy_def_list subst def_list', 
	 make_and_find_cond (Terms.copy_term subst t') 
	   (Terms.make_and_list (List.map2 (fun t ri -> Terms.make_equal t (Terms.term_from_repl_index ri)) l b.args_at_creation)), p')) branches_rest)
      (* Case the array access to br is done with indices different from the current 
	 replication indices => I can leave br as it is *)
      @ branches_rest

let generate_branches ((bl, def_list, t, _) as ext_branch) ((bl3, def_list3, t3, p4) as br) =
  let accu = ref [] in
  collect_array_accesses accu (List.map fst bl) def_list3;
  (* In case of nested array references, I need to handle the bigger
     array reference first (so it must occur last in the list),
     because after substitution of the smaller one with an index variable,
     we would not recognize the bigger one. 
     To do that, I sort the list of array accesses by increasing size. *)
  let array_accesses_sorted = List.sort sort_fun (!accu) in
  let br' = generate_branches_rec ext_branch br array_accesses_sorted in
  List.map (fun (bl3, def_list3, t3, p4) ->
    (bl @ bl3, def_list @ def_list3, make_and_find_cond t t3, p4)) br'

(* Simplification of terms with if/let/find/res.
   The simplifications are very similar to those performed
   on processes below. *)

exception OneBranchTerm of term findbranch

let rec simplify_term_w_find cur_array true_facts t =
  let pp = DTerm t in
  match t.t_desc with
    Var _ | FunApp _ | ReplIndex _ ->     
      simplify_term cur_array DepAnal2.init false true_facts t
  | TestE(t1,t2,t3) ->
      if (!Settings.auto_remove_if_find_cond) && (t2.t_type = Settings.t_bool) then
	begin
	  Settings.changed := true;
          current_pass_transfos := (STestEElim(t)) :: (!current_pass_transfos);
	  let t' = Terms.make_or (Terms.make_and t1 t2) (Terms.make_and (Terms.make_not t1) t3) in
	  let (transfos, t'') = Transf_expand.final_pseudo_expand (!whole_game) cur_array true_facts t' in
	  current_pass_transfos := transfos @ (!current_pass_transfos);
	  simplify_term_w_find cur_array true_facts t''
	end
      else
      begin
      let t1' = simplify_term cur_array DepAnal2.init false true_facts t1 in
      let t_or_and = Terms.or_and_form t1' in
      try
	(* The facts that are true in the "else" branch *)
	let true_facts' = Facts.simplif_add (dependency_anal cur_array DepAnal2.init) true_facts (Terms.make_not t1') in
	(* Simplify the "else" branch *)
	let t3' = simplify_term_w_find cur_array true_facts' t3 in
	simplify_term_if t cur_array true_facts t2 t3' t_or_and
      with Contradiction ->
	Settings.changed := true;
	current_pass_transfos := (STestTrue(pp)) :: (!current_pass_transfos);
	simplify_term_w_find cur_array true_facts t2
      end

  | FindE(l0,t3,find_info) -> 
      begin
      (* Expand find in conditions of find when the inner find is "unique".
	 The outer find is unique after transformation if and only if it
	 was unique before transformation. *)
      let done_expand = ref false in
      let l0' = 
	if (!Settings.unique_branch_reorg) then
	  try
	  let rec expand_find = function
	      [] -> []
	    | (((bl, def_list, t', t2) as br1)::r) ->
		let r' = expand_find r in 
		match t'.t_desc with
		  FindE(l2, t4, find_info') when Terms.is_false t4 && (is_unique l2 find_info' == Unique) ->
		    let result = 
		      (List.map (fun (bl3, def_list3, t5, t6) ->
			(* Replace references to variables in bl3 with the corresponding 
			   replication indices in t6 (because t6 occurred in the "then" branch
			   before transformation, and occurs in the condition after
			   transformation). 
			   The transformation would be incorrect if t6 tested for the definition
			   of variables in bl3, because these variables are defined more
			   in the initial game than in the transformed game.
			   However, this cannot happen because variables of bl3 are defined
			   in the condition of a find, so there are no array accesses on them. *)
			let t6' = Terms.subst3 (List.map (fun (b,b') -> (b, Terms.term_from_repl_index b')) bl3) t6 in
			(* The variables in bl3 are no longer used, but I need to have some variables there.
			   Moreover, the old variables of bl3 cannot be kept, because their
			   args_at_creation is not correct in the transformed game *)
			let bl3' = List.map (fun (b,b') -> (Terms.create_binder b.sname b.btype cur_array, b')) bl3 in
			(bl @ bl3', def_list @ def_list3, make_and_find_cond t5 t6', t2)) l2) @ r'
		    in
		    done_expand := true;
		    current_pass_transfos := (SFindinFindCondition(pp,t')) :: (!current_pass_transfos);
		    result
		| _ -> br1 :: r'
	  in
	  expand_find l0
	  with CannotExpand -> l0
	else
	  l0
      in
      if (!done_expand) then
	begin
	  Settings.changed := true;
	  let find_info = is_unique l0' find_info in
	  Terms.build_term2 t (FindE(l0', t3, find_info))
	end
      else

      (* Expand find in branch of find when both finds are "unique"
	 TO DO I could perform several of these transformations in a single step,
	 but I'm not sure if I want to have many nested Finds in the else branch *)
      let l0', t3' = 
	if (!Settings.unique_branch_reorg) then
	  try
	  let rec expand_find seen = function
	      [] -> l0, t3
	    | (((bl, def_list, t', t2) as br1)::r) ->
		match t2.t_desc with
		  FindE(l3, t4, Unique) when (find_info == Unique) -> 
		    (* bl is defined in a condition of find, so these variables
		       will be SArenamed by auto_sa_rename. This SArename advice is
		       therefore not necessary. 
		    List.iter (fun b ->
		      Settings.advise := Terms.add_eq (SArenaming b) (!Settings.advise)) bl;
		    *)

		    let result = 
		      (List.rev_append seen ((List.concat (List.map (generate_branches br1) l3)) @ r)),
		      (Terms.build_term_type t3.t_type (FindE([bl, def_list, t', t4], t3, Unique)))
		    in
		    current_pass_transfos := (SFindinFindBranch(pp,DTerm t2)) :: (!current_pass_transfos);
		    result
		| _ -> expand_find (br1::seen) r
	  in
	  expand_find [] l0
	  with CannotExpand -> l0,t3
	else
	  l0, t3
      in
      if l0' != l0 then
	begin
	  Settings.changed := true;
	  let find_info = is_unique l0' find_info in
	  Terms.build_term2 t (FindE(l0', t3', find_info))
	end
      else

      match l0 with
	[] ->
	  simplify_term_w_find cur_array true_facts t3
      |	[([],def_list,t1,t2)] when Facts.reduced_def_list t.t_facts def_list = [] && 
	                              (match t1.t_desc with Var _ | FunApp _ -> true | _ -> false) -> 
	  Settings.changed := true;
	  current_pass_transfos := (SFindtoTest pp) :: (!current_pass_transfos);
	  simplify_term_w_find cur_array true_facts (Terms.build_term2 t (TestE(t1,t2,t3)))
      |	_ ->
      try
      let def_vars = Facts.get_def_vars_at pp in
      let current_history = Facts.get_initial_history pp in 
      let t3' = 
	try
	  simplify_term_w_find cur_array (add_elsefind (dependency_anal cur_array DepAnal2.init) def_vars true_facts l0) t3
	with Contradiction ->
	  (* The else branch of the find will never be executed
             => use some constant to simplify *)
	  match t3.t_desc with
	    FunApp(_,[]) -> t3 (* t3 is already a constant, leave it as it is *)
	  | _ ->
	      Settings.changed := true;
	      current_pass_transfos := (SFindElseRemoved(pp)) :: (!current_pass_transfos);
	      Terms.cst_for_type t3.t_type
      in
      let rec simplify_findl seen = function
	  [] -> []
	| ((bl, def_list, t1, t2) as cur_branch)::l ->
	    begin
	    let l' = simplify_findl (cur_branch::seen) l in
	    let vars = List.map fst bl in
	    let repl_indices = List.map snd bl in
	    let cur_array_cond = repl_indices @ cur_array in
	    let vars_terms = List.map Terms.term_from_binder vars in
	    try
	      let def_list' = Facts.reduced_def_list t.t_facts def_list in
	      let def_vars_cond = Facts.def_vars_from_defined current_history def_list' in
	      let facts_def_list = Facts.facts_from_defined current_history def_list in
	      let true_facts_t1 = Facts.simplif_add_list (dependency_anal cur_array_cond DepAnal2.init) true_facts facts_def_list in
	      let facts_from_elsefind_facts =
		if !Settings.elsefind_facts_in_simplify then
		  let def_vars_cond' = Terms.union_binderref def_vars_cond def_vars in
		  Simplify1.get_facts_of_elsefind_facts (!whole_game) cur_array_cond true_facts_t1 def_vars_cond'
		else
		  []
	      in
	      let true_facts_t1 = Facts.simplif_add_list (dependency_anal cur_array_cond DepAnal2.init) true_facts_t1 facts_from_elsefind_facts in
	      (* Set priorities of variables defined by this find, 
	         to orient rewrite rules preferably in the direction
	         b[..] -> t where b \in bl *)
	      incr current_max_priority;
	      List.iter (fun b -> 
		b.priority <- (!current_max_priority); 
		priority_list := b :: (!priority_list)) vars;
	      let (t1', facts_cond, def_vars_cond', elsefind_cond) =
		match t1.t_desc with
		  Var _ | FunApp _ ->
		    let t1' = simplify_term cur_array_cond DepAnal2.init false true_facts_t1 t1 in
		    (t1', t1' :: facts_from_elsefind_facts @ facts_def_list, def_vars_cond, [])
		| _ -> 
		   let t1' = simplify_term_w_find cur_array_cond true_facts_t1 t1 in
                   let (sure_facts_t1', sure_def_vars_t1', elsefind_t1') = Terms.def_vars_and_facts_from_term t1' in
		   let then_node = Facts.get_initial_history (DTerm t2) in
                   let def_vars_t1' = Facts.def_vars_from_defined then_node sure_def_vars_t1' in
                   let facts_def_vars_t1' = Facts.facts_from_defined then_node sure_def_vars_t1' in
		   (t1', facts_def_vars_t1' @ sure_facts_t1' @ facts_from_elsefind_facts @ facts_def_list,
                    def_vars_t1' @ def_vars_cond, elsefind_t1')
	      in

	      (* [facts_cond] contains the facts that hold,
		 using repl_indices as indices. We substitute vars from them to obtain
		 the facts that hold in the then branch.*)
	      let facts_cond' = List.map (Terms.subst repl_indices vars_terms) facts_cond in
	      let elsefind_cond' = List.map (Terms.subst_else_find repl_indices vars_terms) elsefind_cond in
	      let tf' =
		(* When the find is Unique, I know that the other branches fail,
		   so I can add the corresponding elsefind facts *)
		if find_info == Unique then 
		  add_elsefind (dependency_anal cur_array DepAnal2.init) def_vars true_facts (List.rev_append seen l)
		else
		  true_facts
	      in
	      let tf' =  Terms.add_else_find elsefind_cond' tf' in
	      let tf' = update_elsefind_with_def vars tf' in
	      let tf' =
		Facts.simplif_add_list (dependency_anal cur_array DepAnal2.init) tf' facts_cond'
	      in

	      (* Check that the "defined" conditions can hold,
		 if not remove the branch *)
	      (* [def_vars_cond] contains the variables that are certainly defined 
		 using repl_indices as indices. We substitute vars from them to obtain
		 the variables certainly defined in the then branch. *)
	      let def_vars_accu = Terms.subst_def_list repl_indices vars_terms def_vars_cond' in
	      (* [Terms.def_list_at_pp_fact] adds facts inferred from the knowledge 
		 that the variables in [def_vars_accu] are defined
	         at the current program point *)
	      let cur_array_term = List.map Terms.term_from_repl_index cur_array in
	      let new_facts = Terms.def_list_at_pp_facts [] (DTerm t2) cur_array_term def_vars_accu in
	      let tf' = Facts.simplif_add_list (dependency_anal cur_array DepAnal2.init) tf' new_facts in
	      (* [Terms.both_def_list_facts] adds facts inferred from the knowledge
		 that all variables in [def_vars] and [def_vars_accu] are
		 simultaneously defined. *)
	      let tf' = 
		if !Settings.detect_incompatible_defined_cond then
		  let new_facts = Terms.both_def_list_facts [] def_vars def_vars_accu in
		  Facts.simplif_add_list (dependency_anal cur_array DepAnal2.init) tf' new_facts 
		else tf'
	      in
	      let def_vars' = 
		(* Using def_vars_accu instead of def_list' is more precise *)
	        def_vars_accu @ def_vars
	      in
	      let tf' = convert_elsefind (dependency_anal cur_array DepAnal2.init) def_vars' tf' in


	      let t2' = simplify_term_w_find cur_array tf' t2 in

	      (* When i = M implied by def_list & t, remove i from bl
		 and substitute M for i *)
	      let keep_bl = ref [] in
	      let subst = ref [] in
	      List.iter (fun (b, b') -> 
		let b_im = Terms.try_no_var tf' (Terms.term_from_binder b) in
		if (List.exists (fun (b', b_im') -> Terms.refers_to b b_im' || Terms.refers_to b' b_im) (!subst)) ||
		   (Terms.refers_to b b_im)
		then
		  keep_bl := (b, b') :: (!keep_bl)
		else
		  subst := (b, b_im) :: (!subst);
					  ) bl;
	      let (def_vars_cond, bl', def_list', t1', t2') =
		if (!subst) != [] then
		  begin
		    Settings.changed := true;
		    current_pass_transfos := (SFindIndexKnown(pp, (bl, def_list, t1, DTerm t2), !subst)) :: (!current_pass_transfos);
		    let bl' = !keep_bl in
		    let subst_repl_indices_source = List.map (fun (b,_) -> List.assq b bl) (!subst) in
		    let bl_rev_subst = List.map (fun (b,b') -> (b, Terms.term_from_repl_index b')) bl in
		    let subst_repl_indices_target = 
		      List.map (fun (_, b_im) -> Terms.subst3 bl_rev_subst b_im) (!subst) 
		    in
		    let subst_deflist = Terms.subst_def_list subst_repl_indices_source subst_repl_indices_target in		    
		    (* I also update def_vars_cond because
		       I need it to update the defined condition below *)
		    let def_vars_cond_tmp = ref (subst_deflist def_vars_cond) in
		    List.iter (Terms.close_def_term def_vars_cond_tmp) subst_repl_indices_target;
		    let def_vars_cond = !def_vars_cond_tmp in
		    let def_list' = subst_deflist def_list' in 
		    let t1' = Terms.update_args_at_creation ((List.map snd bl') @ cur_array) 
			(Terms.subst subst_repl_indices_source subst_repl_indices_target t1') in
		    let t2' = add_let_term (Terms.subst3 (!subst) t2') (!subst) in
		    (def_vars_cond, bl', def_list', t1', t2')
	      	  end
		else
		  (def_vars_cond, bl, def_list', t1', t2')
	      in
	      (* End of "When i = M implied by def_list & t, remove i from bl
		 and substitute M for i"*)

	      (* Update the defined condition *)
	      let (bl', def_list3, t1', t2') as find_branch = 
		Facts.update_def_list_term def_vars def_vars_cond bl' def_list' t1' t2' in
              if List.length def_list3 < List.length def_list then
                begin
                  Settings.changed := true;
                  current_pass_transfos := (SFindDeflist(pp, def_list, def_list3)) :: (!current_pass_transfos)
		end
              else if not (Facts.eq_deflists def_list def_list3)  then
		current_pass_transfos := (SFindDeflist(pp, def_list, def_list3)) :: (!current_pass_transfos);

              (* If the find is marked "unique", and we can prove that
	         the current branch succeeds, keep only that branch *)
              if (!Settings.unique_branch) &&
		(match t1'.t_desc with
		  Var _ | FunApp _ -> true
		| _ -> false)
	      then 
		try 
		  branch_succeeds find_branch (dependency_anal cur_array_cond DepAnal2.init) true_facts def_vars;
		  find_branch :: l'
		with SuccessBranch(subst, keep_bl) ->
		  (* If the find has a single branch, which always succeeds, and the
	             indices defined by the find are not used, we can remove
	             the find, keeping only its then branch *)
		  if ((find_info == Unique) || (List.length l0 = 1)) && 
		    (not (List.exists (fun b -> Terms.has_array_ref_q b (!whole_game).current_queries || Terms.refers_to b t2') (List.map fst bl'))) then
		    begin
		      let def_list4 = filter_deflist_indices bl' def_list3 in
		      if (bl' != []) && (def_list4 != []) && (List.length l0 = 1) 
                          (* When def_list4 == [] or List.length l0 > 1, the change is recorded below *) then
			begin
			  Settings.changed := true;
			  current_pass_transfos := (SFindSingleBranch(pp,(bl', def_list3, t1', DTerm t2'))) :: (!current_pass_transfos);
			end;
		      raise (OneBranchTerm([], def_list4, Terms.make_true(), t2'))
		    end
		  else if not (find_info == Unique) then 
		    find_branch :: l' 
		  else
		    begin
		      (* Subst is a substitution for replication indices,
			 compute the substitution for the corresponding variables *)
		      let subst_repl_indices_source = List.map (fun (_,b,_) -> b) subst in
		      let subst_repl_indices_target = List.map (fun (_,_,b_im) -> b_im) subst in
		      let subst = List.map (fun (b, _, b_im) -> 
			(b, Terms.subst repl_indices vars_terms b_im)
			  ) subst 
		      in
		      if List.exists (fun (b, b_im) -> 
			List.exists (fun (b', b_im') -> Terms.refers_to b b_im') subst
			  ) subst
		      then raise (OneBranchTerm(find_branch));
		      if subst != [] then 
			begin
			  Settings.changed := true;
			  current_pass_transfos := (SFindIndexKnown(pp, (bl, def_list, t1, DTerm t2), subst)) :: (!current_pass_transfos)
			end;
		      let def_list_tmp = ref [] in
		      List.iter (fun br ->
			Terms.get_deflist_subterms def_list_tmp 
			  (Terms.subst subst_repl_indices_source subst_repl_indices_target (Terms.term_from_binderref br))) def_list3;
		      let def_list3 = !def_list_tmp in 
		      let t1' = Terms.update_args_at_creation ((List.map snd keep_bl) @ cur_array) 
			  (Terms.subst subst_repl_indices_source subst_repl_indices_target t1') in
		      let t2' = add_let_term (Terms.subst3 subst t2') subst in
		      raise (OneBranchTerm(keep_bl, def_list3, t1', t2'))
		    end
	      else
		find_branch :: l'

	      (*let t_or_and = Terms.or_and_form t' in
	      simplify_find true_facts' l' bl def_list' t_or_and p1 *)
	    with Contradiction ->
	      Settings.changed := true;
	      current_pass_transfos := (SFindBranchRemoved(pp,(bl, def_list, t1, DTerm t2))) :: (!current_pass_transfos);
	      l'
	    end
      in
      try 
	let l0' = simplify_findl [] l0 in
	if l0' == [] then
	  begin
	    Settings.changed := true;
	    current_pass_transfos := (SFindRemoved(pp)) :: (!current_pass_transfos);
	    t3'
	  end
	else
	  let (find_info', change) = infer_unique (!whole_game) cur_array true_facts def_vars (dependency_anal cur_array DepAnal2.init) current_history l0' find_info in
          if change then
            begin
	      Settings.changed := true;
	      current_pass_transfos := (SFindInferUnique(pp)) :: (!current_pass_transfos)
            end;
	  Terms.build_term2 t (FindE(l0', t3',find_info'))
      with OneBranchTerm(find_branch) ->
	match find_branch with
	  ([],[],t1,t2) -> 
	    Settings.changed := true;
	    current_pass_transfos := (SFindSingleBranch(pp,([],[],t1,DTerm t2))) :: (!current_pass_transfos);
	    t2
	| (bl,def_list,t1,t2) ->
            (* The else branch of the find will never be executed
               => use some constant to simplify *)
	    let t3'' = 
	      match t3'.t_desc with
		FunApp(_,[]) -> t3'
	      |	_ -> Terms.cst_for_type t3'.t_type 
	    in
	    if List.length l0 > 1 then 
	      begin
		Settings.changed := true;
		current_pass_transfos := (SFindSingleBranch(pp,(bl,def_list,t1,DTerm t2))) :: (!current_pass_transfos)
	      end
	    else if not (Terms.equal_terms t3' t3'') then
	      begin
		Settings.changed := true;
		current_pass_transfos := (SFindElseRemoved(pp)) :: (!current_pass_transfos)
	      end;
	    Terms.build_term2 t (FindE([find_branch], t3'',find_info))
      with Contradiction ->
	(* The whole Find will never be executed.
           Use the else branch as a simplification *)
	simplify_term_w_find cur_array true_facts t3
      end

  | LetE(pat,t1,t2,topt) ->
      begin
      let true_facts' = update_elsefind_with_def (Terms.vars_from_pat [] pat) true_facts in
      let t1' = simplify_term cur_array DepAnal2.init (Terms.is_pat_tuple pat) true_facts t1 in
      let true_facts_else =
	try
	  Facts.simplif_add (dependency_anal cur_array DepAnal2.init) true_facts (Terms.make_for_all_diff (Terms.gen_term_from_pat pat) t1)
	with Terms.NonLinearPattern | Contradiction 
          (* TO DO We ignore the contradiction here. A contradiction happens 
	     when the [let] always succeeds; we could modify the else branch 
	     to any term *) -> true_facts
      in
      simplify_term_let t true_facts_else cur_array true_facts' t2 topt t1' pat
      end

  | ResE(b,t0) ->
      let true_facts = update_elsefind_with_def [b] true_facts in
      let t' = simplify_term_w_find cur_array true_facts t0 in
      if not ((Terms.has_array_ref_q b (!whole_game).current_queries) || (Terms.refers_to b t0)) then
	begin
	  Settings.changed := true;
	  current_pass_transfos := (SResRemoved(pp)) :: (!current_pass_transfos);
	  t'
	end
      else if not (b.array_ref || b.std_ref || (Settings.occurs_in_queries b (!whole_game).current_queries)) then
	begin
	  Settings.changed := true;
	  current_pass_transfos := (SResToAssign(pp)) :: (!current_pass_transfos);
	  Terms.build_term2 t (LetE(PatVar b,  Terms.cst_for_type b.btype, t', None))
	end
      else
	Terms.build_term2 t (ResE(b, t'))

  | EventAbortE _ | EventE _ | GetE _ | InsertE _ ->
      Parsing_helper.internal_error "Event, event_abort, get, insert should have been expanded"

and simplify_term_if if_t cur_array true_facts ttrue tfalse t' =
  match t'.t_desc with
    FunApp(f, []) when f == Settings.c_false -> 
      Settings.changed := true;
      current_pass_transfos := (STestFalse(DTerm if_t)) :: (!current_pass_transfos);
      tfalse
  | FunApp(f, []) when f == Settings.c_true -> 
      Settings.changed := true;
      current_pass_transfos := (STestTrue(DTerm if_t)) :: (!current_pass_transfos);
      simplify_term_w_find cur_array true_facts ttrue
  | FunApp(f, [t1; t2]) when f == Settings.f_or ->
      Settings.changed := true;
      current_pass_transfos := (STestOr(DTerm if_t)) :: (!current_pass_transfos);
      simplify_term_if if_t cur_array true_facts ttrue (simplify_term_if if_t cur_array true_facts ttrue tfalse t2) t1
  | _ -> 
      try
	let true_facts' = Facts.simplif_add (dependency_anal cur_array DepAnal2.init) true_facts t' in
	(* Simplify the "then" branch *)
	let ttrue' = simplify_term_w_find cur_array true_facts' ttrue in
	Terms.build_term2 if_t (TestE(t', ttrue', tfalse))
      with Contradiction ->
	Settings.changed := true;
	current_pass_transfos := (STestFalse(DTerm if_t)) :: (!current_pass_transfos);
	tfalse

and simplify_term_let let_t true_facts_else cur_array true_facts ttrue tfalse t' pat =
  try
    let (transfos, test, bind) = Terms.simplify_let_tuple (get_tuple cur_array DepAnal2.init true_facts) pat t' in
    if transfos != [] then
      begin
	Settings.changed := true;
	current_pass_transfos := (SLetSimplifyPattern(DTerm let_t, transfos)) :: (!current_pass_transfos);
      end;
    (* always_succeeds = true when the let never fails *)
    let always_succeeds =
      (Terms.is_true test) &&
      (match bind with
      | (PatTuple _, _)::_ -> false
      | _ -> true)
    in
    if always_succeeds && (tfalse != None) then 
      begin
	Settings.changed := true;
	current_pass_transfos := (SLetElseRemoved(DTerm let_t)) :: (!current_pass_transfos);
      end;
    if Terms.is_true test then
      (* Simplify the process tfalse if it will be used at least once *)
      let tfalse' =
	if always_succeeds then None else
	Some(simplify_term_w_find cur_array true_facts_else (Terms.get_else tfalse))
      in
      (* Simplify the process ttrue *)
      let rec add_true_facts true_facts = function
	  [] -> true_facts
	| (PatVar b, t)::l ->
	    add_true_facts
	      (Facts.simplif_add (dependency_anal cur_array DepAnal2.init) true_facts
		 (Terms.make_let_equal (Terms.term_from_binder b) t)) l
	| (pat, t)::l ->
	    add_true_facts
	      (Facts.simplif_add (dependency_anal cur_array DepAnal2.init) true_facts 
		 (Terms.make_equal (Terms.term_from_pat pat) t)) l
      in
      let true_facts' = add_true_facts true_facts bind in
      let ttrue' = simplify_term_w_find cur_array true_facts' ttrue in
      (* Put the lets. There is no test *)
      Terms.put_lets_term bind ttrue' tfalse'
    else
      let t3 = Terms.get_else tfalse in
      let plet = Terms.put_lets_term bind ttrue tfalse in
      let ptest = Terms.build_term2 let_t (TestE(test, plet, t3)) in
      simplify_term_w_find cur_array true_facts ptest
  with
    Terms.Impossible ->
      let t3 = Terms.get_else tfalse in
      Settings.changed := true;
      current_pass_transfos := (SLetSimplifyPattern(DTerm let_t, [pat, DImpossibleTuple])) :: (!current_pass_transfos);
      simplify_term_w_find cur_array true_facts_else t3
  | Contradiction ->
	(* Adding facts to simplify ttrue raised a contradiction,
           ttrue is never executed, tfalse is always executed *)
      let t3 = Terms.get_else tfalse in
      Settings.changed := true;
      current_pass_transfos := (SLetRemoved(DTerm let_t)) :: (!current_pass_transfos);
      simplify_term_w_find cur_array true_facts_else t3

(* Simplification of processes *)

exception OneBranchProcess of process findbranch

let rec simplify_process cur_array dep_info true_facts p = 
  (* print_string "Simplify occ "; print_int p.i_occ; print_newline(); *)
  let dep_info' = DepAnal2.update_dep_info cur_array dep_info true_facts p in
  Terms.iproc_from_desc2 p (
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) -> Par(simplify_process cur_array dep_info' true_facts p1,
		      simplify_process cur_array dep_info' true_facts p2)
  | Repl(b,p) -> Repl(b, simplify_process (b::cur_array) dep_info' true_facts p)
  | Input((c,tl), pat, p) ->
      begin
	match true_facts with
	  (_,_,[]) -> ()
	| _ -> Parsing_helper.internal_error "There should be no elsefind facts at inputs"
      end;
      Input((c, List.map (fun t -> simplify_term cur_array dep_info false true_facts t) tl), 
	    simplify_pat cur_array dep_info true_facts pat, 
	    simplify_oprocess cur_array dep_info' true_facts p))


and simplify_oprocess cur_array dep_info true_facts p =
  (* print_string "Simplify occ "; print_int p.p_occ; print_newline(); *)
  if (not (is_adv_loses p)) &&
    (contradicts_known_when_adv_wins (cur_array, DProcess p) true_facts)
  then
    begin
      Settings.changed := true;
      current_pass_transfos := (SAdvLoses(DProcess p)) :: (!current_pass_transfos);
      Terms.oproc_from_desc2 p (EventAbort Settings.e_adv_loses)
    end
  else
  let (p', dep_info_list') = DepAnal2.update_dep_infoo cur_array dep_info true_facts p in
  let pp = DProcess p' in
  match p'.p_desc with
    Yield -> Terms.oproc_from_desc Yield
  | EventAbort f -> Terms.oproc_from_desc2 p' (EventAbort f)
  | Restr(b,p0) -> 
      begin
	match p0.p_desc with
	| EventAbort _ ->
	    (* If we abort immediately after defining b, we will never
	       read b, even through array accesses or queries *)
	    p0
	| _ ->
	    let true_facts = update_elsefind_with_def [b] true_facts in
	    let p1 = simplify_oprocess cur_array (List.hd dep_info_list') true_facts p0 in
	    if not ((Terms.has_array_ref_q b (!whole_game).current_queries) || (Terms.refers_to_oprocess b p0)) then
	      begin
		Settings.changed := true;
		current_pass_transfos := (SResRemoved(pp)) :: (!current_pass_transfos);
		p1
	      end
	    else if not (b.array_ref || b.std_ref || (Settings.occurs_in_queries b (!whole_game).current_queries)) then
	      begin
		Settings.changed := true;
		current_pass_transfos := (SResToAssign(pp)) :: (!current_pass_transfos);
		Terms.oproc_from_desc2 p' (Let(PatVar b,  Terms.cst_for_type b.btype, p1, Terms.oproc_from_desc Yield))
	      end
	    else
	      Terms.oproc_from_desc2 p' (Restr(b, p1))
      end
  | Test(t, p1, p2) ->
      begin
	match p1.p_desc, p2.p_desc with
	| EventAbort f, EventAbort f' when f == f' ->
	    p2
	| _ -> 
	    let dep_info_branch = List.hd dep_info_list' in
	    let t' = simplify_term cur_array dep_info false true_facts t in
	    let t_or_and = Terms.or_and_form t' in
	    try
	      (* The facts that are true in the [else] branch *)
	      let true_facts' = Facts.simplif_add (dependency_anal cur_array dep_info) true_facts (Terms.make_not t') in
	      (* Simplify the [else] branch *)
	      let p2' = simplify_oprocess cur_array dep_info_branch true_facts' p2 in
	      simplify_if p' dep_info_branch cur_array true_facts p1 p2' t_or_and
	    with Contradiction ->
	      Settings.changed := true;
	      current_pass_transfos := (STestTrue(pp)) :: (!current_pass_transfos);	  	
	      simplify_oprocess cur_array dep_info_branch true_facts p1
      end
  | Find(l0, p2, find_info) ->
      begin
	match p2.p_desc with
	| EventAbort f when List.for_all (fun (_,_,_,p1) ->
	    match p1.p_desc with
	    | EventAbort f' -> f == f'
	    | _ -> false) l0 ->
		p2
	| _ -> 
      match dep_info_list' with
	[] -> Parsing_helper.internal_error "Non empty dep_info_list' needed"
      |	dep_info_else :: dep_info_branches ->

      (* Expand find in conditions of find when the inner find is "unique"
	 The outer find is unique after transformation iff it is unique before transformation *)
      let done_expand = ref false in
      let l0' = 
	if (!Settings.unique_branch_reorg) then
	  try
	  let rec expand_find = function
	      [] -> []
	    | (((bl, def_list, t, p1) as br1)::r) ->
		let r' = expand_find r in 
		match t.t_desc with
		  FindE(l2, t2, find_info') when Terms.is_false t2 && (is_unique l2 find_info' == Unique) ->
		    let result = 
		      (List.map (fun (bl3, def_list3, t3, t4) ->
			(* Replace references to variables in bl3 with the corresponding 
			   replication indices in t4 (because t4 occurred in the "then" branch
			   before transformation, and occurs in the condition after
			   transformation). 
			   The transformation would be incorrect if t4 tested for the definition
			   of variables in bl3, because these variables are defined more
			   in the initial game than in the transformed game.
			   However, this cannot happen because variables of bl3 are defined
			   in the condition of a find, so there are no array accesses on them. *)
			let t4' = Terms.subst3 (List.map (fun (b,b') -> (b, Terms.term_from_repl_index b')) bl3) t4 in
			(* The variables in bl3 are no longer used, but I need to have some variables there.
			   Moreover, the old variables of bl3 cannot be kept, because their
			   args_at_creation is not correct in the transformed game *)
			let bl3' = List.map (fun (b,b') -> (Terms.create_binder b.sname b.btype cur_array, b')) bl3 in
			(bl @ bl3', def_list @ def_list3, make_and_find_cond t3 t4', p1)) l2) @ r'
		    in
		    done_expand := true;
		    current_pass_transfos := (SFindinFindCondition(pp,t)) :: (!current_pass_transfos);
		    result
		| _ -> br1 :: r'
	  in
	  expand_find l0
	  with CannotExpand -> l0
	else
	  l0
      in
      if (!done_expand) then
	begin
	  Settings.changed := true;
	  let find_info = is_unique l0' find_info in
	  Terms.oproc_from_desc2 p' (Find(l0', p2, find_info))
	end
      else

      (* Expand find in branch of find when both finds are "unique"
	 TO DO I could perform several of these transformations in a single step,
	 but I'm not sure if I want to have many nested Finds in the else branch *)
      let l0', p2' = 
	if (!Settings.unique_branch_reorg) then
	  try
	  let rec expand_find seen = function
	      [] -> l0, p2
	    | (((bl, def_list, t, p1) as br1)::r) ->
		match p1.p_desc with
		  Find(l3, p3, Unique) ->
		    List.iter (fun (b,_) ->
		      Settings.advise := Terms.add_eq (SArenaming b) (!Settings.advise)) bl;
		    let result = 
		      (List.rev_append seen ((List.concat (List.map (generate_branches br1) l3)) @ r)),
		      (Terms.oproc_from_desc (Find([bl, def_list, t, p3], p2, Unique)))
		    in
		    current_pass_transfos := (SFindinFindBranch(pp,DProcess p1)) :: (!current_pass_transfos);
		    result
		| _ -> expand_find (br1::seen) r
	  in
	  if find_info == Unique then
	    expand_find [] l0
	  else
	    l0, p2
	  with CannotExpand -> l0, p2
	else
	  l0, p2
      in
      if l0' != l0 then
	begin
	  Settings.changed := true;
	  let find_info = is_unique l0' find_info in
	  Terms.oproc_from_desc2 p' (Find(l0', p2', find_info))
	end
      else

      match l0 with
	[] ->
	  simplify_oprocess cur_array dep_info true_facts p2
      |	[([],def_list,t1,p1)] when (Facts.reduced_def_list p'.p_facts def_list = []) && 
	                              (match t1.t_desc with Var _ | FunApp _ -> true | _ -> false) -> 
	  Settings.changed := true;
	  current_pass_transfos := (SFindtoTest pp) :: (!current_pass_transfos);
	  simplify_oprocess cur_array dep_info true_facts (Terms.oproc_from_desc2 p'  (Test(t1,p1,p2)))
      |	_ ->
      try
      let def_vars = Facts.get_def_vars_at pp in
      let current_history = Facts.get_initial_history pp in 
      let p2' = 
	if p2.p_desc == Yield then Terms.oproc_from_desc Yield else
	try
	  simplify_oprocess cur_array dep_info_else (add_elsefind (dependency_anal cur_array dep_info_else) def_vars true_facts l0) p2
	with Contradiction ->
	  Settings.changed := true;
	  current_pass_transfos := (SFindElseRemoved(pp)) :: (!current_pass_transfos);
	  Terms.oproc_from_desc Yield
      in
      let rec simplify_findl seen dep_info_l1 l1 = 
	match (dep_info_l1,l1) with
	  [],[] -> []
	| (dep_info_cond::dep_info_then::dep_info_l),(((bl, def_list, t, p1) as cur_branch)::l) ->
	    begin
	    let l' = simplify_findl (cur_branch::seen) dep_info_l l in
	    let vars = List.map fst bl in
	    let repl_indices = List.map snd bl in
	    let cur_array_cond = repl_indices @ cur_array in
	    let vars_terms = List.map Terms.term_from_binder vars in
	    try
	      let def_list' = Facts.reduced_def_list p'.p_facts def_list in
	      let def_vars_cond = Facts.def_vars_from_defined current_history def_list' in
	      let facts_def_list = Facts.facts_from_defined current_history def_list in
	      let true_facts_t = Facts.simplif_add_list (dependency_anal cur_array_cond dep_info_cond) true_facts facts_def_list in
	      let facts_from_elsefind_facts =
		if !Settings.elsefind_facts_in_simplify then
		  let def_vars_cond' = Terms.union_binderref def_vars_cond def_vars in
		  Simplify1.get_facts_of_elsefind_facts (!whole_game) cur_array_cond true_facts_t def_vars_cond'
		else
		  []
	      in
	      let true_facts_t = Facts.simplif_add_list (dependency_anal cur_array_cond dep_info_cond) true_facts_t facts_from_elsefind_facts in
	      (* Set priorities of variables defined by this find, 
	         to orient rewrite rules preferably in the direction
	         b[..] -> t where b \in bl *)
	      incr current_max_priority;
	      List.iter (fun b -> 
		b.priority <- (!current_max_priority);
		priority_list := b :: (!priority_list)) vars;
	      let (t', facts_cond, def_vars_cond', elsefind_cond) =
		match t.t_desc with
		  Var _ | FunApp _ ->
		    let t' = simplify_term cur_array_cond dep_info_cond false true_facts_t t in
		    (t', t' :: facts_from_elsefind_facts @ facts_def_list, def_vars_cond, [])
		| _ -> 
		    let t' = simplify_term_w_find cur_array_cond true_facts_t t in
                    let (sure_facts_t', sure_def_vars_t', elsefind_t') = Terms.def_vars_and_facts_from_term t' in
		    let then_node = Facts.get_initial_history (DProcess p1) in
                    let def_vars_t' = Facts.def_vars_from_defined then_node sure_def_vars_t' in
                    let facts_def_vars_t' = Facts.facts_from_defined then_node sure_def_vars_t' in
		    (t', facts_def_vars_t' @ sure_facts_t' @ facts_from_elsefind_facts @ facts_def_list,
                     def_vars_t' @ def_vars_cond, elsefind_t')
	      in

	      (* [facts_cond] contains the facts that hold,
		 using repl_indices as indices. We substitute vars from them to obtain
		 the facts that hold in the then branch.
		 Same substitution for the dependency info. *)
	      let facts_cond' = List.map (Terms.subst repl_indices vars_terms) facts_cond in
	      let elsefind_cond' = List.map (Terms.subst_else_find repl_indices vars_terms) elsefind_cond in
	      let tf' =
		(* When the find is Unique, I know that the other branches fail,
		   so I can add the corresponding elsefind facts *)
		if find_info == Unique then 
		  add_elsefind (dependency_anal cur_array dep_info_else) def_vars true_facts (List.rev_append seen l)
		else
		  true_facts
	      in
	      let tf' = Terms.add_else_find elsefind_cond' tf' in
	      let tf' = update_elsefind_with_def vars tf' in
	      let tf' = 
		Facts.simplif_add_list (dependency_anal cur_array dep_info_then) tf' facts_cond'
	      in

	      (* Check that the "defined" conditions can hold,
		 if not remove the branch *)
	      (* [def_vars_cond] contains the variables that are certainly defined 
		 using repl_indices as indices. We substitute vars from them to obtain
		 the variables certainly defined in the then branch. *)
	      let def_vars_accu = Terms.subst_def_list repl_indices vars_terms def_vars_cond' in
	      (* [Terms.def_list_at_pp_facts] adds facts inferred from the knowledge 
		 that the variables in [def_vars_accu] are defined
	         at the current program point *)
	      let cur_array_term = List.map Terms.term_from_repl_index cur_array in
	      let new_facts = Terms.def_list_at_pp_facts [] (DProcess p1) cur_array_term def_vars_accu in
	      let tf' = Facts.simplif_add_list (dependency_anal cur_array DepAnal2.init) tf' new_facts in
	      (* [Terms.both_def_list_facts] adds facts inferred from the knowledge
		 that all variables in [def_vars] and [def_vars_accu] are
		 simultaneously defined. *)
	      let tf' = 
		if !Settings.detect_incompatible_defined_cond then
		  let new_facts = Terms.both_def_list_facts [] def_vars def_vars_accu in
		  Facts.simplif_add_list (dependency_anal cur_array dep_info_then) tf' new_facts 
		else tf'
	      in
	      let def_vars' = 
		(* Using def_vars_accu instead of def_list' is more precise *)
		def_vars_accu @ def_vars
	      in
	      let tf' = convert_elsefind (dependency_anal cur_array dep_info_then) def_vars' tf' in


                if (!Settings.debug_simplify) then
                  begin
	            Printf.printf "\n_________________\nOcc = %d : \n" p.p_occ;
	            Facts.display_facts tf'
                  end;

	      let p1' = simplify_oprocess cur_array dep_info_then tf' p1 in

	      (* When i = M implied by def_list & t, remove i from bl
		 and substitute M for i *)
	      let keep_bl = ref [] in
	      let subst = ref [] in
	      List.iter (fun (b, b') -> 
		let b_im = Terms.try_no_var tf' (Terms.term_from_binder b) in
		if (List.exists (fun (b', b_im') -> Terms.refers_to b b_im' || Terms.refers_to b' b_im) (!subst)) ||
		   (Terms.refers_to b b_im)
		then
		  keep_bl := (b, b') :: (!keep_bl)
		else
		  subst := (b, b_im) :: (!subst)
					  ) bl;
	      let (def_vars_cond, bl', def_list', t', p1') =
		if (!subst) != [] then 
		  begin
		    Settings.changed := true;
		    current_pass_transfos := (SFindIndexKnown(pp, (bl, def_list, t, DProcess p1), !subst)) :: (!current_pass_transfos);
		    let bl' = !keep_bl in
		    let subst_repl_indices_source = List.map (fun (b,_) -> List.assq b bl) (!subst) in
		    let bl_rev_subst = List.map (fun (b,b') -> (b, Terms.term_from_repl_index b')) bl in
		    let subst_repl_indices_target = 
		      List.map (fun (_, b_im) -> Terms.subst3 bl_rev_subst b_im) (!subst) 
		    in
		    let subst_deflist = Terms.subst_def_list subst_repl_indices_source subst_repl_indices_target in		    
		    (* I also update def_vars_cond because
		       I need it to update the defined condition below *)
		    let def_vars_cond_tmp = ref (subst_deflist def_vars_cond) in
		    List.iter (Terms.close_def_term def_vars_cond_tmp) subst_repl_indices_target;
		    let def_vars_cond = !def_vars_cond_tmp in
		    let def_list' = subst_deflist def_list' in 
		    let t' = Terms.update_args_at_creation ((List.map snd bl') @ cur_array) 
			(Terms.subst subst_repl_indices_source subst_repl_indices_target t') in
		    let p1' = add_let (Terms.subst_oprocess3 (!subst) p1') (!subst) in
		    (def_vars_cond, bl', def_list', t', p1')
	      	  end
		else
		  (def_vars_cond, bl, def_list', t', p1')
	      in
	      (* End of "When i = M implied by def_list & t, remove i from bl
		 and substitute M for i"*)

	      (* Update the defined condition *)
	      let (bl', def_list3, t', p1') as find_branch = 
		Facts.update_def_list_process def_vars def_vars_cond bl' def_list' t' p1' in
              if List.length def_list3 < List.length def_list then
                begin
                  Settings.changed := true;
                  current_pass_transfos := (SFindDeflist(pp, def_list, def_list3)) :: (!current_pass_transfos)
		end
              else if not (Facts.eq_deflists def_list def_list3)  then
		current_pass_transfos := (SFindDeflist(pp, def_list, def_list3)) :: (!current_pass_transfos);

              (* If the find is marked "unique", and we can prove that
	         the current branch succeeds, keep only that branch *)
              if (!Settings.unique_branch) &&
		(match t'.t_desc with
		  Var _ | FunApp _ -> true
		| _ -> false)
	      then 
		try
		  branch_succeeds find_branch (dependency_anal cur_array_cond dep_info_cond) true_facts def_vars;
		  find_branch :: l'
		with SuccessBranch(subst, keep_bl) ->
		  (* If the find has a single branch, which always succeeds, and the
	             indices defined by the find are not used, we can remove
	             the find, keeping only its then branch *)
		  if ((find_info == Unique) || (List.length l0 = 1)) && 
		    (not (List.exists (fun b -> Terms.has_array_ref_q b (!whole_game).current_queries || Terms.refers_to_oprocess b p1') (List.map fst bl'))) then
		    begin
		      let def_list4 = filter_deflist_indices bl' def_list3 in
		      if (bl' != []) && (p2.p_desc == Yield) && (def_list4 != []) && (List.length l0 = 1) 
                          (* When p2.p_desc != Yield or def_list4 == [] or List.length l0 > 1, the change is recorded below *) then
			begin
			  Settings.changed := true;
			  current_pass_transfos := (SFindSingleBranch(pp,(bl', def_list3, t', DProcess p1'))) :: (!current_pass_transfos);
			end;
		      raise (OneBranchProcess([], def_list4, Terms.make_true(), p1'))
		    end
		  else if not (find_info == Unique) then 
		    find_branch :: l' 
		  else
	            begin
		      (* Subst is a substitution for replication indices,
		         compute the substitution for the corresponding variables *)
		      let subst_repl_indices_source = List.map (fun (_,b,_) -> b) subst in
		      let subst_repl_indices_target = List.map (fun (_,_,b_im) -> b_im) subst in
		      let subst = List.map (fun (b, _, b_im) -> 
			(b, Terms.subst repl_indices vars_terms b_im)
			  ) subst 
		      in
		      if List.exists (fun (b, b_im) -> 
			(List.exists (fun (b', b_im') -> Terms.refers_to b b_im') subst)
			  ) subst
		      then raise (OneBranchProcess(find_branch));
		      if subst != [] then 
			begin
			  Settings.changed := true;
			  current_pass_transfos := (SFindIndexKnown(pp, (bl, def_list, t, DProcess p1), subst)) :: (!current_pass_transfos)
			end;
		      let def_list_tmp = ref [] in
		      List.iter (fun br ->
			Terms.get_deflist_subterms def_list_tmp 
			  (Terms.subst subst_repl_indices_source subst_repl_indices_target (Terms.term_from_binderref br))) def_list3;
		      let def_list3 = !def_list_tmp in 
		      let t' = Terms.update_args_at_creation ((List.map snd keep_bl) @ cur_array) 
			  (Terms.subst subst_repl_indices_source subst_repl_indices_target t') in
		      let p1' = add_let (Terms.subst_oprocess3 subst p1') subst in
		      raise (OneBranchProcess(keep_bl, def_list3, t', p1'))
		    end
	      else
		find_branch :: l'

	      (*let t_or_and = Terms.or_and_form t' in
	      simplify_find true_facts' l' bl def_list' t_or_and p1 *)
	    with Contradiction ->
	      Settings.changed := true;
	      current_pass_transfos := (SFindBranchRemoved(pp,(bl, def_list, t, DProcess p1))) :: (!current_pass_transfos);
	      l'
	    end
	| _ -> Parsing_helper.internal_error "Different lengths in simplify/Find"
      in
      try
	let l0' = simplify_findl [] dep_info_branches l0 in
	if l0' == [] then
	  begin
	    Settings.changed := true;
	    current_pass_transfos := (SFindRemoved(pp)) :: (!current_pass_transfos);
	    p2'
	  end
	else
	  begin
	    if (p2'.p_desc == Yield) && (List.for_all (fun (bl,_,t,p1) ->
	      (p1.p_desc == Yield) && (not (List.exists (fun b -> Terms.has_array_ref_q b (!whole_game).current_queries) (List.map fst bl)))
		) l0') then
	      begin
		Settings.changed := true;
		current_pass_transfos := (SFindRemoved(pp)) :: (!current_pass_transfos);
		Terms.oproc_from_desc Yield
	      end
	    else
	      let (find_info', change) = infer_unique (!whole_game) cur_array true_facts def_vars (dependency_anal cur_array dep_info) current_history l0' find_info in
              if change then
                begin
	          Settings.changed := true;
	          current_pass_transfos := (SFindInferUnique(pp)) :: (!current_pass_transfos)
                end;
	      Terms.oproc_from_desc2 p' (Find(l0', p2', find_info'))
	  end
      with OneBranchProcess(find_branch) ->
	match find_branch with
	  ([],[],t1,p1) -> 
	    Settings.changed := true;
	    current_pass_transfos := (SFindSingleBranch(pp, ([],[],t1,DProcess p1))) :: (!current_pass_transfos);
	    p1
	| (bl,def_list,t1,p1) ->
	    (* the else branch of the find will never be executed *)
	    if (List.length l0 > 1) || (p2.p_desc != Yield) then 
	      begin
		Settings.changed := true;
		current_pass_transfos := (SFindSingleBranch(pp,(bl,def_list,t1,DProcess p1))) :: (!current_pass_transfos);
	      end;
	    Terms.oproc_from_desc2 p' (Find([find_branch], Terms.oproc_from_desc Yield, find_info))

      with Contradiction ->
	(* The whole Find will never be executed *)
	Terms.oproc_from_desc Yield
      end
  | Let(pat, t, p1, p2) ->
      begin
	match pat, p1.p_desc, p2.p_desc with
	(* If we abort immediately after defining variables, we will never
	   read them, even through array accesses or queries *)
	| PatVar _, EventAbort _, _ ->
	    p1
	| _, EventAbort f, EventAbort f' when f == f' ->
	    p1
	| _ -> 
	    let true_facts' = update_elsefind_with_def (Terms.vars_from_pat [] pat) true_facts in
	    match dep_info_list' with
	      [dep_info_in; dep_info_else] ->
		let t' = simplify_term cur_array dep_info (Terms.is_pat_tuple pat) true_facts t in
		begin
		  try
		    let true_facts_else =
		      try
			Facts.simplif_add (dependency_anal cur_array dep_info_else) true_facts (Terms.make_for_all_diff (Terms.gen_term_from_pat pat) t) 
		      with Terms.NonLinearPattern -> true_facts
		    in
		    simplify_let p' dep_info_else true_facts_else dep_info dep_info_in cur_array true_facts' p1 p2 t' pat
		  with Contradiction ->
		    if p2.p_desc != Yield then 
		      begin
			Settings.changed := true;
			current_pass_transfos := (SLetElseRemoved(pp)) :: (!current_pass_transfos);
		      end;
		    simplify_let p' dep_info_else true_facts dep_info dep_info_in cur_array true_facts' p1 (Terms.oproc_from_desc Yield) t' pat
		end
	    | [dep_info_in] -> 
		let t' = simplify_term cur_array dep_info (Terms.is_pat_tuple pat) true_facts t in
		simplify_let p' dep_info true_facts dep_info dep_info_in cur_array true_facts' p1 (Terms.oproc_from_desc Yield) t' pat 
	    | _ -> Parsing_helper.internal_error "Bad dep_info_list' in case Let"
      end
  | Output((c,tl),t2,p) ->
      (* Remove all "Elsefind" facts since variables may be defined 
         between the output and the following input *)
      let (subst, facts, _) = true_facts in
      let true_facts' = (subst, facts, []) in
      Terms.oproc_from_desc2 p' 
	(Output((c, List.map (fun t -> simplify_term cur_array dep_info false true_facts t) tl), 
	     simplify_term cur_array dep_info false true_facts t2,
	     simplify_process cur_array (List.hd dep_info_list') true_facts' p))
  | EventP(t,p) ->
      begin
      match t.t_desc with
	FunApp(f,_) ->
	  if not (Settings.event_occurs_in_queries f (!whole_game).current_queries) then
	    begin
	      Settings.changed := true;
	      current_pass_transfos := (SEventRemoved(pp)) :: (!current_pass_transfos);
	      simplify_oprocess cur_array (List.hd dep_info_list') true_facts p
	    end
	  else
	    Terms.oproc_from_desc2 p' (EventP(simplify_term cur_array dep_info false true_facts t,
					  simplify_oprocess cur_array (List.hd dep_info_list') true_facts p))
      |	_ ->
	  Parsing_helper.internal_error "Events must be function applications"
      end
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

and simplify_if if_p dep_info cur_array true_facts ptrue pfalse t' =
  match t'.t_desc with
    FunApp(f, []) when f == Settings.c_false -> 
      Settings.changed := true;
      current_pass_transfos := (STestFalse(DProcess if_p)) :: (!current_pass_transfos);
      pfalse
  | FunApp(f, []) when f == Settings.c_true -> 
      Settings.changed := true;
      current_pass_transfos := (STestTrue(DProcess if_p)) :: (!current_pass_transfos);
      simplify_oprocess cur_array dep_info true_facts ptrue
  | FunApp(f, [t1; t2]) when f == Settings.f_or ->
      Settings.changed := true;
      current_pass_transfos := (STestOr(DProcess if_p)) :: (!current_pass_transfos);
      simplify_if if_p dep_info cur_array true_facts ptrue (simplify_if if_p dep_info cur_array true_facts ptrue pfalse t2) t1
  | _ -> 
      try
	let true_facts' = Facts.simplif_add (dependency_anal cur_array dep_info) true_facts t' in
	(* Simplify the "then" branch *)
	let ptrue' =  simplify_oprocess cur_array dep_info true_facts' ptrue in
	if (ptrue'.p_desc == Yield) && (pfalse.p_desc == Yield) then 
	  begin
	    Settings.changed := true;
	    current_pass_transfos := (STestMerge(DProcess if_p)) :: (!current_pass_transfos);
	    Terms.oproc_from_desc Yield
	  end
	else
	  Terms.oproc_from_desc2 if_p (Test(t', ptrue', pfalse))
      with Contradiction ->
	Settings.changed := true;
	current_pass_transfos := (STestFalse(DProcess if_p)) :: (!current_pass_transfos);
	pfalse

(*
and simplify_find true_facts accu bl def_list t' ptrue = 
  match t'.t_desc with
    FunApp(f, []) when f == Settings.c_false -> 
      Settings.changed := true;
      accu
  | FunApp(f, [t1; t2]) when f == Settings.f_or ->
      Settings.changed := true;
      simplify_find true_facts (simplify_find true_facts accu bl def_list t2 ptrue) bl def_list t1 ptrue
  | _ -> 
      try
	let tf' = Facts.simplif_add true_facts t' in
	(bl, def_list, t', simplify_oprocess tf' ptrue) :: accu
      with Contradiction ->
	Settings.changed := true;
	accu
*)

and simplify_let let_p dep_info_else true_facts_else dep_info dep_info_in cur_array true_facts ptrue pfalse t' pat =
  try
    let (transfos, test, bind) = Terms.simplify_let_tuple (get_tuple cur_array dep_info true_facts) pat t' in
    if transfos != [] then
      begin
	Settings.changed := true;
	current_pass_transfos := (SLetSimplifyPattern(DProcess let_p, transfos)) :: (!current_pass_transfos);
      end;
    (* always_succeeds = true when the let never fails *)
    let always_succeeds =
      (Terms.is_true test) &&
      (match bind with
      | (PatTuple _, _)::_ -> false
      | _ -> true)
    in
    if always_succeeds && (pfalse.p_desc != Yield) then 
      begin
	Settings.changed := true;
	current_pass_transfos := (SLetElseRemoved(DProcess let_p)) :: (!current_pass_transfos);
      end;
    if Terms.is_true test then
      (* Simplify the process tfalse if it will be used at least once *)
      let pfalse' =
	if always_succeeds then Terms.oproc_from_desc Yield else
	simplify_oprocess cur_array dep_info_else true_facts_else pfalse
      in
      (* Simplify the process ttrue *)
      let rec add_true_facts true_facts = function
	  [] -> true_facts
	| (PatVar b, t)::l ->
	    add_true_facts
	      (Facts.simplif_add (dependency_anal cur_array dep_info_in) true_facts
		 (Terms.make_let_equal (Terms.term_from_binder b) t)) l
	| (pat, t)::l ->
	    add_true_facts
	      (Facts.simplif_add (dependency_anal cur_array dep_info_in) true_facts 
		 (Terms.make_equal (Terms.term_from_pat pat) t)) l
      in
      let true_facts' = add_true_facts true_facts bind in
      let ptrue' = simplify_oprocess cur_array dep_info_in true_facts' ptrue in
      (* Put the lets. There is no test *)
      if (ptrue'.p_desc == Yield) && (pfalse'.p_desc == Yield) &&
	(List.for_all (fun (pat, _) -> not (needed_vars_in_pat pat (!whole_game).current_queries)) bind) then
	begin
	  Settings.changed := true;
	  current_pass_transfos := (SLetRemoved(DProcess let_p)) :: (!current_pass_transfos);
	  Terms.oproc_from_desc Yield
	end
      else
	Terms.put_lets bind ptrue' pfalse'
    else
      let plet = Terms.put_lets bind ptrue pfalse in
      let ptest = Terms.oproc_from_desc2 let_p (Test(test, plet, pfalse)) in
      simplify_oprocess cur_array dep_info true_facts ptest
  with
    Terms.Impossible ->
      Settings.changed := true;
      current_pass_transfos := (SLetSimplifyPattern(DProcess let_p, [pat, DImpossibleTuple])) :: (!current_pass_transfos);
      simplify_oprocess cur_array dep_info_else true_facts_else pfalse
  | Contradiction ->
      (* Adding facts to simplify ptrue raised a contradiction,
         ptrue is never executed, pfalse is always executed *)
      Settings.changed := true;
      current_pass_transfos := (SLetRemoved(DProcess let_p)) :: (!current_pass_transfos);
      simplify_oprocess cur_array dep_info_else true_facts_else pfalse

let simplify_main collector coll_elim g =
  let g_proc = Terms.get_process g in
  let tmp_changed = !Settings.changed in
  Settings.changed := false;
  reset coll_elim g;
  begin
    match collector with
    | Some l -> assert (l != [])
    | _ -> ()
  end;
  known_when_adv_wins := collector;
  current_pass_transfos := [];
  Terms.array_ref_process g_proc;
  Simplify1.improved_def_process None true g_proc;
  try
    let p' = simplify_process [] DepAnal2.init ([],[],[]) g_proc in
    let current_transfos = !current_pass_transfos in
    final_reset g_proc;
    (* I need to apply auto_sa_rename because I duplicate some code
     (for example when there is an || inside a test, or when
     I reorganize a find inside a condition of find). I may then
     duplicate assignments to variables inside conditions of find,
     and thus break the invariant that these variables have a single
     definition. auto_sa_rename restores this invariant.
   *)
    if !Settings.changed then
        (* Add probability for eliminated collisions *)
	let proba = final_add_proba() in
        let (g',proba_sa_rename, renames) = Transf_auto_sa_rename.auto_sa_rename (Terms.build_transformed_game p' g) in
        (g',proba @ proba_sa_rename,renames @ [DSimplify(current_transfos)])
    else
	begin
          Settings.changed := tmp_changed;
	  (g,[],[])
	end
  with Restart (b,g') ->
    final_reset g_proc;
    (* Add probability for eliminated collisions *)
    let proba = final_add_proba() in
    (g', proba, [DGlobalDepAnal(b, !Proba.elim_collisions_on_password_occ)])
