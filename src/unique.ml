open Types

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
      let new_facts = Facts_of_elsefind.get_facts_of_elsefind_facts g cur_array simp_facts def_vars in
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
      let new_facts = Facts_of_elsefind.get_facts_of_elsefind_facts g cur_array simp_facts def_vars in
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
         
