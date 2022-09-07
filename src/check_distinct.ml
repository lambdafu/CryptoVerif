open Types

(*****
   [check_distinct b g] shows that elements of the array [b] 
   at different indices are always different (up to negligible probability).
   [g] is the full game.
   This is useful for showing secrecy of a key.
 *****)


let make_indexes cur_array =
  List.map Terms.new_repl_index cur_array

let rename_facts bindex index (facts, def_vars, elsefind_facts) =
  (* Rename session identifiers in facts, variables, and elsefind facts *)
  List.iter2 (fun b t -> b.ri_link <- (TLink t)) bindex index;
  let new_facts = List.map (Terms.copy_term Terms.Links_RI) facts in
  let new_def_vars = Terms.copy_def_list Terms.Links_RI def_vars in
  let new_elsefind_facts = List.map Terms.copy_elsefind elsefind_facts in
  List.iter (fun b -> b.ri_link <- NoLink) bindex;
  (new_facts, new_def_vars, new_elsefind_facts)
    
let collect_facts def =
  let facts = Facts.get_facts_at def.definition_success in
  let def_vars = Facts.get_def_vars_at def.definition_success in
  let elsefind_facts = Facts.get_elsefind_facts_at def.definition_success in
  (facts, def_vars, elsefind_facts)
  
let collect_facts_list bindex index1 index2 defs =
  List.fold_left (fun accu d ->
    try
      let facts = collect_facts d in
      (d, rename_facts bindex index1 facts, rename_facts bindex index2 facts)::accu
    with Contradiction ->
      accu) [] defs

let check_distinct collector b g =
  Proba.reset [] g;
  (* Already done in success.ml
     Improved_def.improved_def_game None false g; *)
  let r_index1 = make_indexes b.args_at_creation in
  let r_index2 = make_indexes b.args_at_creation in
  let index1 = List.map Terms.term_from_repl_index r_index1 in
  let index2 = List.map Terms.term_from_repl_index r_index2 in
  let diff_index = Terms.make_or_list (List.map2 Terms.make_diff index1 index2) in
  let bindex = b.args_at_creation in
  let dwithfacts = collect_facts_list bindex index1 index2 b.def in
  let distinct_def
      (d1,(d1facts,d1def_vars,d1elsefind_facts),_)
      (d2,_,(d2facts,d2def_vars,d2elsefind_facts)) =
    let distinct_def_aux (b1',l1) (b2',l2) =
      (b1' != b2') || 
      (
      try
	let eq_b = Terms.make_and_list 
	    (List.map2 Terms.make_equal 
	       (List.map (Terms.subst bindex index1) l1) 
	       (List.map (Terms.subst bindex index2) l2))
	in
	let facts1 = diff_index :: eq_b :: (List.rev_append d1facts d2facts) in
	let simp_facts1 = Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) facts1 in
	let def_vars = List.rev_append d1def_vars d2def_vars in
	let facts2 = 
	  if !Settings.elsefind_facts_in_success then
	    Facts_of_elsefind.get_facts_of_elsefind_facts g (r_index1 @ r_index2) simp_facts1 
	      def_vars
	  else
	    []
	in
	let simp_facts2 = Facts.simplif_add_list Facts.no_dependency_anal simp_facts1 facts2 in
	(* The following part is commented out because it is too costly. 
	   
	   We assume that the 2nd Let is executed after the 1st one.
	   WARNING: if I use this code, I must scan the whole lists dwithfacts 
	   for both definitions, so that the other case is checked symmetrically.
	   Hence the elsefind facts at the 2nd let hold. 
	let (subst, facts, _) = simp_facts2 in
	let simp_facts3 = (subst, facts, d2elsefind_facts) in
	let simp_facts4 = Facts.convert_elsefind Facts.no_dependency_anal def_vars simp_facts3 in *)
	Terms.add_to_collector collector (r_index1 @ r_index2, [(index1, d1.definition); (index2, d2.definition)], simp_facts2, def_vars);
	false
      with Contradiction -> true
	  )
    in
    match Terms.def_kind d1.definition, Terms.def_kind d2.definition with
    | RestrDef, RestrDef -> true
    | RestrDef, AssignDef(b',l) | AssignDef(b',l), RestrDef ->
	if not (Terms.is_restr b') then
	  Parsing_helper.internal_error "restriction should be checked when testing secrecy";
	distinct_def_aux (Terms.binderref_from_binder b) (b',l)
    | AssignDef(b1',l1), AssignDef(b2',l2) ->
	if not ((Terms.is_restr b1') && (Terms.is_restr b2')) then
	  Parsing_helper.internal_error "restriction should be checked when testing secrecy";
	distinct_def_aux (b1',l1) (b2',l2)
    | _ -> 
	Parsing_helper.internal_error "definition cases should be checked when testing secrecy"
  in
  let rec all_distinct = function
    | [] -> true
    | a::l ->
	(List.for_all (distinct_def a) (a::l)) &&
	(all_distinct l)
  in
  let rec all_distinct_all_test = function
    | [] -> true
    | a::l ->
	let av = Terms.for_all_all_test (distinct_def a) (a::l) in
	let lv = all_distinct l in
	av && lv
  in
  let r =
    if collector != None then
      all_distinct_all_test dwithfacts
    else
      all_distinct dwithfacts
  in
  (* Must not empty, because may be used by other queries;
     Will be emptied in success.ml
     Simplify1.empty_improved_def_process false g.proc; *)
  if r then
    (* Add probability for eliminated collisions *)
    let p = Proba.final_add_proba[] in 
    (true, p @ p)
  else
    begin
      print_string ("Proof of secrecy of " ^ 
		    (Display.binder_to_string b) ^ " failed:\n");
      print_string "  Proved one-session secrecy but not secrecy.\n";
      (false, [])
    end
