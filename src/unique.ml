open Types
open Parsing_helper

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

let prove_unique g cur_array simp_facts def_vars dep_info node l0 =
  let l0' = List.map (fun (bl, def_list1, t1, _) ->
    let (sure_facts, defined_vars, _) = Info_from_term.def_vars_and_facts_from_term g.expanded true t1 in
    (bl, defined_vars @ def_list1, sure_facts)
      ) l0
  in
  let unique_branch (bl, def_list1, tl1) =
    let repl_index1 = List.map snd bl in
    let repl_index1_term = List.map Terms.term_from_repl_index repl_index1 in
    let repl_index2 = List.map Terms.new_repl_index repl_index1 in
    let repl_index2_term = List.map Terms.term_from_repl_index repl_index2 in
    let def_list2 = Terms.subst_def_list repl_index1 repl_index2_term def_list1 in
    let tl2 = List.map (Terms.subst repl_index1 repl_index2_term) tl1 in
    try 
      let def_vars1 = Facts.def_vars_from_defined node def_list1 in
      let facts_def_list1 = Facts.facts_from_defined node def_list1 in
      let def_vars2 = Facts.def_vars_from_defined node def_list2 in
      let facts_def_list2 = Facts.facts_from_defined node def_list2 in
      let def_vars = Terms.union_binderref (Terms.union_binderref def_vars def_vars1) def_vars2 in
      let diff_ri1_ri2 = Terms.make_or_list (List.map2 Terms.make_diff repl_index1_term repl_index2_term) in
      let simp_facts = Facts.simplif_add_list dep_info simp_facts (diff_ri1_ri2 :: tl2 @ tl1 @ facts_def_list1 @ facts_def_list2) in
      let new_facts = Facts_of_elsefind.get_facts_of_elsefind_facts g cur_array simp_facts def_vars in
      let _ = Facts.simplif_add_list dep_info simp_facts new_facts in
      false
    with Contradiction -> true
  in
  let incompatible_branch (bl1, def_list1, tl1) (bl2, def_list2_orig, tl2_orig) =
    let repl_index2_orig = List.map snd bl2 in
    let repl_index2 = List.map Terms.new_repl_index repl_index2_orig in
    let repl_index2_term = List.map Terms.term_from_repl_index repl_index2 in
    let def_list2 = Terms.subst_def_list repl_index2_orig repl_index2_term def_list2_orig in
    let tl2 = List.map (Terms.subst repl_index2_orig repl_index2_term) tl2_orig in
    try 
      let def_vars1 = Facts.def_vars_from_defined node def_list1 in
      let facts_def_list1 = Facts.facts_from_defined node def_list1 in
      let def_vars2 = Facts.def_vars_from_defined node def_list2 in
      let facts_def_list2 = Facts.facts_from_defined node def_list2 in
      let def_vars = Terms.union_binderref (Terms.union_binderref def_vars def_vars1) def_vars2 in
      let simp_facts = Facts.simplif_add_list dep_info simp_facts (tl2 @ tl1 @ facts_def_list1 @ facts_def_list2) in
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

(* Prove that the inserted find[unique] are really unique *)

let whole_game = ref Terms.empty_game
let initial = ref false
let transfo_done = ref None
    
let prove_unique1 pp l0 find_info ext =
  if find_info = UniqueToProve then
    let proved() =
      begin
	match !transfo_done with
	| None -> transfo_done := Some DProveUnique
	| _ -> ()
      end;
      Unique
    in
    try 
      let cur_array =
	match Incompatible.get_facts pp with
	| Some(cur_array,_,_,_,_,_,_) -> cur_array
	| None -> failwith "(missing information, should not happen)"
      in
      let true_facts = Facts.simplif_add_list Facts.no_dependency_anal Terms.simp_facts_id (Facts.get_facts_at pp) in
      let def_vars = Facts.get_def_vars_at pp in
      let current_history = Facts.get_initial_history pp in 
      if prove_unique (!whole_game) cur_array true_facts def_vars Facts.no_dependency_anal current_history l0 then
	proved()
      else
	failwith ""
    with
    | Failure comment -> 
	if !initial then
	  if !Settings.allow_unproved_unique then
	    begin
	      input_warning ("The initial game contains a find[unique] or get[unique] but I could not prove that it is really unique"^comment^". It is your responsability to make sure that it is really unique.") ext;
	      transfo_done := Some DProveUniqueFailed;
	      Unique
	    end
	  else
	    raise (Error("The initial game contains a find[unique] or get[unique] but I could not prove that it is really unique"^comment, ext))
	else
	  raise (Error("You inserted a find[unique] but I could not prove that it is really unique"^comment, ext))
    | Contradiction ->
	(* The find[unique] is unreachable, I can consider it unique without problem *)
	proved()
  else
    find_info
	
let rec prove_uniquet t =
  match t.t_desc with
    ResE(b,p) ->
      Terms.build_term t (ResE(b, prove_uniquet p))
  | EventE(t1,p) ->
      Terms.build_term t (EventE(prove_uniquet t1, prove_uniquet p))
  | GetE _ | InsertE _ ->
      Parsing_helper.internal_error "get, insert should not occur as term"
  | TestE(t1,t2,t3) ->
      let t1' = prove_uniquet t1 in
      let t2' = prove_uniquet t2 in
      let t3' = prove_uniquet t3 in
      Terms.build_term t (TestE(t1',t2',t3'))
  | LetE(pat,t1,t2,topt) ->
      let pat' = prove_uniquepat pat in
      let t1' = prove_uniquet t1 in
      let t2' = prove_uniquet t2 in
      let topt' = 
	match topt with
	  None -> None
	| Some t3 -> Some (prove_uniquet t3)
      in
      Terms.build_term t (LetE(pat',t1',t2',topt'))
  | FindE(l0,t3, find_info) ->
      let find_info' = prove_unique1 (DTerm t) l0 find_info t.t_loc in
      let t3' = prove_uniquet t3 in
      let l0' = List.map (fun (bl, def_list, tc, p) ->
	let p' = prove_uniquet p in
	let tc' = prove_uniquet tc in
	(bl, def_list, tc', p')
	  ) l0 
      in
      Terms.build_term t (FindE(l0',t3',find_info'))
  | Var(b,l) ->
      Terms.build_term t (Var(b, List.map prove_uniquet l))
  | FunApp(f,l) ->
      Terms.build_term t (FunApp(f, List.map prove_uniquet l))      
  | ReplIndex _ | EventAbortE _ -> t 

and prove_uniquepat = function
  | PatVar b -> PatVar b
  | PatTuple(f,l) -> PatTuple(f, List.map prove_uniquepat l)
  | PatEqual t -> PatEqual (prove_uniquet t)
	
let rec prove_uniquei p =
    Terms.iproc_from_desc_loc p (
    match p.i_desc with
      Nil -> Nil
    | Par(p1,p2) -> 
	Par(prove_uniquei p1,
	    prove_uniquei p2)
    | Repl(b,p) ->
	Repl(b, prove_uniquei p)
    | Input((c, tl), pat, p) ->
	Input((c, List.map prove_uniquet tl),
	      prove_uniquepat pat, prove_uniqueo p))

and prove_uniqueo p =
  Terms.oproc_from_desc_loc p (
    match p.p_desc with
      Yield -> Yield
    | EventAbort f -> EventAbort f
    | Restr(b,p) -> Restr(b, prove_uniqueo p)
    | Test(t,p1,p2) -> Test(prove_uniquet t,
			    prove_uniqueo p1,
			    prove_uniqueo p2)
    | Find(l0,p2,find_info) ->
	let find_info' = prove_unique1 (DProcess p) l0 find_info p.p_loc in
	Find(List.map (fun (bl,def_list,t,p1) ->
	       (bl,def_list,prove_uniquet t,
	        prove_uniqueo p1)) l0,
	     prove_uniqueo p2, find_info')
    | Output((c, tl),t,p) ->
	Output((c, List.map prove_uniquet tl),
	       prove_uniquet t,prove_uniquei p)
    | Let(pat,t,p1,p2) ->
	Let(prove_uniquepat pat,
	    prove_uniquet t,prove_uniqueo p1,
	    prove_uniqueo p2)
    | EventP(t,p) ->
	EventP(prove_uniquet t, prove_uniqueo p)
    | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here")

let prove_unique_game initial_game g =
  Terms.move_occ_game g;
  let g_proc = Terms.get_process g in
  whole_game := g;
  initial := initial_game;
  transfo_done := None;
  Array_ref.array_ref_process g_proc;
  Improved_def.improved_def_game None true g;
  Depanal.reset [] g;
  let cleanup() =
    Array_ref.cleanup_array_ref();
    Improved_def.empty_improved_def_game true g;
    whole_game := Terms.empty_game;
    transfo_done := None
  in
  let p' =
    try
      prove_uniquei g_proc
    with Error(mess, extent) ->
      cleanup();
      raise (Error(mess, extent))
  in
  let g' = Terms.build_transformed_game p' g in
  let transfos = !transfo_done in
  cleanup();
  match transfos with
  | None -> (g, [], [])
  | Some t ->
      Settings.changed := true;
      (g', Depanal.final_add_proba(), if initial_game then [t] else [])
    
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
         
