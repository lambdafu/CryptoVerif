open Types
open Parsing_helper

(* For backtracking *)
exception Backtrack

let rec forget_games final_game state =
  let g = state.game in
  match g.proc with
  | Forgotten _ -> ()
  | RealProcess p ->
     if g != final_game then
       begin
         let s = Filename.temp_file "game" ".cv" in
         Display.file_out s dummy_ext (fun () ->
           Display.display_process p);
	 at_exit (fun () -> Unix.unlink s);
         let tex_s = 
           if (!Settings.tex_output) <> "" then
             let s = Filename.temp_file "game" ".tex" in
             Displaytex.file_out s dummy_ext (fun () ->
               Displaytex.display_process p);
	     at_exit (fun () -> Unix.unlink s);
             Some s
           else
             None
         in
         g.proc <- Forgotten { text_display = s; tex_display = tex_s }
       end;
     match state.prev_state with
     | None -> ()
     | Some (_,_,_,s') -> forget_games final_game s'           
       
let forget_old_games state =
  match state.prev_state with
    None -> ()
  | Some (_,_,_,s') -> forget_games state.game s'
          
let eq_list l1 l2 =
  (List.for_all (fun x -> List.memq x l1) l2) &&
  (List.for_all (fun x -> List.memq x l2) l1)

let has_common_elem l1 l2 =
  List.exists (fun x -> List.memq x l1) l2

let rec replace_list b bl = function
  | [] -> []
  | b' :: l ->
      if b' == b then
	bl @ (replace_list b bl l)
      else
	b' :: (replace_list b bl l)
    
let sa_rename_ins_updater b bl = function
    (ExpandIfFindGetInsert | Simplify _ | RemoveAssign(All) | 
     RemoveAssign(Minimal) | RemoveAssign(FindCond) | 
     MoveNewLet(MAll | MNoArrayRef | MLet | MNew | MNewNoArrayRef) | 
     Proof _ | InsertEvent _ | InsertInstruct _ | ReplaceTerm _ | MergeBranches |
     MergeArrays _ (* MergeArrays does contain variable names, but it is advised only when these variables have a single definition, so they are not modified by SArename *)) as x -> [x]
  | RemoveAssign (Binders l) ->
      [RemoveAssign (Binders (replace_list b bl l))]
  | SArenaming b' -> 
      if b' == b then
	 (* If b' == b, useless after SArenaming b *)
	[]
      else
	[SArenaming b']
  | MoveNewLet (MBinders l) -> 
      [MoveNewLet (MBinders (replace_list b bl l))]
  | GlobalDepAnal (b',l) ->
      if b' == b then
	List.map (fun b'' -> GlobalDepAnal (b'',l)) bl
      else
	[GlobalDepAnal (b',l)]
  | CryptoTransf(eq,VarList(bl',stop)) ->
      if List.memq b bl' then
	List.map (fun b'' -> CryptoTransf(eq, VarList(List.map (fun b' -> if b' == b then b'' else b') bl', stop))) bl
      else
	[CryptoTransf(eq,VarList(bl',stop))]
  | CryptoTransf(eq,Detailed(None,_)) ->
      [CryptoTransf(eq,Detailed(None,None))] (* term mapping cannot be preserved *)
  | CryptoTransf(eq,Detailed(Some(vmap,vl,stop), _)) ->
      if List.exists (fun (b',_) -> b'==b) vmap then
	List.map (fun b'' -> CryptoTransf(eq, Detailed(Some(
	   List.map (fun (b',r) -> if b' == b then (b'',r) else (b',r)) vmap, vl, stop), None))) bl
      else if List.memq b vl then
	List.map (fun b'' -> CryptoTransf(eq, Detailed(Some(vmap, List.map (fun b' -> if b' == b then b'' else b') vl, stop), None))) bl
      else
	[CryptoTransf(eq,Detailed(Some(vmap,vl,stop), None))]
	  
let compos_ins_updater a b = match a, b with
  None, x -> x
| x, None -> x
| Some f1, Some f2 -> Some (fun t -> List.concat (List.map f2 (f1 t)))

let apply_ins_updater ins_up i =
  match ins_up with
    None -> [i]
  | Some f -> f i

let apply_ins_updater_list ins_up l =
  match ins_up with
    None -> l
  | Some f -> List.concat (List.map f l)

let rec compos_sa_rename = function
    [] -> None
  | (DSArenaming(b,bl')::l) -> compos_ins_updater (Some (sa_rename_ins_updater b bl')) (compos_sa_rename l)
  | _::l -> compos_sa_rename l

let compos_transf f (g, proba, done_ins) =
  let (g', proba', done_ins') = f g in
  (g', proba' @ proba, done_ins' @ done_ins)

let execute g ins =
  let (g', proba, done_ins) = 
    match ins with
      ExpandIfFindGetInsert -> 
	compos_transf Transf_expand.expand_process (Transf_tables.reduce_tables g)
    | Simplify l -> Transf_simplify.simplify_main l g
    | GlobalDepAnal (b,l) -> Transf_globaldepanal.main b l g
    | MoveNewLet s -> Transf_move.move_new_let s g
    | RemoveAssign r -> Transf_remove_assign.remove_assignments r g
    | SArenaming b -> Transf_sarename.sa_rename b g
    | InsertEvent(s,occ) -> Transf_insert_event.insert_event occ s g
    | InsertInstruct(s,ext_s,occ,ext_o) -> 
	Transf_insert_replace.insert_instruct occ ext_o s ext_s g
    | ReplaceTerm(s,ext_s,occ,ext_o) ->
	Transf_insert_replace.replace_term occ ext_o s ext_s g 
    | MergeArrays(bll, m) ->
	Transf_merge.merge_arrays bll m g
    | MergeBranches ->
	Transf_merge.merge_branches g
    | CryptoTransf _ | Proof _ -> 
	Parsing_helper.internal_error "CryptoTransf/Proof unexpected in execute"
  in
  (g', proba, done_ins, compos_sa_rename done_ins)


let execute_state_basic state i =
  let tmp_changed = !Settings.changed in
  Settings.changed := false;
  print_string "Doing ";
  Display.display_instruct i;
  print_string "... "; flush stdout;
  let (g', proba, done_ins, ins_update) = execute state.game i in
  if !Settings.changed then
    begin
      print_string "Done.";
      print_newline()
    end
  else
    begin
      print_string "No change.";
      print_newline()
    end;
  if !Settings.debug_instruct then
    begin
      print_string " Resulting game:\n";
      Display.display_game_process g'
    end;
  if !Settings.changed then
    begin
      Terms.move_occ_game g';
      Invariants.global_inv g';
      ({ game = g';
	 prev_state = Some (i, proba, done_ins, state) }, ins_update)
    end
  else
    begin
      Settings.changed := tmp_changed;
      (state, None)
    end

let default_remove_assign() =
  let r = if !Settings.auto_remove_assign_find_cond then FindCond else Minimal in
  RemoveAssign(r)
      
let rec execute_state state = function
    SArenaming b ->
      (* Adding simplification after SArenaming *)
      let tmp_changed = !Settings.changed in
      Settings.changed := false;
      let (state', ins_updater) = execute_state_basic state (SArenaming b) in
      if !Settings.changed then 
	if !Settings.simplify_after_sarename then 
	  let (state'', ins_updater') = execute_state_basic state' (default_remove_assign()) in
	  let (state''', ins_updater'') = execute_state state'' (Simplify []) in
	  (state''', compos_ins_updater (compos_ins_updater ins_updater ins_updater') ins_updater'')
	else
	  (state', ins_updater)
      else
	begin
	  Settings.changed := tmp_changed;
	  (state', ins_updater)
	end
  | (Simplify l) as i ->
      (* Iterate Simplify (!Settings.max_iter_simplif) times *)
      let tmp_changed = !Settings.changed in
      Settings.changed := false;
      print_string "Doing ";
      Display.display_instruct i;
      print_string "... "; flush stdout;
      let rec iterate iter state =
	let (g', proba, done_ins, ins_updater) = execute state.game i in
	if !Settings.debug_instruct then
	  begin
	    print_string " Resulting game after one simplification pass:\n";
	    Display.display_game_process g'
	  end;
	match done_ins with
	  [] ->
	    (* No change in this pass *)
	    print_string "Run simplify ";
            print_int ((!Settings.max_iter_simplif) - iter + 1);
	    print_string " time(s). Fixpoint reached.\n";
	    (state, None)
	| [DGlobalDepAnal _] ->
	    (* Global dependency analysis done; iterate simplification the same number of times *)
	    Terms.move_occ_game g';
	    Invariants.global_inv g';
	    let state' =  
	      { game = g';
		prev_state = Some (i, proba, done_ins, state) }
	    in
	    let (state'', ins_updater') = iterate iter state' in
	    (state'', compos_ins_updater ins_updater ins_updater')
	| _ ->
	    (* Simplification done *)
	    Terms.move_occ_game g';
	    Invariants.global_inv g';
	    let state' =  
	      { game = g';
		prev_state = Some (i, proba, done_ins, state) }
	    in
	    if iter != 1 then
	      let (state'', ins_updater') = iterate (iter-1) state' in
	      (state'', compos_ins_updater ins_updater ins_updater')
	    else
	      begin
		print_string "Run simplify ";
		print_int ((!Settings.max_iter_simplif) - iter + 1);
		print_string " time(s). Maximum reached.\n";
		(state', ins_updater)
              end
      in
      let result = iterate (!Settings.max_iter_simplif) state in
      (* Transfer the local advice of Globaldepanal to the global advice in Settings.advise *)
      List.iter (fun x -> Settings.advise := Terms.add_eq x (!Settings.advise)) (!Transf_globaldepanal.advise);
      Transf_globaldepanal.advise := [];

      if !Settings.changed then
	begin
	  print_string "Done.";
	  print_newline();
	  result
	end
      else
	begin
	  print_string "No change.";
	  print_newline();
	  Settings.changed := tmp_changed;
	  (state, None)
	end
  | i -> execute_state_basic state i

let rec execute_with_advise state i = 
  let tmp_changed0 = !Settings.changed in
  Settings.changed := false;
  Settings.advise := [];
  let (state', ins_update) = execute_state state i in
  if (!Settings.advise) != [] then
    (* Retry after executing the advise *)
    let tmp_changed = !Settings.changed in
    Settings.changed := false;
    if !Settings.debug_instruct then
      begin
	print_string "Trying advice ";
	Display.display_list Display.display_instruct (!Settings.advise);
	print_newline()
      end;
    let (state'', ins_update') = execute_list_with_advise state' (!Settings.advise) in
    if !Settings.changed then
      let (state3, ins_update'') = execute_list_with_advise state'' (apply_ins_updater ins_update' i) in
      (state3, compos_ins_updater ins_update (compos_ins_updater ins_update' ins_update''))
    else
      begin
	Settings.changed := tmp_changed0 || tmp_changed;
	(state', ins_update)
      end
  else
    begin
      Settings.changed := tmp_changed0 || (!Settings.changed);
      (state', ins_update)
    end

and execute_list_with_advise state = function
    [] -> (state, None)
  | (a::l) -> 
      let (state1, ins_update1) = execute_with_advise state a in
      let (state2, ins_update2) = execute_list_with_advise state1 (apply_ins_updater_list ins_update1 l) in
      (state2, compos_ins_updater ins_update1 ins_update2)

let execute_with_advise_last state i = 
  (* No need to update next instructions, so we can ignore the ins_updater *)
  let (state', _) = execute_with_advise state i in
  state'


let execute_display_advise state i =
  if !Settings.auto_advice then
    execute_with_advise_last state i 
  else
    let tmp_changed0 = !Settings.changed in
    Settings.changed := false;
    Settings.advise := [];
    let (state', _) = execute_state state i in
    if (!Settings.advise) != [] then
      begin
	print_string "Advised transformations ";
	Display.display_list Display.display_instruct (!Settings.advise);
	print_newline()
      end;
    Settings.changed := tmp_changed0 || (!Settings.changed);
    state'

type trans_res =
    CSuccess of state
  | CFailure of (equiv_nm * crypto_transf_user_info * instruct list) list

let move_new_let state =
  if !Settings.auto_move then
    execute_with_advise_last state (MoveNewLet MAll)
  else
    state

let remove_assign_no_sa_rename state =
  let tmp_auto_sa_rename = !Settings.auto_sa_rename in
  Settings.auto_sa_rename := false;
  let state' = execute_with_advise_last state (default_remove_assign()) in
  Settings.auto_sa_rename := tmp_auto_sa_rename;
  state'

let merge state =
  if !Settings.merge_branches then
    execute_with_advise_last state MergeBranches
  else
    state

let simplify state = merge (execute_with_advise_last (move_new_let (execute_with_advise_last (remove_assign_no_sa_rename state) (Simplify []))) (default_remove_assign()))

let expand_simplify state = simplify (execute_with_advise_last state ExpandIfFindGetInsert)

let display_failure_reasons failure_reasons =
  if failure_reasons == [] then
    begin
      print_string "."; print_newline()
    end
  else
    begin
      print_string ":"; print_newline()
    end;
  List.iter (fun (bl, failure_reason) ->
    if bl != [] then
      begin
	print_string "Random variables: ";
	Display.display_list (fun (b1,b2) -> Display.display_binder b1; print_string " -> "; Display.display_binder b2) bl;
	print_newline()
      end;
    Transf_crypto.display_failure_reason failure_reason
      ) failure_reasons

let crypto_transform no_advice equiv user_info state =
  print_string "Trying "; Display.display_instruct (CryptoTransf(equiv, user_info)); print_string "... "; flush stdout;
  let res = Transf_crypto.crypto_transform no_advice equiv user_info state.game in
  match res with
    TSuccess (proba,ins,g'') -> 
      if !Settings.debug_instruct then
	begin
	  Display.display_game_process state.game;
	  print_string "Applying ";
	  Display.display_equiv_with_name equiv;
	  Display.display_with_user_info user_info;
	  print_string " succeeds. Resulting game:\n";
	  Display.display_game_process g''
	end
      else
	print_string "Succeeded.\n"; 
      flush stdout;
      (* Always expand FindE *)
      Terms.move_occ_game g'';
      Invariants.global_inv g'';
      CSuccess ({ game = g''; 
			   prev_state = Some (CryptoTransf(equiv, user_info), proba, ins, state) })
  | TFailure (l,failure_reasons) ->
      if !Settings.debug_instruct then
	begin
	  Display.display_game_process state.game;
	  print_string "Applying ";
	  Display.display_equiv_with_name equiv;
	  Display.display_with_user_info user_info;
	  print_string " failed";
	  display_failure_reasons failure_reasons;
	  if l != [] then print_string "Suggestions: \n";
	  List.iter (fun (_, user_info, to_do) ->
	    Display.display_user_info user_info;
	    print_string ", after executing ";
	    Display.display_list Display.display_instruct to_do;
	    print_newline()
	      ) l
	end
      else
	begin
	  print_string "Failed";
	  display_failure_reasons failure_reasons
	end;
      CFailure l

let get_var_list = function
    VarList(l,_) -> l
  | Detailed(vmopt,_) ->
      match vmopt with
	None -> []
      | Some (vm,vl,_) -> vl @ (List.map fst vm) 
	
let rec execute_crypto_list continue = function
    [] -> continue (CFailure [])
  | ((equiv, user_info, to_do), state, first_try)::l ->
      (* Try after executing the advice *)
      Settings.changed := false;
      if to_do == [] then
        (* When no advice is given and it's not the first time the transfo is tried, apply the crypto transformation without advice *)
	match crypto_transform ((not first_try) || (!Settings.no_advice_crypto)) equiv user_info state with
	  CSuccess state'' -> 
	    begin
	      try
		continue (CSuccess state'')
	      with Backtrack ->
		if !Settings.backtrack_on_crypto then
	          (* Filter the choices to avoid considering too many similar choices *)
		  let l = List.filter (fun ((equiv', user_info', _), _, _) -> 
		    equiv' != equiv || not (has_common_elem (get_var_list user_info') (get_var_list user_info))) l
		  in
		  (*
		  print_string "Just tried\n";
		  Display.display_instruct (CryptoTransf(equiv, bl_assoc));
		  print_string "\nContinuing with:\n";
		  List.iter (fun ((equiv, bl_assoc, _), _, _) -> Display.display_instruct (CryptoTransf(equiv, bl_assoc)); print_newline()) l;
		  print_string "End of list\n";
		  *)
		  if l = [] then raise Backtrack;
		  execute_crypto_list continue l
		else
		  raise Backtrack
	    end
	| CFailure l' -> execute_crypto_list continue ((List.map (fun x -> (x, state, false)) l') @ l) 
      else
	let (state', ins_updater) = execute_list_with_advise state to_do in
	if !Settings.changed then
	  let l_crypto_transf = apply_ins_updater ins_updater (CryptoTransf(equiv, user_info)) in
	  execute_crypto_list continue ((List.map (function
	      CryptoTransf(equiv, user_info) -> ((equiv, user_info, []), state', true)
	    | _ -> Parsing_helper.internal_error "The result of an ins_updater on CryptoTransf should be a list of CryptoTransf") l_crypto_transf) @ l)
	else
	  execute_crypto_list continue l
	

let rec execute_any_crypto_rec continue state = function
    [] -> continue (CFailure [])
  | (((_,_,_,_,opt,_),_) as equiv::equivs) ->
      match opt with
	ManualEqopt -> 
          (* This equivalence should be applied only manually, and we are in automatic mode, so skip it *) 
	  execute_any_crypto_rec continue state equivs
      |	_ ->
      match crypto_transform (!Settings.no_advice_crypto) equiv (VarList([],false)) state with
	CSuccess state' -> 
	  begin
	    try
	      continue (CSuccess (simplify state'))
	    with Backtrack ->
	      if !Settings.backtrack_on_crypto then
		begin
		  (*
		  print_string "Just tried equivalence\n";
		  Display.display_equiv equiv;
		  print_string "\nContinuing with equivalences:\n";
		  List.iter Display.display_equiv equivs;
		  print_string "End of list\n";
		  *)
		  execute_any_crypto_rec continue state equivs
		end
	      else
		raise Backtrack
	  end
      | CFailure l -> 
	  execute_any_crypto_rec (function  
	      CSuccess state' -> continue (CSuccess state')
	    | CFailure l' -> continue (CFailure (l @ l'))) state equivs

let rec issuccess_with_advise state = 
  Settings.advise := [];
  let (proved_queries, is_done) = Success.is_success state in
  let state' = 
    if proved_queries != [] then
      { game = state.game;
	prev_state = Some (Proof proved_queries, [], [], state) }
    else
      state
  in
  if is_done then
    (state', true)
  else 
    let (state'', is_done'') = 
      if (!Settings.advise) != [] then
        (* Retry after executing the advise *)
	let tmp_changed = !Settings.changed in
	Settings.changed := false;
	if !Settings.debug_instruct then
	  begin
	    print_string "Trying advice ";
	    Display.display_list Display.display_instruct (!Settings.advise);
	    print_newline()
	  end;
	let (state'',_) = execute_list_with_advise state' (!Settings.advise) in
	if !Settings.changed then
	  let (state_after_success, _) as result = issuccess_with_advise state'' in
	  if state_after_success == state'' then
	    (* Nothing was proved by the call to issuccess_with_advise,
	       undo the advised transformations *)
	    (state', false)
	  else
	    (* Something was proved by issuccess_with_advise, keep it *)
	    result
	else
	  begin
	    Settings.changed := tmp_changed;
	    (state', false)
	  end
      else
	(state', false)
    in
    if (state'' == state') && (proved_queries == []) && (is_done'' == false) then
      (state, false) (* Forget useless changes *)
    else
      (state'', is_done'')

let rec is_full_state query_list g state =
  if state.game == g then
    true
  else
    match state.prev_state with
      None -> Parsing_helper.internal_error "Instruct.is_full_state: Game not found"
    | Some(_, proba, _, s') ->
        (List.for_all (is_full_proba query_list) proba) &&
	(is_full_state query_list g s')

and is_full_proba query_list = function
    SetProba _ -> true
  | SetEvent(f,g,pub_vars,poptref) ->
      match !poptref with
	Some _ -> true
      |	None -> false

let display_state final state =
  (* AbsentQuery is proved in the current state, if present *)
  let old_queries = state.game.current_queries in
  let state' = 
    let eq_queries = List.filter (function (AbsentQuery, _),_,_ -> true | _ -> false) state.game.current_queries in
    if eq_queries == [] then
      state
    else
      begin
	state.game.current_queries <-
	   List.map (function 
	       (AbsentQuery, g), poptref, popt -> 
		 let proof = Some([], state) in
		 if is_full_state old_queries g state then 
		   poptref := proof;
		 (AbsentQuery, g), poptref, proof
	     | q -> q) old_queries;
	{ game = state.game;
	  prev_state = Some (Proof (List.map (fun (q, _, _) -> (q, [])) eq_queries), [], [], state) }
      end
  in
  (* Display the state *)
  if final && ((!Settings.proof_output) <> "" || (!Settings.tex_output) <> "") then
    begin
      if (!Settings.proof_output) <> "" then
	begin
	  print_string ("Outputting proof in " ^ (!Settings.proof_output));
	  print_newline();
	  Display.file_out (!Settings.proof_output) dummy_ext (fun () ->
	    Display.display_state state')
	end;
      if (!Settings.tex_output) <> "" then
	begin
	  print_string ("Outputting latex proof in " ^ (!Settings.tex_output));
	  print_newline();
	  Displaytex.display_state state';
	end;
      Display.display_conclusion state'
    end
  else
    Display.display_state state';
  (* Undo the proof of AbsentQuery *)
  state.game.current_queries <- old_queries;
  List.iter (function 
      (AbsentQuery, g), poptref, popt -> poptref := None
    | _ -> ()) old_queries

let rec display_short_state state =
  match state.prev_state with
    None -> ()
  | Some(CryptoTransf _ as i, _, _, s) ->
      display_short_state s;
      Display.display_instruct i;
      print_newline()
  | Some(_,_,_,s) ->
      display_short_state s

(* Insertion sort; used to sort the equivalences according to their priority.
   The elements of same priority are grouped in a list *)

let get_prio ((_,_,_,_,opt,_),_) =
  match opt with
    StdEqopt | ManualEqopt -> 0
  | PrioEqopt n -> n
    
let rec insert_elem a = function
    [] -> [[a]]
  | (l1::l) ->
      match l1 with
	[] -> Parsing_helper.internal_error "Empty list unexpected in insert_elem"
      |	first_l1::_ ->
	  let prio_l1 = get_prio first_l1 in
	  let prio_a = get_prio a in
	  if prio_l1 = prio_a then (a::l1)::l else
	  if prio_l1 < prio_a then l1 :: (insert_elem a l) else
	  [a]::l1::l
	  
let rec insert_sort sorted = function
    [] -> sorted
  | (a::l) ->
      let sorted' = insert_sort sorted l in
      (* Insert a into sorted' *)
      insert_elem a sorted'

(* [execute_any_crypto_rec1 state] returns
   - [CSuccess state'] when the proof of all properties succeeded.
   - [CFailure ...] otherwise
   The proof is not displayed. *)
let rec execute_any_crypto_rec1 interactive state =
  try 
    let (state', is_done) =  issuccess_with_advise state in
    if is_done then
      (CSuccess state', state)
    else
      let equiv_list = insert_sort [] (!Settings.equivs) in
      let rec apply_equivs = function
        | [] -> 
	   if !Settings.backtrack_on_crypto then
	     begin
	       print_string "Examined sequence:\n";
	       display_short_state state';
	       print_string "Backtracking...\n";
	       raise Backtrack
	     end
	   else
	     (CFailure [], state')
        | lequiv::rest_equivs ->
	   execute_any_crypto_rec (function
	       | CSuccess state'' -> execute_any_crypto_rec1 interactive state''
	       | CFailure l -> execute_crypto_list (function 
		   | CFailure _ -> 
		       apply_equivs rest_equivs
		   | CSuccess state''' ->
		       let state''' = simplify state''' in
                       if !Settings.forget_old_games then
                         forget_old_games state''';
		       execute_any_crypto_rec1 interactive state''')
                     (List. map (fun x -> (x, state', false)) l)) state' lequiv
      in
      apply_equivs equiv_list
  with
  | Sys.Break ->
     if interactive then
       begin
         print_string "Stopped. Restarting from last crypto transformation.\n";
         (CFailure [], state)
       end
     else
       raise Sys.Break

(* [execute_any_crypto state] returns
   - [CSuccess state'] when the proof of all properties succeeded.
   - [CFailure ...] otherwise
   The proof is displayed in case [CFailure] and not displayed in case [CSuccess]. *)
let execute_any_crypto state =
  (* Always begin with find/if/let expansion *)
  try
    let (res, state') = execute_any_crypto_rec1 false (expand_simplify state) in
    begin
      match res with
	CFailure _ -> 
	  print_string "===================== Proof starts =======================\n";
	  flush stdout;
	  display_state true state'
      |	CSuccess _ -> ()
    end;
    res
  with Backtrack ->
    print_string "===================== Proof starts =======================\n";
    flush stdout;
    display_state true state;
    CFailure []
	    
(* Interactive prover *)

(* [get_nth_occ ext s n] returns the [n]-th occurrence number
   found in string [s]. *)
      
let get_nth_occ ext s n =
  try
    let rec aux idx n =
      assert (n>=1);
      let start_idx = String.index_from s idx '{' in
      let end_idx = String.index_from s start_idx '}' in
      if n = 1 then
	let occ_num = String.sub s (start_idx + 1) (end_idx - start_idx - 1) in
	int_of_string occ_num
      else
	aux end_idx (n-1)
    in
    aux 0 n
  with Not_found | Failure _ ->
    raise(Error("No occurrence number found", ext))


(* [get_occ_of_line p ext regexp_str occ_loc n is_max] 
   returns the occurrence at the [n]-th match
   for regular expression [regexp_str] in the display of process [p].
   If [occ_loc == Before], return the line that matches. 
   If [occ_loc == After], return the line that follows the one that matches 
   If [occ_loc == At _], return the substring that matches.
   If [is_max] is true, the [n]-th line should be the last one.  *)

type occ_loc_t =
    Before
  | After
  | At of int

type occ_searcher_state_t =
  | Looking of int (* [Looking n] means that we look for the [n]-th match *)
  | After (* [After] means that we have just found the desired match, but we want to return the line after that match *)
  | Found of string (* [Found s] means that we have found the desired match, it is [s] *)

exception Stop (* raised when we do not need to look at the rest of the game *)
	
let get_occ_of_line p ext regexp_str occ_loc n is_max =
  let regexp = Str.regexp regexp_str in
  let state = ref (Looking n) in
  let buffer = Buffer.create 100 in
  let check_no_further_match is_max start_in_line line =
    (* if [is_max] is true, checks that there is no match
       of the regular expression in line [line] after position
       [start_in_line] *)
    if is_max then
      begin
	try
	  let _ = Str.search_forward regexp line start_in_line in
	  raise(Error("Several matches for the regular expression you specified. You should try specifying the occurence with before_nth, after_nth, or at_nth.", ext))
	with Not_found -> 
	  ()
      end
  in
  let rec line_handler start_in_line line =
    match !state with
    | Looking n ->
	begin
	  try
	    let match_pos = Str.search_forward regexp line start_in_line in
            (* Line matches *)
	    if n = 1 then
	      begin
		match occ_loc with
		| Before ->
		    state := Found line;
		    if not is_max then raise Stop
		| After ->
		    state := After
		| At _ ->
		    check_no_further_match is_max (match_pos+1) line;
		    state := Found (Str.matched_string line);
		    if not is_max then raise Stop
	      end
	    else
	      begin
		state := (Looking (n-1));
		match occ_loc with
		| At _ -> line_handler (match_pos+1) line
		| _ -> ()
	      end
	  with Not_found ->
	    ()
	end
    | After ->
	begin
	  check_no_further_match is_max 0 line;
	  try
	    let _ = get_nth_occ ext line 1 in
	    state := Found line;
	    if not is_max then raise Stop
	  with Error _ ->
	    (* No occurrence found on this line, try the next line *)
	    ()
	end
    | Found s ->
	check_no_further_match is_max 0 line
  in
  let rec string_handler s =
    let l = Buffer.length buffer in
    Buffer.add_string buffer s;
    try
      let pos_ret = l + (String.index s '\n') in
      (* "\n" found => we have an entire line in the buffer *)
      let line = Buffer.sub buffer 0 pos_ret in
      let rest = Buffer.sub buffer (pos_ret+1) (Buffer.length buffer-pos_ret-1) in
      Buffer.clear buffer;
      line_handler 0 line;
      string_handler rest
    with Not_found -> ()
  in
  begin
    try 
      Display.fun_out string_handler (fun () ->
	Display.display_occurrences := true;
	Display.display_process p;
	Display.display_occurrences := false)
    with Stop -> ()
  end;
  match !state with
  | Looking _ | After ->
      raise(Error("Not enough matches for the regular expression you specified.", ext))
  | Found l ->
      let occ_num_in_line =
	match occ_loc with
	| At n -> n
	| _ -> 1
      in
      let occ = get_nth_occ ext l occ_num_in_line in
      occ

let int_of_cmd (num, ext) =
  try
    int_of_string num
  with Failure _ ->
    raise (Error(num ^ " should be an integer", ext))

   
open Ptree
	
let interpret_occ state occ_exp =
  let p = Terms.get_process state.game in
  match occ_exp with
  | POccBefore (regexp, ext) ->
      get_occ_of_line p ext regexp Before 1 true
  | POccBeforeNth(n, (regexp, ext)) ->
      get_occ_of_line p ext regexp Before n false
  | POccAfter(regexp, ext) ->
      get_occ_of_line p ext regexp After 1 true
  | POccAfterNth(n, (regexp, ext)) ->
      get_occ_of_line p ext regexp After n false
  | POccAt(n_in_pat, (regexp, ext)) ->
      get_occ_of_line p ext regexp (At n_in_pat) 1 true
  | POccAtNth(n, n_in_pat, (regexp, ext))  ->
      get_occ_of_line p ext regexp (At n_in_pat) n false
  | POccInt(occ) ->
      occ


exception End of state
exception EndSuccess of state

let add accu b =
  let s = Display.binder_to_string b in
  if not (Hashtbl.mem accu s) then
    Hashtbl.add accu s b

let rec find_binders_term accu t =
  match t.t_desc with
    Var(_,l) | FunApp(_,l) ->
      List.iter (find_binders_term accu) l
  | ReplIndex _ -> ()
  | TestE(t1,t2,t3) ->
      find_binders_term accu t1;
      find_binders_term accu t2;
      find_binders_term accu t3
  | FindE(l0,t3,_) ->
      List.iter (fun (bl,def_list,t1,t2) ->
	List.iter (fun (b,_) -> add accu b) bl;
        List.iter (find_binders_br accu) def_list;
	find_binders_term accu t1;
	find_binders_term accu t2) l0;
      find_binders_term accu t3
  | ResE(b,t) ->
      add accu b;
      find_binders_term accu t
  | EventAbortE _ -> ()
  | LetE(pat, t1, t2, topt) ->
      find_binders_pat accu pat;
      find_binders_term accu t1;
      find_binders_term accu t2;
      begin
      match topt with
	None -> ()
      |	Some t3 -> find_binders_term accu t3
      end
  | EventE(t,p) ->
      find_binders_term accu t;
      find_binders_term accu p
  | GetE _|InsertE _ -> Parsing_helper.internal_error "Get/Insert should not appear here"
      
and find_binders_pat accu = function
    PatVar b -> add accu b
  | PatTuple(_,l) -> List.iter (find_binders_pat accu) l
  | PatEqual t -> find_binders_term accu t

and find_binders_br accu (b,l) =
  List.iter (find_binders_term_def_list accu) l;
  add accu b

and find_binders_term_def_list accu t =
  match t.t_desc with
    Var(b,l) -> 
      List.iter (find_binders_term_def_list accu) l;
      add accu b
  | FunApp(_,l) ->
      List.iter (find_binders_term_def_list accu) l
  | ReplIndex _ -> ()
  | _ -> 
      Parsing_helper.internal_error "if/let/find/new forbidden in def_list"

let rec find_binders_rec accu p =
  match p.i_desc with
    Nil -> ()
  | Par(p1,p2) -> 
      find_binders_rec accu p1;
      find_binders_rec accu p2
  | Repl(b,p) -> find_binders_rec accu p
  | Input((c, tl),pat,p) ->
      List.iter (find_binders_term accu) tl;
      find_binders_pat accu pat;
      find_binders_reco accu p

and find_binders_reco accu p =
  match p.p_desc with
    Yield | EventAbort _ -> ()
  | Restr(b,p) -> 
      add accu b;
      find_binders_reco accu p
  | Test(t,p1,p2) ->
      find_binders_term accu t;
      find_binders_reco accu p1;
      find_binders_reco accu p2
  | Find(l0,p2,_) ->
      List.iter (fun (bl,def_list,t,p1) ->
	List.iter (fun (b,_) -> add accu b) bl;
        List.iter (find_binders_br accu) def_list;
	find_binders_term accu t;
	find_binders_reco accu p1) l0;
      find_binders_reco accu p2
  | Output((c, tl),t2,p) ->
      List.iter (find_binders_term accu) tl;      
      find_binders_term accu t2;
      find_binders_rec accu p
  | Let(pat, t, p1, p2) ->
      find_binders_pat accu pat;
      find_binders_term accu t;
      find_binders_reco accu p1;
      find_binders_reco accu p2
  | EventP(t,p) ->
      find_binders_term accu t;
      find_binders_reco accu p
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

let find_binders game =
  let p = Terms.get_process game in
  let accu = Hashtbl.create 7 in
  find_binders_rec accu p;
  accu 

let find_binder_list_one_id binders (s,ext) =
  let regexp = Str.regexp s in
  let found_ids =
    Hashtbl.fold (fun id b accu ->
      if (Str.string_match regexp id 0) && (Str.matched_string id = id) then
	b::accu
      else
	accu) binders []
  in
  if found_ids == [] then
    raise (Error("Binder " ^ s ^ " not found", ext));
  found_ids

let find_binder_list binders l =
  let rec aux accu = function
      [] -> accu
    | a::l -> aux (List.rev_append (find_binder_list_one_id binders a) accu) l
  in
  aux [] l

let find_binder binders ((s,ext) as id) =
  let found_ids = find_binder_list_one_id binders id in
  match found_ids with
  | [b] -> b
  | _ -> raise (Error("Regular expression " ^ s ^ " matches several identifiers", ext))
      
let rec find_funsymb f t =
  match t.t_desc with
    Var(b,l) -> List.exists (find_funsymb f) l
  | FunApp(f',l) -> (f = f'.f_name) || (List.exists (find_funsymb f) l)
  | ReplIndex _ -> false
  | _ -> Parsing_helper.internal_error "If / find / let should not occur in left members of equivalences"

let rec find_funsymb_fg f = function
    ReplRestr(_,_,l) -> List.exists (find_funsymb_fg f) l
  | Fun(_,_,r,_) -> find_funsymb f r

let rec find_proba f = function
    Proba (p,_) -> f = p.prname
  | Count _ | OCount _ | Cst _ | Zero | Card _ | AttTime | Time _ 
  | ActTime _ | Maxlength _ |  TypeMaxlength _ | EpsFind | EpsRand _ 
  | PColl1Rand _ | PColl2Rand _ -> false
  | Add(x,y) | Sub(x,y) | Mul(x,y) | Div(x,y) -> (find_proba f x) || (find_proba f y)
  | Max(l) | Length(_,l) -> List.exists (find_proba f) l

let find_equiv f ((n,lm,_,set,_,_),_) =
  (List.exists (fun (fg, _) -> find_funsymb_fg f fg) lm) ||
  (List.exists (function 
      SetProba r -> find_proba f r
    | SetEvent(e,_,_,_) -> f = e.f_name) set)

let find_equiv_by_name f ((n,_,_,_,_,_),_) =
  match n with
    NoName -> false
  | CstName (s,_) -> f = s
  | ParName ((s1,_),(s2,_)) -> f = (s1 ^ "(" ^ s2 ^ ")")

let rec find_list f = function
    [] -> raise Not_found
  | (a::l) ->
      try
	f a
      with Not_found ->
	find_list f l
	
let rec find_oracle_fg s = function
    Fun(n,_,res,_) -> if s = n.cname then res else raise Not_found
  | ReplRestr(_,_,l) -> find_list (find_oracle_fg s) l
	
let find_oracle (s,ext) ((_,lm,_,_,_,_),_) =
  try
    find_list (fun (a,_) -> find_oracle_fg s a) lm
  with Not_found ->
    raise (Error("Oracle " ^ s ^ " not found in equivalence", ext))

let rec find_restr_fg s = function
    Fun _ -> raise Not_found
  | ReplRestr(_,restr,l) ->
      try
	find_list (fun (b,_) ->
	  if Display.binder_to_string b = s then b else raise Not_found) restr
      with Not_found ->
	find_list (find_restr_fg s) l
    
let find_restr (s,ext) ((_,lm,_,_,_,_),_) =
  try 
    find_list (fun (a,_) -> find_restr_fg s a) lm
  with Not_found ->
    raise (Error("Random variable " ^ s ^ " not found in equivalence", ext))
    
let get_equiv_info () =
  print_string "Please enter variable and/or term mapping for this equivalence: ";
  let s = read_line() in
  let lexbuf = Lexing.from_string s in
  try 
    Parser.cryptotransfinfo Lexer.token lexbuf
  with
    Parsing.Parse_error -> raise (Error("Syntax error", extent lexbuf))

let do_equiv ext equiv parsed_user_info state = 
  match parsed_user_info with
    Ptree.PRepeat(fast) ->
      let rec repeat_crypto equiv state = 
	match crypto_transform (!Settings.no_advice_crypto) equiv (VarList([],false)) state with
	  CSuccess state' ->
	    let state' = if fast then state' else simplify state' in
	    repeat_crypto equiv state'
	| CFailure l -> 
	    execute_crypto_list (function 
		CSuccess state'' ->
		  let state'' = if fast then state'' else simplify state'' in
		  repeat_crypto equiv state''
	      | CFailure _ -> print_string "Done all possible transformations with this equivalence.\n"; flush stdout; state) (List.map (fun x -> (x, state, false)) l) 
      in
      let state1 = repeat_crypto equiv state in
      (* In fast mode, we do not simplify between each crypto transformation,
         but we simplify in the end *)
      if fast then simplify state1 else state1
  | _ ->
      let user_info =
	match parsed_user_info with
	  Ptree.PRepeat _ -> Parsing_helper.internal_error "PRepeat should have been handled earlier"
	| Ptree.PVarList(lb, stop) -> 
           (* When the list of binders lb ends with a ".", do not add more binders
              automatically *)
	    let binders = find_binders state.game in	      	  
	    let lb' = find_binder_list binders lb in
	    VarList(lb',stop)
	| Ptree.PDetailed l ->
	    let binders = find_binders state.game in	      	  
	    let var_mapping = ref None in
	    let term_mapping = ref None in
	    List.iter (function
		Ptree.PVarMapping(map, stop) ->
		  let old_var_mapping, old_stop =
		    match !var_mapping with
		      None -> [], false
		    | Some (l,_,old_stop) -> (l,old_stop) 
		  in
		  var_mapping := Some (List.fold_right (fun (id_g,id_equiv) accu ->
		    let v_g_l = find_binder_list_one_id binders id_g in
		    let v_equiv = find_restr id_equiv equiv in
		    List.iter (fun v_g ->
		      if v_g.btype != v_equiv.btype then
			raise (Error ("Variable " ^ (Display.binder_to_string v_g) ^ 
				      " should have the same type as " ^ 
				      (Display.binder_to_string v_equiv), snd id_g));
		      if List.exists (fun (v_g', _) -> v_g == v_g') accu then
			raise (Error ("Variable " ^ (Display.binder_to_string v_g) ^ 
				      " mapped several times", snd id_g))
			  ) v_g_l;
		    List.rev_append (List.rev_map (fun v_g -> (v_g, v_equiv)) v_g_l) accu
		      ) map old_var_mapping, [], stop || old_stop)
	      | Ptree.PTermMapping(map,stop) ->
		  let old_term_mapping, old_stop =
		    match !term_mapping with
		      None -> [], false
		    | Some(l, old_stop) -> l, old_stop
		  in
		  term_mapping := Some ((List.map (fun (occ,id_oracle) ->
		    (interpret_occ state occ, find_oracle id_oracle equiv)) map) @ old_term_mapping,
					stop || old_stop)
		       ) l;
	    Detailed (!var_mapping, !term_mapping)
      in
      match crypto_transform (!Settings.no_advice_crypto) equiv user_info state with
	CSuccess state' -> simplify state'
      | CFailure l -> 
	  if !Settings.auto_advice then
	    execute_crypto_list (function 
	      CSuccess state'' -> simplify state''
	    | CFailure _ -> raise (Error ("Cryptographic transformation failed", ext))) (List.map (fun x -> (x, state, false)) l) 
	  else
	    begin
	      if l != [] then print_string "Failed. Suggestions: \n";
	      List.iter (fun (_, user_info, to_do) ->
		Display.display_user_info user_info;
		print_string ", after executing ";
		Display.display_list Display.display_instruct to_do;
		print_newline()
		  ) l;
	      raise (Error ("Cryptographic transformation failed", ext))
	    end


let rec undo ext state n =
  if n <= 0 then
    begin
      match state.game.proc with
      | RealProcess _ -> state
      | Forgotten _ ->
         raise (Error("Cannot undo: game no longer in memory", ext))
    end
  else
  match state.prev_state with
    None -> 
      raise (Error("Could not undo more steps than those already done", ext))
  | Some (ExpandIfFindGetInsert,_,_, { prev_state = None }) ->
      raise (Error("Cannot undo the first expansion", ext))
  | Some (ExpandIfFindGetInsert,_,_,_) ->
      Parsing_helper.internal_error "ExpandIfFindGetInsert should occur only as first instruction"
  | Some (_,_,_,state') -> undo ext state' (n-1)
	
let display_facts_at state occ_cmd =
  let occ = interpret_occ state occ_cmd in
  (* First compute the facts, then display them *)
  let g_proc = Terms.get_process state.game in
  Simplify1.improved_def_process None true g_proc;
  Facts.display_facts_at g_proc occ;
  Simplify1.empty_improved_def_process true g_proc
    

let interpret_coll_elim state = function
  | PCollVars l -> CollVars(List.map fst l)
  | PCollTypes l -> CollTypes(List.map fst l)
  | PCollTerms l -> CollTerms(List.map (interpret_occ state) l)
    
exception NthFailed
	
let nth l n =
  try
    List.nth l n
  with _ ->
    raise NthFailed

let help() =
  print_string (
  "List of available commands\n" ^
  "remove_assign useless        : remove useless assignments\n" ^
  "remove_assign findcond       : remove useless assignments and assignments in conditions of \"find\"\n" ^
  "remove_assign binder <ident> : remove assignments on variable <ident>\n" ^
  "remove_assign all            : remove all assignments (not recommended)\n" ^
 (if (!Settings.front_end) == Settings.Channels then
  "move all                     : move all \"new\" and \"let\" down in the game\n" ^
  "move noarrayref              : move \"new\" and \"let\" without array references down in the game\n" ^
  "move random                  : move all \"new\" down in the game\n" ^
  "move random_noarrayref       : move \"new\" without array references down in the game\n" ^
  "move assign                  : move all \"let\" down in the game\n" ^
  "move binder <ident>          : move \"new <ident>\" or \"let <ident>\" down in the game\n"
  else
  "move all                     : move all \"<-R\" and \"<-\" down in the game\n" ^
  "move noarrayref              : move \"<-R\" and \"<-\" without array references down in the game\n" ^
  "move random                  : move all \"<-R\" down in the game\n" ^
  "move random_noarrayref       : move \"<-R\" without array references down in the game\n" ^
  "move assign                  : move all \"<-\" down in the game\n" ^
  "move binder <ident>          : move \"<ident> <-R\" or \"<ident> <-\" down in the game\n") ^
  "move array <ident>           : move the generation of the random <ident> to its first usage\n" ^
  "SArename <ident>    : rename several definitions of <ident> to distinct names\n" ^
  "global_dep_anal <ident>      : global dependency analysis on <ident>\n" ^
  "crypto                       : apply a cryptographic transformation\n" ^
  "(can be used alone or with a specifier of the transformation; see the manual)\n" ^
  "simplify                     : simplify the game\n" ^
  "simplify coll_elim <locations> : simplify the game, allowing collision elimination at <locations> (variables, types, occurrences)\n" ^
  "all_simplify                 : remove_assign useless, simplify, move all\n" ^
  "insert_event <ident> <occ>   : insert an event <ident> at occurrence <occ>\n" ^
  "insert <occ> <ins>           : insert instruction <ins> at occurrence <occ>\n" ^
  "replace <occ> <term>         : replace term at occurrence <occ> with <term> (when equal)\n" ^
  "merge_arrays <ident> ...     : merge all given variables\n" ^
  "merge_branches               : merge find branches\n" ^
  "start_from_other_end         : in equivalence proofs, transform the other game\n" ^
  "success                      : check the desired properties\n" ^
  "show_game                    : show the current game\n" ^
  "show_game occ                : show the current game with occurrences\n" ^
  "show_state                   : show the sequence of games up to now\n" ^
  "show_facts <occ>             : show the facts that hold at program point <occ>\n" ^
  "out_game <filename>          : output the current game to <filename>\n" ^
  "out_game <filename> occ      : output the current game with occurrences to <filename>\n" ^
  "out_state <filename>         : output the sequence of games up to now to <filename>\n" ^
  "out_facts <filename> <occ>   : output the facts that hold at program point <occ> to <filename>\n" ^
  "auto                         : try to terminate the proof automatically\n" ^
  "set <param> = <value>        : set the value of various parameters\n" ^
  "allowed_collisions <formulas>: determine when to eliminate collisions\n" ^
  "undo                         : undo the last transformation\n" ^
  "undo <n>                     : undo the last n transformations\n" ^
  "restart                      : restart from the initial game\n" ^
  "forget_old_games             : remove old games from memory, to have more space (prevents undo)\n" ^
  "quit                         : quit interactive mode\n" ^
  "help                         : display this help message\n" ^
  "?                            : display this help message\n")

let map_param (s,ext) =
  match s with
    "noninteractive" -> Settings.psize_NONINTERACTIVE
  | "passive" -> Settings.psize_PASSIVE
  | "small" -> Settings.psize_DEFAULT
  | _ -> (* option "size<n>" where <n> is an integer *)
      try
	if (String.sub s 0 4) <> "size" then raise Not_found;
	int_of_string (String.sub s 4 (String.length s - 4))
      with _ ->
	raise (Error("Unknown parameter size " ^ s, ext))

let map_type (s,ext) =   
  try
    Settings.parse_type_size s 
  with Not_found ->
    raise (Error("Unknown type size " ^ s, ext))

(* [interpret_command interactive state command] runs the command [command]
   in state [state]. 
   Returns the new state.
   Raises 
   - [Error _] in case of error
   - [End state'] in case it terminated by "quit" in state [state']
   - [EndSuccess state'] in case it terminated with all properties proved in state [state']
   *)
      
let rec interpret_command interactive state = function
  | CRemove_assign(arg) ->
      begin
	match arg with
	| RemCst x -> execute_display_advise state (RemoveAssign x)
	| RemBinders l ->
		let binders = find_binders state.game in
		execute_display_advise state (RemoveAssign (Binders (find_binder_list binders l)))
      end
  | CMove(arg) ->
      begin
	match arg with
	| MoveCst x -> execute_display_advise state (MoveNewLet x)
	| MoveBinders l ->
	    let binders = find_binders state.game in	      
	    execute_display_advise state (MoveNewLet (MBinders (find_binder_list binders l)))
	| MoveArray((s,ext2) as id) ->
	    begin
	      let binders = find_binders state.game in	      
	      let bl = find_binder_list_one_id binders id in
	      let ty =
		match bl with
		| [] -> Parsing_helper.internal_error "At least one variable should be found"
		| b::rest ->
		    let ty = b.btype in
		    if List.exists (fun b' -> b'.btype != ty) rest then
		      raise (Error("In \"move array\", all identifiers should have the same type", ext2));
		    ty
	      in
	      if not (Proba.is_large ty) then
		raise (Error("Transformation \"move array\" is allowed only for large types", ext2));
 	      if (ty.toptions land Settings.tyopt_CHOOSABLE) == 0 then
		raise (Error("Transformation \"move array\" is allowed only for fixed, bounded, or nonuniform types",ext2));
	      try
		let equiv = List.assq ty (!Settings.move_new_eq) in
		match crypto_transform (!Settings.no_advice_crypto) equiv (VarList(bl,true)) state with
		  CSuccess state' -> simplify state'
		| CFailure l -> 
		    raise (Error ("Transformation \"move array\" failed", ext2))
	      with Not_found ->
		raise (Error("Transformation for \"move array\" not found, perhaps the macro move_array_internal_macro is not defined in your library", ext2))
	    end
      end
  | CSimplify(coll_elim) -> 
      execute_display_advise state (Simplify (List.map (interpret_coll_elim state) coll_elim))
  | CInsert_event((s, ext1), (occ_cmd, ext)) ->
      begin
	try
	  if String.length s = 0 then raise Not_found;
	  if (s.[0] < 'A' || s.[0] >'Z') && (s.[0] < 'a' || s.[0] > 'z') then raise Not_found;
	  for i = 1 to String.length s - 1 do
	    if s.[i] <> '\'' && s.[i] <> '_' && (s.[i] < 'A' || s.[i] >'Z') && (s.[i] < 'a' || s.[0] > 'z') && (s.[i] < '\192' || s.[i] > '\214') && (s.[i] < '\216' || s.[i] > '\246') && (s.[i] < '\248') && (s.[i] < '0' && s.[i] > '9') then raise Not_found;
	  done;
	  let occ = interpret_occ state occ_cmd in
	  execute_display_advise state (InsertEvent(s,occ))
	with 
	  Not_found ->
	    raise (Error(s ^ " should be a valid identifier: start with a letter, followed with letters, accented letters, digits, underscores, quotes", ext1))
      end
  | CInsert((occ_cmd, ext_o), (ins_s, ext_s)) ->
      let occ = interpret_occ state occ_cmd in
      execute_display_advise state (InsertInstruct(ins_s,ext_s,occ,ext_o))
  | CReplace((occ_cmd, ext_o), (ins_s, ext_s)) ->
      let occ = interpret_occ state occ_cmd in
      execute_display_advise state (ReplaceTerm(ins_s,ext_s,occ,ext_o))
  | CMerge_arrays(args, ext) ->
      begin
	let binders = find_binders state.game in
	let bl = List.map (List.map (fun ((s, ext2)as id) ->
	  (find_binder binders id, ext2))) args in
	let fl = List.hd bl in
	if List.length fl < 2 then
	  raise (Error("You should give at least two variables to merge", ext));
	List.iter (fun al ->
	  if List.length al != List.length fl then
	    raise (Error("All lists of variables to merge should have the same length", ext))) bl;
	execute_display_advise state (MergeArrays(bl, MCreateBranchVar))
      end
  | CMerge_branches ->
      execute_display_advise state MergeBranches
  | CSArename(id) ->
      let binders = find_binders state.game in
      List.fold_left (fun state b ->
	execute_display_advise state (SArenaming b))
	state (find_binder_list_one_id binders id)
  | CGlobal_dep_anal(id, coll_elim) ->
      let coll_elim' = List.map (interpret_coll_elim state) coll_elim in
      let binders = find_binders state.game in	      
      List.fold_left (fun state b ->
	execute_display_advise state (GlobalDepAnal (b, coll_elim')))
	state (find_binder_list_one_id binders id)	
  | CAll_simplify ->
      simplify state
  | CCrypto(eqname, info, ext) ->
      begin
	let (possible_equivs, ext_equiv) =
	  match eqname with
	    PNoName -> (!Settings.equivs, ext)
	  | PParName((n1, ext1), (n2,ext2)) -> 
	      let s = n1 ^ "(" ^ n2 ^ ")" in
	      let eq_list = List.filter (find_equiv_by_name s) (!Settings.equivs) in
	      (eq_list, Parsing_helper.merge_ext ext1 ext2)
	  | PN(n, s_ext) ->
	      begin
		try
		  ([nth (!Settings.equivs) (n - 1)], s_ext)
		with 
		  NthFailed ->
		    raise (Error("Equivalence number " ^ (string_of_int n) ^ " does not exist", s_ext))
	      end
	  | PCstName(s, s_ext) ->
	      let eq_list = List.filter (find_equiv_by_name s) (!Settings.equivs) in
	      if eq_list = [] then
		        (* if the equivalence is not found by its name, try the old way of finding it,
		           by function symbol or probability name *)
		let eq_list' = List.filter (find_equiv s) (!Settings.equivs) in
		(eq_list', s_ext)
	      else
		(eq_list, s_ext)
	in
	match possible_equivs with
	  [] -> raise (Error("No equivalence corresponds to the one you mention", ext_equiv))
	| [equiv] -> 
	    begin
	      match eqname with
		PNoName -> 
		  if interactive then
		    begin
		      print_string "Applying ";
		      Display.display_equiv equiv; print_newline();
		      do_equiv ext equiv (get_equiv_info()) state
		    end
		  else
		    do_equiv ext equiv info state
	      | _ -> do_equiv ext equiv info state
	    end
	| _ -> 
	    if interactive then
	      begin
		let n = ref 0 in
		List.iter (fun equiv -> incr n; print_int (!n); print_string ". "; Display.display_equiv equiv; print_newline()) possible_equivs;
		print_string "Please enter number of equivalence to consider: ";
		let s = read_line() in
		try
		  let equiv = List.nth possible_equivs (int_of_string s - 1) in
		  match eqname with
		    PNoName -> do_equiv ext equiv (get_equiv_info ()) state
		  | _ -> do_equiv ext equiv info state
		with Failure _ -> 
		  raise (Error("Incorrect number", dummy_ext))
	      end
	    else
	      raise (Error("Several equivalences correspond to what you mention", ext_equiv))
      end
  | CStart_from_other_end(ext) ->
      let rec remove_eq_query state =
        state.game.current_queries <-
           List.filter (function ((QEquivalence _,_),_, None) -> false | _ -> true)
             state.game.current_queries;
        match state.prev_state with
          None -> ()
        | Some(_,_,_,s') -> remove_eq_query s'
      in
      let rec add_query q state =
        state.game.current_queries <- q :: state.game.current_queries;
        match state.prev_state with
          None -> ()
        | Some(_,_,_,s') -> add_query q s'
      in
      let (equivalence_q, other_q) =
        List.partition (function ((QEquivalence _,_),_, None) -> true | _ -> false) state.game.current_queries
      in
      begin
        match equivalence_q with
        | [] ->
            raise (Error("start_from_other_end applies only when there is an equivalence query to prove", ext))
        | [(QEquivalence(state_other_end, pub_vars), g), _, None] ->
            remove_eq_query state;
            let init_game_other_end = Display.get_initial_game state_other_end in
            let new_equivalence_q =
              (QEquivalence(state, pub_vars), init_game_other_end), ref None, None
            in
            add_query new_equivalence_q state_other_end;
            state_other_end
        | _ ->
            Parsing_helper.internal_error "There should be at most one equivalence query to prove"
      end
  | CQuit ->
      raise (End state)
  | CSuccesscom ->
      let (state', is_done) = issuccess_with_advise state in
      if is_done then
	raise (EndSuccess state')
      else
	begin
	  print_string "Sorry, the following queries remain unproved:\n";
	  List.iter (fun (a, _, popt) ->
	    if popt == None then
	      begin
		print_string "- ";
		Display.display_query a;
		print_newline()
	      end
		) state'.game.current_queries;
	  state'
	end
  | CShow_game(occ) ->
      Display.display_occurrences := occ;
      Display.display_game_process state.game;
      Display.display_occurrences := false;
      state
  | CShow_state ->
      display_state false state;
      state
  | CShow_facts(occ_cmd) ->
      display_facts_at state occ_cmd;
      state
  | COut_game((s,ext), occ) ->
      Display.file_out s ext (fun () ->
	Display.display_occurrences := occ;
	Display.display_game_process state.game;
	Display.display_occurrences := false);
      state
  | COut_state(s,ext) ->
      Display.file_out s ext (fun () ->
	display_state false state);
      state
  | COut_facts((s, ext1), occ_cmd) ->
      Display.file_out s ext1 (fun () ->
        display_facts_at state occ_cmd);
      state
  | CAuto ->
      begin
	try
	  let (res, state') = execute_any_crypto_rec1 true state in
	  match res with
	    CFailure l -> state'
	  | CSuccess state' -> raise (EndSuccess state')
	with Backtrack ->
	  print_string "Returned to same state after failure of proof with backtracking.\n";
	  state
      end
  | CSetting((s,ext1), pval) ->
      begin
	try
	  Settings.do_set s pval
	with
	| Not_found -> raise (Error("Unknown parameter or value", ext1))
      end;
      state
  | CAllowed_collisions(coll) ->
      begin
	Settings.allowed_collisions := [];
	Settings.allowed_collisions_collision := [];
	List.iter (fun (pl,topt) -> 
	  let pl' = List.map (fun (p,exp) -> (map_param p, exp)) pl in
	  match topt with
	    Some t -> Settings.allowed_collisions := (pl', map_type t) :: (!Settings.allowed_collisions)
	  | None -> Settings.allowed_collisions_collision :=  pl' :: (!Settings.allowed_collisions_collision)
								       ) coll;
	state
      end
  | CUndo(v, ext) ->
      undo ext state v
  | CFocus(l) ->
      let lparsed = List.concat (List.map (fun (s, ext_s) ->
	let lexbuf = Lexing.from_string s in
	Parsing_helper.set_start lexbuf ext_s;
	let (vars, ql) = 
	  try 
	    Parser.focusquery Lexer.token lexbuf
	  with
	    Parsing.Parse_error -> raise (Error("Syntax error", extent lexbuf))
	in
	List.map (function
	  PQEventQ(vars', t1, t2, pub_vars) ->
	    assert(vars' == []);
	    PQEventQ(vars, t1, t2, pub_vars)
	| q -> q
	      ) ql
	  ) l)
      in
      let lq = List.map Syntax.check_query lparsed in
      raise (Error("To implem", dummy_ext))      
  | CUndoFocus ->
      raise (Error("To implem", dummy_ext))
  | CRestart(ext) ->
      let rec restart state =
	match state.prev_state with
	  None -> state
	| Some (_,_,_,state') -> restart state'
      in
      let state' = restart state in 
      begin
	match state'.game.proc with
	| RealProcess _ -> expand_simplify state'
	| Forgotten _ ->
	    raise (Error("Cannot restart: game no longer in memory", ext))
      end
  | CForget_old_games ->
      forget_old_games state;
      state
  | CHelp ->
      help(); state
  | CInteractive(ext) ->
      if interactive then 
	raise (Error("Command interactive not allowed when already in interactive mode", ext));
      begin
	match interactive_loop state with
	  CSuccess s -> s
	| _ -> Parsing_helper.internal_error "interactive_loop should return CSuccess _"
      end

and interpret_command_forget interactive state command =
  let state' = interpret_command interactive state command in
  if !Settings.forget_old_games then
    forget_old_games state';
  state'
                
(* [interactive_loop state] runs the interactive prover starting from [state].
   Returns [CSuccess state'] when the prover terminated by "quit" in state [state']
   Raises [EndSuccess state'] when the prover terminated with all properties proved in state [state'] *)
and interactive_loop state =
  try 
    print_string "Please enter a command: ";
    let s = read_line() in
    let lexbuf = Lexing.from_string s in
    Lexer.in_proof := true;
    let commands =
      try
	Parser.proofoptsemi Lexer.token lexbuf
      with Parsing.Parse_error ->
	Lexer.in_proof := false;
	raise (Error("Syntax error", extent lexbuf))
    in
    Lexer.in_proof := false;
    let rec run_commands state = function
      | [] -> state
      | c1:: rest ->
	  let state' = interpret_command_forget true state c1 in
	  run_commands state' rest
    in
    interactive_loop (run_commands state commands)
  with
    End s ->
      CSuccess s
  | Error(mess, extent) ->
      Parsing_helper.display_error mess extent;
      interactive_loop state
  | Sys.Break ->
      print_string "Stopped. Restarting from the state before the last command.\n";
      interactive_loop state

(* [execute_proofinfo proof state] runs the proof [proof] in state [state].
   Returns [CSuccess state'] where [state'] is the state reached after the proof.
   (In case of failure of some proof step, the program terminates.) *)
let rec execute_proofinfo proof state =
  match proof with
  | [] -> 
      CSuccess state
  | com::rest -> 
     try
       execute_proofinfo rest (interpret_command_forget false state com)
     with
     | End s | EndSuccess s->
	CSuccess s
     | Error(mess, extent) ->
	Parsing_helper.input_error mess extent

let do_proof proof state =
  if (!Settings.tex_output) <> "" then
    Displaytex.start();
  let r = 
    match proof with
      Some pr -> execute_proofinfo pr (expand_simplify state)
    | None ->
	if !Settings.interactive_mode then
	  try
	    interactive_loop (expand_simplify state)
	  with EndSuccess s -> CSuccess s
	else
	  execute_any_crypto state
  in
  begin
    match r with
      CSuccess state' ->
	print_string "===================== Proof starts =======================\n";
	display_state true state'
    | CFailure _ -> ()
  end;
  if (!Settings.tex_output) <> "" then
    Displaytex.stop()

