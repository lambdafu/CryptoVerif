open Types
open Parsing_helper

let command_out_file = ref None

type command_t =
  | ComQuit
  | ComOther of string
    
let run_commands = ref ([]: command_t list)

let out_command f semi a =
  match a with
  | ComQuit ->
      output_string f "\n(* end of interactive section *)\n"
  | ComOther s ->
      output_string f s;
      if semi then output_string f ";"

(* Remove final semi-colons and white space from [s] *)
let strip_semi s =
  let rec aux last =
    match s.[last] with
    | ' ' | '\009' | '\012' | '\010' | '\013' | ';' -> aux (last-1)
    | _ ->
	String.sub s 0 (last+1)
  in
  aux (String.length s -1)

let add_command state_before state_after s commands =
  if (state_before != state_after) ||
  ( List.exists (function
    (* Commands to keep even if they do not change state *)
    | Ptree.CQuit | Ptree.CSetting _ | Ptree.CAllowed_collisions _
    | Ptree.CTag _ | CForget_old_games -> true
    | _ -> false
	) commands) then
    let command = 
      match commands with
      | [ CQuit ] -> ComQuit
      | _ -> ComOther (strip_semi s)
    in
    begin
      match !command_out_file with
      | None -> ()
      | Some f -> 
         out_command f true command; output_string f "\n"; flush f
    end;
    run_commands := command :: (!run_commands)
       
let out_commands always_semi f =
  let rec aux = function
    | [] -> ()
    | [a] -> out_command f always_semi a; output_string f "\n"; flush f
    | a::l ->
	out_command f true a; output_string f "\n";
	aux l
  in
  aux (List.rev (!run_commands))


let allowed_file_name s =
  let rec allowed_chars s n =
    (n >= String.length s) ||
    (let c = s.[n] in
    (c == '%' || c == '+' || c == '-' || c == '.' ||
    (c >= '0' && c <= '9') || c == '=' ||
    (c >= '@' && c <= 'Z') || c == '_' ||
    (c >= 'a' && c <= 'z') || c == '~') && (allowed_chars s (n+1)))
  in
  s <> "" && s.[0] <> '.' &&
  (allowed_chars s 0)

let prepare_filename s ext =
  if not (allowed_file_name s) then
    raise (Error("File name " ^ s ^ " is not allowed.\nAllowed characters: 0-9A-Za-z%+-.=@_~\n. is not allowed as first character.", ext));
  Filename.concat (!Settings.out_dir) s 
    
let final_out_commands() =
  begin
    match !command_out_file with
    | Some f -> close_out f; command_out_file := None
    | None -> ()
  end;
  if !Settings.command_output <> "" then
    let fname = prepare_filename (!Settings.command_output) dummy_ext in
    try 
      let f = open_out fname in
      out_commands false f;
      close_out f
    with Sys_error s ->
      raise (Error("Cannot open file " ^ fname ^ ": " ^ s, dummy_ext))
    
    
(* For backtracking *)
exception Backtrack

let rec forget_games final_game ins_next state =
  let g = state.game in
  match g.proc with
  | Forgotten _ -> ()
  | RealProcess p ->
     if g != final_game && state.tag = None (* Do not forget tagged states *) then
       begin
         let s = Filename.temp_file "game" ".cv" in
         Display.file_out s dummy_ext (fun () ->
	   Display.mark_occs ins_next;
           Display.display_process p;
	   Display.useful_occs := []);
	 at_exit (fun () -> Unix.unlink s);
         let tex_s = 
           if (!Settings.tex_output) <> "" then
             let s = Filename.temp_file "game" ".tex" in
             Displaytex.file_out s dummy_ext (fun () ->
	       Display.mark_occs ins_next;
               Displaytex.display_process p;
	       Display.useful_occs := []);
	     at_exit (fun () -> Unix.unlink s);
             Some s
           else
             None
         in
         g.proc <- Forgotten { text_display = s; tex_display = tex_s }
       end;
     match state.prev_state with
     | None -> ()
     | Some (IFocus _,_,ins,s') ->
	 (* Do not forget the game just before a [focus] instruction *)
	 forget_games s'.game ins s'
     | Some (_,_,ins,s') -> forget_games final_game ins s'           
       
let forget_old_games state =
  match state.prev_state with
    None -> ()
  | Some (IFocus _,_,ins,s') ->
	 (* Do not forget the game just before a [focus] instruction *)
      forget_games s'.game ins s'
  | Some (_,_,ins,s') -> forget_games state.game ins s'


let rec undo_focus ext state =
  match state.prev_state with
    None -> raise (Error("No previous focus command found", ext))
  | Some (IFocus _,_,_,s') -> s'
  | Some (_,_,_,s') -> undo_focus ext s'

let rec undo_tag s ext state =
  match state.tag with
  | Some s' when s = s' -> state
  | _ ->
      match state.prev_state with
      | None -> raise (Error("State with tag " ^ s ^ " not found", ext))
      | Some(_,_,_,state') -> undo_tag s ext state'

let has_inactive state =
  List.exists (fun q -> Settings.get_query_status q == Inactive) state.game.current_queries
    
let rec undo_find_inactive_rec state =
  match state.prev_state with
    None -> Parsing_helper.internal_error "When there is an inactive query, there should be a previous focus or guess_branch command"
  | Some (IFocus _,_,_,s') -> s'
  | Some (GuessBranch _,_,_,s') ->
      begin
	match Transf_guess.next_case state with
	| Some next_g ->
            (* Prepare the new game as it is done after game transformations *)
	    Terms.move_occ_game next_g;
	    Invariants.global_inv next_g;
	    { game = next_g;
              prev_state = state.prev_state;
              tag = None }	   
	| None -> undo_find_inactive_rec s'
      end
  | Some (_,_,_,s') -> undo_find_inactive_rec s'

let undo_find_inactive state =
  print_string "All active queries proved. Going back to the last focus or guess_branch command."; print_newline();
  undo_find_inactive_rec state
	
let has_common_elem l1 l2 =
  List.exists (fun x -> List.memq x l1) l2

let rec replace_list b bl = function
  | [] -> []
  | b' :: l ->
      if b' == b then
	bl @ (replace_list b bl l)
      else
	b' :: (replace_list b bl l)

let default_file_out s ext f =
  Display.file_out (prepare_filename s ext) ext f
		
let sa_rename_ins_updater b bl = function
    (ExpandGetInsert_ProveUnique | Expand | Simplify _ | SimplifyNonexpanded | 
     RemoveAssign(_, (Minimal | FindCond | EqSide | NoRemAssign)) | 
     MoveNewLet(MAll | MNoArrayRef | MLet | MNew | MNewNoArrayRef) | 
     Proof _ | InsertEvent _ | InsertInstruct _ | ReplaceTerm _ | MergeBranches |
     MergeArrays _ (* MergeArrays does contain variable names, but it is advised only when these variables have a single definition, so they are not modified by SArename *) |
     IFocus _ | Guess _ | GuessBranch _ | MoveIf _) as x -> [x]
  | RemoveAssign (sarename_new, Binders l) ->
      [RemoveAssign (sarename_new, Binders (replace_list b bl l))]
  | UseVariable l ->
      [UseVariable (replace_list b bl l)]
  | SArenaming b' -> 
      if b' == b then
	 (* If b' == b, useless after SArenaming b *)
	[]
      else
	[SArenaming b']
  | MoveNewLet (MBinders l) -> 
      [MoveNewLet (MBinders (replace_list b bl l))]
  | MoveNewLet (MUp(l,occ,ext)) ->
      [MoveNewLet (MUp(replace_list b bl l,occ,ext))]
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

let update_for_transformed_game = function
  | Simplify(collector, l) ->
      (* [collector] becomes invalid as soon as the game is transformed *)
      Simplify(None, l)
  | i -> i
      
let apply_ins_updater ins_up i =
  let i = update_for_transformed_game i in
  match ins_up with
    None -> [i]
  | Some f -> f i

let apply_ins_updater_list ins_up l =
  let l = List.map update_for_transformed_game l in
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

let execute state ins =
  let g = state.game in
  let (g', proba, done_ins) = 
    match ins with
      ExpandGetInsert_ProveUnique -> 
	let g_done = Transf_tables.reduce_tables g in
	compos_transf (Unique.prove_unique_game true) g_done
    | Expand ->
	Transf_expand.expand_process g
    | Simplify(collector, l) ->
	Transf_simplify.simplify_main collector l g
    | SimplifyNonexpanded ->
	Transf_simplify_nonexpanded.main g
    | GlobalDepAnal (b,l) -> Transf_globaldepanal.main b l g
    | MoveNewLet s -> Transf_move.move_new_let s g
    | RemoveAssign (sarename_new, r) -> Transf_remove_assign.remove_assignments sarename_new r g
    | UseVariable l -> Transf_use_variable.use_variable l g
    | SArenaming b -> Transf_sarename.sa_rename b g
    | InsertEvent(s,ext_s,occ,ext_o) -> Transf_insert_event.insert_event occ ext_o s ext_s g
    | InsertInstruct(s,ext_s,occ,ext_o) -> 
	Transf_insert_replace.insert_instruct occ ext_o s ext_s g
    | ReplaceTerm(s,ext_s,occ,ext_o,check_opt) ->
	Transf_insert_replace.replace_term occ ext_o s ext_s check_opt g 
    | MergeArrays(bll, m) ->
	Transf_merge.merge_arrays bll m g
    | MergeBranches ->
	Transf_merge.merge_branches g
    | Guess(arg) ->
	Transf_guess.guess arg state g
    | GuessBranch(occ,no_test,ext_o) ->
	Transf_guess.guess_branch occ no_test ext_o state g
    | MoveIf(arg) ->
	Transf_move_if.move_if arg g
    | CryptoTransf _ | Proof _ | IFocus _ -> 
	Parsing_helper.internal_error "CryptoTransf/Proof/IFocus unexpected in execute"
  in
  (g', proba, done_ins, compos_sa_rename done_ins)


let execute_state_basic state i =
  let tmp_changed = !Settings.changed in
  Settings.changed := false;
  print_string "Doing ";
  Display.display_instruct i;
  print_string "... "; flush stdout;
  let (g', proba, done_ins, ins_update) = execute state i in
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
	 prev_state = Some (i, proba, done_ins, state);
         tag = None }, ins_update)
    end
  else
    begin
      Settings.changed := tmp_changed;
      (state, None)
    end

let default_remove_assign sarename_new =
  let r = if !Settings.auto_remove_assign_find_cond then FindCond else Minimal in
  RemoveAssign(sarename_new, r)
      
let rec execute_state state = function
    SArenaming b ->
      (* Adding simplification after SArenaming *)
      let tmp_changed = !Settings.changed in
      Settings.changed := false;
      let (state', ins_updater) = execute_state_basic state (SArenaming b) in
      if !Settings.changed then 
	if !Settings.simplify_after_sarename then 
	  let (state'', ins_updater') = execute_state_basic state' (default_remove_assign(!Settings.auto_sa_rename)) in
	  let (state''', ins_updater'') = execute_state state'' (Simplify(None, [])) in
	  (state''', compos_ins_updater (compos_ins_updater ins_updater ins_updater') ins_updater'')
	else
	  (state', ins_updater)
      else
	begin
	  Settings.changed := tmp_changed;
	  (state', ins_updater)
	end
  | Simplify _ when not state.game.expanded ->
      (* Fall back to SimplifyNonexpanded when the
	 game is not expanded *)
      execute_state_basic state SimplifyNonexpanded
  | (Simplify _) as i when state.game.expanded ->
      (* Iterate Simplify (!Settings.max_iter_simplif) times *)
      let tmp_changed = !Settings.changed in
      Settings.changed := false;
      print_string "Doing ";
      Display.display_instruct i;
      print_string "... "; flush stdout;
      let rec iterate i iter state =
	let (g', proba, done_ins, ins_updater) = execute state i in
	if !Settings.debug_instruct then
	  begin
	    print_string " Resulting game after one simplification pass:\n";
	    Display.display_game_process g'
	  end;
	let i_next =
	  match i with
	  | Simplify(_,coll_elim) ->
	      (* Drop the collected information in the next iteration,
		 in case the first iteration modifies the game in
		 ways that invalidate that information. *)
	      Simplify(None, coll_elim)
	  | _ -> i
	in
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
		prev_state = Some (i, proba, done_ins, state);
	        tag = None }
	    in
	    let (state'', ins_updater') = iterate i_next iter state' in
	    (state'', compos_ins_updater ins_updater ins_updater')
	| _ ->
	    (* Simplification done *)
	    Terms.move_occ_game g';
	    Invariants.global_inv g';
	    let state' =  
	      { game = g';
		prev_state = Some (i, proba, done_ins, state);
	        tag = None }
	    in
	    if iter != 1 then
	      let (state'', ins_updater') = iterate i_next (iter-1) state' in
	      (state'', compos_ins_updater ins_updater ins_updater')
	    else
	      begin
		print_string "Run simplify ";
		print_int ((!Settings.max_iter_simplif) - iter + 1);
		print_string " time(s). Maximum reached.\n";
		(state', ins_updater)
              end
      in
      let result = iterate i (!Settings.max_iter_simplif) state in
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

let execute_with_advise_last i state = 
  (* No need to update next instructions, so we can ignore the ins_updater *)
  let (state', _) = execute_with_advise state i in
  state'


let execute_display_advise i state =
  if !Settings.auto_advice then
    execute_with_advise_last i state 
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
    execute_display_advise (MoveNewLet MAll) state
  else
    state

let merge state =
  if !Settings.merge_branches then
    execute_display_advise MergeBranches state
  else
    state

let expand state =
  if !Settings.auto_expand && not state.game.expanded then
    execute_display_advise Expand state
  else
    state

exception End of state
exception EndSuccess of state

let basic_success collector state =
  Settings.advise := [];
  let (proved_queries, is_done) = Success.is_success collector state in
  let state' = 
    if proved_queries != [] then
      { game = state.game;
	prev_state = Some (Proof proved_queries, [], [], state);
        tag = None }
    else
      state
  in
  if is_done then
    begin
      if has_inactive state' then
	begin
          (* undo until focus/guess_branch when there is an inactive query *)
	  (undo_find_inactive state', proved_queries != [], is_done)
	end
      else
	raise (EndSuccess state')
    end
  else
    (state', proved_queries != [], is_done)

let basic_success_state state =
  let (state', _,_) = basic_success None state in
  state'
      
let simplify state =
  state
  |> execute_display_advise (default_remove_assign false) 
  |> execute_display_advise (Simplify(None,[]))
  |> move_new_let
  |> execute_display_advise (default_remove_assign(!Settings.auto_sa_rename))
  |> merge

let crypto_simplify state =
  state
  |> execute_display_advise SimplifyNonexpanded
  |> expand
  |> simplify
    
let initial_expand_simplify state =
  state
  |> execute_display_advise ExpandGetInsert_ProveUnique
  |> execute_display_advise SimplifyNonexpanded
  |> expand
  |> simplify

let initial_expand_simplify_success state =
  state
  |> initial_expand_simplify
  |> basic_success_state

let move_if arg state =
  state
  |> execute_display_advise (MoveIf arg)
  |> expand

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
		  prev_state = Some (CryptoTransf(equiv, user_info), proba, ins, state);
		  tag = None })
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
  | equiv::equivs ->
      match equiv.eq_exec with
	ManualEqopt -> 
          (* This equivalence should be applied only manually, and we are in automatic mode, so skip it *) 
	  execute_any_crypto_rec continue state equivs
      |	_ ->
	  let equiv =
	    try
	      Special_equiv.generate equiv Ptree.AutoCall
	    with Error(mess, extent) ->
	      Parsing_helper.input_error mess extent
	  in
      match crypto_transform (!Settings.no_advice_crypto) (Terms.get_actual_equiv equiv) (VarList([],false)) state with
	CSuccess state' -> 
	  begin
	    try
	      continue (CSuccess (crypto_simplify state'))
	    with Backtrack ->
	      if !Settings.backtrack_on_crypto then
		begin
		  (*
		  print_string "Just tried equivalence\n";
		  Display.display_equiv_gen equiv;
		  print_string "\nContinuing with equivalences:\n";
		  List.iter Display.display_equiv_gen equivs;
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

let rec issuccess_with_advise collector state =
  let (state', query_proved, is_done) = basic_success collector state in
  if is_done || (collector != None) then
    (* We do not apply advice when doing [success simplify].
       The goal is to simplify the game by removing useless code,
       not necessarily to prove all queries.
       Applying advice would be rather complicated, because it
       is difficult to know whether the value of [collector]
       after applying advice is better than the one without advice. *)
    (state', is_done)
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
	  let (state_after_success, _) as result = issuccess_with_advise None state'' in
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
    if (state'' == state') && (not query_proved) && (not is_done'') then
      (state, false) (* Forget useless changes *)
    else
      (state'', is_done'')

let display_state final state =
  let state_display_info = Compute_state_display_info.compute_state_display_info state in
  (* Display the state *)
  if final && ((!Settings.proof_output) <> "" || (!Settings.tex_output) <> "") then
    begin
      if (!Settings.proof_output) <> "" then
	begin
	  print_string ("Outputting proof in " ^ (!Settings.proof_output));
	  print_newline();
	  Display.file_out (!Settings.proof_output) dummy_ext (fun () ->
	    Display.display_state state_display_info)
	end;
      if (!Settings.tex_output) <> "" then
	begin
	  print_string ("Outputting latex proof in " ^ (!Settings.tex_output));
	  print_newline();
	  Displaytex.display_state state_display_info;
	end;
      Display.display_conclusion state_display_info
    end
  else
    Display.display_state state_display_info

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

let get_prio equiv =
  match equiv.eq_exec with
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

(* [execute_any_crypto_rec1 state] 
   - raises [EndSuccess state'] when the proof of all properties succeeded.
   - returns [state'] otherwise
   The proof is not displayed. *)
let rec execute_any_crypto_rec1 interactive state =
  try 
    let (state', is_done) =  issuccess_with_advise None state in
    if is_done (* all active queries proved, but inactive query remains *) then
      execute_any_crypto_rec1 interactive state'
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
	     state'
        | lequiv::rest_equivs ->
	   execute_any_crypto_rec (function
	       | CSuccess state'' -> execute_any_crypto_rec1 interactive state''
	       | CFailure l -> execute_crypto_list (function 
		   | CFailure _ -> 
		       apply_equivs rest_equivs
		   | CSuccess state''' ->
		       let state''' = crypto_simplify state''' in
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
         state
       end
     else
       raise Sys.Break

(* [execute_any_crypto state] 
   - raises [EndSuccess state'] when the proof of all properties succeeded.
   - returns [()] otherwise
   The proof is displayed in case [()] and not displayed in case [EndSuccess]. *)
let execute_any_crypto state =
  (* For the automatic proof strategy, we always use auto_expand and auto_advice *)
  Settings.auto_expand := true;
  Settings.auto_advice := true;
  (* Always begin with find/if/let expansion *)
  try
    let state' = execute_any_crypto_rec1 false (initial_expand_simplify state) in
    print_string "===================== Proof starts =======================\n";
    flush stdout;
    display_state true state'
  with Backtrack ->
    print_string "===================== Proof starts =======================\n";
    flush stdout;
    display_state true state
	    
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

let extract_regexp (s,ext) =
  try
    Str.regexp s
  with Failure err ->
    raise(Error("Incorrect regular expression: " ^ err, ext))
    
let get_occ_of_line p ((regexp_str, ext) as regexp_id) occ_loc n is_max =
  let regexp = extract_regexp regexp_id in
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
		    let matched_string = Str.matched_string line in
		    check_no_further_match is_max (match_pos+1) line;
		    state := Found matched_string;
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
  Display.display_occurrences :=
     (match occ_loc with
     | Before | After -> ProcessOccs
     | At _ -> AllOccs);
  begin
    try 
      Display.fun_out string_handler (fun () ->
	Display.display_process p)
    with Stop -> ()
  end;
  Display.display_occurrences := NoOcc;
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
  | POccBefore regexp_id ->
      get_occ_of_line p regexp_id Before 1 true
  | POccBeforeNth(n, regexp_id) ->
      get_occ_of_line p regexp_id Before n false
  | POccAfter regexp_id ->
      get_occ_of_line p regexp_id After 1 true
  | POccAfterNth(n, regexp_id) ->
      get_occ_of_line p regexp_id After n false
  | POccAt(n_in_pat, regexp_id) ->
      get_occ_of_line p regexp_id (At n_in_pat) 1 true
  | POccAtNth(n, n_in_pat, regexp_id)  ->
      get_occ_of_line p regexp_id (At n_in_pat) n false
  | POccInt(occ) ->
      occ

let find_binders game =
  let p = Terms.get_process game in
  let accu = Hashtbl.create 7 in
  let add b =
    let s = Display.binder_to_string b in
    if not (Hashtbl.mem accu s) then
      Hashtbl.add accu s b
  in
  let rec aux_def_list_t t =
    match t.t_desc with
    | Var(b,l) -> 
	List.iter aux_def_list_t l;
	add b
    | FunApp(_,l) ->
	List.iter aux_def_list_t l
    | ReplIndex _ -> ()
    | _ -> 
	Parsing_helper.internal_error "if/let/find/new forbidden in def_list"
  in
  let aux_def_list def_list =
    List.iter (fun (b,l) -> List.iter aux_def_list_t l; add b) def_list
  in
  let rec aux_t t =
    begin
      match t.t_desc with
      | FindE(l0,t3,_) ->
	  List.iter (fun (bl,def_list,t1,t2) ->
	    List.iter (fun (b,_) -> add b) bl;
	    ) l0
      | ResE(b,t) ->
	  add b
      | _ -> ()
    end;
    Terms.iter_subterm aux_t aux_def_list aux_pat t
  and aux_pat = function
    | PatVar b -> add b
    | pat -> Terms.iter_subpat aux_t aux_pat pat
  and aux_i p =
    Terms.iter_subiproc aux_i (fun (c, tl) pat p ->
      List.iter aux_t tl;
      aux_pat pat;
      aux_o p) p
  and aux_o p =
    begin
      match p.p_desc with
      | Restr(b,p) -> 
	  add b
      | Find(l0,p2,_) ->
	  List.iter (fun (bl,def_list,t,p1) ->
	    List.iter (fun (b,_) -> add b) bl;
	    ) l0
      | _ -> ()
    end;
    Terms.iter_suboproc aux_o aux_t aux_def_list aux_pat aux_i p
  in
  aux_i p;
  accu 

let find_binder_list_one_id binders ((s,ext) as regexp_id) =
  let regexp = extract_regexp regexp_id in
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


let find_repl_indices game =
  let p = Terms.get_process game in
  let accu = Hashtbl.create 7 in
  let add_ri b =
    let s = Display.repl_index_to_string b in
    if not (Hashtbl.mem accu s) then
      Hashtbl.add accu s b
  in
  let rec aux_i p =
    match p.i_desc with
      Nil -> ()
    | Par(p1,p2) -> aux_i p1; aux_i p2
    | Repl(b,p) -> add_ri b; aux_i p
    | Input(_ch,_pat,p) -> aux_o p
  and aux_o p =
    Terms.iter_suboproc aux_o (fun _ -> ()) (fun _ -> ()) (fun _ -> ()) aux_i p
  in
  aux_i p;
  accu 

let find_guess_binder binders (id,ext) =
  try
    Hashtbl.find binders id
  with Not_found ->
    raise (Error("Variable "^id^" not found", ext))

let find_repl_index_or_binder repl_indices binders (id,ext) =
  try
    GuessRepl(Hashtbl.find repl_indices id, false, ext)
  with Not_found ->
    try
      let b' = Hashtbl.find binders id in
      let l_b = List.length b'.args_at_creation in
      if l_b != 0 then
	raise (Error("Variable "^(Display.binder_to_string b')^" expects "^(string_of_int l_b)^
		     " indices, but is here given no index", ext));
      GuessVar((b',[]), false, ext)
    with Not_found ->
      raise (Error("Replication index or variable "^id^" not found", ext))
    
let find_repl_index repl_indices (id,ext) =
  try
    GuessRepl(Hashtbl.find repl_indices id, true, ext)
  with Not_found ->
    raise (Error("Replication index "^id^" not found", ext))
	
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
  | Proba (p,_) -> f = p.prname
  | p -> Terms.exists_sub_probaf (find_proba f) p

let find_equiv f equiv =
  match equiv.eq_fixed_equiv with
  | None -> false
  | Some (lm, _, set, _) ->
      (List.exists (fun (fg, _) -> find_funsymb_fg f fg) lm) ||
      (List.exists (function 
	  SetProba r -> find_proba f r
	| SetEvent(e,_,_,_) -> f = e.f_name) set)

let find_equiv_by_name f equiv =
  match equiv.eq_name with
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
	find_list (fun (b,_,_) ->
	  if Display.binder_to_string b = s then b else raise Not_found) restr
      with Not_found ->
	find_list (find_restr_fg s) l
    
let find_restr (s,ext) ((_,lm,_,_,_,_),_) =
  try 
    find_list (fun (a,_) -> find_restr_fg s a) lm
  with Not_found ->
    raise (Error("Random variable " ^ s ^ " not found in equivalence", ext))
    
let get_equiv_info need_info equiv =
  match equiv.eq_special with
  | None when not need_info -> PVarList([],false) 
  | _ ->
      print_string "Please enter variable and/or term mapping for this equivalence: ";
      let s = read_line() in
      Syntax.parse_from_string Parser.cryptotransfinfo (s, dummy_ext)

let get_special_args equiv =
  match equiv.eq_special with
  | None -> []
  | Some _ ->
      print_string "Please enter the option for this \"special\" equivalence: ";
      let s = read_line() in
      Syntax.parse_from_string Parser.special_args (s, dummy_ext)

exception NthFailed
	
let nth l n =
  try
    List.nth l n
  with _ ->
    raise NthFailed

let get_equiv need_info interactive eqname special_args info ext =
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
	  with NthFailed ->
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
  let (equiv, special_args, info) = 
    match possible_equivs with
    | [] -> raise (Error("No equivalence corresponds to the one you mention", ext_equiv))
    | [equiv] -> 
	begin
	  match eqname with
	  | PNoName when interactive -> 
	      print_string "Using ";
	      Display.display_equiv_gen equiv; print_newline();
	      let special_args = get_special_args equiv in
	      let info = get_equiv_info need_info equiv in
	      (equiv, special_args, info)
	  | _ -> (equiv, special_args, info)
	end
    | _ -> 
	if interactive then
	  begin
	    let n = ref 0 in
	    List.iter (fun equiv -> incr n; print_int (!n); print_string ". "; Display.display_equiv_gen equiv; print_newline()) possible_equivs;
	    print_string "Please enter number of equivalence to consider: ";
	    let s = read_line() in
	    try
	      let equiv = List.nth possible_equivs (int_of_string s - 1) in
	      match eqname with
	      | PNoName ->
		  let special_args = get_special_args equiv in
		  let info = get_equiv_info need_info equiv in
		  (equiv, special_args, info)
	      | _ -> (equiv, special_args, info)
	    with Failure _ -> 
	      raise (Error("Incorrect number", dummy_ext))
	  end
	else
	  raise (Error("Several equivalences correspond to what you mention", ext_equiv))
    in
  if equiv.eq_special == None && special_args <> [] then
    raise (Error("Only special equivalences support special arguments in the crypto/show_equiv/out_equiv command", ext));
  let info' = 
    match info with
    | Ptree.PRepeat _ -> PVarList([],false) 
    | _ -> info
  in
  let equiv1 = Special_equiv.generate equiv (ManualCall(special_args, info')) in
  let equiv2 = Terms.get_actual_equiv equiv1 in
  (equiv2, info)

	
let do_equiv ext equiv2 parsed_user_info state =
  match parsed_user_info with
    Ptree.PRepeat(fast) ->
      let empty_user_info = VarList([],false) in
      let rec repeat_crypto state = 
	match crypto_transform (!Settings.no_advice_crypto) equiv2 empty_user_info state with
	  CSuccess state' ->
	    let state' = if fast then state' else crypto_simplify state' in
	    repeat_crypto state'
	| CFailure l -> 
	    execute_crypto_list (function 
		CSuccess state'' ->
		  let state'' = if fast then state'' else crypto_simplify state'' in
		  repeat_crypto state''
	      | CFailure _ -> print_string "Done all possible transformations with this equivalence.\n"; flush stdout; state) (List.map (fun x -> (x, state, false)) l) 
      in
      let state1 = repeat_crypto state in
      (* In fast mode, we do not simplify between each crypto transformation,
         but we simplify in the end *)
      if fast then crypto_simplify state1 else state1
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
		    let v_equiv = find_restr id_equiv equiv2 in
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
		    (interpret_occ state occ, find_oracle id_oracle equiv2)) map) @ old_term_mapping,
					stop || old_stop)
		       ) l;
	    Detailed (!var_mapping, !term_mapping)
      in
      match crypto_transform (!Settings.no_advice_crypto) equiv2 user_info state with
	CSuccess state' -> crypto_simplify state'
      | CFailure l -> 
	  if !Settings.auto_advice then
	    execute_crypto_list (function 
	      CSuccess state'' -> crypto_simplify state''
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
  | Some (ExpandGetInsert_ProveUnique,_,_, { prev_state = None }) ->
      raise (Error("Cannot undo the first expansion", ext))
  | Some (ExpandGetInsert_ProveUnique,_,_,_) ->
      Parsing_helper.internal_error "ExpandGetInsert_ProveUnique should occur only as first instruction"
  | Some (_,_,_,state') -> undo ext state' (n-1)
	
let display_facts_at state occ_cmd =
  let occ = interpret_occ state occ_cmd in
  (* First compute the facts, then display them *)
  Improved_def.improved_def_game None true state.game;
  Facts.display_facts_at (Terms.get_process state.game) occ;
  Improved_def.empty_improved_def_game true state.game
    

let interpret_coll_elim state = function
  | PCollVars l -> CollVars(List.map fst l)
  | PCollTypes l -> CollTypes(List.map fst l)
  | PCollTerms l -> CollTerms(List.map (interpret_occ state) l)
    
let help() =
  print_string (
  "List of available commands\n" ^
  "remove_assign useless        : remove useless assignments\n" ^
  "remove_assign findcond       : remove useless assignments and assignments in conditions of \"find\"\n" ^
  "remove_assign binder <ident> : remove assignments on variable <ident>\n" ^
  "remove_assign all            : remove all assignments (not recommended)\n" ^
  "use_variable <ident>         : replace terms equal to <ident> with <ident>\n" ^
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
  "crypto ...                   : apply a cryptographic transformation\n" ^
  "(can be used alone or with a specifier of the transformation; see the manual)\n" ^
  "simplify                     : simplify the game\n" ^
  "simplify coll_elim <locations> : simplify the game, allowing collision elimination at <locations> (variables, types, occurrences)\n" ^
  "all_simplify                 : remove_assign useless, simplify, move all, merge_branches\n" ^
  "insert_event <ident> <occ>   : insert an event <ident> at occurrence <occ>\n" ^
  "insert <occ> <ins>           : insert instruction <ins> at occurrence <occ>\n" ^
  "replace <occ> <term>         : replace term at occurrence <occ> with <term> (when equal)\n" ^
  "merge_arrays <ident> ...     : merge all given variables\n" ^
  "merge_branches               : merge find branches\n" ^
  "expand                       : expand terms if, let, find, new, event, event_abort into processes\n" ^
  "guess <i>                    : guess replication index <i>\n" ^
  "guess <i> && above           : guess replication indices above replication index <i>\n" ^
  "guess <occ>                  : guess replication index at occurrence <occ>\n" ^
  "guess <occ> && above         : guess replication indices above replication at occurrence <occ>\n" ^
  "guess \"x[i1...in]\"           : test equality of x[i1...in] with a guessed value\n" ^
  "guess \"x[i1...in]\" no_test   : replace x[i1...in] with a guessed value\n" ^  
  "guess_branch <occ>           : guess which branch is taken at occurrence <occ>; abort in case of wrong guess\n" ^
  "guess_branch <occ> no_test   : guess which branch is taken at occurrence <occ>; always run that branch\n" ^
  "move_if_fun <occ> ...        : move the predefined function if_fun from inside terms at the given occurrences to their root\n" ^
  "move_if_fun <f> ...          : move if_fun from under the given function symbols to just above\n" ^
  "move_if_fun level <n>        : move if_fun <n> function symbols up\n" ^
  "move_if_fun to_term          : transform if_fun into if ... then ... else ... everywhere\n" ^
  "move_if_fun to_term <occ> ...: transform if_fun into if ... then ... else ... at the given occurrences\n" ^
  "start_from_other_end         : in equivalence proofs, transform the other game\n" ^
  "success                      : check the desired properties\n" ^
  "success simplify             : remove code that cannot make properties to prove false\n" ^
  "show_game                    : show the current game\n" ^
  "show_game occ                : show the current game with occurrences\n" ^
  "show_state                   : show the sequence of games up to now\n" ^
  "show_facts <occ>             : show the facts that hold at program point <occ>\n" ^
  "show_equiv ...               : display the equivalence used by a cryptographic transformation\n" ^
  "show_commands                : display the executed interactive commands\n" ^
  "out_game <filename>          : output the current game to <filename>\n" ^
  "out_game <filename> occ      : output the current game with occurrences to <filename>\n" ^
  "out_state <filename>         : output the sequence of games up to now to <filename>\n" ^
  "out_facts <filename> <occ>   : output the facts that hold at program point <occ> to <filename>\n" ^
  "out_equiv <filename> ...     : output the equivalence used by a cryptographic transformation to <filename>\n" ^
  "out_commands <filename>      : output the executed interactive commands to <filename>\n" ^
  "auto                         : try to terminate the proof automatically\n" ^
  "set <param> = <value>        : set the value of various parameters\n" ^
  "allowed_collisions <formulas>: determine when to eliminate collisions\n" ^
  "focus \"query 1\", ..., \"query n\" : try proving only the mentioned queries\n" ^
  "undo                         : undo the last transformation\n" ^
  "undo <n>                     : undo the last n transformations\n" ^
  "undo focus                   : go back until before the last focus command\n" ^
  "tag <tag>                    : give the name <tag> to the current state\n" ^
  "undo <tag>                   : undo the transformation until the state named <tag>\n" ^
  "restart                      : restart from the initial game\n" ^
  "forget_old_games             : remove old games from memory, to have more space (prevents undo)\n" ^
  "quit                         : quit interactive mode\n" ^
  "help                         : display this help message\n" ^
  "?                            : display this help message\n")

(* Equality test for command focus *)

	
let empty_pubvars = function
  | QSecret(_,[],_)
  | QEventQ(_,_,[])
  | QEquivalence(_,[],_)
  | QEquivalenceFinal(_,[]) -> true
  | _ -> false
  
	
let rec map_queries accu focusql allql =
  match focusql with
    [] -> accu
  | (q, ext)::restfocusql ->
      let found_list = 
	if empty_pubvars q then
          (* When q has no public variables, we allow matching
	     queries with any public variables, provided only one
	     of them matches. Otherwise, we match the exact query *)
	  let equal_q = List.filter (function (q',_),_ -> Terms.equal_query_any_pubvars q q') allql in
	  match equal_q with
	  | _::_::_ ->
	      List.filter (function (q',_),_ -> Terms.equal_query q q') allql
	  | _ -> equal_q
	else
	  List.filter (function (q',_),_ -> Terms.equal_query q q') allql
      in
      match found_list with
      | [] -> (* Not found *)
	  print_string "Focus: the following query is not found\n";
	  print_string "  "; Display.display_query3 q; print_newline();
	  raise (Error("Focus: query not found", ext));
      | [qentry] ->
	  begin
	    match Settings.get_query_status qentry with
	    | Inactive ->
		print_string "Focus: the following query is inactive:\n";
		print_string "  "; Display.display_query3 q; print_newline();
		raise (Error("You cannot focus on a query that is already inactive", ext))
	    | Proved _ ->
		print_string "Focus: the following query is already proved:\n";
		print_string "  "; Display.display_query3 q; print_newline();
		raise (Error("You cannot focus on a query that is already proved", ext))		
	    | ToProve -> ()
	  end;
	  if List.memq qentry accu then
	    begin
	      print_string "Focus: the following query is already mentioned in the same focus command\n";
	      print_string "  "; Display.display_query3 q; print_newline();
	      raise (Error("Focusing on several times the same query", ext))
	    end;
	  map_queries (qentry::accu) restfocusql allql
      | _ -> Parsing_helper.internal_error "Duplicate query"

let rec last_extent = function
    [] -> Parsing_helper.internal_error "empty list in last_extent"
  | [_, ext] -> ext
  | _ ::l -> last_extent l

let list_extent = function
    [] -> Parsing_helper.internal_error "empty list in list_extent"
  | ((_, first_ext)::_) as l -> Parsing_helper.merge_ext first_ext (last_extent l)
	    
(* For debugging: display information collected when the adversary wins *)
	
let display_collector coll =
  print_string "When the adversary wins, one of the following cases holds:\n";
  List.iter (function
    | CollectorNoInfo ->
	print_string "* no information collected"
    | CollectorFacts(all_indices, pp_list, simp_facts, def_list) ->
	print_string "* \n";
	print_string "indices: ";
	Display.display_list Display.display_repl_index all_indices;
	print_newline();
	print_string "pp:\n";
	Display.display_pps pp_list;
	Display.display_facts simp_facts;
	print_string "def vars:\n";
	Display.display_def_list_lines def_list;
	print_newline()
    | CollectorProba proba_state ->
	print_string "* probabilities:\n";
	Depanal.display_proba_state proba_state
	  ) coll
	
let success_command do_simplify state =
  (* [collector] collects facts that are known to hold when the adversary
     wins, i.e. falsifies a query.
     The list inside [collector] is a disjunction. *)
  let collector =
    if do_simplify = None then
      None
    else
      Some (ref [])
  in
  let (state', is_done) = issuccess_with_advise collector state in
  if is_done then
    state'
  else
    begin
      print_string "Sorry, the following queries remain unproved:\n";
      List.iter (fun (((a,_), _) as q) ->
	if Settings.get_query_status q == ToProve then
	  begin
	    print_string "- ";
	    Display.display_query3 a;
	    print_newline()
	  end
	    ) state'.game.current_queries;
      match do_simplify, collector with
      |	Some coll_elim, Some coll_ref ->
	  let coll_content = !coll_ref in
	  if Terms.is_collector_no_info coll_content then
	    begin
	      print_string "Sorry, I could not infer simplification information via success.\n";
	      state'
	    end
	  else
	    begin
	      (* simplify *)
	      assert(coll_content != []);
	      if !Settings.debug_event_adv_loses then
		display_collector coll_content;
	      execute_display_advise (Simplify (Some coll_content, coll_elim)) state'
	    end
      | None, None -> state'
      | _ ->
	  Parsing_helper.internal_error "Instruct.success_command: incoherent do_simplify and collector"
    end

	
	
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
	| RemCst x -> execute_display_advise (RemoveAssign(false, x)) state 
	| RemBinders l ->
	    let binders = find_binders state.game in
	    execute_display_advise (RemoveAssign (false, Binders (find_binder_list binders l))) state 
      end
  | CUse_variable(l) ->
      let binders = find_binders state.game in
      execute_display_advise (UseVariable(find_binder_list binders l)) state 
  | CMove(arg) ->
      begin
	match arg with
	| MoveCst x -> execute_display_advise (MoveNewLet x) state 
	| MoveBinders l ->
	    let binders = find_binders state.game in	      
	    execute_display_advise (MoveNewLet (MBinders (find_binder_list binders l))) state 
	| MoveArray(((s,ext2) as id), collisions) ->
	    begin
	      let binders = find_binders state.game in	      
	      let bl = find_binder_list_one_id binders id in
	      let equiv = Terms.get_actual_equiv (Special_equiv.move_array_equiv ext2 bl collisions) in 
	      match crypto_transform (!Settings.no_advice_crypto) equiv (VarList(bl,true)) state with
		CSuccess state' -> crypto_simplify state'
	      | CFailure l -> 
		  raise (Error ("Transformation \"move array\" failed", ext2))
	    end
	| MoveUp(l, (occ_cmd, ext)) ->
	    begin
	      let binders = find_binders state.game in	      
	      let bl = find_binder_list binders l in
	      let occ = interpret_occ state occ_cmd in
	      execute_display_advise (MoveNewLet (MUp (bl, occ, ext))) state 
	    end
      end
  | CSimplify(coll_elim) -> 
      execute_display_advise (Simplify (None, List.map (interpret_coll_elim state) coll_elim)) state 
  | CInsert_event((s, ext1), (occ_cmd, ext)) ->
      begin
	try
	  if String.length s = 0 then raise Not_found;
	  if (s.[0] < 'A' || s.[0] >'Z') && (s.[0] < 'a' || s.[0] > 'z') then raise Not_found;
	  for i = 1 to String.length s - 1 do
	    if s.[i] <> '\'' && s.[i] <> '_' && (s.[i] < 'A' || s.[i] >'Z') && (s.[i] < 'a' || s.[0] > 'z') && (s.[i] < '\192' || s.[i] > '\214') && (s.[i] < '\216' || s.[i] > '\246') && (s.[i] < '\248') && (s.[i] < '0' && s.[i] > '9') then raise Not_found;
	  done;
	  let occ = interpret_occ state occ_cmd in
	  expand (execute_display_advise (InsertEvent(s,ext1,occ,ext)) state)
	with 
	  Not_found ->
	    raise (Error(s ^ " should be a valid identifier: start with a letter, followed with letters, accented letters, digits, underscores, quotes", ext1))
      end
  | CInsert((occ_cmd, ext_o), (ins_s, ext_s)) ->
      let occ = interpret_occ state occ_cmd in
      execute_display_advise (InsertInstruct(ins_s,ext_s,occ,ext_o)) state 
  | CReplace((occ_cmd, ext_o), (ins_s, ext_s), check_opt) ->
      let occ = interpret_occ state occ_cmd in
      execute_display_advise (ReplaceTerm(ins_s,ext_s,occ,ext_o,check_opt)) state 
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
	execute_display_advise (MergeArrays(bl, MCreateBranchVar)) state 
      end
  | CMerge_branches ->
      execute_display_advise MergeBranches state 
  | CSArename(id) ->
      let binders = find_binders state.game in
      List.fold_left (fun state b ->
	execute_display_advise (SArenaming b) state)
	state (find_binder_list_one_id binders id)
  | CSArenameNew ->
      execute_display_advise (RemoveAssign(true, NoRemAssign)) state       
  | CGlobal_dep_anal(id, coll_elim) ->
      let coll_elim' = List.map (interpret_coll_elim state) coll_elim in
      let binders = find_binders state.game in	      
      List.fold_left (fun state b ->
	execute_display_advise (GlobalDepAnal (b, coll_elim')) state)
	state (find_binder_list_one_id binders id)
  | CExpand ->
      execute_display_advise Expand state
  | CAll_simplify ->
      simplify state
  | CCrypto(eqname, special_args, info, ext) ->
      let (equiv, info) = get_equiv true interactive eqname special_args info ext in
      do_equiv ext equiv info state
  | CShow_equiv(eqname, special_args, info, ext) ->
      let (equiv, _) = get_equiv false interactive eqname special_args info ext in
      Display.display_equiv equiv ;
      state
  | COut_equiv((s,ext),eqname, special_args, info, ext2) ->
      let (equiv, _) = get_equiv false interactive eqname special_args info ext2 in
      default_file_out s ext (fun () ->
	Display.display_equiv equiv);
      state
  | CShow_commands ->
      out_commands true stdout;
      state
  | COut_commands(s,ext) ->
      begin
	let new_file =
	  if s = "" then
	    None
	  else
	    let fname = prepare_filename s ext in
	    try
	      Some (open_out fname)
	    with Sys_error e ->
	      raise (Error("Cannot open file " ^ fname ^ ": " ^ e, ext))
	in
	if !Settings.command_output <> "" then
	  begin
	    final_out_commands();
	    print_string ("Passed commands output to "^(!Settings.command_output)^".\n");
	    run_commands := [];
	    Settings.command_output := s;
	    command_out_file := new_file;
	    if s = "" then
	      print_string "Future commands will not be output.\n"
	    else
	      print_string ("Future commands will be output to "^s^".\n");
	  end
	else if s = "" then
	  (* Situation unchanged: no output before and after the command *)
	  print_string "Interactive commands not output.\n"
	else
	  begin
	    Settings.command_output := s;
	    command_out_file := new_file;
	    print_string ("Interactive commands output to "^s^".\n");
	    match new_file with
	    | None -> assert false
	    | Some f -> out_commands true f
	  end
      end;
      state
  | CStart_from_other_end(ext) ->
      let rec remove_eq_query state =
        state.game.current_queries <-
           List.filter (function ((QEquivalence _,_),poptref) -> !poptref != ToProve | _ -> true)
             state.game.current_queries;
        match state.prev_state with
          None -> ()
        | Some(_,_,_,s') -> remove_eq_query s'
      in
      let rec add_query q state =
	begin
	  match state.game.current_queries with
	  | q' :: _ when q' == q -> ()
		(* The case above is needed to avoid adding [q] several times
                   when several states contain the same game. That can happen
                   with the [success] command. *)
	  | _ -> state.game.current_queries <- q :: state.game.current_queries;
	end;
        match state.prev_state with
          None -> ()
        | Some(_,_,_,s') -> add_query q s'
      in
      let (equivalence_q, other_q) =
        List.partition (function ((QEquivalence _,_),poptref) -> !poptref = ToProve | _ -> false) state.game.current_queries
      in
      begin
        match equivalence_q with
        | [] ->
            raise (Error("start_from_other_end applies only when there is an equivalence query to prove", ext))
        | [(QEquivalence(state_other_end, pub_vars, current_is_lhs), g), _] ->
            remove_eq_query state;
            let init_game_other_end = Display.get_initial_game state_other_end in
            let new_equivalence_q =
              (QEquivalence(state, pub_vars, not current_is_lhs), init_game_other_end), ref ToProve
            in
            add_query new_equivalence_q state_other_end;
            state_other_end
        | _ ->
            Parsing_helper.internal_error "start_from_other_end: There should be at most one equivalence query to prove"
      end
  | CQuit ->
      raise (End state)
  | CSuccesscom ->
      success_command None state
  | CSuccessSimplify(coll_elim) ->
      success_command (Some (List.map (interpret_coll_elim state) coll_elim)) state
  | CShow_game(occ) ->
      Display.display_occurrences := if occ then AllOccs else NoOcc;
      Display.display_game_process state.game;
      Display.display_occurrences := NoOcc;
      state
  | CShow_state ->
      display_state false state;
      state
  | CShow_facts(occ_cmd) ->
      display_facts_at state occ_cmd;
      state
  | COut_game((s,ext), occ) ->
      default_file_out s ext (fun () ->
	Display.display_occurrences := if occ then AllOccs else NoOcc;
	Display.display_game_process state.game;
	Display.display_occurrences := NoOcc);
      state
  | COut_state(s,ext) ->
      default_file_out s ext (fun () ->
	display_state false state);
      state
  | COut_facts((s, ext1), occ_cmd) ->
      default_file_out s ext1 (fun () ->
        display_facts_at state occ_cmd);
      state
  | CAuto ->
      begin
	(* In command "auto", we always use auto_expand and auto_advice *)
	let old_auto_expand = !Settings.auto_expand in
	let old_auto_advice = !Settings.auto_advice in
	Settings.auto_expand := true;
	Settings.auto_advice := true;
	try
	  let state' = execute_any_crypto_rec1 true state in
	  Settings.auto_expand := old_auto_expand;
	  Settings.auto_advice := old_auto_advice;
	  state'
	with Backtrack ->
	  Settings.auto_expand := old_auto_expand;
	  Settings.auto_advice := old_auto_advice;
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
	match coll with
	| Allowed_Coll_Exact(proba_est) ->
	    Settings.trust_size_estimates := true;
	    Settings.tysize_MIN_Coll_Elim := Settings.parse_pest proba_est
	| Allowed_Coll_Asympt(coll_list) ->
	    Settings.allowed_collisions := [];
	    Settings.trust_size_estimates := false;
	    List.iter (fun (pl,pest) -> 
	      let pl' = List.map (fun (p,exp) ->
		if exp <= 0 then
		  raise (Error("Exponent should be strictly positive", snd p));
		(Settings.parse_psize p, exp)) pl in
	      Settings.allowed_collisions := (pl', Settings.parse_pest pest) :: (!Settings.allowed_collisions)
										  ) coll_list;
	    Settings.tysize_MIN_Coll_Elim :=
	       Terms.min_list (fun (_, ty_size) -> ty_size) (!Settings.allowed_collisions);
	    (* Optimization: when elimination of collision is entirely forbidden,
	       disable without trying it and finding that the probability is too large *)
	    Settings.proba_zero := (coll_list == [])
      end;
      state
  | CUndo(v, ext) ->
      undo ext state v
  | CFocus(l) ->
      (* Note: in case the query contains several subqueries:
            query q1; ...; qn
	 the extent that we provide will be the extent of the whole
	 group of queries instead of the extent of each qi. This is
	 not perfect, but better than nothing. *)
      let lparsed = List.concat (List.map (fun (s, ext_s) ->
	let (vars, ql) = Syntax.parse_from_string Parser.focusquery (s,ext_s) in
	Syntax.queries_map_vars vars ql
	  ) l)
      in
      let query_vars = Settings.get_public_vars state.game.current_queries in
      Stringmap.set_binder_env
	(List.fold_left (fun env b ->
	  Stringmap.add_in_env1existing env (Display.binder_to_string b) b  
	    ) Stringmap.empty_binder_env query_vars);
      let lq =
	try
	  List.map (fun q -> (Syntax.check_query q, snd q)) lparsed
	with Stringmap.Undefined(i,ext) ->
	  raise (Error (i ^ " not defined in a query", ext))
      in
      let lqentries = map_queries [] lq state.game.current_queries in
      let made_inactive = ref false in
      let queries' = List.map (fun (((q, g) as qg, poptref) as qentry) ->
	if Settings.get_query_status qentry = ToProve then
	  if List.memq qentry lqentries then
	    qentry
	  else
	    begin
	      made_inactive := true;
	      (qg, ref Inactive)
	    end
	else
	  qentry) state.game.current_queries
      in
      if not (!made_inactive) then
	raise (Error("Focus: useless command since all queries remain active", list_extent l));
      let game' = { state.game with current_queries = queries' } in
      { game = game';
	prev_state = Some(IFocus (List.map fst lq), [], [], state);
        tag = None }    
  | CUndoFocus(ext) ->
      undo_focus ext state
  | CTag(s,ext) ->
      begin
	match state.tag with
	| Some s' ->
	    print_string ("Warning: current state was already tagged "^ s' ^". Cancelling that tag.\n")
	| None -> ()
      end;
      state.tag <- Some s;
      state
  | CUndoTag(s,ext) ->
      undo_tag s ext state
  | CGuess(arg) ->
      let interpreted_arg =
	match arg with
	| CGuessId(id,no_test,false) ->
	    begin
	      match Syntax.parse_from_string Parser.guess_binderref id with
	      | (b,l) ->
		  let binders = find_binders state.game in
		  let b' = find_guess_binder binders b in
		  let l_b = List.length b'.args_at_creation in
		  let l_l = List.length l in
		  if l_b != l_l then
		    raise (Error("Variable "^(Display.binder_to_string b')^" expects "^(string_of_int l_b)^
		       " indices, but is here given "^(string_of_int l_l)^" indices", snd id));
		  let get_cst ri (s,ext) =
		    let f = Stringmap.get_function_no_letfun_no_if (!Stringmap.env) s ext in
		    (* "if_fun" rejected because it takes 3 arguments *)
		    if fst f.f_type <> [] then
		      raise (Error("Indices of variable should be constants in the guess command", ext));
		    if snd f.f_type != ri.ri_type then
		      raise (Error("Variable "^(Display.binder_to_string b')^" expects an index of type "^
				   ri.ri_type.tname^" but is here given an index of type "^
				   (snd f.f_type).tname, ext));
		    Terms.app f []
		  in
		  let l' = List.map2 get_cst b'.args_at_creation l in
		  GuessVar((b',l'),no_test,snd id)
	      | exception (Error _) ->
		  let repl_indices = find_repl_indices state.game in
		  let binders = find_binders state.game in
		  if no_test then
		    let b' = find_guess_binder binders id in
		    GuessVar((b',[]),no_test,snd id)
		  else
		    find_repl_index_or_binder repl_indices binders id 
	    end
	| CGuessId(id,false,true) ->
	    let repl_indices = find_repl_indices state.game in
	    find_repl_index repl_indices id
	| CGuessId(id,true,true) ->
	    Parsing_helper.internal_error "guess <..> no_test and above should not be allowed by the parser" 
	| CGuessOcc(occ_cmd, and_above, ext_o) ->
	    let occ = interpret_occ state occ_cmd in
	    GuessOcc(occ, and_above, ext_o)
      in
      execute_display_advise (Guess interpreted_arg) state
  | CGuess_branch(occ_br, no_test, ext_o) ->
      let occ = interpret_occ state occ_br in
      execute_display_advise (GuessBranch(occ, no_test, ext_o)) state
  | CMove_if arg ->
      begin
	match arg with
	| CMovePos l ->
	    let l' = List.map (function
	      | CMoveOcc(occ,ext) -> MoveOcc(interpret_occ state occ, ext)
	      | CMoveFun(id,ext) ->
		  let f = Stringmap.get_function_no_letfun_no_if (!Stringmap.env) id ext in
		  if f == Stringmap.dummy_if_fun then
		    raise (Error("Cannot move_if_fun to if_fun itself", ext));
		  MoveFun(f, ext)
			      ) l
	    in
	    move_if (MovePos l') state
	| CMoveLevel (n,ext) ->
	    if n <= 0 then
	      raise (Error("In command move_if_fun, the number of levels to move must be strictly positive", ext));
	    move_if (MoveLevel n) state
	| CMoveToTerm lopt ->
	    let lopt' =
	      match lopt with
	      | None -> None
	      | Some l -> Some (List.map (fun (occ,ext) -> (interpret_occ state occ, ext)) l)
	    in
	    move_if (MoveToTerm lopt') state
      end
  | CRestart(ext) ->
      let rec restart state =
	match state.prev_state with
	  None -> state
	| Some (_,_,_,state') -> restart state'
      in
      let state' = restart state in 
      begin
	match state'.game.proc with
	| RealProcess _ -> initial_expand_simplify_success state'
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
    Lexer.in_proof := true;
    let commands =
      try
	Syntax.parse_from_string Parser.proofoptsemi (s, dummy_ext)
      with e ->
	Lexer.in_proof := false;
	raise e
    in
    Lexer.in_proof := false;
    let rec run_commands state = function
      | [] -> state
      | c1:: rest ->
	  let state' = interpret_command_forget true state c1 in
	  run_commands state' rest
    in
    let state' =
      try
	run_commands state commands
      with (End state' | EndSuccess state') as e ->
	add_command state state' s commands;
	raise e
    in
    add_command state state' s commands;
    interactive_loop state'
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
  if !Settings.command_output <> "" then
    begin
      let fname = prepare_filename (!Settings.command_output) dummy_ext in
      try
	command_out_file := Some (open_out fname)
      with Sys_error s ->
	Parsing_helper.user_error ("Cannot open file " ^ fname ^ ": " ^ s)
    end;
  let r =
    try
      match proof with
	Some pr -> execute_proofinfo pr (initial_expand_simplify_success state)
      | None ->
	  if !Settings.interactive_mode then
	    interactive_loop (initial_expand_simplify_success state)
	  else
	    begin
	      execute_any_crypto state;
	      CFailure []
	    end
    with EndSuccess s -> CSuccess s
  in
  begin
    match r with
      CSuccess state' ->
	print_string "===================== Proof starts =======================\n";
	display_state true state'
    | CFailure _ -> ()
  end;
  if (!Settings.tex_output) <> "" then
    Displaytex.stop();
  final_out_commands()

