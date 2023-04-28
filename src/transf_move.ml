open Types

(* Move new and let: 
   (1) when a restriction has several uses under different
   branches of if/find, move it down under if/find.  It will be later
   SA renamed, which can allow to distinguish cases easily.
   (2) when a variable defined by let has no array reference and is used only in
   one branch of a if/let/find, we move it under the if/let/find to reduce
   the number of cases in which it is computed.
  *)

let whole_game = ref Terms.empty_game

let done_transfos = ref []

let beneficial = ref false

let rec move_a_binder put_process b p =
  Terms.iproc_from_desc (
  match p.i_desc with 
    Nil -> 
      Settings.changed := true;
      Nil
  | Par(p1,p2) ->
      let r1 = Terms.refers_to_process b p1 in
      let r2 = Terms.refers_to_process b p2 in
      if r1 && r2 then
	raise Not_found
      else 
	begin
	  Settings.changed := true;
	  if r1 then
	    Par(move_a_binder put_process b p1,p2)
	  else if r2 then
	    Par(p1, move_a_binder put_process b p2)
	  else
	    Par(p1,p2)
	end
  | Repl(b',p) -> raise Not_found
  | Input((c,tl), pat, p) ->
      if (List.exists (Terms.refers_to b) tl) || (Terms.refers_to_pat b pat) then
	raise Not_found
      else
	Input((c,tl), pat, move_a_bindero put_process false b p))

and move_a_bindero put_process array_ref b p = 
  Terms.oproc_from_desc (
  match p.p_desc with
    Yield -> 
      if array_ref then
	put_process Yield
      else
	Yield
  | EventAbort f -> EventAbort f
  | Restr(b',p) -> 
      Settings.changed := true;
      Restr(b', move_a_bindero put_process array_ref b p)
  | Test(t,p1,p2) ->
      if Terms.refers_to b t then
	put_process (Test(t,p1,p2))
      else
	begin
	  Settings.changed:= true;
	  beneficial := true;
	  Test(t, move_a_bindero put_process array_ref b p1, move_a_bindero put_process array_ref b p2)
	end
  | Find(l0,p,find_info) ->
      if List.exists (fun (bl, def_list, t, _) ->
	(List.exists (Terms.refers_to_br b) def_list) ||
	Terms.refers_to b t) l0 then
	put_process (Find(l0,p,find_info))
      else
	begin
	  Settings.changed := true;
	  beneficial := true;
	  Find(List.map (fun (bl, def_list, t, p1) ->
	    (bl, def_list, t, 
	     move_a_bindero put_process array_ref b p1)) l0,
	       move_a_bindero put_process array_ref b p, find_info)
	end
  | Output((c,tl),t2,p) ->
      if (List.exists (Terms.refers_to b) tl) || (Terms.refers_to b t2) || array_ref then
	put_process (Output((c,tl),t2,p))
      else
	begin
	  try
	    let p' = move_a_binder put_process b p in
	    Settings.changed := true;
	    Output((c,tl), t2, p')
	  with Not_found ->
	    put_process (Output((c,tl),t2,p))
	end
  | Let(pat, t, p1, p2) ->
      if (Terms.refers_to b t) || (Terms.refers_to_pat b pat) then
	put_process (Let(pat, t, p1, p2))
      else
	begin
	  Settings.changed := true;
	  match pat with
	    PatVar _ -> 
	      Let(pat, t, move_a_bindero put_process array_ref b p1, Terms.oproc_from_desc Yield)
	  | _ -> 
	      beneficial := true;
	      Let(pat, t, move_a_bindero put_process array_ref b p1, 
		  move_a_bindero put_process array_ref b p2)
	end
  | EventP(t,p) ->
      if Terms.refers_to b t then
	put_process (EventP(t,p))
      else
	begin
	  Settings.changed := true;
	  EventP(t, move_a_bindero put_process array_ref b p)
	end
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"
  )

let rec move_a_let (b,t0) p = 
  Terms.iproc_from_desc (
  match p.i_desc with
    Nil -> 
      Settings.changed := true;
      Nil
  | Par(p1,p2) ->
      let r1 = Terms.refers_to_process b p1 in
      let r2 = Terms.refers_to_process b p2 in
      if r1 && r2 then
	raise Not_found
      else 
	begin
	  Settings.changed := true;
	  if r1 then
	    Par(move_a_let (b,t0) p1,p2)
	  else if r2 then
	    Par(p1, move_a_let (b,t0) p2)
	  else
	    Par(p1,p2)
	end
  | Repl(b',p) -> raise Not_found
  | Input((c,tl), pat, p) ->
      if (List.exists (Terms.refers_to b) tl) || (Terms.refers_to_pat b pat) then
	raise Not_found
      else
	Input((c,tl), pat, move_a_leto (b,t0) p)
  )

and move_a_leto (b,t0) p =
  Terms.oproc_from_desc (
  match p.p_desc with
    Yield -> Yield
  | EventAbort f -> EventAbort f
  | Restr(b',p) -> 
      Settings.changed := true;
      Restr(b', move_a_leto (b,t0) p)
  | Test(t,p1,p2) ->
      let r1 = Terms.refers_to_oprocess b p1 in
      let r2 = Terms.refers_to_oprocess b p2 in
      if (Terms.refers_to b t) || (r1 && r2) then
	Let(PatVar b, t0, Terms.oproc_from_desc (Test(t,p1,p2)), Terms.oproc_from_desc Yield)
      else
	begin
	  Settings.changed:= true;
	  beneficial := true;
	  Test(t, (if r1 then move_a_leto (b,t0) p1 else p1), 
	          (if r2 then move_a_leto (b,t0) p2 else p2))
	end
  | Find(l0,p,find_info) ->
      let rl = List.map (fun (bl, def_list, t, p1) ->
	Terms.refers_to_oprocess b p1) l0
      in
      let r2 = Terms.refers_to_oprocess b p in
      let count_ref = ref 0 in
      List.iter (fun b -> if b then incr count_ref) rl;
      if r2 then incr count_ref;
      if List.exists (fun (bl, def_list, t, _) ->
	(List.exists (Terms.refers_to_br b) def_list) ||
	Terms.refers_to b t) l0 || (!count_ref) > 1 then
	Let(PatVar b, t0, Terms.oproc_from_desc (Find(l0,p,find_info)), Terms.oproc_from_desc Yield)
      else
	begin
	  Settings.changed := true;
	  beneficial := true;
	  Find(List.map2 (fun (bl, def_list, t, p1) r1 ->
	    (bl, def_list, t, 
	     if r1 then move_a_leto (b,t0) p1 else p1)) l0 rl,
	       (if r2 then move_a_leto (b,t0) p else p), find_info)
	end
  | Output((c,tl),t2,p) ->
      if (List.exists (Terms.refers_to b) tl) || (Terms.refers_to b t2) then
	Let(PatVar b, t0, Terms.oproc_from_desc (Output((c,tl),t2,p)), Terms.oproc_from_desc Yield)
      else
	begin
	  try
	    let p' = move_a_let (b,t0) p in
	    Settings.changed := true;
	    Output((c,tl), t2, p')
	  with Not_found ->
	    Let(PatVar b, t0, Terms.oproc_from_desc (Output((c,tl),t2,p)), Terms.oproc_from_desc Yield)
	end
  | Let(pat, t, p1, p2) ->
      let r1 = Terms.refers_to_oprocess b p1 in
      let r2 = Terms.refers_to_oprocess b p2 in
      if (Terms.refers_to b t) || (Terms.refers_to_pat b pat) || (r1 && r2) then
	Let(PatVar b, t0, Terms.oproc_from_desc (Let(pat, t, p1, p2)), Terms.oproc_from_desc Yield)
      else
	begin
	  Settings.changed := true;
	  match pat with
	    PatVar _ -> 
	      Let(pat, t, (if r1 then move_a_leto (b,t0) p1 else p1), Terms.oproc_from_desc Yield)
	  | _ -> 
	      beneficial := true;
	      Let(pat, t, (if r1 then move_a_leto (b,t0) p1 else p1), 
		  (if r2 then move_a_leto (b,t0) p2 else p2))
	end
  | EventP(t,p) ->
      if Terms.refers_to b t then
	Let(PatVar b, t0, Terms.oproc_from_desc (EventP(t,p)), Terms.oproc_from_desc Yield)
      else
	begin
	  Settings.changed := true;
	  EventP(t, move_a_leto (b,t0) p)
	end
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"
  )


let do_move_new move_set array_ref b =
  match move_set with
    MAll | MNew -> true
  | MNoArrayRef | MNewNoArrayRef -> not array_ref
  | MLet -> false
  | MBinders l -> List.memq b l
  | MUp _ -> assert false

(* The result of do_move_let can be:
   0: do not move
   1: move but do not duplicate the let binding;
      this case happens only when b has no array accesses. 
   2: move, perhaps duplicating the let binding. *)

let do_move_let move_set array_ref b t =
  match move_set with
    MAll | MLet | MNoArrayRef -> 
      begin
	match t.t_desc with
	  FunApp(_,[]) -> 2 (* t is a constant; we allow duplicating its evaluation *)
	| _ -> if array_ref then 0 else 1
	(* Lets are moved only when there are no array references.
	   Moving them is interesting only when it reduces the cases in
           which the value is computed, which can never be done when there
	   are array references. *)
      end
  | MNew | MNewNoArrayRef -> 0
  | MBinders l -> if List.memq b l then 2 else 0
      (* When the user instructs the move on the binder b, we perform
	 the move even if b has array references and/or we duplicate the let. *)
  | MUp _ -> assert false
      
let rec move_new_let_rec move_set p =
  Terms.iproc_from_desc (
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) -> Par(move_new_let_rec move_set p1,
		      move_new_let_rec move_set p2)
  | Repl(b,p) -> Repl(b,move_new_let_rec move_set p)
  | Input(t, pat, p) ->
      Input(t, pat, move_new_let_reco move_set p))

and move_new_let_reco move_set p =
  match p.p_desc with
    Yield -> Terms.oproc_from_desc Yield
  | EventAbort f -> Terms.oproc_from_desc (EventAbort f)
  | Restr(b,p) ->
      let array_ref = Array_ref.has_array_ref_q b (!whole_game).current_queries in
      if (not (do_move_new move_set array_ref b)) then
	Terms.oproc_from_desc (Restr(b, move_new_let_reco move_set p))
      else
	let p' = move_new_let_reco move_set p in
	let tmp_changed = !Settings.changed in
	Settings.changed := false;
	beneficial := false;
	let p'' = move_a_bindero (fun p_desc -> Restr(b, Terms.oproc_from_desc p_desc)) array_ref b p' in
	if (!beneficial) || (match move_set with MBinders _ -> true | _ -> false) then
	  begin
	    Settings.changed := (!Settings.changed) || tmp_changed;
	    done_transfos := (DMoveNew b) :: (!done_transfos);
	    p''
	  end
	else
	  begin
	    (* Don't do a move all/noarrayref if it is not beneficial *)
	    Settings.changed := tmp_changed;
	    Terms.oproc_from_desc (Restr(b, p'))
	  end
  | Test(t,p1,p2) -> 
      Terms.oproc_from_desc 
	(Test(t, move_new_let_reco move_set p1,
	      move_new_let_reco move_set p2))
  | Find(l0,p,find_info) ->
      Terms.oproc_from_desc 
	(Find(List.map (fun (bl,def_list,t,p1) ->
	  (bl, def_list, t, move_new_let_reco move_set p1)) l0,
	   move_new_let_reco move_set p, find_info))
  | Output(t1,t2,p) ->
      Terms.oproc_from_desc (Output(t1,t2,move_new_let_rec move_set p))
  | Let(pat,t,p1,p2) ->
      begin
	match pat with
	  PatVar b ->
	    let array_ref = Array_ref.has_array_ref_q b (!whole_game).current_queries in
	    let move_decision = do_move_let move_set array_ref b t in
	    if move_decision = 0 then
	      begin
		(* Do not move *)
		Terms.oproc_from_desc 
		  (Let(pat,t,move_new_let_reco move_set p1,
		       move_new_let_reco move_set p2))
	      end
	    else
	      begin
		let p1' = move_new_let_reco move_set p1 in
		let tmp_changed = !Settings.changed in
		Settings.changed := false;
		beneficial := false;
		let p1'' = 
		  if move_decision = 1 then 
		    (* Move the let, trying to evaluate it less often.
		       We never do that when b has array references.
		       In this case, the let binding is never duplicated. *)
		    move_a_leto (b,t) p1' 
		  else
		    (* Move the let, even if b has array references.
		       In this case, the let binding may be duplicated. *)
		    move_a_bindero (fun p_desc -> 
		      Let(pat, t, Terms.oproc_from_desc p_desc, Terms.oproc_from_desc Yield)) array_ref b p1'
		in
		if (!beneficial) || (match move_set with MBinders _ -> true | _ -> false) then
		  begin
		    Settings.changed := (!Settings.changed) || tmp_changed;
		       done_transfos := (DMoveLet b) :: (!done_transfos);
		       p1''
		  end
		else
		  begin
	        (* Don't do a move all/noarrayref if it is not beneficial *)
		    Settings.changed := tmp_changed;
		    Terms.oproc_from_desc (Let(pat, t, p1', Terms.oproc_from_desc Yield))
		  end
	      end
	| _ -> 
	    Terms.oproc_from_desc 
	      (Let(pat,t,move_new_let_reco move_set p1,
		move_new_let_reco move_set p2))
      end
  | EventP(t,p) ->
      Terms.oproc_from_desc (EventP(t, move_new_let_reco move_set p))
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

let move_down move_set g =
  (* The transformation "move" supports non-expanded games,
     but will move only new and let that occur at the process level *)
  let g_proc = Terms.get_process g in
  whole_game := g;
  done_transfos := [];
  Array_ref.array_ref_process g_proc;
  let r = move_new_let_rec move_set g_proc in
  Array_ref.cleanup_array_ref();
  let transfos = !done_transfos in
  done_transfos := [];
  whole_game := Terms.empty_game;
  (Terms.build_transformed_game r g, [], transfos)



(** [move_up bl occ ext] moves upwards variables [bl]
    defined by [let] or [new] to occurrence [occ].
    [occ] must be a process occurrence *)

(* [find_bl_* bl new_b ext p] returns
   - the list of definitions of variables in [bl] inside [p],
   of the form (b, definition of b)
   - a version [p'] of [p] in which these definitions are 
   replaced with [let b = new_b in] or removed in case [b] is [new_b] 
   It is an error in case a variable in [bl] is defined by 
   other definition than [new b] or [let b = ...],
   or if several variables of [bl] are simultaneously defined. *)

type possible_def =
  | DefNew of program_point
  | DefLet of term

let combine_simultaneous dl1 dl2 ext =
  if dl1 = [] then dl2 else
  if dl2 = [] then dl1 else
  let dl1string = String.concat ", " (List.map (fun (b1, _) -> Display.binder_to_string b1) dl1) in
  let dl2string = String.concat ", " (List.map (fun (b1, _) -> Display.binder_to_string b1) dl2) in
  raise (Parsing_helper.Error("Variables "^dl1string^" on the one hand and "^dl2string^" on the other hand may be simultaneously defined", ext))
	
let rec find_bl_t bl new_b ext t =
  match t.t_desc with
  | Var(b,l) ->
      let (dl, l') = find_bl_tl bl new_b ext l in
      (dl, Terms.build_term2 t (Var(b,l')))
  | FunApp(f,l) ->
      let (dl, l') = find_bl_tl bl new_b ext l in
      (dl, Terms.build_term2 t (FunApp(f,l')))
  | ReplIndex _ | EventAbortE _ -> [], t
  | TestE(t1, t2, t3) ->
      let (dl1, t1') = find_bl_t bl new_b ext t1 in
      let (dl2, t2') = find_bl_t bl new_b ext t2 in
      let (dl3, t3') = find_bl_t bl new_b ext t3 in
      (combine_simultaneous dl1 (dl2 @ dl3) ext,
       Terms.build_term2 t (TestE(t1', t2', t3')))
  | FindE(l0,t3,find_info) ->
      let (dl3, t3') = find_bl_t bl new_b ext t3 in
      let accu_dl_branch = ref dl3 in
      let accu_dl_cond = ref [] in
      let l0' = List.map (fun (bl0, def_list, t1, t2) ->
	List.iter (fun (b,_) ->
	  if List.memq b bl then
	    raise (Parsing_helper.Error("Variable "^(Display.binder_to_string b)^" is defined by a find. Only variables defined by random number generations and assignments can be moved up", ext))
	  ) bl0;
	let (dl1, t1') = find_bl_t bl new_b ext t1 in
	let (dl2, t2') = find_bl_t bl new_b ext t2 in
	accu_dl_branch := dl2 @ (!accu_dl_branch);
	accu_dl_cond := combine_simultaneous dl1 (!accu_dl_cond) ext;
	(* def_list cannot contain definitions of variables *)
	(bl0, def_list, t1', t2')
	  ) l0
      in
      (combine_simultaneous (!accu_dl_cond) (!accu_dl_branch) ext,
       Terms.build_term2 t (FindE(l0',t3',find_info)))
  | ResE(b,t1) ->
      let (dl,t1') = find_bl_t bl new_b ext t1 in
      if List.memq b bl then
	begin
	  let dl' = combine_simultaneous [b, DefNew (DTerm t)] dl ext in
	  if b == new_b then
	    (dl', t1')
	  else
	    (dl', Terms.build_term2 t (LetE(PatVar b, Terms.term_from_binder new_b, t1', None)))
	end
      else
	(dl, Terms.build_term2 t (ResE(b,t1')))
  | LetE (PatVar b, t1, t2, _) ->
      let (dl1, t1') = find_bl_t bl new_b ext t1 in
      let (dl2, t2') = find_bl_t bl new_b ext t2 in
      if List.memq b bl then
	begin
	  let dl' = combine_simultaneous [b, DefLet t1'] (combine_simultaneous dl1 dl2 ext) ext in
	  if b == new_b then
	    (dl', t2')
	  else
	    (dl', Terms.build_term2 t (LetE(PatVar b, Terms.term_from_binder new_b, t2', None)))
	end
      else
	(combine_simultaneous dl1 dl2 ext,
	 Terms.build_term2 t (LetE(PatVar b, t1', t2', None)))
  | LetE(pat, t1, t2, topt) ->
      let (dlpat, pat') = find_bl_pat bl new_b ext pat in
      let (dl1, t1') = find_bl_t bl new_b ext t1 in
      let (dl2, t2') = find_bl_t bl new_b ext t2 in
      let (dlopt, topt') =
	match topt with
	| None -> [], None
	| Some t3 ->
	    let (dl3,t3') = find_bl_t bl new_b ext t3 in
	    (dl3, Some t3')
      in
      (combine_simultaneous dlpat (combine_simultaneous dl1 (dl2 @ dlopt) ext) ext,
       Terms.build_term2 t (LetE(pat', t1', t2', topt')))
  | EventE(t1,t2) ->
      let (dl1, t1') = find_bl_t bl new_b ext t1 in
      let (dl2, t2') = find_bl_t bl new_b ext t2 in
      (combine_simultaneous dl1 dl2 ext, Terms.build_term2 t (EventE(t1', t2')))
  | GetE _ | InsertE _ -> assert false

and find_bl_tl bl new_b ext = function
  | [] -> [], []
  | a::l ->
      let (dl1,a') = find_bl_t bl new_b ext a in
      let (dl2,l') = find_bl_tl bl new_b ext l in
      (combine_simultaneous dl1 dl2 ext, a'::l')

and find_bl_pat bl new_b ext = function
  | PatVar b ->
      if List.memq b bl then
	raise (Parsing_helper.Error("Variable "^(Display.binder_to_string b)^" is defined by a let with pattern-matching or an "^(if !Settings.front_end = Oracles then "oracle definition" else "input")^". Only variables defined by random number generations and assignments can be moved up", ext));
      [], PatVar b
  | PatTuple(f,l) ->
      let (dl, l') = find_bl_patl bl new_b ext l in
      (dl, PatTuple(f,l'))
  | PatEqual t ->
      let (dl,t') = find_bl_t bl new_b ext t in
      (dl, PatEqual t')

and find_bl_patl bl new_b ext = function
  | [] -> [],[]
  | a::l ->
      let (dl1,a') = find_bl_pat bl new_b ext a in
      let (dl2,l') = find_bl_patl bl new_b ext l in
      (combine_simultaneous dl1 dl2 ext, a'::l')

let rec find_bl_i bl new_b ext p =
  match p.i_desc with
  | Nil -> ([], p)
  | Par(p1,p2) ->
      let (dl1, p1') = find_bl_i bl new_b ext p1 in
      let (dl2, p2') = find_bl_i bl new_b ext p2 in
      (combine_simultaneous dl1 dl2 ext, Terms.iproc_from_desc_at p (Par(p1',p2')))
  | Repl(i,p1) ->
      let (dl1, p1') = find_bl_i bl new_b ext p1 in
      (dl1, Terms.iproc_from_desc_at p (Repl(i,p1')))
  | Input((c,tl), pat, p1) ->
      let (dl, tl') = find_bl_tl bl new_b ext tl in
      let (dlpat, pat') = find_bl_pat bl new_b ext pat in
      let (dlp, p') = find_bl_o bl new_b ext p1 in
      (combine_simultaneous dl (combine_simultaneous dlpat dlp ext) ext,
       Terms.iproc_from_desc_at p (Input((c,tl'),pat', p')))

and find_bl_o bl new_b ext p =
  match p.p_desc with
  | Yield | EventAbort _ -> ([], p)
  | Restr(b,p1) ->
      let (dl,p1') = find_bl_o bl new_b ext p1 in
      if List.memq b bl then
	begin
	  let dl' = combine_simultaneous [b, DefNew (DProcess p)] dl ext in
	  if b == new_b then
	    (dl', p1')
	  else
	    (dl', Terms.oproc_from_desc_at p (Let(PatVar b, Terms.term_from_binder new_b, p1', Terms.oproc_from_desc Yield)))
	end
      else
	(dl, Terms.oproc_from_desc_at p (Restr(b,p1')))
  | Test(t1, p2, p3) ->
      let (dl1, t1') = find_bl_t bl new_b ext t1 in
      let (dl2, p2') = find_bl_o bl new_b ext p2 in
      let (dl3, p3') = find_bl_o bl new_b ext p3 in
      (combine_simultaneous dl1 (dl2 @ dl3) ext,
       Terms.oproc_from_desc_at p (Test(t1', p2', p3')))
  | Find(l0,p3,find_info) ->
      let (dl3, p3') = find_bl_o bl new_b ext p3 in
      let accu_dl_branch = ref dl3 in
      let accu_dl_cond = ref [] in
      let l0' = List.map (fun (bl0, def_list, t1, p2) ->
	List.iter (fun (b,_) ->
	  if List.memq b bl then
	    raise (Parsing_helper.Error("Variable "^(Display.binder_to_string b)^" is defined by a find. Only variables defined by random number generations and assignments can be moved up", ext))
	  ) bl0;
	let (dl1, t1') = find_bl_t bl new_b ext t1 in
	let (dl2, p2') = find_bl_o bl new_b ext p2 in
	accu_dl_branch := dl2 @ (!accu_dl_branch);
	accu_dl_cond := combine_simultaneous dl1 (!accu_dl_cond) ext;
	(* def_list cannot contain definitions of variables *)
	(bl0, def_list, t1', p2')
	  ) l0
      in
      (combine_simultaneous (!accu_dl_cond) (!accu_dl_branch) ext,
       Terms.oproc_from_desc_at p (Find(l0',p3',find_info)))
  | Let (PatVar b, t1, p2, _) ->
      let (dl1, t1') = find_bl_t bl new_b ext t1 in
      let (dl2, p2') = find_bl_o bl new_b ext p2 in
      if List.memq b bl then
	begin
	  let dl' = combine_simultaneous [b, DefLet t1'] (combine_simultaneous dl1 dl2 ext) ext in
	  if b == new_b then
	    (dl', p2')
	  else
	    (dl', Terms.oproc_from_desc_at p (Let(PatVar b, Terms.term_from_binder new_b, p2', Terms.oproc_from_desc Yield)))
	end
      else
	(combine_simultaneous dl1 dl2 ext,
	 Terms.oproc_from_desc_at p (Let(PatVar b, t1', p2', Terms.oproc_from_desc Yield)))
  | Let(pat, t1, p2, p3) ->
      let (dlpat, pat') = find_bl_pat bl new_b ext pat in
      let (dl1, t1') = find_bl_t bl new_b ext t1 in
      let (dl2, p2') = find_bl_o bl new_b ext p2 in
      let (dl3, p3') = find_bl_o bl new_b ext p3 in
      (combine_simultaneous dlpat (combine_simultaneous dl1 (dl2 @ dl3) ext) ext,
       Terms.oproc_from_desc_at p (Let(pat', t1', p2', p3')))
  | EventP(t1,p2) ->
      let (dl1, t1') = find_bl_t bl new_b ext t1 in
      let (dl2, p2') = find_bl_o bl new_b ext p2 in
      (combine_simultaneous dl1 dl2 ext, Terms.oproc_from_desc_at p (EventP(t1', p2')))
  | Output((c,tl),t1,p2) ->
      let (dl, tl') = find_bl_tl bl new_b ext tl in
      let (dl1, t1') = find_bl_t bl new_b ext t1 in
      let (dl2, p2') = find_bl_i bl new_b ext p2 in
      (combine_simultaneous dl (combine_simultaneous dl1 dl2 ext) ext,
       Terms.oproc_from_desc_at p (Output((c,tl'),t1', p2')))      
  | Insert _ | Get _ -> assert false


type state_t =
    { bl : binder list;
      occ : int;
      ext : Parsing_helper.extent;
      queries : cur_queries_t;
      cur_array : repl_index list;
      found : bool ref;
      assign_up : bool ref }
	
let error_def state b =
  if List.memq b state.bl then
    raise (Parsing_helper.Error("Variable "^(Display.binder_to_string b)^" is defined above occurrence "^(string_of_int state.occ), state.ext))
    
let rec iter_def_t iter_def t =
  begin
    match t.t_desc with
    | FindE(l0,_,_) ->
	List.iter (fun (bl0,_,_,_) ->
	  List.iter (fun (b,_) ->
	    iter_def b
		    ) bl0
		  ) l0
    | ResE(b,_) ->
	iter_def b
    | _ -> ()
  end;
  Terms.iter_subterm (iter_def_t iter_def) (fun _ -> ()) (iter_def_pat iter_def) t

and iter_def_pat iter_def pat =
  let patvars = Terms.vars_from_pat [] pat in
  List.iter iter_def patvars;
  Terms.iter_subpat (iter_def_t iter_def) (iter_def_pat iter_def) pat

(* [check_same_kind ext (b1,k1) (b2,k2)] checks that [b1] and [b2] are defined 
   either both by random number generations or both by assignments *)

let error_new_let ext b1 b2 =
  let msg =
    if b1 == b2 then
      "Variable "^(Display.binder_to_string b1)^" is defined both by a random number generation and by an assignment"
    else
      "Variable "^(Display.binder_to_string b1)^" is defined by a random number generation and variable "^(Display.binder_to_string b2)^" is defined by an assignment"
  in
  raise (Parsing_helper.Error(msg,ext))

let check_same_kind ext (b1,k1) (b2,k2) =
  match k1,k2 with
  | DefNew _, DefNew _
  | DefLet _, DefLet _ -> ()
  | DefNew _, DefLet _ ->
      error_new_let ext b1 b2
  | DefLet _, DefNew _ ->
      error_new_let ext b2 b1

(* [check_once state (b,d)] checks that the definition of [b] at [d] is
   executed at most once. [b] must be defined by a random number generation. *)

let check_once state (b,d) =
  match d with
  | DefLet _ -> assert false
  | DefNew pp ->
      if Terms.equal_lists (==) state.cur_array b.args_at_creation then () else
      (* [state.cur_array] must be a suffix [b.args_at_creation],
	  since [b] is defined under [occ] *)
      let (add_indices, copy_cur_array) = Terms.split (List.length b.args_at_creation - List.length state.cur_array) b.args_at_creation in
      assert (Terms.equal_lists (==) state.cur_array copy_cur_array);
      try
	let (facts,_,_,_) = Facts.get_facts_at pp in
	let simp_facts = Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) facts in
	let nsimpfacts = Facts.true_facts_from_simp_facts simp_facts in 
	let diff_fact = Terms.make_or_list (List.map (fun ri ->
	  let ri_term = Terms.term_from_repl_index ri in
	  let ri_term' = Terms.term_from_repl_index (Terms.new_repl_index ri) in
	  ri.ri_link <- TLink ri_term';
	  Terms.make_diff ri_term ri_term'
						     ) add_indices)
	in
	let facts_other_indices = List.map (Terms.copy_term Terms.Links_RI) nsimpfacts in
	List.iter (fun ri -> ri.ri_link <- NoLink) add_indices;
	let _ = Facts.simplif_add_list Facts.no_dependency_anal simp_facts (diff_fact::facts_other_indices) in
	raise (Parsing_helper.Error("I could not prove that the definition of "^(Display.binder_to_string b)^" at occurrence "^(string_of_int (Terms.occ_from_pp pp))^" is executed at most once for each execution of occurrence "^(string_of_int state.occ)^".", state.ext))
      with Contradiction ->
	(* OK: the definition can be executed at most once *)
	()	

(* [make_simple ext t] transforms [t] into a simple term, when possible *)

let rec make_simple ext t =
  match t.t_desc with
  | Var(b,l) ->
      Terms.build_term2 t (Var(b, List.map (make_simple ext) l))
  | FunApp(f,l) ->
      Terms.build_term2 t (FunApp(f, List.map (make_simple ext) l))
  | ReplIndex _ -> t
  | TestE(t1,t2,t3) ->
      let f = Settings.get_if_fun t2.t_type in
      Terms.build_term2 t (FunApp(f, List.map (make_simple ext) [t1;t2;t3]))
  | LetE _ | FindE _ | ResE _ | EventE _ | EventAbortE _ ->
      raise (Parsing_helper.Error("In move up, assigned terms should contain only variables, function applications, and tests. This is not true for the term at occurrence "^(string_of_int t.t_occ), ext))
  | GetE _ | InsertE _ -> assert false

(* [is_defined cur_array def_vars t] returns true when [t] is defined,
   knowing that the variables in [def_vars] and the 
   replication indices [cur_array] are defined. *)
	
let rec is_defined cur_array def_vars t =
  match t.t_desc with
  | Var(b,l) ->
      Terms.mem_binderref (b,l) def_vars
  | FunApp(f,l) ->
      List.for_all (is_defined cur_array def_vars) l
  | ReplIndex i -> List.memq i cur_array
  | _ -> assert false

	
(* [move_up_rec_* bl occ ext p] returns the modified process [p']
   with definitions of [bl] under [occ] moved to [occ].
   [occ] must be an output process/oracle body occurrence.
   It checks that no variable of [bl] is defined syntactically above [occ].
   It collects the definitions of [bl] under [occ] by [find_bl_o]. *)
	
let rec move_up_rec_i state p =
  if state.occ = p.i_occ then
    raise (Parsing_helper.Error("Occurrence "^(string_of_int state.occ)^" must be the occurrence of "^(if !Settings.front_end = Oracles then "an oracle body" else "an output process"), state.ext));
  if state.occ < p.i_occ || state.occ > p.i_max_occ then p else 
  match p.i_desc with
  | Nil -> p
  | Par(p1,p2) ->
      Terms.iproc_from_desc_at p (Par(move_up_rec_i state p1, move_up_rec_i state p2))
  | Repl(i,p1) ->
      Terms.iproc_from_desc_at p (Repl(i,move_up_rec_i { state with cur_array = i :: state.cur_array } p1))
  | Input((c,tl),pat,p1) ->
      List.iter (iter_def_t (error_def state)) tl;
      iter_def_pat (error_def state) pat;
      Terms.iproc_from_desc_at p (Input((c,tl),pat,move_up_rec_o state p1))

and move_up_rec_o state p =
   if state.occ < p.p_occ || state.occ > p.p_max_occ then p else 
   if state.occ = p.p_occ then
     begin
       (* Do the transformation *)
       state.found := true;
       let new_b =
	 try
	   (* We can reuse as new variable at [occ] a variable of [bl]
	      when it has the same replication indices at creation and 
	      it has no array accesses (because its definition will move) *)
	   List.find (fun b ->
	     Terms.equal_lists (==) b.args_at_creation state.cur_array &&
	     not (Array_ref.has_array_ref_q b state.queries)) state.bl
	 with Not_found ->
	   (* [bl] cannot be the empty list (by construction of the command) *)
	   let b0 = List.hd state.bl in
	   Terms.create_binder b0.sname b0.btype state.cur_array
       in
       let (dl,p') = find_bl_o state.bl new_b state.ext p in
       match dl with
       | [] ->
	   let blstring = String.concat ", " (List.map Display.binder_to_string state.bl) in
	   raise (Parsing_helper.Error("No variable of "^blstring^" is defined under occurrence "^(string_of_int state.occ), state.ext))
       | d0::drest ->
	   List.iter (check_same_kind state.ext d0) drest;
	   match d0 with
	   | (_, DefNew _) ->
	       (* We are moving random number generations up *)
	       (* Check that the definitions are executed at most once *)
	       List.iter (check_once state) dl;
	       Settings.changed := true;
	       done_transfos := [DMoveNewUp(state.bl, state.occ, new_b)];
	       Terms.oproc_from_desc_at p (Restr(new_b, p'))
	   | (_, DefLet _) ->
	       (* We are moving assignments up *)
	       state.assign_up := true;
	       (* Check that terms are copiable (that is, they consist of variables,
                  function applications, and tests) *)
	       let dl' = List.map (function
		 | (_, DefNew _) -> assert false
		 | (b, DefLet t) -> (b, t, make_simple state.ext t)
				  ) dl
	       in
	       (* Check that the term we are going to use is defined at [occ] *)
	       let (_,def_vars,_) =
		 try
		   Facts.get_def_vars_at (DProcess p)
		 with Contradiction ->
		   raise (Parsing_helper.Error("The program point at "^(string_of_int state.occ)^" is in fact unreachable. Just simplify the game to remove it.", state.ext))
	       in
	       let (_,candidate_term,candidate_term_simp) =
		 try
		   List.find (fun (_,_,tsimp) ->
		     is_defined state.cur_array def_vars tsimp
			     ) dl'
		 with Not_found ->
		   let blstring = String.concat ", " (List.map Display.binder_to_string state.bl) in
		   raise (Parsing_helper.Error("None of the terms that define variable(s) in "^blstring^" is defined at occurrence "^(string_of_int state.occ), state.ext))
	       in
	       (* Check that all definitions of variables in [bl] are equal *)
	       List.iter (fun (_,t,tsimp') ->
		 if candidate_term_simp == tsimp' then () else
		 try 
		   let (facts,_,_,_) = Facts.get_facts_at (DTerm t) in
		   let simp_facts = Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) facts in
		   if not (Terms.simp_equal_terms simp_facts true candidate_term_simp tsimp') then
		     let blstring = String.concat ", " (List.map Display.binder_to_string state.bl) in
		     let candidate_term_string = Display.string_out (fun () -> Display.display_term candidate_term) in
		     let t_string = Display.string_out (fun () -> Display.display_term t) in
		     raise (Parsing_helper.Error("I could not prove that all terms that define variables in "^blstring^" are equal: "^candidate_term_string^" may be different from "^t_string, state.ext))
		 with Contradiction ->
		   (* Term [t] is in fact unreachable *)
		   ()
			 ) dl';

	       Settings.changed := true;
	       done_transfos := [DMoveLetUp(state.bl, state.occ, new_b)];
	       Terms.oproc_from_desc_at p (Let(PatVar new_b, candidate_term, p', Terms.oproc_from_desc Yield))
     end
   else
     match p.p_desc with
     | Yield | EventAbort _ -> p
     | Restr(b,p1) ->
	 error_def state b;
	 Terms.oproc_from_desc_at p (Restr(b,move_up_rec_o state p1))
     | Test(t,p1,p2) ->
	 iter_def_t (error_def state) t;
	 Terms.oproc_from_desc_at p (Test(t,move_up_rec_o state p1,move_up_rec_o state p2))
     | Find(l0,p2, find_info) ->
	 begin
	   try
	     let def_vars_info = Facts.get_def_vars_at (DProcess p) in
	     let p2' = move_up_rec_o state p2 in
	     let l0' = List.fold_right (fun (bl,def_list,t,p1) laccu ->
	       List.iter (fun (b,_) -> error_def state b) bl;
	       iter_def_t (error_def state) t;
	       let p1' = move_up_rec_o state p1 in
	       if !(state.assign_up) then
		 try
		   (* fix [def_list] if needed when we moved an assignment up *)
		   (Facts.update_def_list_process def_vars_info None bl def_list t p1')::laccu
		 with Contradiction ->
	           (* The variables in the defined condition cannot be defined,
		      I can just remove the branch *)
		   laccu
	       else
		 (bl,def_list,t,move_up_rec_o state p1) :: laccu
				       ) l0 []
	     in
	     Terms.oproc_from_desc_at p (Find(l0',p2',find_info))
	   with Contradiction ->
	     (* The process is in fact unreachable *)
	     Terms.oproc_from_desc_at p Yield
	 end
     | Output((c,tl),t1,p2) ->
	 List.iter (iter_def_t (error_def state)) tl;
	 iter_def_t (error_def state) t1;
	 Terms.oproc_from_desc_at p (Output((c,tl),t1,move_up_rec_i state p2))
     | EventP(t1,p2) ->
	 iter_def_t (error_def state) t1;
	 Terms.oproc_from_desc_at p (EventP(t1,move_up_rec_o state p2))
     | Let(pat,t1,p2,p3) ->
	 iter_def_pat (error_def state) pat;
	 iter_def_t (error_def state) t1;
	 Terms.oproc_from_desc_at p (Let(pat,t1,move_up_rec_o state p2,move_up_rec_o state p3))
     | Insert _ | Get _ -> assert false
	
let move_up bl occ ext g =
  (* All variables of [bl] must have the same type *)
  begin
    match bl with
    | [] -> assert false
    | b::l ->
	List.iter (fun b' ->
	  if b.btype != b'.btype then
	    raise (Parsing_helper.Error("In move up, all variables must have the same type. The variable "^(Display.binder_to_string b)^" has type "^b.btype.tname^" but "^(Display.binder_to_string b')^" has type "^b'.btype.tname, ext))
		  ) l
  end;
  Depanal.reset [] g;      
  Improved_def.improved_def_game None false g;
  let g_proc = Terms.get_process g in
  Array_ref.array_ref_process g_proc;
  done_transfos := [];
  let cleanup() = 
    Improved_def.empty_improved_def_game false g;
    Array_ref.cleanup_array_ref();
    done_transfos := []
  in
  let state =
    { bl = bl;
      occ = occ;
      ext = ext;
      queries = g.current_queries;
      cur_array = [];
      found = ref false;
      assign_up = ref false }
  in
  try
    let p' =  move_up_rec_i state g_proc in
    if not (!(state.found)) then
      raise (Parsing_helper.Error("Occurrence "^(string_of_int occ)^" not found. Expected occurrence of "^(if !Settings.front_end = Oracles then "an oracle body" else "an output process"), ext));
    let proba = Depanal.final_add_proba() in
    let transfos = !done_transfos in
    cleanup();
    (Terms.build_transformed_game p' g, proba, transfos)
  with (Parsing_helper.Error _) as e ->
    cleanup();
    raise e
      
(** Dispatch between [move_up] and [move_down] *)
    
let move_new_let move_set g =
  match move_set with
  | MUp(bl,occ,ext) -> 
      move_up bl occ ext g
  | _ ->
      move_down move_set g
