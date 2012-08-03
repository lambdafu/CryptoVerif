open Types

(* Move new and let: 
   (1) when a restriction has several uses under different
   branches of if/find, move it down under if/find.  It will be later
   SA renamed, which can allow to distinguish cases easily.
   (2) when a variable defined by let has no array reference and is used only in
   one branch of a if/let/find, we move it under the if/let/find to reduce
   the number of cases in which it is computed.
  *)

let done_transfos = ref []

let beneficial = ref false

let rec move_a_new b p =
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
	    Par(move_a_new b p1,p2)
	  else if r2 then
	    Par(p1, move_a_new b p2)
	  else
	    Par(p1,p2)
	end
  | Repl(b',p) -> raise Not_found
  | Input((c,tl), pat, p) ->
      if (List.exists (Terms.refers_to b) tl) || (Terms.refers_to_pat b pat) then
	raise Not_found
      else
	Input((c,tl), pat, move_a_newo false b p))

and move_a_newo array_ref b p = 
  Terms.oproc_from_desc (
  match p.p_desc with
    Yield -> 
      if array_ref then
	Restr(b, Terms.yield_proc)
      else
	Yield
  | Abort -> Abort
  | Restr(b',p) -> 
      Settings.changed := true;
      Restr(b', move_a_newo array_ref b p)
  | Test(t,p1,p2) ->
      if Terms.refers_to b t then
	Restr(b, Terms.oproc_from_desc (Test(t,p1,p2)))
      else
	begin
	  Settings.changed:= true;
	  beneficial := true;
	  Test(t, move_a_newo array_ref b p1, move_a_newo array_ref b p2)
	end
  | Find(l0,p,find_info) ->
      if List.exists (fun (bl, def_list, t, _) ->
	(List.exists (Terms.refers_to_br b) def_list) ||
	Terms.refers_to b t) l0 then
	Restr(b, Terms.oproc_from_desc (Find(l0,p,find_info)))
      else
	begin
	  Settings.changed := true;
	  beneficial := true;
	  Find(List.map (fun (bl, def_list, t, p1) ->
	    (bl, def_list, t, 
	     move_a_newo array_ref b p1)) l0,
	       move_a_newo array_ref b p, find_info)
	end
  | Output((c,tl),t2,p) ->
      if (List.exists (Terms.refers_to b) tl) || (Terms.refers_to b t2) || array_ref then
	Restr(b, Terms.oproc_from_desc (Output((c,tl),t2,p)))
      else
	begin
	  try
	    let p' = move_a_new b p in
	    Settings.changed := true;
	    Output((c,tl), t2, p')
	  with Not_found ->
	    Restr(b, Terms.oproc_from_desc (Output((c,tl),t2,p)))
	end
  | Let(pat, t, p1, p2) ->
      if (Terms.refers_to b t) || (Terms.refers_to_pat b pat) then
	Restr(b, Terms.oproc_from_desc (Let(pat, t, p1, p2)))
      else
	begin
	  Settings.changed := true;
	  match pat with
	    PatVar _ -> 
	      Let(pat, t, move_a_newo array_ref b p1, Terms.yield_proc)
	  | _ -> 
	      beneficial := true;
	      Let(pat, t, move_a_newo array_ref b p1, 
		  move_a_newo array_ref b p2)
	end
  | EventP(t,p) ->
      if Terms.refers_to b t then
	Restr(b, Terms.oproc_from_desc (EventP(t,p)))
      else
	begin
	  Settings.changed := true;
	  EventP(t, move_a_newo array_ref b p)
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
  | Abort -> Abort
  | Restr(b',p) -> 
      Settings.changed := true;
      Restr(b', move_a_leto (b,t0) p)
  | Test(t,p1,p2) ->
      let r1 = Terms.refers_to_oprocess b p1 in
      let r2 = Terms.refers_to_oprocess b p2 in
      if (Terms.refers_to b t) || (r1 && r2) then
	Let(PatVar b, t0, Terms.oproc_from_desc (Test(t,p1,p2)), Terms.yield_proc)
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
	Let(PatVar b, t0, Terms.oproc_from_desc (Find(l0,p,find_info)), Terms.yield_proc)
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
	Let(PatVar b, t0, Terms.oproc_from_desc (Output((c,tl),t2,p)), Terms.yield_proc)
      else
	begin
	  try
	    let p' = move_a_let (b,t0) p in
	    Settings.changed := true;
	    Output((c,tl), t2, p')
	  with Not_found ->
	    Let(PatVar b, t0, Terms.oproc_from_desc (Output((c,tl),t2,p)), Terms.yield_proc)
	end
  | Let(pat, t, p1, p2) ->
      let r1 = Terms.refers_to_oprocess b p1 in
      let r2 = Terms.refers_to_oprocess b p2 in
      if (Terms.refers_to b t) || (Terms.refers_to_pat b pat) || (r1 && r2) then
	Let(PatVar b, t0, Terms.oproc_from_desc (Let(pat, t, p1, p2)), Terms.yield_proc)
      else
	begin
	  Settings.changed := true;
	  match pat with
	    PatVar _ -> 
	      Let(pat, t, (if r1 then move_a_leto (b,t0) p1 else p1), Terms.yield_proc)
	  | _ -> 
	      beneficial := true;
	      Let(pat, t, (if r1 then move_a_leto (b,t0) p1 else p1), 
		  (if r2 then move_a_leto (b,t0) p2 else p2))
	end
  | EventP(t,p) ->
      if Terms.refers_to b t then
	Let(PatVar b, t0, Terms.oproc_from_desc (EventP(t,p)), Terms.yield_proc)
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
  | MOneBinder b' -> b == b'

let do_move_let move_set b =
  match move_set with
    MAll | MLet | MNoArrayRef -> 
      not (Terms.has_array_ref_q b)
	(* Lets are moved only when there are no array references.
	   Moving them is interesting only when it reduces the cases in
           which the value is computed, which can never be done when there
	   are array references. *)
  | MNew | MNewNoArrayRef -> false
  | MOneBinder b' -> b == b'

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
    Yield -> Terms.yield_proc
  | Abort -> Terms.abort_proc
  | Restr(b,p) ->
      let array_ref = Terms.has_array_ref_q b in
      if (not (do_move_new move_set array_ref b)) then
	Terms.oproc_from_desc (Restr(b, move_new_let_reco move_set p))
      else
	let p' = move_new_let_reco move_set p in
	let tmp_changed = !Settings.changed in
	Settings.changed := false;
	beneficial := false;
	let p'' = move_a_newo array_ref b p' in
	if (!beneficial) || (match move_set with MOneBinder _ -> true | _ -> false) then
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
	  PatVar b when do_move_let move_set b ->
	    let p1' = move_new_let_reco move_set p1 in
	    let tmp_changed = !Settings.changed in
	    Settings.changed := false;
	    beneficial := false;
	    let p1'' = move_a_leto (b,t) p1' in
	    if (!beneficial) || (match move_set with MOneBinder _ -> true | _ -> false) then
	      begin
		Settings.changed := (!Settings.changed) || tmp_changed;
		done_transfos := (DMoveLet b) :: (!done_transfos);
		p1''
	      end
	    else
	      begin
	        (* Don't do a move all/noarrayref if it is not beneficial *)
		Settings.changed := tmp_changed;
		Terms.oproc_from_desc (Let(pat, t, p1', Terms.yield_proc))
	      end
	| _ -> 
	    Terms.oproc_from_desc 
	      (Let(pat,t,move_new_let_reco move_set p1,
		move_new_let_reco move_set p2))
      end
  | EventP(t,p) ->
      Terms.oproc_from_desc (EventP(t, move_new_let_reco move_set p))
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

let move_new_let move_set g =
  done_transfos := [];
  Terms.array_ref_process g.proc;
  let r = move_new_let_rec move_set g.proc in
  Terms.cleanup_array_ref();
  let transfos = !done_transfos in
  done_transfos := [];
  ({ proc = r; game_number = -1}, [], transfos)

