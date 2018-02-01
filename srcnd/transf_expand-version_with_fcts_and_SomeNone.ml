open Types

(* Expand all if, let, and find in expressions, so that they occur only in 
   processes. 

expand_term returns either
  None: the term is unchanged
  Some(f,l): a function f that takes a list of processes (of the same
  length as l) as argument and a list of terms l. 

expand_term_list returns either
  None: the list of terms is unchanged
  Some(f,l): a function f that takes a list of processes (of the same
  length as l) as argument and a list of lists of terms l. 

After expansion, if/let/find/res may occur in terms only in conditions of find.
*)

(* Try to simplify a bit before expanding, to reduce the size of the expanded game *)

let current_pass_transfos = ref []

let simplify_term t = 
  if (Terms.check_no_ifletfindres t) && (not (Terms.is_true t || Terms.is_false t)) then
    begin
      try
	let facts = Facts.get_facts_at t.t_facts in
	let simp_facts = Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) facts in
	let t' = Facts.simplify_term Facts.no_dependency_anal simp_facts t in
	(* When the obtained term is a complex term, using array accesses, I may
	   need to update defined conditions above the current program point.
	   To avoid the burden of doing that, I keep the result only when it is 
	   true or false. This is the only useful case for obtaining a smaller game in
	   expand, and the full simplification will be done later. *)
	if Terms.is_true t' || Terms.is_false t' then
	  begin
	    Settings.changed := true;
	    current_pass_transfos := (SReplaceTerm(t,t')) :: (!current_pass_transfos);
	    t'
	  end
	else
          (* The change is not really useful, don't do it *)
	  t
      with Contradiction ->
	(* The current program point is unreachable, I can return any term.
	   Returning false seems to be the best to get a smaller game.
	   Notice that simplify_term is called only for boolean terms
	   (conditions of if/find) so false is of the correct type. *)
	Settings.changed := true;
	let t' = Terms.make_false() in
	current_pass_transfos := (SReplaceTerm(t,t')) :: (!current_pass_transfos);
	t'
    end
  else
    t

let rec filter_find tfind = function
    [] -> []
  | ((bl, def_list, t, p) as findbranch)::r ->
      let r' = filter_find tfind r in
      let t' = simplify_term t in
      if Terms.is_false t' then 
	begin
	  current_pass_transfos := (SFindEBranchRemoved(tfind,findbranch)) :: (!current_pass_transfos);
	  r' 
	end
      else 
	(bl, def_list, t', p)::r'


let rec simplify_cterm t = 
  match t.t_desc with
    Var(b,l) -> Terms.build_term2 t (Var(b, List.map simplify_cterm l))
  | ReplIndex i -> Terms.build_term2 t (ReplIndex i)
  | FunApp(f,l) -> Terms.build_term2 t (FunApp(f, List.map simplify_cterm l))
  | TestE(t1,t2,t3) -> 
      (* Some trivial simplifications *)
      let t1' = simplify_term t1 in
      if Terms.is_true t1' then 
	begin
	  current_pass_transfos := (STestETrue t) :: (!current_pass_transfos);
	  simplify_cterm t2
	end
      else if Terms.is_false t1' then 
	begin
	  current_pass_transfos := (STestEFalse t) :: (!current_pass_transfos);
	  simplify_cterm t3
	end
      else
      Terms.build_term2 t (TestE(simplify_cterm t1', simplify_cterm t2, simplify_cterm t3))
  | FindE(l0,t3, find_info) -> 
      (* Remove useless branches if possible *)
      let l0 = filter_find t l0 in
      let l0' = List.map (fun (bl,def_list,t1,t2) ->
	let t1' = simplify_cterm t1 in
	let t2' = simplify_cterm t2 in
	(bl, def_list, t1', t2')) l0
      in
      let t3' = simplify_cterm t3 in
      Terms.build_term2 t (FindE(l0', t3', find_info))
  | LetE(pat, t1, t2, topt) ->
      let pat' = simplify_pat pat in
      let t1' = simplify_cterm t1 in
      let t2' = simplify_cterm t2 in
      let topt' = match topt with
	None -> None
      | Some t3 -> Some (simplify_cterm t3)
      in
      Terms.build_term2 t (LetE(pat', t1', t2', topt'))
  | ResE(b,t) ->
      Terms.build_term2 t (ResE(b, simplify_cterm t))
  | EventAbortE(f) ->
      Terms.build_term2 t (EventAbortE(f))

and simplify_pat = function
    PatVar b -> PatVar b
  | PatTuple (f,l) -> PatTuple(f,List.map simplify_pat l)
  | PatEqual t -> PatEqual(simplify_cterm t)

let rec simplify_process p = 
  Terms.iproc_from_desc 
      (match p.i_desc with
	Nil -> Nil
      | Par(p1,p2) -> 
	  let p1' = simplify_process p1 in
	  let p2' = simplify_process p2 in
	  Par(p1', p2')
      | Repl(b,p) -> Repl(b, simplify_process p)
      | Input((c,tl),pat,p) ->
	  let tl' = List.map simplify_cterm tl in
	  let pat' = simplify_pat pat in
	  let p' = simplify_oprocess p in
	  Input((c, tl'), pat', p'))

and simplify_oprocess p =
  Terms.oproc_from_desc 
      (match p.p_desc with
	Yield -> Yield
      |	EventAbort f -> EventAbort f
      | Restr(b,p) -> Restr(b, simplify_oprocess p)
      | Test(t,p1,p2) -> 
	  let t' = simplify_cterm t in
	  let p1' = simplify_oprocess p1 in
	  let p2' = simplify_oprocess p2 in
	  Test(t', p1', p2')
      | Find(l0, p2, find_info) -> 
	  let l0' = List.map (fun (bl, def_list, t, p1) -> 
	    let t' = simplify_cterm t in
	    let p1' = simplify_oprocess p1 in
	    (bl, def_list, t', p1')) l0
	  in
	  let p2' = simplify_oprocess p2 in
	  Find(l0', p2', find_info)
      | Let(pat,t,p1,p2) ->
	  let pat' = simplify_pat pat in
	  let t' = simplify_cterm t in
	  let p1' = simplify_oprocess p1 in
	  let p2' = simplify_oprocess p2 in	  
	  Let(pat', t', p1', p2')
      | Output((c,tl),t2,p) ->
	  let tl' = List.map simplify_cterm tl in
	  let t2' = simplify_cterm t2 in
	  let p' = simplify_process p in
	  Output((c, tl'), t2', p')
      | EventP(t,p) ->
	  let t' = simplify_cterm t in
	  let p' = simplify_oprocess p in
	  EventP(t', p')
      | Get(tbl,patl,topt,p1,p2) -> 
	  let patl' = List.map simplify_pat patl in
	  let topt' = 
	    match topt with 
	      Some t -> Some (simplify_cterm t) 
	    | None -> None
	  in
	  let p1' = simplify_oprocess p1 in
	  let p2' = simplify_oprocess p2 in	  
          Get(tbl,patl',topt',p1', p2')
      | Insert (tbl,tl,p) -> 
	  let tl' = List.map simplify_cterm tl in
	  let p' = simplify_oprocess p in
          Insert(tbl, tl', p'))

let simplify_process g =
  current_pass_transfos := [];
  Proba.reset [] g;
  Terms.build_def_process None g.proc;
  let p' = simplify_process g.proc in
  let simplif_transfos = 
    if (!current_pass_transfos) != [] then
      [DSimplify(!current_pass_transfos)]
    else
      []
  in
  current_pass_transfos := [];
  let proba = Proba.final_add_proba [] in
  (p', proba, simplif_transfos)

let check_no_ifletfind t =
  if not (Terms.check_no_ifletfindres t) then
    Parsing_helper.input_error "I cannot handle if, let, find, new inside the definition condition of a find. Sorry." t.t_loc

let check_no_ifletfind_br (_,l) =
  List.iter check_no_ifletfind l

(* Check if a term/pattern needs to be modified by expansion *)

let rec need_expand t =
  match t.t_desc with
    Var(_,l) | FunApp(_,l) -> List.exists need_expand l
  | ReplIndex _ -> false
  | _ -> true

let rec need_expand_pat = function
    PatVar _ -> false
  | PatTuple(_,l) -> List.exists need_expand_pat l
  | PatEqual t -> need_expand t
    
let always_some t = function
    None -> (fun context -> context t)
  | Some(f) -> f


(* Expand term to term. Useful for conditions of find when they cannot be expanded to processes.
   Guarantees the invariant that if/let/find/res terms occur only in
   - conditions of find
   - at [ ] positions in TestE(t,[then],[else]), ResE(b,[...]), LetE(b,t,[in],[else]), 
     FindE((bl,def_list,[cond],[then]) list,[else])

   context = fun term -> C[term]
   tex = fun context -> C[term]

*)

let rec pseudo_expand_term t = 
  match t.t_desc with
    Var(b,l) ->
      begin
	match pseudo_expand_term_list l with
	  None -> None
	| Some lex ->
	    Some (fun context -> lex (fun li -> context (Terms.build_term t (Var(b,li)))))
      end
  | ReplIndex _ -> None
  | FunApp(f,l) ->
      begin
	match pseudo_expand_term_list l with
	  None -> None
	| Some lex ->
	    Some (fun context -> lex (fun li -> context (Terms.build_term t (FunApp(f,li)))))
      end
  | TestE(t1,t2,t3) ->
      let t1ex = always_some t1 (pseudo_expand_term t1) in
      let t2ex = always_some t2 (pseudo_expand_term t2) in
      let t3ex = always_some t3 (pseudo_expand_term t3) in
      Some (fun context ->
	t1ex (fun t1i ->
          (* Some trivial simplifications *)
          if Terms.is_true t1i then t2ex context else
          if Terms.is_false t1i then t3ex context else
	  let t2' = t2ex context in
	  Terms.build_term t2' (TestE(t1i, t2', t3ex context))))

  | LetE(pat, t1, t2, topt) ->
      let patex = always_some pat (pseudo_expand_pat pat) in
      let t1ex = always_some t1 (pseudo_expand_term t1) in
      let t2ex = always_some t2 (pseudo_expand_term t2) in
      begin
	match topt with
	  None ->
	    Some (fun context ->
	      t1ex (fun t1i ->
		patex (fun pati ->
		  let t2' = t2ex context in
		  Terms.build_term t2' (LetE(pati, t1i, t2', None)))))
	| Some t3 ->
	    let t3ex = always_some t3 (pseudo_expand_term t3) in
	    Some (fun context ->
	      t1ex (fun t1i ->
		patex (fun pati ->
		  let t2' = t2ex context in
		  Terms.build_term t2' (LetE(pati, t1i, t2', Some (t3ex context))))))
      end
  | FindE(l0, t3, find_info) ->
      let rec expand_cond_find_list = function
	  [] -> (fun context -> context [])
	| ((bl, def_list, t1, t2)::restl) ->
	    List.iter check_no_ifletfind_br def_list;
	    let restlex = expand_cond_find_list restl in
	    let t1ex = always_some t1 (pseudo_expand_term t1) in
                  (* I move something outside a condition of
                     "find" only when bl and def_list are empty.  
                     I could be more precise, I would need to
                     check not only that what I move out does not
                     refer to the indices of "find", but also that it
                     is does not refer to the variables in the
                     "defined" condition---otherwise, some variable
                     accesses may not be defined after the
                     transformation *)
	    if bl != [] || def_list != [] then
	      (fun context ->
		restlex (fun li -> context ((bl, def_list, t1ex (fun t -> t), t2)::li)))
	    else
	      (fun context ->
		t1ex (fun t1i ->
		  restlex (fun li -> context ((bl, def_list, t1i, t2)::li))))
      in

      let rec expand_res_find_list = function
	  [] -> (fun context -> [])
	| ((bl, def_list, t1, t2)::restl) ->
	    let restlex = expand_res_find_list restl in
	    let t2ex = always_some t2 (pseudo_expand_term t2) in
	    (fun context ->
	      (bl, def_list, t1, t2ex context) :: (restlex context))
      in 
      let l0ex = expand_res_find_list l0 in
      let t3ex = always_some t3 (pseudo_expand_term t3) in
      Some (fun context ->
	let expanded_res_l = l0ex context in
	let expanded_res_t3 = t3ex context in
	let l0ex2 = expand_cond_find_list expanded_res_l in
        l0ex2 (fun l1i -> Terms.build_term expanded_res_t3 (FindE(l1i, expanded_res_t3, find_info))))
  | ResE(b, t) ->
      let tex = always_some t (pseudo_expand_term t) in
      Some (fun context -> let t' = tex context in Terms.build_term t' (ResE(b, t')))
  | EventAbortE _ ->
      Parsing_helper.internal_error "Events should not occur in conditions of find before expansion"

and pseudo_expand_term_list = function
  [] -> None 
| (a::l) -> 
    let aex = pseudo_expand_term a in
    let lex = pseudo_expand_term_list l in
    match aex, lex with
      None, None -> None
    | _ ->
	let aex = always_some a aex in
	let lex = always_some l lex in
	Some (fun context -> aex (fun a' -> lex (fun l' -> context (a'::l'))))

and pseudo_expand_pat = function
    PatVar b -> None
  | PatTuple (ft,l) ->
      begin
	match pseudo_expand_pat_list l with
	  None -> None
	| Some lex ->
	    Some (fun context -> lex (fun li -> context (PatTuple (ft,li))))
      end
  | PatEqual t ->
      begin
	match pseudo_expand_term t with
	  None -> None
	| Some tex ->
	    Some (fun context -> tex (fun ti -> context (PatEqual ti)))
      end

and pseudo_expand_pat_list = function
  [] -> None
| (a::l) -> 
    let aex = pseudo_expand_pat a in
    let lex = pseudo_expand_pat_list l in
    match aex, lex with
      None, None -> None
    | _ ->
	let aex = always_some a aex in
	let lex = always_some l lex in
	Some (fun context -> aex (fun a' -> lex (fun l' -> context (a'::l'))))

and final_pseudo_expand t =
  match pseudo_expand_term t with
    None -> t
  | Some tex -> tex (fun t -> t)

(* Expand term to process *)

let rec expand_term t = 
  match t.t_desc with
    Var(b,l) ->
      begin
        match expand_term_list l with
          None -> None
	| Some lex -> 
	    Some (fun context -> lex (fun li -> context (Terms.build_term t (Var(b,li)))))
      end
  | ReplIndex _ -> None
  | FunApp(f,l) ->
      begin
        match expand_term_list l with
          None -> None
	| Some lex -> 
	    Some (fun context -> lex (fun li -> context (Terms.build_term t (FunApp(f,li)))))
      end
  | TestE(t1,t2,t3) ->
      let t1ex = always_some t1 (expand_term t1) in
      let t2ex = always_some t2 (expand_term t2) in
      let t3ex = always_some t3 (expand_term t3) in
      Some (fun context ->
	t1ex (fun t1i ->
          (* Some trivial simplifications *)
          if Terms.is_true t1i then t2ex context else
          if Terms.is_false t1i then t3ex context else
	  Terms.oproc_from_desc (Test(t1i, t2ex context, t3ex context))))

  | LetE(pat, t1, t2, topt) ->
      let patex = always_some pat (expand_pat pat) in
      let t1ex = always_some t1 (expand_term t1) in
      let t2ex = always_some t2 (expand_term t2) in
      begin
	match topt with
	  None ->
	    Some (fun context ->
	      t1ex (fun t1i ->
		patex (fun pati ->
		  Terms.oproc_from_desc (Let(pati, t1i, t2ex context, Terms.oproc_from_desc Yield)))))
	| Some t3 ->
	    let t3ex = always_some t3 (expand_term t3) in
	    Some (fun context ->
	      t1ex (fun t1i ->
		patex (fun pati ->
		  Terms.oproc_from_desc (Let(pati, t1i, t2ex context, t3ex context)))))
      end
  | FindE(l0, t3, find_info) ->
      let rec expand_cond_find_list = function
	  [] -> (fun context -> context [])
	| ((bl, def_list, t1, t2)::restl) ->
	    List.iter check_no_ifletfind_br def_list;
	    let restlex = expand_cond_find_list restl in
                  (* I move something outside a condition of
                     "find" only when bl and def_list are empty.  
                     I could be more precise, I would need to
                     check not only that what I move out does not
                     refer to the indices of "find", but also that it
                     is does not refer to the variables in the
                     "defined" condition---otherwise, some variable
                     accesses may not be defined after the
                     transformation *)
            if bl != [] || def_list != [] then
	      (fun context ->
		restlex (fun li -> context ((bl, def_list, final_pseudo_expand t1, t2)::li)))
	    else
	      let t1ex = always_some t1 (expand_term t1) in
	      (fun context ->
		t1ex (fun t1i ->
		  restlex (fun li -> context ((bl, def_list, t1i, t2)::li))))
      in

      let rec expand_res_find_list = function
	  [] -> (fun context -> [])
	| ((bl, def_list, t1, t2)::restl) ->
	    let restlex = expand_res_find_list restl in
	    let t2ex = always_some t2 (expand_term t2) in
	    (fun context ->
	      (bl, def_list, t1, t2ex context) :: (restlex context))
      in 
      let l0ex = expand_res_find_list l0 in
      let t3ex = always_some t3 (expand_term t3) in
      Some (fun context ->
	let expanded_res_l = l0ex context in
	let l0ex2 = expand_cond_find_list expanded_res_l in
        l0ex2 (fun l1i -> Terms.oproc_from_desc (Find(l1i, t3ex context, find_info))))
  | ResE(b, t) ->
      let tex = always_some t (expand_term t) in
      Some (fun context -> Terms.oproc_from_desc (Restr(b, tex context)))
  | EventAbortE(f) ->
      (* The event is expanded to a process that stops just after the event.
	 Events in terms are used only in the RHS of equivalences, and 
	 one includes their probability of execution in the probability of
	 breaking the protocol. *)
      Some (fun context -> Terms.oproc_from_desc (EventAbort f))

and expand_term_list = function
  [] -> None
| (a::l) -> 
    let aex = expand_term a in
    let lex = expand_term_list l in
    match aex, lex with
      None, None -> None
    | _ ->
	let aex = always_some a aex in
	let lex = always_some l lex in
	Some (fun context -> aex (fun a' -> lex (fun l' -> context (a'::l'))))

and expand_pat = function
    PatVar b -> None
  | PatTuple (ft,l) ->
      begin
      match expand_pat_list l with
	None -> None
      | Some lex ->
	  Some (fun context -> lex (fun li -> context (PatTuple (ft,li))))
      end
  | PatEqual t ->
      begin
      match expand_term t with
	None -> None
      | Some tex ->  
	  Some (fun context -> tex (fun ti -> context (PatEqual ti)))
      end

and expand_pat_list = function
  [] -> None
| (a::l) -> 
    let aex = expand_pat a in
    let lex = expand_pat_list l in
    match aex, lex with
      None, None -> None
    | _ ->
	let aex = always_some a aex in
	let lex = always_some l lex in
	Some (fun context -> aex (fun a' -> lex (fun l' -> context (a'::l'))))


(* Expand process to process *)

let rec expand_process cur_array p = 
  match p.i_desc with
    Nil -> Terms.iproc_from_desc Nil
  | Par(p1,p2) ->
      Terms.iproc_from_desc  (Par(expand_process cur_array p1,
				  expand_process cur_array p2))
  | Repl(b,p) ->
      Terms.iproc_from_desc (Repl(b, expand_process (b::cur_array) p))
  | Input((c,tl),pat,p) ->
      List.iter check_no_ifletfind tl;
      match expand_pat pat with
	None -> Terms.iproc_from_desc (Input((c,tl),pat, expand_oprocess cur_array p))
      | Some patex ->
	  Settings.changed := true;
	  let b = Terms.create_binder "patv" (Terms.new_vname()) 
	      Settings.t_bitstring cur_array
	  in
	  Terms.iproc_from_desc (Input((c,tl),PatVar b, 
	      patex (fun pati -> Terms.oproc_from_desc 
                  (Let(pati, Terms.term_from_binder b,
		       expand_oprocess cur_array p, Terms.oproc_from_desc Yield)))))

and expand_oprocess cur_array p =
  match p.p_desc with 
    Yield -> Terms.oproc_from_desc Yield
  | EventAbort f -> Terms.oproc_from_desc (EventAbort f)
  | Restr(b,p) -> Terms.oproc_from_desc (Restr(b, expand_oprocess cur_array p))
  | Test(t,p1,p2) ->
      begin
	match expand_term t with
	  None ->
	    Terms.oproc_from_desc (Test(t,expand_oprocess cur_array p1,
					expand_oprocess cur_array p2))
	| Some tex ->
	    Settings.changed := true;
	    tex (fun ti ->
            (* Some trivial simplifications *)
              if Terms.is_true ti then expand_oprocess cur_array p1 else
              if Terms.is_false ti then expand_oprocess cur_array p2 else
	      Terms.oproc_from_desc (Test(ti,expand_oprocess cur_array p1,
					  expand_oprocess cur_array p2)))
      end
  | Find(l0, p2, find_info) ->
      let rec expand_find_list next_f = function
	  [] -> next_f []
	| ((bl, def_list, t, p1)::rest_l) ->
	    List.iter check_no_ifletfind_br def_list;
	    if bl != [] || def_list != [] then
	      match pseudo_expand_term t with
		None ->
		  expand_find_list (fun rest_l' ->
		    next_f ((bl, def_list, t, expand_oprocess cur_array p1)::rest_l')) rest_l
	      | Some tex ->
		  Settings.changed := true;
		  expand_find_list (fun rest_l' ->
		    next_f ((bl, def_list, tex (fun t -> t),
			     expand_oprocess cur_array p1)::rest_l')) rest_l
	    else
	      match expand_term t with
		None ->
		  expand_find_list (fun rest_l' ->
		    next_f ((bl, def_list, t, expand_oprocess cur_array p1)::rest_l')) rest_l
	      | Some tex ->
		  Settings.changed := true;
		  tex (fun ti -> expand_find_list (fun rest_l' ->
		    next_f ((bl, def_list, ti, expand_oprocess cur_array p1)::rest_l')) rest_l)
      in
      expand_find_list (fun l0' -> Terms.oproc_from_desc (Find(l0', expand_oprocess cur_array p2, find_info))) l0
  | Output((c,tl),t2,p) ->
      begin
	match expand_term_list tl, expand_term t2 with
	  None, None -> Terms.oproc_from_desc (Output((c,tl),t2, expand_process cur_array p))
	| tlex, t2ex ->
	    Settings.changed := true;
	    let tlex = always_some tl tlex in
	    let t2ex = always_some t2 t2ex in
	    tlex (fun tli ->
	      t2ex (fun t2i ->
		Terms.oproc_from_desc (Output((c,tli),t2i,expand_process cur_array p))))
      end
  | Let(pat,t,p1,p2) ->
      begin
	match expand_term t, expand_pat pat with
	  None, None -> Terms.oproc_from_desc (Let(pat, t, expand_oprocess cur_array p1, 
						   expand_oprocess cur_array p2))
	| tex, patex ->
	    Settings.changed := true;
	    let tex = always_some t tex in
	    let patex = always_some pat patex in
	    tex (fun ti ->
	      patex (fun pati ->
		Terms.oproc_from_desc (Let(pati,ti,expand_oprocess cur_array p1, expand_oprocess cur_array p2))))
      end
  | EventP(t,p) ->
      begin
	match expand_term t with
	  None -> Terms.oproc_from_desc (EventP(t, expand_oprocess cur_array p))
	| Some tex ->
	    Settings.changed := true;
	    tex (fun ti -> Terms.oproc_from_desc (EventP(ti, expand_oprocess cur_array p)))
      end
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

(* Main function for expansion of if and find
   Call auto_sa_rename after expand_process, so that facts associated with 
   nodes are emptied, and variables defined in
   conditions of find have a single definition. 
   Expansion is called only when there is no advice pending, so we can simply 
   ignore the list of done SArenamings.
*)

let expand_process g =
  let tmp_changed = !Settings.changed in
  let (p', proba, simplif_transfos) = simplify_process g in
  let p'' = expand_process [] p' in
  if !Settings.changed then 
    let (g', proba', ins) = Transf_auto_sa_rename.auto_sa_rename { proc = p''; game_number = -1; current_queries = g.current_queries } in
    (g', proba' @ proba, ins @ (DExpandIfFind :: simplif_transfos))
  else
    begin
      Settings.changed := tmp_changed;
      Transf_auto_sa_rename.auto_sa_rename g
    end
    
