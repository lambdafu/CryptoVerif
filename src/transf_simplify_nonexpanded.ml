open Types

(* Simplification for non-expanded games. 
   Less powerful than the one for expanded games, but better than nothing. *)

let current_pass_transfos = ref []

let simplify_term t = 
  if (Terms.check_simple_term t) && (not (Terms.is_true t || Terms.is_false t)) then
    begin
      try
	let facts = Facts.get_facts_at (DTerm t) in
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
  | (bl, def_list, t, p)::r ->
      let r' = filter_find tfind r in
      let t' = simplify_term t in
      if Terms.is_false t' then 
	begin
	  Settings.changed := true;
	  current_pass_transfos := (SFindBranchRemoved(DTerm tfind,(bl, def_list, t, DTerm p))) :: (!current_pass_transfos);
	  r' 
	end
      else 
	(bl, def_list, t', p)::r'


let rec simplify_cterm t =
  let pp = DTerm t in
  match t.t_desc with
    Var(b,l) -> Terms.build_term t (Var(b, List.map simplify_cterm l))
  | ReplIndex i -> Terms.build_term t (ReplIndex i)
  | FunApp(f,l) -> Terms.build_term t (FunApp(f, List.map simplify_cterm l))
  | TestE(t1,t2,t3) -> 
      (* Some trivial simplifications *)
      let t1' = simplify_term t1 in
      if Terms.is_true t1' then 
	begin
	  Settings.changed := true;
	  current_pass_transfos := (STestTrue pp) :: (!current_pass_transfos);
	  simplify_cterm t2
	end
      else if Terms.is_false t1' then 
	begin
	  Settings.changed := true;
	  current_pass_transfos := (STestFalse pp) :: (!current_pass_transfos);
	  simplify_cterm t3
	end
      else
      Terms.build_term t (TestE(simplify_cterm t1', simplify_cterm t2, simplify_cterm t3))
  | FindE(l0,t3, find_info) -> 
      (* Remove useless branches if possible *)
      let l0 = filter_find t l0 in
      if l0 == [] then  
	begin
	  Settings.changed := true;
	  current_pass_transfos := (SFindRemoved(pp)) :: (!current_pass_transfos);
	  simplify_cterm t3
	end
      else
      let l0' = List.map (fun (bl,def_list,t1,t2) ->
	let t1' = simplify_cterm t1 in
	let t2' = simplify_cterm t2 in
	(bl, def_list, t1', t2')) l0
      in
      let t3' = simplify_cterm t3 in
      Terms.build_term t (FindE(l0', t3', find_info))
  | LetE(pat, t1, t2, topt) ->
      let pat' = simplify_pat pat in
      let t1' = simplify_cterm t1 in
      let t2' = simplify_cterm t2 in
      let topt' = match topt with
	None -> None
      | Some t3 -> Some (simplify_cterm t3)
      in
      Terms.build_term t (LetE(pat', t1', t2', topt'))
  | ResE(b,t1) ->
      Terms.build_term t (ResE(b, simplify_cterm t1))
  | EventAbortE(f) ->
      Terms.build_term t (EventAbortE(f))
  | EventE(t1,p) ->
      let t1' = simplify_cterm t1 in
      let p' = simplify_cterm p in
      Terms.build_term t (EventE(t1', p'))
  | GetE _ | InsertE _ ->
      Parsing_helper.internal_error "Get/Insert should not appear in Transf_expand.simplify_cterm"

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
      | Get _ | Insert _ -> 
	  Parsing_helper.internal_error "Get/Insert should not appear in Transf_expand.simplify_oprocess")

let main g =
  current_pass_transfos := [];
  Proba.reset [] g;
  let g_proc = Terms.get_process g in
  Def.build_def_process None g_proc;
  let p' = simplify_process g_proc in
  let simplif_transfos = 
    if (!current_pass_transfos) != [] then
      [DSimplify(!current_pass_transfos)]
    else
      []
  in
  current_pass_transfos := [];
  let proba = Proba.final_add_proba [] in
  (* Cannot cleanup here because it may delete information
     in the initial game, needed to compute the probabilities.
     Terms.empty_def_process g.proc; *)
  (Terms.build_transformed_game p' g, proba, simplif_transfos)
