open Types


(* Auto SA rename: when a variable x defined in find conditions has
   several definitions (and no array accesses---it must not have
   array accesses), rename variable x into x1...xn. That's necessary
   to satisfy the invariants. This transformation must be called after
   each transformation that duplicates processes. 

   This transformation supports processes with TestE/LetE/FindE/ResE
   inside terms (not only in find conditions).
*)

let done_sa_rename = ref []
      
let new_binder b =
  if Terms.has_array_ref_q b then
    Parsing_helper.internal_error ("Variable " ^ (Display.binder_to_string b) ^ " is defined in a condition of find; it should have no array reference.");
  if b.count_def > 1 then
    let b' = Terms.new_binder b in
    b.link <- (TLink (Terms.term_from_binder b'));
    Settings.changed := true;
    done_sa_rename := (b,b') :: (!done_sa_rename);
    b'
  else
    b

let rec auto_sa_rename_fc t =
  Terms.build_term2 t 
     (match t.t_desc with
	Var(b,l) ->
          let (b', l') = auto_sa_rename_fc_binder (b,l) in
          Var(b', l')
      | ReplIndex(b) -> ReplIndex(b)
      | FunApp(f,l) ->
	  FunApp(f, List.map (auto_sa_rename_fc) l)
      | TestE(t1,t2,t3) ->
          TestE(auto_sa_rename_fc t1,
		auto_sa_rename_fc t2,
		auto_sa_rename_fc t3)
      | FindE(l0,t3,find_info) ->
          FindE(List.map (fun (bl, def_list, t1,t2) ->
            let bl' = List.map (fun (b,b') -> (new_binder b, b')) bl in
            let branch' = 
	      (bl', List.map auto_sa_rename_fc_binder def_list,
	       auto_sa_rename_fc t1,
	       auto_sa_rename_fc t2)
            in
            List.iter (fun (b,_) -> b.link <- NoLink) bl;
            branch') l0,
		auto_sa_rename_fc t3, find_info)
      | LetE(pat, t1, t2, topt) ->
          let t1' = auto_sa_rename_fc t1 in
          let topt' = 
            match topt with
	      Some t3 -> Some (auto_sa_rename_fc t3)
	    | None -> None
          in
          let pat' = auto_sa_rename_fc_pat pat in
          let t2' = auto_sa_rename_fc t2 in
          List.iter (fun b -> b.link <- NoLink) (Terms.vars_from_pat [] pat);
	  LetE(pat', t1', t2', topt')
      |	ResE _ | EventE _ -> 
	  Parsing_helper.internal_error "New and event should not occur in find condition")

and auto_sa_rename_fc_binder (b,l) =
  let b' =
    match b.link with
      NoLink -> b
    | TLink { t_desc = Var(b',_) } -> b'
    | TLink _ -> Parsing_helper.internal_error "Unexpected link in auto_sa_rename"
  in 
  (b', List.map (auto_sa_rename_fc) l)

and auto_sa_rename_fc_pat = function
    PatVar b -> PatVar (new_binder b)
  | PatTuple (f,l) -> PatTuple (f,List.map auto_sa_rename_fc_pat l)
  | PatEqual t -> PatEqual (auto_sa_rename_fc t)

let rec auto_sa_rename_term t =
  Terms.build_term2 t 
     (match t.t_desc with
	Var(b,l) -> Var(b, List.map (auto_sa_rename_term) l)
      | ReplIndex(b) -> ReplIndex(b)
      | FunApp(f,l) ->
	  FunApp(f, List.map (auto_sa_rename_term) l)
      | TestE(t1,t2,t3) ->
          TestE(auto_sa_rename_term t1,
		auto_sa_rename_term t2,
		auto_sa_rename_term t3)
      | FindE(l0,t3,find_info) ->
          FindE(List.map (fun (bl, def_list, t1,t2) ->
	    (bl, def_list (* def_list contains only Var/FunApp/ReplIndex so no change *),
	     auto_sa_rename_fc t1,
	     auto_sa_rename_term t2)) l0,
		auto_sa_rename_term t3, find_info)
      | LetE(pat, t1, t2, topt) ->
          let t1' = auto_sa_rename_term t1 in
          let topt' = 
            match topt with
	      Some t3 -> Some (auto_sa_rename_term t3)
	    | None -> None
          in
          let pat' = auto_sa_rename_pat pat in
          let t2' = auto_sa_rename_term t2 in
	  LetE(pat', t1', t2', topt')
      |	ResE(b,t) ->
	  ResE(b, auto_sa_rename_term t)
      |	EventE(t) -> 
          EventE(auto_sa_rename_term t))

and auto_sa_rename_pat = function
    PatVar b -> PatVar b
  | PatTuple (f,l) -> PatTuple (f,List.map auto_sa_rename_pat l)
  | PatEqual t -> PatEqual (auto_sa_rename_term t)

let rec auto_sa_rename_process p = 
  Terms.iproc_from_desc2 p (
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) -> Par(auto_sa_rename_process p1, 
		      auto_sa_rename_process p2)
  | Repl(b,p) ->
      Repl(b, auto_sa_rename_process p)
  | Input((c,tl),pat,p) ->
      let tl' = List.map auto_sa_rename_term tl in
      let pat' = auto_sa_rename_pat pat in
      let p' = auto_sa_rename_oprocess p in
      Input((c, tl'), pat', p'))

and auto_sa_rename_oprocess p = 
  Terms.oproc_from_desc2 p (
  match p.p_desc with
    Yield -> Yield
  | Abort -> Abort
  | Restr(b,p) ->
      Restr(b, auto_sa_rename_oprocess p)
  | Test(t,p1,p2) ->
      Test(auto_sa_rename_term t,
	   auto_sa_rename_oprocess p1,
	   auto_sa_rename_oprocess p2)
  | Find(l0, p2, find_info) ->
      Find(List.map (fun (bl, def_list, t, p1) ->
	  (bl, def_list(* def_list contains only Var/FunApp/ReplIndex so no change *),
	   auto_sa_rename_fc t,
	   auto_sa_rename_oprocess p1)) l0,
	   auto_sa_rename_oprocess p2, find_info)
  | Let(pat,t,p1,p2) ->
      Let(auto_sa_rename_pat pat, 
	  auto_sa_rename_term t, 
	  auto_sa_rename_oprocess p1,
	  auto_sa_rename_oprocess p2)
  | Output((c,tl),t2,p) ->
      Output((c, List.map auto_sa_rename_term tl),
	     auto_sa_rename_term t2,
	     auto_sa_rename_process p)
  | EventP(t,p) ->
      EventP(auto_sa_rename_term t,
	     auto_sa_rename_oprocess p)
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"
  )

let rec do_sa_rename = function
    [] -> []
  | ((b,b')::l) ->
      let lb = List.map snd (List.filter (fun (b1,b1') -> b1 == b) l) in
      let lr = do_sa_rename (List.filter (fun (b1,b1') -> b1 != b) l) in
      if b.count_def > List.length lb + 1 then
	(* b has not been renamed for all its definitions, so keep it *)
	(DSArenaming(b, b::b'::lb))::lr
      else
	(DSArenaming(b, b'::lb))::lr

let auto_sa_rename g =
  Terms.array_ref_process g.proc;
  let p' = auto_sa_rename_process g.proc in
  Terms.cleanup_array_ref();
  let sa_rename = !done_sa_rename in
  done_sa_rename := [];
  ({ proc = p'; game_number = -1; current_queries = g.current_queries }, [], do_sa_rename sa_rename)

