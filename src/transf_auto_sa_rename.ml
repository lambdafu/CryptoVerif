open Types


(* Auto SA rename: when a variable x defined in find conditions has
   several definitions (and no array accesses---it must not have
   array accesses), rename variable x into x1...xn. That's necessary
   to satisfy the invariants. This transformation must be called after
   each transformation that duplicates processes. 

   This transformation supports processes with TestE/LetE/FindE/ResE
   inside terms (not only in find conditions).
*)

let whole_game = ref Terms.empty_game

let done_sa_rename = ref []
      
let new_binder b =
  if Array_ref.has_array_ref_q b (!whole_game).current_queries then
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
      |	ResE _ | EventAbortE _ | EventE _ | GetE _ | InsertE _ -> 
	  Parsing_helper.internal_error "New, get, insert, event, and event_abort should not occur in find condition")

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
	    (bl, List.map Terms.move_occ_br def_list (* def_list contains only Var/FunApp/ReplIndex so no change
							I still need to copy the def_list to make sure that all
							terms are physically distinct, for a correct computation of facts. *),
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
      |	EventAbortE(f) -> 
	  EventAbortE(f)
      | EventE(t,p) ->
	  EventE(auto_sa_rename_term t,
		 auto_sa_rename_term p)
      | GetE _ |InsertE _ -> Parsing_helper.internal_error "Get/Insert should not appear in auto_sa_rename_term"
	    )

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
  | EventAbort f -> EventAbort f
  | Restr(b,p) ->
      Restr(b, auto_sa_rename_oprocess p)
  | Test(t,p1,p2) ->
      Test(auto_sa_rename_term t,
	   auto_sa_rename_oprocess p1,
	   auto_sa_rename_oprocess p2)
  | Find(l0, p2, find_info) ->
      Find(List.map (fun (bl, def_list, t, p1) ->
	  (bl, List.map Terms.move_occ_br def_list(* def_list contains only Var/FunApp/ReplIndex so no change *),
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
  | Get _ | Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear in auto_sa_rename_oprocess"
  )

let rec do_sa_rename accu = function
    [] -> accu
  | ((b,b')::l) ->
      let (list_b, list_not_b) = List.partition (fun (b1,b1') -> b1 == b) l in
      let lb = List.map snd list_b in
      let b_rename = 
	if b.count_def > List.length lb + 1 then
	  (* b has not been renamed for all its definitions, so keep it *)
	  DSArenaming(b, b::b'::lb)
	else
	  DSArenaming(b, b'::lb)
      in
      do_sa_rename (b_rename::accu) list_not_b

let auto_sa_rename g =
  whole_game := g;
  let g_proc = Terms.get_process g in
  Array_ref.array_ref_process g_proc;
  let p' = auto_sa_rename_process g_proc in
  Array_ref.cleanup_array_ref();
  let sa_rename = !done_sa_rename in
  done_sa_rename := [];
  let res = (Terms.build_transformed_game p' g, [], do_sa_rename [] sa_rename) in
  whole_game := Terms.empty_game;
  res

