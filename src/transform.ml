open Types

(* Set when a game is modified *)

let changed = ref false

(* Instructions are added in advise when an instruction I cannot be fully
   performed. The added instructions correspond to suggestions of instructions
   to apply before I so that instruction I can be better performed. *)

let advise = ref ([] : instruct list)

(***************************************************************************)

let queries = ref []

let public_vars = ref []

let collect_public_vars() =
  List.iter (function 
      (QSecret b',_) | (QSecret1 b',_) -> 
         if not (List.memq b' (!public_vars)) then
           public_vars := b' :: (!public_vars)
    | (QEventQ _,_) -> ()
    | (AbsentQuery,_) -> ()) (!queries)

let occurs_in_queries b = List.memq b (!public_vars)

let has_array_ref b =
  (Terms.has_array_ref b) || (occurs_in_queries b)

let event_occurs_in_term f t = 
  match t.t_desc with
    FunApp(f',_) -> f == f'
  | _ -> false

let rec event_occurs_in_qterm f = function
    QEvent(_,t) -> event_occurs_in_term f t
  | QTerm _ -> false
  | QAnd(t1,t2) | QOr(t1,t2) -> 
      (event_occurs_in_qterm f t1) || (event_occurs_in_qterm f t2)

let event_occurs_in_queries f =
  List.exists (function
      ((QSecret _|QSecret1 _), _) -> false
    | (AbsentQuery, _) -> true
    | (QEventQ (l,r),_) -> 
	(List.exists (fun (_,t) -> event_occurs_in_term f t) l) ||
	(event_occurs_in_qterm f r)
	  ) (!queries)

(***************************************************************************)

let statements = ref []

let collisions = ref []

let equivs = ref []

let move_new_eq = ref []

(****************************************************************************)

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
  if has_array_ref b then
    Parsing_helper.internal_error ("Variable " ^ (Display.binder_to_string b) ^ " is defined in a condition of find; it should have no array reference.");
  if b.count_def > 1 then
    let b' = Terms.new_binder b in
    b.link <- (TLink (Terms.term_from_binder b'));
    changed := true;
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
  ({ proc = p'; game_number = -1 }, [], do_sa_rename sa_rename)

(***************************************************************************)


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

let rec cross_product l1 = function
    [] -> []
  | (a::l) -> (List.map (fun l1i -> (l1i,a)) l1) @ (cross_product l1 l)

let rec split_every n = function
    [] -> []
  | l ->
      let (l1,l2) = Terms.split n l in
      l1 :: (split_every n l2)

let rec check_no_ifletfindres t =
  match t.t_desc with
    Var(_,l) | FunApp(_,l) ->
      List.for_all check_no_ifletfindres l
  | ReplIndex _ -> true
  | TestE _ | FindE _ | LetE _ | ResE _ | EventE _ ->
      false

let check_no_ifletfind t =
  if not (check_no_ifletfindres t) then
    Parsing_helper.input_error "I cannot handle if, let, find, new inside the definition condition of a find. Sorry." t.t_loc

let check_no_ifletfind_br (_,l) =
  List.iter check_no_ifletfind l

let pairing_expand a l aex lex =
  match aex, lex with
    None, None -> None
  | Some(fa,la),None -> Some(fa, List.map (fun lai -> (lai,l)) la)
  | None,Some(fl,ll) -> Some(fl, List.map (fun lli -> (a,lli)) ll)
  | Some(fa,la),Some(fl,ll) ->
      let len = List.length la in
      Some((fun l -> let l' = split_every len l in
                     fl (List.map fa l')), cross_product la ll)

let extract_elem = function
    [p] -> p
  | _ -> Parsing_helper.internal_error "list with single element expected"

let always_some t = function
    None -> (extract_elem, [t])
  | Some(f,l) -> (f,l)

(* Expand term to term. Useful for conditions of find when they cannot be expanded to processes.
   Guarantees the invariant that if/let/find/res terms occur only in
   - conditions of find
   - at [ ] positions in TestE(t,[then],[else]), ResE(b,[...]), LetE(b,t,[in],[else]), 
     FindE((bl,def_list,[cond],[then]) list,[else])
*)

let rec pseudo_expand_term t = 
  match t.t_desc with
    Var(b,l) ->
      begin
        match pseudo_expand_term_list l with
          None -> None
        | Some(f,l') ->
            Some(f, List.map (fun li -> Terms.build_term t (Var(b,li))) l')
      end 
  | ReplIndex _ -> None 
  | FunApp(f,l) ->
      begin
        match pseudo_expand_term_list l with
          None -> None
        | Some(f',l') -> Some(f', List.map (fun li -> Terms.build_term t (FunApp(f,li))) l')
      end
  | TestE(t1,t2,t3) ->
      (* I always expand this test *)
      let (f2, l2) = always_some t2 (pseudo_expand_term t2) in
      let (f3, l3) = always_some t3 (pseudo_expand_term t3) in
      let (f1, l1) = always_some t1 (pseudo_expand_term t1) in
      let len2 = List.length l2 in
      Some((fun l -> 
	let (l2part, l3part) = Terms.split len2 l in
	f1 (List.map (fun t1i -> 
            (* Some trivial simplifications *)
            if Terms.is_true t1i then f2 l2part else
            if Terms.is_false t1i then f3 l3part else
            let t2' = f2 l2part in Terms.build_term t2' (TestE(t1i, t2', f3 l3part))) l1)), l2 @ l3)
  | LetE(pat, t1, t2, topt) ->
      let (fpat,lpat) = always_some pat (pseudo_expand_pat pat) in
      let (f1,l1) = always_some t1 (pseudo_expand_term t1) in
      let (f2,l2) = always_some t2 (pseudo_expand_term t2) in
      begin
	match topt with
	  None ->
	    Some ((fun l -> 
	      f1 (List.map (fun t1i -> 
		fpat (List.map (fun pati ->
                  let t2' = f2 l in
		  Terms.build_term t2' (LetE(pati, t1i, t2', None))) lpat)) l1)), l2)
	| Some t3 ->
	    let (f3,l3) = always_some t3 (pseudo_expand_term t3) in
	    let len2 = List.length l2 in
	    Some ((fun l -> 
	      let (l2part, l3part) = Terms.split len2 l in
	      f1 (List.map (fun t1i -> 
		fpat (List.map (fun pati ->
                  let t2' = f2 l2part in
		  Terms.build_term t2' (LetE(pati, t1i, t2', Some (f3 l3part)))) lpat)) l1)), l2 @ l3)
      end
  | FindE(l0, t3, find_info) ->
      let rec expand_cond_find_list = function
	  [] -> None
	| ((bl, def_list, t1, t2)::restl) ->
	    List.iter check_no_ifletfind_br def_list;
	    let rest_lex = expand_cond_find_list restl in
	    let ex1 = pseudo_expand_term t1 in
	    let ex1 = 
	      match ex1 with
		None -> None
	      | Some(f,l) ->
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
                    Some(extract_elem, [f l])
                  else 
                    ex1
		  (*let tf = f (List.map (fun t -> 
		    let b = Terms.create_binder "tmp"
			      (Terms.new_vname()) t.t_type []
		    in 
		    Terms.build_term t (Var(b,[]))) l) 
		  in
		  if List.exists (fun b -> Terms.refers_to b tf) bl || [tf refers to variables in def_list] then
		    Some(extract_elem, [f l]) (* We cannot move the condition of the find outside, because it refers to variables defined in the find. In this case, we leave the term without expanding it. *)
                  else
                    ex1*)
            in
	    match pairing_expand t1 restl ex1 rest_lex with
	      None -> None
	    | Some(f,l') -> Some(f, List.map (fun (a,l'') -> (bl, def_list, a, t2)::l'') l')
      in

      let rec expand_res_find_list = function
	  [] -> ((fun l -> []), [])
	| ((bl, def_list, t1, t2)::restl) ->
	    let (frestl, lrestl) = expand_res_find_list restl in
	    let (f2, l2) = always_some t2 (pseudo_expand_term t2) in
	    let len2 = List.length l2 in
	    ((fun l -> 
	      let (l2part, l3part) = Terms.split len2 l in
	      (bl, def_list, t1, f2 l2part) :: (frestl l3part)),
	     l2 @ lrestl)
      in 
      let (f2, l2) = expand_res_find_list l0 in
      let (f3, l3) = always_some t3 (pseudo_expand_term t3) in
      let len3 = List.length l3 in
      Some((fun l -> 
	let (l3part, l2part) = Terms.split len3 l in
	let expanded_res_l = f2 l2part in
	let expanded_res_t3 = f3 l3part in
	let (f1, l1) = always_some expanded_res_l (expand_cond_find_list expanded_res_l) in
        f1 (List.map (fun l1i -> Terms.build_term expanded_res_t3 (FindE(l1i, expanded_res_t3, find_info))) l1)), l3 @ l2)
  | ResE(b, t) ->
      let (f,l) = always_some t (pseudo_expand_term t) in
      Some((fun l -> let t' = f l in Terms.build_term t' (ResE(b, t'))), l)
  | EventE _ ->
      Parsing_helper.internal_error "Events should not occur in conditions of find before expansion"

and pseudo_expand_term_list = function
  [] -> None
| (a::l) -> 
    let aex = pseudo_expand_term a in
    let lex = pseudo_expand_term_list l in
    match pairing_expand a l aex lex with
      None -> None
    | Some(f,l') -> Some(f, List.map (fun (a,l'') -> a::l'') l')

and pseudo_expand_pat = function
    PatVar b -> None
  | PatTuple (ft,l) -> 
      begin
	match pseudo_expand_pat_list l with
	  None -> None
	| Some(f,l') -> Some(f, List.map (fun li -> PatTuple (ft,li)) l')
      end 
  | PatEqual t -> 
      begin
	match pseudo_expand_term t with
	  None -> None
	| Some(f,l) -> Some (f, List.map (fun ti -> PatEqual ti) l)
      end

and pseudo_expand_pat_list = function
  [] -> None
| (a::l) -> 
    let aex = pseudo_expand_pat a in
    let lex = pseudo_expand_pat_list l in
    match pairing_expand a l aex lex with
      None -> None
    | Some(f,l') -> Some(f, List.map (fun (a,l'') -> a::l'') l')

and final_pseudo_expand t =
  match pseudo_expand_term t with
    None -> t
  | Some(f,l) -> f l

(* Expand term to process *)

let rec expand_term t = 
  match t.t_desc with
    Var(b,l) ->
      begin
        match expand_term_list l with
          None -> None
        | Some(f,l') ->
            Some(f, List.map (fun li -> Terms.build_term t (Var(b,li))) l')
      end 
  | ReplIndex _ -> None 
  | FunApp(f,l) ->
      begin
        match expand_term_list l with
          None -> None
        | Some(f',l') -> Some(f', List.map (fun li -> Terms.build_term t (FunApp(f,li))) l')
      end
  | TestE(t1,t2,t3) ->
      (* I always expand this test *)
      let (f2, l2) = always_some t2 (expand_term t2) in
      let (f3, l3) = always_some t3 (expand_term t3) in
      let (f1, l1) = always_some t1 (expand_term t1) in
      let len2 = List.length l2 in
      Some((fun l -> 
	let (l2part, l3part) = Terms.split len2 l in
	f1 (List.map (fun t1i -> 
          (* Some trivial simplifications *)
          if Terms.is_true t1i then f2 l2part else
          if Terms.is_false t1i then f3 l3part else
          Terms.oproc_from_desc (Test(t1i, f2 l2part, f3 l3part))) l1)), l2 @ l3)
  | LetE(pat, t1, t2, topt) ->
      let (fpat,lpat) = always_some pat (expand_pat pat) in
      let (f1,l1) = always_some t1 (expand_term t1) in
      let (f2,l2) = always_some t2 (expand_term t2) in
      begin
	match topt with
	  None ->
	    Some ((fun l -> 
	      f1 (List.map (fun t1i -> 
		fpat (List.map (fun pati ->
		  Terms.oproc_from_desc (Let(pati, t1i, f2 l, Terms.yield_proc))) lpat)) l1)), l2)
	| Some t3 ->
	    let (f3,l3) = always_some t3 (expand_term t3) in
	    let len2 = List.length l2 in
	    Some ((fun l -> 
	      let (l2part, l3part) = Terms.split len2 l in
	      f1 (List.map (fun t1i -> 
		fpat (List.map (fun pati ->
		  Terms.oproc_from_desc (Let(pati, t1i, f2 l2part, f3 l3part))) lpat)) l1)), l2 @ l3)
      end
  | FindE(l0, t3, find_info) ->
      let rec expand_cond_find_list = function
	  [] -> None
	| ((bl, def_list, t1, t2)::restl) ->
	    List.iter check_no_ifletfind_br def_list;
	    let rest_lex = expand_cond_find_list restl in
	    let ex1 = expand_term t1 in
	    let ex1 = 
	      match ex1 with
		None -> None
	      | Some(f,l) ->
                  if bl != [] || def_list != [] then
                    Some(extract_elem, [final_pseudo_expand t1])
                  else
                    ex1
		  (*let fNil = f (List.map (fun _ -> Terms.yield_proc) l) in
		  if List.exists (fun b -> Terms.refers_to_oprocess b fNil) bl || [fNil refers to variables in def_list] | [fNil contains new and bl != [] ] then
		    Some (extract_elem, [final_pseudo_expand t1]) (* We cannot move the condition of the find outside, because it refers to variables defined in the find. In this case, we leave the term with if/let/find/res in it. *)
                  else
                    ex1*)
            in
	    match pairing_expand t1 restl ex1 rest_lex with
	      None -> None
	    | Some(f,l') -> Some(f, List.map (fun (a,l'') -> (bl, def_list, a, t2)::l'') l')
      in

      let rec expand_res_find_list = function
	  [] -> ((fun l -> []), [])
	| ((bl, def_list, t1, t2)::restl) ->
	    let (frestl, lrestl) = expand_res_find_list restl in
	    let (f2, l2) = always_some t2 (expand_term t2) in
	    let len2 = List.length l2 in
	    ((fun l -> 
	      let (l2part, l3part) = Terms.split len2 l in
	      (bl, def_list, t1, f2 l2part) :: (frestl l3part)),
	     l2 @ lrestl)
      in 
      let (f2, l2) = expand_res_find_list l0 in
      let (f3, l3) = always_some t3 (expand_term t3) in
      let len3 = List.length l3 in
      Some((fun l -> 
	let (l3part, l2part) = Terms.split len3 l in
	let expanded_res_l = f2 l2part in
	let expanded_res_t3 = f3 l3part in
	let (f1, l1) = always_some expanded_res_l (expand_cond_find_list expanded_res_l) in
        f1 (List.map (fun l1i -> Terms.oproc_from_desc (Find(l1i, expanded_res_t3, find_info))) l1)), l3 @ l2)
  | ResE(b, t) ->
      let (f,l) = always_some t (expand_term t) in
      Some((fun l -> Terms.oproc_from_desc (Restr(b, f l))), l)
  | EventE(t) ->
      (* The event is expanded to a process that stops just after the event.
	 Events in terms are used only in the RHS of equivalences, and 
	 one includes their probability of execution in the probability of
	 breaking the protocol. *)
      let (f1, l1) = always_some t (expand_term t) in
      Some((fun l -> 
	f1 (List.map (fun ti -> Terms.oproc_from_desc (EventP(ti,Terms.abort_proc))) l1)), [])

and expand_term_list = function
  [] -> None
| (a::l) -> 
    let aex = expand_term a in
    let lex = expand_term_list l in
    match pairing_expand a l aex lex with
      None -> None
    | Some(f,l') -> Some(f, List.map (fun (a,l'') -> a::l'') l')

and expand_pat = function
    PatVar b -> None
  | PatTuple (ft,l) -> 
      begin
	match expand_pat_list l with
	  None -> None
	| Some(f,l') -> Some(f, List.map (fun li -> PatTuple (ft,li)) l')
      end 
  | PatEqual t -> 
      begin
	match expand_term t with
	  None -> None
	| Some(f,l) -> Some (f, List.map (fun ti -> PatEqual ti) l)
      end

and expand_pat_list = function
  [] -> None
| (a::l) -> 
    let aex = expand_pat a in
    let lex = expand_pat_list l in
    match pairing_expand a l aex lex with
      None -> None
    | Some(f,l') -> Some(f, List.map (fun (a,l'') -> a::l'') l')


(* Expand process to process *)

let rec expand_process cur_array p = 
  match p.i_desc with
    Nil -> Terms.iproc_from_desc Nil
  | Par(p1,p2) -> Terms.iproc_from_desc  (Par(expand_process cur_array p1,
		      expand_process cur_array p2))
  | Repl(b,p) -> Terms.iproc_from_desc (Repl(b, expand_process ((Terms.term_from_repl_index b)::cur_array) p))
  | Input((c,tl),pat,p) ->
      List.iter check_no_ifletfind tl;
      begin
	let patex = expand_pat pat in
	match patex with
	  None -> 
            Terms.iproc_from_desc (Input((c,tl),pat, expand_oprocess cur_array p))
	| Some(f,l) -> 
	    changed := true;
	    let b = Terms.create_binder "patv" (Terms.new_vname()) 
		Settings.t_bitstring cur_array
	    in
	    Terms.iproc_from_desc (Input((c,tl),PatVar b, 
	      f (List.map (fun pati -> Terms.oproc_from_desc 
                  (Let(pati, Terms.term_from_binder b,
		       expand_oprocess cur_array p, Terms.yield_proc))) l)))
      end

and expand_oprocess cur_array p =
  match p.p_desc with 
    Yield -> Terms.yield_proc
  | Abort -> Terms.abort_proc
  | Restr(b,p) -> Terms.oproc_from_desc (Restr(b, expand_oprocess cur_array p))
  | Test(t,p1,p2) ->
	begin
	  match expand_term t with
	    None -> Terms.oproc_from_desc (Test(t,expand_oprocess cur_array p1,
			 expand_oprocess cur_array p2))
	  | Some(f,l) ->
	      changed := true;
	      f (List.map (fun ti ->
                   (* Some trivial simplifications *)
                   if Terms.is_true ti then expand_oprocess cur_array p1 else
                   if Terms.is_false ti then expand_oprocess cur_array p2 else
		   Terms.oproc_from_desc (Test(ti,expand_oprocess cur_array p1,
		        expand_oprocess cur_array p2))) l)
	end
  | Find(l0, p2, find_info) ->
      let rec expand_find_list next_f = function
	  [] -> next_f []
	| ((bl, def_list, t, p1)::rest_l) ->
	    List.iter check_no_ifletfind_br def_list;
	    let ex1 = expand_term t in
	    let ex1 = 
	      match ex1 with
		None -> None
	      | Some(f,l) ->
                  if bl != [] || def_list != [] then
                    Some(extract_elem, [final_pseudo_expand t])
                  else
                    ex1
		  (*let fNil = f (List.map (fun _ -> Terms.yield_proc) l) in
		  if List.exists (fun b -> Terms.refers_to_oprocess b fNil) bl || [fNil refers to variables in def_list] || [fNil contains new and bl != [] ] then
		    Some(extract_elem, [final_pseudo_expand t]) (* We cannot move the condition of the find outside, because it refers to variables defined in the find. In this case, we leave the term with if/let/find/res in it. *)
                  else
                    ex1*)
	    in
	    match ex1 with
	      None -> 
		expand_find_list (fun rest_l' ->
		  next_f ((bl, def_list, t, expand_oprocess cur_array p1)::rest_l')) rest_l
	    | Some(f,l) ->
		changed := true;
		f (List.map (fun ti -> expand_find_list (fun rest_l' ->
		  next_f ((bl, def_list, ti, expand_oprocess cur_array p1)::rest_l')) rest_l) l)
      in
      expand_find_list (fun l0' -> Terms.oproc_from_desc (Find(l0', expand_oprocess cur_array p2, find_info))) l0
  | Output((c,tl),t2,p) ->
      begin
	let tlex = expand_term_list tl in
	let t2ex = expand_term t2 in
	match pairing_expand tl t2 tlex t2ex with
	  None -> Terms.oproc_from_desc (Output((c,tl),t2, expand_process cur_array p))
	| Some(f,l) -> 
	    changed := true;
	    f (List.map (fun (t1i,t2i) -> Terms.oproc_from_desc (Output((c,t1i),t2i,expand_process cur_array p))) l)
      end
  | Let(pat,t,p1,p2) ->
      begin
	let tex = expand_term t in
	let patex = expand_pat pat in
	match pairing_expand t pat tex patex with
	  None -> Terms.oproc_from_desc (Let(pat, t, expand_oprocess cur_array p1, 
		      expand_oprocess cur_array p2))
	| Some(f,l) -> 
	    changed := true;
	    f (List.map (fun (ti,pati) -> Terms.oproc_from_desc (Let(pati,ti,expand_oprocess cur_array p1, expand_oprocess cur_array p2))) l)
      end
  | EventP(t,p) ->
      begin
	let tex = expand_term t in
	match tex with
	  None -> Terms.oproc_from_desc (EventP(t, expand_oprocess cur_array p))
	| Some(f,l) ->
	    changed := true;
	    f (List.map (fun ti -> Terms.oproc_from_desc (EventP(ti, expand_oprocess cur_array p))) l)
      end
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

(* Main function for expansion of if and find
   Call auto_sa_rename after expand_process, so that occurrences have distinct 
   numbers, facts associated with nodes are emptied, and variables defined in
   conditions of find have a single definition. 
   Expansion is called only when there is no advice pending, so we can simply 
   ignore the list of done SArenamings.
*)

let expand_process g =
  let tmp_changed = !changed in
  let p' = expand_process [] g.proc in
  if !changed then 
    let (g', proba, ins) = auto_sa_rename { proc = p'; game_number = -1 } in
    (g', proba, ins @ [DExpandIfFind])
  else
    begin
      changed := tmp_changed;
      auto_sa_rename g
    end
    
(****************************************************************************)

(* When variable x is assigned at several places, 
   rename variable x into x1, ..., xn and duplicate code if necessary 

This transformation assumes that LetE/FindE/TestE/ResE occur only in 
conditions of find, which is guaranteed after expansion.
(In fact, Terms.copy_process and sa_process support them in all terms, 
although that's not necessary.
ren_out_process and Terms.build_compatible_defs support 
LetE/FindE/TestE/ResE only in conditions of find.
Otherwise, ren_out_process should call ren_out_find_cond for each term,
and not only for find conditions.)
It also assumes that variables defined in conditions of find
have no array references and do not occur in queries.
*)

(* - First pass: look for assignments to x, give a new name to each of them,
   and rename the in-scope references to x with current session identifiers *)
   
let image_name_list = ref []

(* NOTE: when TestE/LetE/FindE/ResE are forbidden, sa_term is the identity *)
let rec sa_term b0 t =
  Terms.build_term t 
     (match t.t_desc with
	Var(b,l) ->
          Var(b, List.map (sa_term b0) l)
      | ReplIndex(b) -> ReplIndex(b)
      | FunApp(f,l) ->
          FunApp(f, List.map (sa_term b0) l)
      | TestE(t1,t2,t3) ->
          TestE(sa_term b0 t1,
		sa_term b0 t2,
		sa_term b0 t3)
      | FindE(l0,t3,find_info) ->
	  let l0' = List.map (fun (bl, def_list, t1, t2) ->
            if List.exists (fun (b,_) -> b == b0) bl then
              let b0' = Terms.new_binder b0 in
              image_name_list := b0' :: (!image_name_list);
              (List.map (fun (b,b') -> ((if b == b0 then b0' else b), b')) bl,
               def_list,
               (* b0 cannot be defined in t1, because the array arguments
                  of b0 are the current indices at the find, which are fewer
                  than the current indices in t1, since the latter include the
                  non-empty list bl *)
               t1,
               Terms.copy_term (Terms.Rename(b0.args_at_creation, b0, b0')) t2)
            else
	      (* def_list does not contain if/let/find/res so
		 no change in it *)
              (bl, def_list, 
               sa_term b0 t1,
               sa_term b0 t2)) l0
	  in
	  FindE(l0', sa_term b0 t3, find_info)
      |	LetE(pat, t1, t2, topt) ->
	  let target_name = ref b0 in
	  let pat' = sa_pat b0 target_name pat in
	  if !target_name == b0 then
	  (* b0 not defined in pat *)
	    LetE(pat', t1, 
		sa_term b0 t2, 
		match topt with
		  Some t3 -> Some (sa_term b0 t3)
		| None -> None)
	  else
	    (* b0 defined in pat and renamed to !target_name *)
	    LetE(pat', t1, 
		Terms.copy_term (Terms.Rename(b0.args_at_creation, b0, !target_name)) t2, 
		match topt with
		  Some t3 -> Some (sa_term b0 t3)
		| None -> None)
      |	ResE(b,t) ->
	  if b == b0 then
	    let b0' = Terms.new_binder b0 in
	    image_name_list := b0' :: (!image_name_list);
	    ResE(b0', Terms.copy_term (Terms.Rename(b0.args_at_creation, b0, b0')) t)
	  else
	    ResE(b, sa_term b0 t)
      |	EventE(t) ->
          Parsing_helper.internal_error "Event should have been expanded")

and sa_pat b0 target_name = function
    PatVar b -> 
      if b == b0 then
	let b0' = Terms.new_binder b0 in
	image_name_list := b0' :: (!image_name_list);
	if (!target_name) != b0 then 
	  Parsing_helper.internal_error "target name already assigned in sa_pat";
	target_name := b0';
	PatVar b0'
      else
	PatVar b
  | PatTuple (f,l) -> PatTuple (f,List.map (sa_pat b0 target_name) l)
  | PatEqual t -> PatEqual (sa_term b0 t)

let rec sa_process b0 p = 
  Terms.iproc_from_desc (
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) -> Par(sa_process b0 p1,
		      sa_process b0 p2)
  | Repl(b,p) ->
      Repl(b, sa_process b0 p)
  | Input((c,tl),pat,p) ->
      let target_name = ref b0 in
      let pat' = sa_pat b0 target_name pat in
      if !target_name == b0 then
	(* b0 not defined in pat *)
	Input((c,List.map (sa_term b0) tl), pat', 
	      sa_oprocess b0 p)
      else
	(* b0 defined in pat and renamed to !target_name *)
	Input((c,List.map (sa_term b0) tl), pat', 
	      Terms.copy_oprocess (Terms.Rename(b0.args_at_creation, b0, !target_name)) p))

and sa_oprocess b0 p = 
  Terms.oproc_from_desc (
  match p.p_desc with
    Yield -> Yield
  | Abort -> Abort
  | Restr(b,p) ->
      if b == b0 then
	let b0' = Terms.new_binder b0 in
	image_name_list := b0' :: (!image_name_list);
	Restr(b0', Terms.copy_oprocess (Terms.Rename(b0.args_at_creation, b0, b0')) p)
      else
	Restr(b, sa_oprocess b0 p)
  | Test(t,p1,p2) ->
      Test(sa_term b0 t, 
	   sa_oprocess b0 p1,
	   sa_oprocess b0 p2)
  | Find(l0, p2, find_info) -> 
      let l0' = List.map (fun (bl, def_list, t, p1) ->
        if List.exists (fun (b,_) -> b == b0) bl then
	  let b0' = Terms.new_binder b0 in
	  image_name_list := b0' :: (!image_name_list);
	  (List.map (fun (b,b') -> ((if b == b0 then b0' else b), b')) bl, 
	   def_list,
               (* b0 cannot be defined in t, because the array arguments
                  of b0 are the current indices at the find, which are fewer
                  than the current indices in t, since the latter include the
                  non-empty list bl *)
	   t,
	   Terms.copy_oprocess (Terms.Rename(b0.args_at_creation, b0, b0')) p1)
	else
	  (* def_list does not contain if/let/find/res so
	     no change in it *)
	  (bl, def_list, 
	   sa_term b0 t,
	   sa_oprocess b0 p1)) l0
      in
      Find(l0', sa_oprocess b0 p2, find_info)
  | Output((c,tl),t2,p) ->
      Output((c, List.map (sa_term b0) tl), 
	     sa_term b0 t2,
	     sa_process b0 p)
  | Let(pat,t,p1,p2) ->
      let target_name = ref b0 in
      let pat' = sa_pat b0 target_name pat in
      if !target_name == b0 then
	(* b0 not defined in pat *)
	Let(pat', t, 
	    sa_oprocess b0 p1, 
	    sa_oprocess b0 p2)
      else
	(* b0 defined in pat and renamed to !target_name *)
	Let(pat', t, 
	    Terms.copy_oprocess (Terms.Rename(b0.args_at_creation, b0, !target_name)) p1, 
	    sa_oprocess b0 p2)
  | EventP(t,p) ->
      EventP(sa_term b0 t,
	     sa_oprocess b0 p)
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"
  )
(* - Second pass: empty b.def 
	          compute new value of b.def
     See terms.ml *)
      
(* - Third pass: rename the out-scope array references to x
   A find ... suchthat defined(M1...Mn) should be split if 
   x[...] is a subterm of M1...Mn 
      x[...] becomes x1[...], ..., xn[...] in the different cases

   If due to other defined conditions, only some of the xi can be
   defined then consider only these xi cases: collect all "defined"
   conditions up to the current point. On the other hand, collect the
   variables defined in the same branch as xi. The case xi needs to be
   considered only when all "defined" conditions up to the current
   point that have session identifiers prefix or suffix of those of xi
   are variables defined in the same branch as xi.  Use
   compatible_defs to test whether two variables are in the same
   branch.  
*)

let proba_accu = ref []

let add_proba_sarename bl find_info =
  (* If find_info = Unique or bl = [], there is a single possible
     choice in the current branch, so SArename will not change the
     order of the elements in the list of successful find choices.
     If find_info != Unique and bl != [], SArename may reorder the
     elements in the list of successful find choices. If the
     distribution is not exactly uniform, this may lead to a change
     of probability EpsFind of these choices, for each execution
     of the find. *)
  if find_info != Unique then
    begin
      match bl with
	[] -> ()
      |	((b,_)::_) ->
	  if (!Settings.ignore_small_times) <= 0 then
	    proba_accu := 
	       (SetProba (Polynom.p_mul ((Proba.card_index b), EpsFind)))
	       :: (!proba_accu)
    end

let rec implies_def_subterm b0 accu (b,l) =
  if (b == b0) && 
    (* Do not add duplicates in accu *)
    (not (List.exists (fun l' -> List.for_all2 Terms.equal_terms l l') (!accu))) then
    accu := l :: (!accu);
  List.iter (implies_def_term b0 accu) l

and implies_def_term b0 accu t =
  match t.t_desc with
    Var(b,l) -> implies_def_subterm b0 accu (b,l)
  | ReplIndex _ -> ()
  | FunApp(f,l) -> List.iter (implies_def_term b0 accu) l
  | _ -> Parsing_helper.internal_error "if/let/find forbidden in defined conditions of find"
    
let implies_def b0 def_list =
  let accu = ref [] in
  List.iter (implies_def_subterm b0 accu) def_list;
  !accu

let rec rename_find p1rename b0 image_list args accu ((bl,def_list,t,p1) as p) =
  match image_list with
    [] -> accu
  | (b::l) ->
      let accu' = 
	if List.for_all (function (b', args') -> (b' == b0) || (Terms.is_compatible (b,args) (b',args'))) def_list then
	  let def_list' = List.map (Terms.copy_binder (Terms.Rename(args, b0, b))) def_list in
	  let def_list'' = 
	    if not (List.exists (fun (b',l') -> (b' == b0) && (List.for_all2 Terms.equal_terms l' args)) def_list) then
	      (b,args)::def_list'
	    else
	      def_list'
	  in
          (* In p1, args uses the variables in bl, instead of the replication indices used in def_list/t *)
          let args' = List.map (Terms.subst (List.map snd bl) (List.map (fun (b,_) -> Terms.term_from_binder b) bl)) args in
	  (bl, def_list'',
	   Terms.copy_term (Terms.Rename(args, b0, b)) t, 
	   p1rename (Terms.Rename(args', b0, b)) p1) :: accu
	else
          accu
      in
      rename_find p1rename b0 l args accu' p

let rec rename_finds p1rename b0 image_list args_list accu p =
  match args_list with
    [] ->  accu 
  | (args::args_list) ->
      rename_finds p1rename b0 image_list args_list (rename_find p1rename b0 image_list args accu p) p

let rec ren_out_find_cond b0 t = 
  Terms.build_term t (
  match t.t_desc with
    Var(b,l) -> Var(b, List.map (ren_out_find_cond b0) l)
  | ReplIndex(b) -> ReplIndex(b)
  | FunApp(f,l) -> FunApp(f, List.map (ren_out_find_cond b0) l)
  | ResE(b,p) -> ResE(b, ren_out_find_cond b0 p)
  | TestE(t,p1,p2) -> 
      TestE(t,
	   ren_out_find_cond b0 p1,
	   ren_out_find_cond b0 p2)
  | FindE(l0, p2, find_info) ->
      let rec ren_out_list = function
	  [] -> []
	| (bl,def_list, t, p1)::l1 ->
	    let l1' = ren_out_list l1 in
	    let p1' = ren_out_find_cond b0 p1 in
            let t' = ren_out_find_cond b0 t in
	    let to_rename = implies_def b0 def_list in
            (* renamings of b0 *)	
	    if to_rename = [] then
	      (bl, def_list, t', p1')::l1'
	    else
	      begin
		add_proba_sarename bl find_info;
		rename_finds Terms.copy_term b0 (!image_name_list) to_rename l1' (bl, def_list, t', p1')
	      end
      in
      FindE(ren_out_list l0, ren_out_find_cond b0 p2, find_info)
  | LetE(pat,t,p1,topt) ->
      begin
      LetE(pat, t, ren_out_find_cond b0 p1,
	  match topt with
            None -> None
          | Some p2 -> Some (ren_out_find_cond b0 p2))
      end
  | EventE(t) ->
      Parsing_helper.internal_error "Event should have been expanded")


let rec ren_out_process b0 p = 
  Terms.iproc_from_desc (
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) -> Par(ren_out_process b0 p1,
		      ren_out_process b0 p2)
  | Repl(b,p) -> Repl(b, ren_out_process b0 p)
  | Input((c,tl),pat,p) ->
      Input((c, tl), pat, ren_out_oprocess b0 p))

and ren_out_oprocess b0 p = 
  Terms.oproc_from_desc (
  match p.p_desc with
    Yield -> Yield
  | Abort -> Abort
  | Restr(b,p) -> Restr(b, ren_out_oprocess b0 p)
  | Test(t,p1,p2) -> 
      Test(t,
	   ren_out_oprocess b0 p1,
	   ren_out_oprocess b0 p2)
  | Find(l0, p2, find_info) ->
      let rec ren_out_list = function
	  [] -> []
	| (bl,def_list, t, p1)::l1 ->
	    let l1' = ren_out_list l1 in
	    let p1' = ren_out_oprocess b0 p1 in
            let t' = ren_out_find_cond b0 t in
	    let to_rename = implies_def b0 def_list in
            (* renamings of b0 *)	
	    if to_rename = [] then
	      (bl, def_list, t', p1')::l1'
	    else
	      begin
		add_proba_sarename bl find_info;
		rename_finds Terms.copy_oprocess b0 (!image_name_list) to_rename l1' (bl, def_list, t', p1')
	      end
      in
      Find(ren_out_list l0, ren_out_oprocess b0 p2, find_info)
  | Output((c,tl),t2,p) ->
      Output((c, tl),t2,ren_out_process b0 p)
  | Let(pat,t,p1,p2) ->
      Let(pat, t, ren_out_oprocess b0 p1,
	  ren_out_oprocess b0 p2)
  | EventP(t,p) ->
      EventP(t, ren_out_oprocess b0 p)
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"
  )

(* Main function for variable renaming into sa *)

let sa_rename b0 g =
  let p = g.proc in
  (* cannot rename if b0 occurs in queries! 
     TO DO in fact, I could replace b0 = M with b' = M; b0 = b',
     replace all references to b0 with b', and apply sa_rename on b' *)
  if occurs_in_queries b0 then (g, [], []) else
  begin
    image_name_list := [];
    proba_accu := [];
    let p' = sa_process b0 p in
    if List.length (!image_name_list) >= 2 then
      begin
	changed := true;
	Terms.build_def_process None p';
	Terms.build_compatible_defs p';
	let p'' = ren_out_process b0 p' in
	let new_names = !image_name_list in
	let probaSArename = !proba_accu in
	image_name_list := [];
	proba_accu := [];
	Terms.empty_comp_process p';
	let (g', proba, renames) = auto_sa_rename { proc = p''; game_number = -1 } in      
	(g', proba @ probaSArename, renames @ [DSArenaming(b0,new_names)])
      end
    else
      begin
	image_name_list := [];
	proba_accu := [];
	(g, [], [])
      end
  end

(****************************************************************************)

(* Remove assignments 

This transformation assumes that LetE/FindE/TestE/ResE occur only in 
conditions of find, which is guaranteed after expansion.
(In fact, it supports them as well in channel names, conditions of tests, events,
outputs, although that's not necessary.)
It also assumes (and checks) that variables defined in conditions of find
have no array references and do not occur in queries.

Note that it is important that there are no LetE or FindE in let
expressions or in patterns! Otherwise, we should verify for each
expression that we copy that it does not contain LetE or FindE: if we
copy a LetE or FindE, we may break the invariant that each variable is
assigned at most once.

Be careful of variables defined at several places!  *)

let replacement_def_list = ref []
(* List of correspondences (b,b'), b = old binder, b' = new binder,
   for defined conditions. When b is used only in "defined" conditions,
   we try to find another binder b' defined in the same cases, so that
   we can remove the definition of b completely. *)

let done_transfos = ref []

(* Function for assignment expansion for terms *)

let expand_assign_term let_t remove_set
    rec_simplif pat t p1 topt =
  match pat with
    PatEqual t' -> 
      changed := true;
      done_transfos := (DLetESimplifyPattern(let_t, pat, DEqTest)) :: (!done_transfos);
      Terms.build_term_type p1.t_type (TestE(Terms.make_equal t t', rec_simplif p1, 
	    match topt with
	      None -> Parsing_helper.internal_error "Missing else part of let"
	    | Some p2 -> rec_simplif p2))
  | PatTuple (f,l) -> 
      (* try to split *)
      begin
	try 
	  let res = rec_simplif
	      (Terms.put_lets_term l (Terms.split_term f t) p1 topt)
	  in
	  changed := true;
          done_transfos := (DLetESimplifyPattern(let_t, pat, DExpandTuple)) :: (!done_transfos);
	  res
	with Not_found -> 
	  Terms.build_term_type p1.t_type (LetE(pat, t, rec_simplif p1, match topt with 
	    None -> None
	  | Some p2 -> Some (rec_simplif p2)))
	| Terms.Impossible -> 
	    changed := true;
            done_transfos := (DLetESimplifyPattern(let_t, pat, DImpossibleTuple)) :: (!done_transfos);
	    match topt with
	      None -> Parsing_helper.internal_error "Missing else part of let"
	    | Some p2 -> rec_simplif p2
      end
  | PatVar b ->
      if has_array_ref b then
	Parsing_helper.internal_error "Variables defined in conditions of find should not have array references and should not occur in queries.";
      if not (check_no_ifletfindres t) then
	Parsing_helper.internal_error "If, find, let, and new should not occur in expand_assign";
      let put_link() =
	if Terms.refers_to b t then
	  (* Cannot replace cyclic assignment *)
	  Terms.build_term_type p1.t_type (LetE(pat, t, rec_simplif p1, None))
	else 
          begin
                (* copy_term exactly replaces 
                   b[b.args_at_creation] with t, without changing any other variable.
                   (Changing other variables led to a bug, because it replaced
                   v[v.args_at_creation] with its value in a "defined" condition,
                   even when v is defined less often than its value.) *)
            let p1' = Terms.copy_term (Terms.OneSubst(b,t,ref false)) p1 in
	    changed := true;
            done_transfos := (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: (!done_transfos);
	    rec_simplif p1'
          end
      in
      if (not (Terms.refers_to b p1)) then
	begin
	  (* Variable is useless *)
	  changed := true;
          done_transfos := (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: (!done_transfos);
	  rec_simplif p1
	end
      else
	match remove_set with
	  All -> put_link()
	| OneBinder b0 when b == b0 -> put_link()
	| _ -> 
	    match t.t_desc with
	      Var _ | ReplIndex _ when !Settings.expand_letxy -> 
		put_link()
	    | _ ->
		Terms.build_term_type p1.t_type (LetE(pat, t, rec_simplif p1, None))

(* Function for assignment expansion for processes *)

let candidate_for_rem_assign remove_set b t p =
  if not (Terms.refers_to_process_nodef b p || b.array_ref || occurs_in_queries b) then
    true
  else
  match remove_set with
    All -> true
  | OneBinder b0 when b == b0 -> true
  | _ -> 
      match t.t_desc with
	Var _ | ReplIndex _ when !Settings.expand_letxy -> true
      | _ -> false

let rec find_replacement_for_def remove_set b p =
  match p.p_desc with
    Yield | Abort -> raise Not_found
  | Restr(b',p') ->
      if b' != b && b'.count_def == 1 then b' else find_replacement_for_def remove_set b p'
  | Let(PatVar b', t, p', _) ->
      if b' != b && b'.count_def == 1 && not (candidate_for_rem_assign remove_set b' t p') then b' else 
      find_replacement_for_def remove_set b p'
  | EventP(_,p') -> find_replacement_for_def remove_set b p'
  | Test _ | Find _ | Output _ | Let _ -> raise Not_found
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"


let expand_assign let_p remove_set above_proc rec_simplif pat t p1 p2 =
  match pat with
    PatEqual t' -> 
      changed := true;
      done_transfos := (DLetSimplifyPattern(let_p, pat, DEqTest)) :: (!done_transfos);
      Terms.oproc_from_desc (Test(Terms.make_equal t t', rec_simplif p1 p1, rec_simplif p2 p2))
  | PatTuple (f,l) -> 
      (* try to split *)
      begin
	try 
          let p' = (Terms.put_lets l (Terms.split_term f t) p1 p2) in
	  let res = rec_simplif p' p' in
          done_transfos := (DLetSimplifyPattern(let_p, pat, DExpandTuple)) :: (!done_transfos);
	  changed := true;
	  res
	with Not_found -> 
	  Terms.oproc_from_desc (Let(pat, t, rec_simplif p1 p1, rec_simplif p2 p2))
	| Terms.Impossible -> 
            done_transfos := (DLetSimplifyPattern(let_p, pat, DImpossibleTuple)) :: (!done_transfos);
	    changed := true;
	    rec_simplif p2 p2
      end
  | PatVar b ->
      let put_link do_advise =
	if Terms.refers_to b t then
	  (* Cannot replace cyclic assignment *)
	  Terms.oproc_from_desc (Let(pat, t, rec_simplif above_proc p1, Terms.yield_proc))
	else 
	  match b.def with
	    [] -> Parsing_helper.internal_error "Should have at least one definition"
	  | [d] -> (* There is a single definition *)
	      begin
		(* All references to binder b will be removed *)
		Terms.link b (TLink t);
		if occurs_in_queries b then
		  (* if b occurs in queries then leave as it is *)
		  Terms.oproc_from_desc (Let(pat, t, rec_simplif above_proc p1, Terms.yield_proc))
		else if b.root_def_array_ref || b.root_def_std_ref || b.array_ref then
		  (* We may keep calls to defined(b), so keep a definition of b
		     but its value does not matter *)
                  try
                    (* Try to remove the definition of b completely, by replacing
                       defined(b[...]) with defined(b'[...]) *)
                    let b' = find_replacement_for_def remove_set b above_proc in
                    changed := true;
                    done_transfos := (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: (!done_transfos);
                    replacement_def_list := (b, b') :: (!replacement_def_list);
                    rec_simplif above_proc p1
                  with Not_found ->
		    let t' = Terms.cst_for_type t.t_type in
		    if not (Terms.equal_terms t t') then 
                      begin
                        done_transfos := (DRemoveAssign(b, DKeepDefPoint, DRemoveAll)) :: (!done_transfos);
                        changed := true
                      end;
		    Terms.oproc_from_desc (Let(pat,  t', rec_simplif above_proc p1, Terms.yield_proc))
		else
		  begin
                    (* b will completely disappear *)
                    changed := true;
                    done_transfos := (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: (!done_transfos);
		    rec_simplif above_proc p1
		  end
	      end
	  | _ -> (* There are several definitions.
		    I can remove in-scope requests, but out-of-scope array accesses will remain *)
              begin
                (* copy_oprocess exactly replaces 
                   b[b.args_at_creation] with t, without changing any other variable.
                   (Changing other variables led to a bug, because it replaced
                   v[v.args_at_creation] with its value in a "defined" condition,
                   even when v is defined less often than its value.) *)
                let copy_changed = ref false in
                let p1' = Terms.copy_oprocess (Terms.OneSubst(b,t,copy_changed)) p1 in
                let subst_def = !copy_changed in (* Set to true if an occurrence of b has really been substituted *)
                changed := (!changed) || subst_def;
                let p1'' = rec_simplif above_proc p1' in
                if b.array_ref then
		  begin
                    (* suggest to use "sa_rename b" before removing assignments *)
		    if do_advise then advise := Terms.add_eq (SArenaming b) (!advise);
                    (* Keep the definition so that out-of-scope array accesses are correct *)
                    if subst_def then
                      done_transfos := (DRemoveAssign(b, DKeepDef, DRemoveNonArray)) :: (!done_transfos);
                    Terms.oproc_from_desc (Let(pat, t, p1'', Terms.yield_proc))
		  end
		else if occurs_in_queries b then
                  begin
		    (* Cannot change definition if b occurs in queries *)
                    if subst_def then
                      done_transfos := (DRemoveAssign(b, DKeepDef, DRemoveAll)) :: (!done_transfos);
 		    Terms.oproc_from_desc (Let(pat, t, p1'', Terms.yield_proc))
                  end
                else if b.root_def_array_ref || b.root_def_std_ref then
		  (* We may keep calls to defined(b), so keep a definition of b
		     but its value does not matter *)
		  let t' = Terms.cst_for_type t.t_type in
		  if not (Terms.equal_terms t t') then 
                    begin
                      done_transfos := (DRemoveAssign(b, DKeepDefPoint, DRemoveAll)) :: (!done_transfos);
                      changed := true
                    end
                  else if subst_def then
                    done_transfos := (DRemoveAssign(b, DKeepDefPoint, DRemoveAll)) :: (!done_transfos);
		  Terms.oproc_from_desc (Let(pat, t', p1'', Terms.yield_proc))
		else
                  (* b will completely disappear *)
		  begin
                    done_transfos := (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: (!done_transfos);
		    changed := true;
		    p1''
		  end
              end
      in
      if (check_no_ifletfindres t) then
	begin
	  if not (Terms.refers_to_process_nodef b p1 || b.array_ref || occurs_in_queries b) then
	    begin
	      (* Value of the variable is useless *)
	      if not (b.root_def_std_ref || b.root_def_array_ref) then
	        (* Variable is useless *)
		begin
		  changed := true;
                  done_transfos := (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: (!done_transfos);
		  rec_simplif above_proc p1
		end
	      else
		begin
	          (* We may keep calls to defined(b), so keep a definition of b
		     but its value does not matter *)
                  try
                    (* Try to remove the definition of b completely, by replacing
                       defined(b[...]) with defined(b'[...]) *)
                    if b.count_def > 1 then raise Not_found;
                    let b' = find_replacement_for_def remove_set b above_proc in
                    changed := true;
                    done_transfos := (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: (!done_transfos);
                    replacement_def_list := (b, b') :: (!replacement_def_list);
                    rec_simplif above_proc p1
                  with Not_found ->
		    let t' = Terms.cst_for_type t.t_type in
		    if not (Terms.equal_terms t t') then 
                      begin
                        done_transfos := (DRemoveAssign(b, DKeepDefPoint, DRemoveAll)) :: (!done_transfos);
                        changed := true
                      end;
		    Terms.oproc_from_desc (Let(pat, t', rec_simplif above_proc p1, Terms.yield_proc))
		end
	    end
	  else
	    match remove_set with
	      All -> put_link true
	    | OneBinder b0 when b == b0 -> put_link true
	    | _ -> 
		match t.t_desc with
		  Var _ | ReplIndex _ when !Settings.expand_letxy -> 
	            (* Always expand assignments let x = x' and let x = constant, if possible,
                       but don't do a lot of work for that, so don't apply advises *)
		    put_link false
		| _ ->
		    Terms.oproc_from_desc (Let(pat, t, rec_simplif above_proc p1, Terms.yield_proc))
	end
      else
	Parsing_helper.internal_error "If, find, let, and new should not occur in expand_assign"

let several_def b =
  match b.def with
    [] | [_] -> false
  | _::_::_ -> true

let rec remove_assignments_term remove_set t =
  match t.t_desc with
    Var(b,l) ->
      Terms.build_term2 t (Var(b, List.map (remove_assignments_term remove_set) l))
  | ReplIndex i -> Terms.build_term2 t (ReplIndex i)
  | FunApp(f,l) ->
      Terms.build_term2 t (FunApp(f, List.map (remove_assignments_term remove_set) l))
  | TestE(t1,t2,t3) ->
      Terms.build_term2 t (TestE(remove_assignments_term remove_set t1,
		       remove_assignments_term remove_set t2,
		       remove_assignments_term remove_set t3))
  | FindE(l0, t3, find_info) ->
      Terms.build_term2 t (FindE(List.map (fun (bl, def_list, t1, t2) ->
	                 (bl, List.map (remove_assignments_br remove_set) def_list,
			  remove_assignments_term remove_set t1,
			  remove_assignments_term remove_set t2)) l0,
		       remove_assignments_term remove_set t3, find_info))
  | LetE(pat,t1,t2,topt) ->
      expand_assign_term t remove_set
	(remove_assignments_term remove_set)
	pat t1 t2 topt
  | ResE(b,t) ->
      if (!Settings.auto_sa_rename) && (several_def b) && (not (has_array_ref b)) then
	begin
	  let b' = Terms.new_binder b in
	  let t' = Terms.copy_term (Terms.Rename(b.args_at_creation, b, b')) t in
	  changed := true;
	  done_sa_rename := (b,b') :: (!done_sa_rename);
	  Terms.build_term2 t' (ResE(b', remove_assignments_term remove_set t'))
	end
      else
	Terms.build_term2 t (ResE(b, remove_assignments_term remove_set t))
  | EventE(t) ->
      Parsing_helper.internal_error "Event should have been expanded"

and remove_assignments_br remove_set (b,l) =
  (b, List.map (remove_assignments_term remove_set) l)

let rec remove_assignments_rec remove_set p = 
  Terms.iproc_from_desc (
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) -> 
      Par(remove_assignments_rec remove_set p1,
	  remove_assignments_rec remove_set p2)
  | Repl(b,p) ->
      Repl(b,remove_assignments_rec remove_set p)
  | Input((c,tl),pat,p) ->
      Input((c, List.map (remove_assignments_term remove_set) tl),pat, 
	    remove_assignments_reco remove_set p p))

and remove_assignments_reco remove_set above_proc p =
  match p.p_desc with
    Yield -> Terms.yield_proc
  | Abort -> Terms.abort_proc
  | Restr(b,p) ->
      if (!Settings.auto_sa_rename) && (several_def b) && (not (has_array_ref b)) then
	begin
	  let b' = Terms.new_binder b in
	  let p' = Terms.copy_oprocess (Terms.Rename(b.args_at_creation, b, b')) p in
	  changed := true;
	  done_sa_rename := (b,b') :: (!done_sa_rename);
          (* Allow using b' for testing whether a variable is defined *) 
          b'.count_def <- 1;
          let above_proc' = Terms.oproc_from_desc (Restr(b',p)) in
	  Terms.oproc_from_desc (Restr(b',remove_assignments_reco remove_set above_proc' p'))
	end
      else
	Terms.oproc_from_desc (Restr(b,remove_assignments_reco remove_set above_proc p))
  | Test(t,p1,p2) ->
      Terms.oproc_from_desc (Test(remove_assignments_term remove_set t, 
	   remove_assignments_reco remove_set p1 p1,
	   remove_assignments_reco remove_set p2 p2))
  | Find(l0,p2,find_info) ->
      Terms.oproc_from_desc 
	(Find(List.map (fun (bl,def_list,t,p1) ->
	     (bl, def_list, 
	      remove_assignments_term remove_set t,
	      remove_assignments_reco remove_set p1 p1)) l0,
	   remove_assignments_reco remove_set p2 p2, find_info))
  | Output((c,tl),t2,p) ->
      Terms.oproc_from_desc 
	(Output((c, List.map (remove_assignments_term remove_set) tl), 
		remove_assignments_term remove_set t2,
		remove_assignments_rec remove_set p))
  | Let(pat, t, p1, p2) ->
      let rec_simplif = remove_assignments_reco remove_set in
      expand_assign p remove_set above_proc rec_simplif pat t p1 p2
  | EventP(t,p) ->
      Terms.oproc_from_desc 
	(EventP(remove_assignments_term remove_set t,
		remove_assignments_reco remove_set above_proc p))
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

(* - Main function for assignment removal *)

let remove_assignments remove_set p =
  Terms.build_def_process None p;
  if !Terms.current_bound_vars != [] then
    Parsing_helper.internal_error "bound vars should be cleaned up (transf1)";
  Terms.array_ref_process p;
  replacement_def_list := [];
  (* - First pass: put links; split assignments of tuples if possible *)
  let p' = remove_assignments_rec remove_set p in
  (* - Second pass: copy the process following the links or replacing just one variable.
       Be careful for array references: update the indexes properly  *)
  let p'' = Terms.copy_process (Terms.Links_Vars_Args(!replacement_def_list)) p' in
  Terms.cleanup();
  Terms.cleanup_array_ref();
  replacement_def_list := [];
  p''

let rec remove_assignments_repeat n remove_set p =
  let tmp_changed = !changed in
  changed := false;
  let p' = remove_assignments remove_set p in
  if n != 1 && !changed then
    remove_assignments_repeat (n-1) remove_set p'
  else
    begin
      changed := tmp_changed;
      p'
    end

let rec do_sa_rename = function
    [] -> []
  | ((b,b')::l) ->
      let lb = List.map snd (List.filter (fun (b1,b1') -> b1 == b) l) in
      let lr = do_sa_rename (List.filter (fun (b1,b1') -> b1 != b) l) in
      if Terms.is_restr b then
	(DSArenaming(b, b'::lb))::lr
      else
	(DSArenaming(b, b::b'::lb))::lr

let remove_assignments remove_set g =
  done_sa_rename := [];
  done_transfos := [];
  let r = 
    if remove_set == Minimal then
      remove_assignments_repeat (!Settings.max_iter_removeuselessassign) remove_set g.proc
    else
      remove_assignments remove_set g.proc
  in
  let sa_rename = !done_sa_rename in
  let transfos = !done_transfos in
  done_transfos := [];
  done_sa_rename := [];
  ({ proc = r; game_number = -1 }, [], (do_sa_rename sa_rename) @ transfos)

(**********************************************************************)

(* Move new and let: 
   (1) when a restriction has several uses under different
   branches of if/find, move it down under if/find.  It will be later
   SA renamed, which can allow to distinguish cases easily.
   (2) when a variable defined by let has no array reference and is used only in
   one branch of a if/let/find, we move it under the if/let/find to reduce
   the number of cases in which it is computed.
  *)

let beneficial = ref false

let rec move_a_new b p =
  Terms.iproc_from_desc (
  match p.i_desc with 
    Nil -> 
      changed := true;
      Nil
  | Par(p1,p2) ->
      let r1 = Terms.refers_to_process b p1 in
      let r2 = Terms.refers_to_process b p2 in
      if r1 && r2 then
	raise Not_found
      else 
	begin
	  changed := true;
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
      changed := true;
      Restr(b', move_a_newo array_ref b p)
  | Test(t,p1,p2) ->
      if Terms.refers_to b t then
	Restr(b, Terms.oproc_from_desc (Test(t,p1,p2)))
      else
	begin
	  changed:= true;
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
	  changed := true;
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
	    changed := true;
	    Output((c,tl), t2, p')
	  with Not_found ->
	    Restr(b, Terms.oproc_from_desc (Output((c,tl),t2,p)))
	end
  | Let(pat, t, p1, p2) ->
      if (Terms.refers_to b t) || (Terms.refers_to_pat b pat) then
	Restr(b, Terms.oproc_from_desc (Let(pat, t, p1, p2)))
      else
	begin
	  changed := true;
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
	  changed := true;
	  EventP(t, move_a_newo array_ref b p)
	end
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"
  )

let rec move_a_let (b,t0) p = 
  Terms.iproc_from_desc (
  match p.i_desc with
    Nil -> 
      changed := true;
      Nil
  | Par(p1,p2) ->
      let r1 = Terms.refers_to_process b p1 in
      let r2 = Terms.refers_to_process b p2 in
      if r1 && r2 then
	raise Not_found
      else 
	begin
	  changed := true;
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
      changed := true;
      Restr(b', move_a_leto (b,t0) p)
  | Test(t,p1,p2) ->
      let r1 = Terms.refers_to_oprocess b p1 in
      let r2 = Terms.refers_to_oprocess b p2 in
      if (Terms.refers_to b t) || (r1 && r2) then
	Let(PatVar b, t0, Terms.oproc_from_desc (Test(t,p1,p2)), Terms.yield_proc)
      else
	begin
	  changed:= true;
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
	  changed := true;
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
	    changed := true;
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
	  changed := true;
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
	  changed := true;
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
      not (has_array_ref b)
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
      let array_ref = has_array_ref b in
      if (not (do_move_new move_set array_ref b)) then
	Terms.oproc_from_desc (Restr(b, move_new_let_reco move_set p))
      else
	let p' = move_new_let_reco move_set p in
	let tmp_changed = !changed in
	changed := false;
	beneficial := false;
	let p'' = move_a_newo array_ref b p' in
	if (!beneficial) || (match move_set with MOneBinder _ -> true | _ -> false) then
	  begin
	    changed := (!changed) || tmp_changed;
	    done_transfos := (DMoveNew b) :: (!done_transfos);
	    p''
	  end
	else
	  begin
	    (* Don't do a move all/noarrayref if it is not beneficial *)
	    changed := tmp_changed;
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
	    let tmp_changed = !changed in
	    changed := false;
	    beneficial := false;
	    let p1'' = move_a_leto (b,t) p1' in
	    if (!beneficial) || (match move_set with MOneBinder _ -> true | _ -> false) then
	      begin
		changed := (!changed) || tmp_changed;
		done_transfos := (DMoveLet b) :: (!done_transfos);
		p1''
	      end
	    else
	      begin
	        (* Don't do a move all/noarrayref if it is not beneficial *)
		changed := tmp_changed;
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


(***** Manual insertion of abort event *****)

let rec replace_process count occ premp p =
  { i_desc = 
    begin
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) -> 
      Par(replace_process count occ premp p1,
	  replace_process count occ premp p2)
  | Repl(b,p) ->
      Repl(b, replace_process count occ premp p)
  | Input(c, pat, p) ->
      Input(c, pat, replace_oprocess count occ premp p)
    end;
    i_occ = p.i_occ;
    i_facts = None }

and replace_oprocess count occ premp p =
  if p.p_occ == occ then
    begin
      incr count;
      premp
    end
  else
    { p_desc = 
      begin
    match p.p_desc with
      Yield -> Yield
    | Abort -> Abort
    | Restr(b,p) -> Restr(b, replace_oprocess count occ premp p)
    | Test(t,p1,p2) -> Test(t, replace_oprocess count occ premp p1,
			    replace_oprocess count occ premp p2)
    | Find(l0,p2,find_info) ->
	Find(List.map (fun (bl,def_list,t,p1) ->
	       (bl,def_list,t,
	        replace_oprocess count occ premp p1)) l0,
	     replace_oprocess count occ premp p2, find_info)
    | Output(c,t,p) ->
	Output(c,t,replace_process count occ premp p)
    | Let(pat,t,p1,p2) ->
	Let(pat,t,replace_oprocess count occ premp p1,
	    replace_oprocess count occ premp p2)
    | EventP(t,p) ->
	EventP(t,replace_oprocess count occ premp p)
    | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"
      end;
      p_occ = p.p_occ;
      p_facts = None  }

let insert_event occ s { proc = p } =
  let f = { f_name = s;
	    f_type = [Settings.t_bitstring],Settings.t_bool;
	    f_cat = Event;
	    f_options = 0;
            f_impl = No_impl;
            f_impl_inv = None }
  in
  let idx = Terms.build_term_type Settings.t_bitstring (FunApp(Settings.get_tuple_fun [], [])) in
  let t = Terms.build_term_type Settings.t_bool (FunApp(f, [idx])) in
  let premp = Terms.oproc_from_desc(EventP(t,Terms.abort_proc)) in
  let count = ref 0 in
  let p' = replace_process count occ premp p in
  if (!count) = 0 then 
    raise (Parsing_helper.Error("Occurrence " ^ (string_of_int occ) ^ " not found. You should use the command show_game occ to determine the desired occurrence.", Parsing_helper.dummy_ext))
  else if (!count > 1) then
    raise (Parsing_helper.Error("Occurrence " ^ (string_of_int occ) ^ " ambiguous. You should use the command show_game occ to determine the desired occurrence.", Parsing_helper.dummy_ext))
  else
    begin
      changed := true;
      let g' = { proc = p'; game_number = -1 } in
      queries := (QEventQ([false, t], QTerm (Terms.make_false())), g') :: (!queries);
      (g', [SetEvent(f, g')], [DInsertEvent(f,occ)])
    end
