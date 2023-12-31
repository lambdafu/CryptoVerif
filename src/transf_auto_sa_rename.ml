open Types


(* Auto SA rename: when a variable x defined in find conditions has
   several definitions (and no array accesses---it must not have
   array accesses), rename variable x into x1...xn. That's necessary
   to satisfy the invariants. This transformation must be called after
   each transformation that duplicates processes. 

   This transformation supports processes with TestE/LetE/FindE/ResE
   inside terms (not only in find conditions).
*)

let queries = ref []

let done_sa_rename = ref []
      
let new_binder b =
  if Array_ref.has_array_ref_q b (!queries) then
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
  Terms.build_term t 
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
      |	ResE (b, t) ->
	  let b' = new_binder b in
	  let t' = auto_sa_rename_fc t in
	  b.link <- NoLink;
	  ResE(b', t')
      | EventAbortE f ->
	  EventAbortE f
      | EventE _ | GetE _ | InsertE _ -> 
	  Parsing_helper.internal_error "get, insert, and event should not occur in find condition")

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
  Terms.build_term t 
    (match t.t_desc with
    | FindE(l0,t3,find_info) ->
        FindE(List.map (fun (bl, def_list, t1,t2) ->
	  (bl, Terms.delete_info_def_list def_list
                (* def_list contains only Var/FunApp/ReplIndex so no change
		   I still need to copy the def_list to make sure that all
		   terms are physically distinct, for a correct computation of facts. *),
	   auto_sa_rename_fc t1,
	   auto_sa_rename_term t2)) l0,
	      auto_sa_rename_term t3, find_info)
    | _ ->
	Terms.map_subterm auto_sa_rename_term Terms.delete_info_def_list
	  auto_sa_rename_pat t)

and auto_sa_rename_pat pat =
  Terms.map_subpat auto_sa_rename_term auto_sa_rename_pat pat

let rec auto_sa_rename_process p = 
  Terms.iproc_from_desc_loc p
    (Terms.map_subiproc auto_sa_rename_process
       (fun (c,tl) pat p ->
	 let tl' = List.map auto_sa_rename_term tl in
	 let pat' = auto_sa_rename_pat pat in
	 let p' = auto_sa_rename_oprocess p in
	 ((c, tl'), pat', p')) p)

and auto_sa_rename_oprocess p = 
  Terms.oproc_from_desc_loc p (
  match p.p_desc with
  | Find(l0, p2, find_info) ->
      Find(List.map (fun (bl, def_list, t, p1) ->
	  (bl, Terms.delete_info_def_list def_list(* def_list contains only Var/FunApp/ReplIndex so no change *),
	   auto_sa_rename_fc t,
	   auto_sa_rename_oprocess p1)) l0,
	   auto_sa_rename_oprocess p2, find_info)
  | _ ->
      Terms.map_suboproc auto_sa_rename_oprocess auto_sa_rename_term
	Terms.delete_info_def_list auto_sa_rename_pat auto_sa_rename_process p
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
  queries := g.current_queries;
  let g_proc = Terms.get_process g in
  Array_ref.array_ref_process g_proc;
  let p' = auto_sa_rename_process g_proc in
  Array_ref.cleanup_array_ref();
  let sa_rename = !done_sa_rename in
  done_sa_rename := [];
  let res = (Terms.build_transformed_game p' g, [], do_sa_rename [] sa_rename) in
  queries := [];
  res


let rec auto_sa_rename_fungroup = function
  | ReplRestr(repl_opt, restr, funlist) ->
      ReplRestr(repl_opt, restr, List.map auto_sa_rename_fungroup funlist)
  | Fun(ch, args, res, priority) ->
      Fun(ch, args, auto_sa_rename_term res, priority)
 
let auto_sa_rename_eqside_aux rm =
  List.map (fun (fg, mode) ->
    (auto_sa_rename_fungroup fg, mode)
      ) rm
    
let auto_sa_rename_eqside rm =
  queries := [];
  Array_ref.array_ref_eqside rm;
  let rm' = auto_sa_rename_eqside_aux rm in
  Array_ref.cleanup_array_ref();
  done_sa_rename := [];
  rm'
