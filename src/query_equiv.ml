open Types

let dummy_channel = { cname = "dummy_channel" }

let rec make_par = function
  | [] -> Terms.iproc_from_desc Nil
  | [a] -> a
  | a::l -> Terms.iproc_from_desc (Par(a, make_par l))

let rec put_restr p = function
  | [] -> p
  | (b,_opt)::l ->
      Terms.oproc_from_desc (Restr(b,put_restr p l))

(* Record the channels used in the equivalence to avoid a clash
   with fresh channels we create *)
	
let rec record_channels_fg = function
  | Fun(c, _,_,_) -> Terms.record_id c.cname Parsing_helper.dummy_ext
  | ReplRestr(_,_,fglist) -> List.iter record_channels_fg fglist

let member_record_channels m =
  List.iter (fun (fg, _) -> record_channels_fg fg) m
	
type channel_struct =
  | CRepl of channel * channel_struct list
  | CFun of channel

let new_channel() =
  let cid = Terms.fresh_id (if !Settings.front_end = Settings.Channels then "c" else "O") in
  { cname = cid } 
  
let rec fungroup_build_ch_struct = function
  | Fun(c, bl, t, _) -> CFun c
  | ReplRestr(_,_,fglist) ->
      CRepl(new_channel(), List.map fungroup_build_ch_struct fglist)

let member_build_ch_struct m = 
  List.map (fun (fg,_) -> fungroup_build_ch_struct fg) m

let put_repl_in_restr_out_par cur_array' idx_opt c restr plist =
  let p = make_par plist in
  let in_ch = (c, List.map Terms.term_from_repl_index cur_array') in
  let out_ch =
    if !Settings.front_end = Settings.Channels then
      (c, List.map Terms.term_from_repl_index cur_array')
    else
      (dummy_channel, [])
  in
  let empty_tuple = Settings.get_tuple_fun [] in
  let out_p = Terms.oproc_from_desc (Output(out_ch, Terms.app empty_tuple [], p)) in
  let restr_p = put_restr out_p restr in
  let in_p = Terms.iproc_from_desc (Input(in_ch, PatTuple(empty_tuple, []), restr_p)) in      
  begin
    match idx_opt with
    | None -> in_p
    | Some idx -> Terms.iproc_from_desc (Repl(idx, in_p))
  end

let put_in cur_array c bl p =
  let in_ch = (c, List.map Terms.term_from_repl_index cur_array) in
  let tyl = List.map (fun b -> b.btype) bl in
  let f = Settings.get_tuple_fun tyl in
  Terms.iproc_from_desc
    (Input(in_ch, PatTuple(f, List.map (fun b -> PatVar b) bl), p))

let put_out cur_array c t =
  let out_ch =
    if !Settings.front_end = Settings.Channels then
      (c, List.map Terms.term_from_repl_index cur_array)
    else
      (dummy_channel, [])
  in
  let nil_p = Terms.iproc_from_desc Nil in
  Terms.oproc_from_desc (Output(out_ch, t, nil_p))
    
let rec fungroup_to_process cur_array ch_struct fg =
  match (ch_struct, fg) with
  | CFun c, Fun(c' , bl, t, _) when c' == c ->
      let out_p = put_out cur_array c t in
      put_in cur_array c bl out_p
  | CRepl(c, ch_struct_l), ReplRestr(idx_opt, restr, fglist) ->
      let cur_array' =
	match idx_opt with
	| None -> cur_array
	| Some idx -> idx :: cur_array
      in
      let plist =
	List.map2 (fungroup_to_process cur_array') ch_struct_l fglist
      in
      put_repl_in_restr_out_par cur_array' idx_opt c restr plist
  | _ -> Parsing_helper.internal_error "ch_struct does not match fg" 
	
let eqmember_to_process ch_struct_l m =
  make_par (List.map2 (fun ch_struct (fg,_) ->
    fungroup_to_process [] ch_struct fg) ch_struct_l m)

(* Computational equivalences:
   We build a process that runs the oracles of the equivalence,
   answers as the LHS and executes event distinguish if the
   RHS does not answer like the LHS. *)

(* Build the mapping of indices and random variables between the LHS and the RHS *)
    
let rec build_mapping_fungroup lm rm =
  match lm, rm with
  | ReplRestr(idx_opt, restr, funlist), ReplRestr(idx_opt', restr', funlist') ->
      begin
	match idx_opt, idx_opt' with
	| None, None -> ()
	| Some idx, Some idx' ->
	    Terms.ri_link idx (TLink (Terms.term_from_repl_index idx')) 
	| _ ->
	    Parsing_helper.internal_error "Structures of left- and right-hand sides of an equivalence must be the same"
      end;
      List.iter2 build_mapping_fungroup funlist funlist';
      if restr = [] then
	()
      else
	List.iter (fun (b',bopt') ->
	  if bopt' == Unchanged then
	    try 
	      let (b,_) = List.find (fun (b,_) -> Terms.equiv_same_vars b b') restr in
	      Terms.link b (TLink (Terms.term_from_binder b'))
	    with Not_found -> ()
		) restr'
  | Fun(_, bl, t, _), Fun(_, bl', t', _) ->
      List.iter2 (fun b b' ->
	Terms.link b (TLink (Terms.term_from_binder b'))) bl bl'
  | _ -> Parsing_helper.internal_error "Structures of left- and right-hand sides of an equivalence must be the same"

let build_mapping lmg rmg =
  List.iter2 (fun (lm,_) (rm,_) -> 
    build_mapping_fungroup lm rm) lmg rmg

(* Rename variables in the LHS to the names in the RHS, as found
   above *)

let rename_idx i =
  match i.ri_link with
  | NoLink -> i
  | TLink { t_desc = ReplIndex i' } -> i'
  | _ -> Parsing_helper.internal_error "Unexpected link in rename_idx"

let rename_var b =
  match b.link with
  | NoLink -> b
  | TLink { t_desc = Var(b',_) } -> b'
  | _ -> Parsing_helper.internal_error "Unexpected link in rename_var"

let rec rename_vars t = 
  match t.t_desc with
  | ReplIndex i ->
      Terms.build_term2 t (ReplIndex(rename_idx i))
  | Var(b,l) ->
      Terms.build_term2 t (Var(rename_var b,
			       List.map rename_vars l))
  | FunApp(f,l) ->
      Terms.build_term2 t (FunApp(f, List.map rename_vars l))
  | TestE _ | LetE _ | FindE _ | ResE _ | EventAbortE _
  | EventE _ | GetE _ | InsertE _ ->
      Parsing_helper.internal_error "Only indices, var, fun app should occur in LHS of equivalences"

let rec rename_vars_fungroup = function
  | ReplRestr(idx_opt, restr, funlist) ->
      let idx_opt' =
	match idx_opt with
	| None -> None
	| Some i -> Some (rename_idx i)
      in
      ReplRestr(idx_opt', List.map (fun (b, opt) -> (rename_var b, opt)) restr,
		List.map rename_vars_fungroup funlist)
  | Fun(c, bl, t, opt) ->
      Fun(c, List.map rename_var bl, rename_vars t, opt)

let rename_vars_member m =
  List.map (fun (fg,opt) -> (rename_vars_fungroup fg, opt)) m
    
let rec eqfungroup_to_process bad_event cur_array lhs rhs =
  match lhs, rhs with
  | ReplRestr(idx_opt, restr, funlist), ReplRestr(idx_opt', restr', funlist') ->
      let cur_array' =
	match idx_opt, idx_opt' with
	| None, None -> cur_array
	| Some idx, Some idx' when idx == idx' -> idx :: cur_array
	| _ -> assert false
      in
      let plist =
	List.map2 (eqfungroup_to_process bad_event cur_array') funlist funlist'
      in      
      put_repl_in_restr_out_par cur_array' idx_opt'
	(new_channel()) (Terms.union (fun (b,_) (b',_) -> b == b') restr restr') plist
  | Fun(_, _, t, _), Fun(c', bl', t', _) ->
      let b_lhs = Terms.create_binder "res_lhs" t.t_type cur_array in
      let b_rhs = Terms.create_binder "res_rhs" t'.t_type cur_array in
      let out_p = put_out cur_array c' (Terms.term_from_binder b_lhs) in
      let test_p = Terms.oproc_from_desc
	  (Test(Terms.make_equal (Terms.term_from_binder b_lhs) (Terms.term_from_binder b_rhs),
		out_p,
		Terms.oproc_from_desc (EventAbort bad_event)))
      in
      let let2_p = Terms.oproc_from_desc (Let(PatVar b_rhs, t', test_p, Terms.oproc_from_desc Yield)) in
      let let1_p = Terms.oproc_from_desc (Let(PatVar b_lhs, t, let2_p, Terms.oproc_from_desc Yield)) in
      put_in cur_array c' bl' let1_p
  | _ ->
      Parsing_helper.internal_error "Structures of left- and right-hand sides of an equivalence must be the same"
    
let eqmembers_to_process bad_event lhs rhs =
  make_par (List.map2 (fun (fg_lhs,_) (fg_rhs,_) ->
    eqfungroup_to_process bad_event [] fg_lhs fg_rhs) lhs rhs)
    
let equiv_to_process ((_, lhs, rhs, _, _, opt), _) =
  member_record_channels lhs;
  match opt with
  | Decisional ->
      let ch_struct = member_build_ch_struct lhs in
      ([], Equivalence(eqmember_to_process ch_struct lhs,
		       eqmember_to_process ch_struct rhs, []))
  | Computational ->
      let bad_event = Terms.create_event (Terms.fresh_id "distinguish") [] in
      let query = Terms.build_event_query bad_event [] in
      build_mapping lhs rhs;
      let lhs' =
	Terms.ri_auto_cleanup (fun () ->
	  Terms.auto_cleanup (fun () ->
	    build_mapping lhs rhs;
	    rename_vars_member lhs))
      in
      ([query], SingleProcess(eqmembers_to_process bad_event lhs' rhs))
