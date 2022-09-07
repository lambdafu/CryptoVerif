open Types

(***** Manual insertion of abort event *****)

type state =
    { mutable count : int;
      mutable need_expand : bool;
      occ : int;
      ext_o : Parsing_helper.extent;
      ev  : funsymb }
      
let no_insert_eventt state t =
  if (state.occ >= t.t_occ) && (state.occ <= t.t_max_occ) then
    raise (Parsing_helper.Error("Cannot insert an event in a defined condition or in a channel of input", state.ext_o))
  
let no_insert_event_def_list state def_list =
  List.iter (fun (b,l) -> List.iter (no_insert_eventt state) l) def_list;
  def_list
  
let rec insert_eventpat state = function
    PatVar b -> PatVar b
  | PatTuple(f,l) -> PatTuple(f, List.map (insert_eventpat state) l)
  | PatEqual t -> PatEqual(insert_eventt state t)

and insert_eventt state t =
  if t.t_occ == state.occ then
    begin
      state.count <- state.count + 1;
      state.need_expand <- true;
      Terms.build_term_type Settings.t_any (EventAbortE(state.ev))
    end
  else if (state.occ < t.t_occ) || (state.occ > t.t_max_occ) then
    (* We are sure that [occ] is not inside [t] *) 
    t
  else
    Terms.build_term t (Terms.map_subterm (insert_eventt state)
			  (no_insert_event_def_list state) (insert_eventpat state) t)

let rec insert_eventi state p =
  if (state.occ < p.i_occ) || (state.occ > p.i_max_occ) then
    (* We are sure that [occ] is not inside [p] *) 
    p
  else
    Terms.iproc_from_desc
      (Terms.map_subiproc (insert_eventi state) (fun (c,tl) pat p ->
	List.iter (no_insert_eventt state) tl;
	((c,tl), insert_eventpat state pat,
	 insert_evento state p)) p)

and insert_evento state p =
  if p.p_occ == state.occ then
    begin
      state.count <- state.count + 1;
      Terms.oproc_from_desc(EventAbort(state.ev))
    end
  else if (state.occ < p.p_occ) || (state.occ > p.p_max_occ) then
    (* We are sure that [occ] is not inside [p] *) 
    p
  else
    Terms.oproc_from_desc
      (Terms.map_suboproc (insert_evento state) (insert_eventt state)
	 (no_insert_event_def_list state) (insert_eventpat state)
	 (insert_eventi state) p)

let get_event queries (s, ext_s) = 
  try
    let f = List.find (fun f -> f.f_name = s) (!Settings.events_to_ignore_lhs) in
    (* [f] is an event that occurs in the RHS of an equivalence we want to prove
       using [query_equiv]. *)
    match queries with
    | [((QEquivalence(_,_,current_is_lhs),_),proof_opt)] when !proof_opt = ToProve ->
	if current_is_lhs then
	  (f, false)
	else
	  raise (Parsing_helper.Error("In query_equiv, to introduce an event used in the right-hand side of the equivalence to prove, one should be working on the left-hand side", ext_s))
    | _ ->
	raise (Parsing_helper.Error("In query_equiv, to introduce an event used in the right-hand side of the equivalence to prove, the only query to prove should be the equivalence", ext_s))
  with Not_found ->
    let (q_equiv, q_not_equiv) = List.partition (function ((QEquivalence _,_),poptref) -> !poptref = ToProve | _ -> false) queries in
    try
      match q_equiv with
      | [] -> raise Not_found
      | [(QEquivalence(state_other_end, pub_vars, current_is_lhs),g), poptref] ->
	  let is_event_query_string s ((q,_),_) =
	    match q with
	    | QEventQ([false, { t_desc = FunApp(f,[_]) }], QTerm t_false, pub_vars) ->
		f.f_name = s && Terms.is_false t_false
	    | _ -> false
	  in
	  let get_event_f ((q,_),_) =
	    match q with
	    | QEventQ([false, { t_desc = FunApp(f,[_]) }], QTerm t_false, pub_vars) when Terms.is_false t_false ->
		f
	    | _ -> assert false
	  in
	    
	  let queries_other_end = state_other_end.game.current_queries in
	  let f = get_event_f
	      (List.find (is_event_query_string s) queries_other_end)
	  in
	  if List.exists (Terms.is_event_query f) queries then
	    raise Not_found;
	  (* When the events has been introduced in the other side of the equivalence and it has not been introduced yet on the current side, I reuse the event symbol. Hence the same events can be introduced on both sides *)
	  (f, true)
      | _ -> Parsing_helper.internal_error "insert_event: There should be at most one equivalence query to prove"
    with Not_found ->
      let s' = Terms.fresh_id s in
      if s' <> s then
	print_string ("Warning: event "^s^" renamed into "^s'^" because "^s^" is already used.\n");
      let f = Terms.create_event s' [] in
      (* Adding the event to Stringmap.env so that it can be used in the "focus" command *)
      Stringmap.env := Stringmap.StringMap.add f.f_name (Stringmap.EEvent f) (!Stringmap.env);
      (f, true)

      
let insert_event occ ext_o s ext_s g =
  let f, add_query = get_event g.current_queries (s,ext_s) in
  let state =
    { need_expand = false;
      count = 0;
      occ = occ;
      ext_o = ext_o;
      ev = f }
  in
  let p' = insert_eventi state (Terms.get_process g) in
  if state.count = 0 then 
    raise (Parsing_helper.Error("Occurrence " ^ (string_of_int occ) ^ " not found. You should use the command show_game occ to determine the desired occurrence.", ext_o))
  else if state.count > 1 then
    raise (Parsing_helper.Error("Occurrence " ^ (string_of_int occ) ^ " ambiguous. You should use the command show_game occ to determine the desired occurrence.", ext_o))
  else
    begin
      Settings.changed := true;
      let g' = Terms.build_transformed_game ~expanded:(g.expanded && (not state.need_expand)) p' g in
      let new_queries =
	if add_query then
	  let pub_vars = Settings.get_public_vars g.current_queries in
	  let query = Terms.build_event_query f pub_vars in
	  let q_proof = ref ToProve in
	  g'.current_queries <- ((query, g'), q_proof) ::
	     (List.map (fun (q, poptref) -> (q, ref (!poptref))) g.current_queries);
	  [SetEvent(f, g', pub_vars, q_proof)]
	else
	  []
      in
      (g', new_queries, [DInsertEvent(f,occ)])
    end
