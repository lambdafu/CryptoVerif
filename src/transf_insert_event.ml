open Types

(***** Manual insertion of abort event *****)

let rec replace_process count occ premp p =
  if (occ < p.i_occ) || (occ > p.i_max_occ) then
    (* We are sure that [occ] is not inside [p] *) 
    p
  else
    Terms.iproc_from_desc3 p (
    match p.i_desc with
      Nil -> Nil
    | Par(p1,p2) -> 
	Par(replace_process count occ premp p1,
	    replace_process count occ premp p2)
    | Repl(b,p) ->
	Repl(b, replace_process count occ premp p)
    | Input(c, pat, p) ->
	Input(c, pat, replace_oprocess count occ premp p))

and replace_oprocess count occ premp p =
  if p.p_occ == occ then
    begin
      incr count;
      premp
    end
  else if (occ < p.p_occ) || (occ > p.p_max_occ) then
    (* We are sure that [occ] is not inside [p] *) 
    p
  else
    Terms.oproc_from_desc3 p (
    match p.p_desc with
      Yield -> Yield
    | EventAbort f -> EventAbort f
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
    | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here")

let insert_event occ s g =
  if not g.expanded then
    raise (Parsing_helper.Error ("insert_event does not support non-expanded games", Parsing_helper.dummy_ext));
  let s' = Terms.fresh_id s in
  if s' <> s then
    print_string ("Warning: event "^s^" renamed into "^s'^" because "^s^" is already used.\n");
  let f = { f_name = s';
	    f_type = [Settings.t_bitstring],Settings.t_bool;
	    f_cat = Event;
	    f_options = 0;
	    f_statements = [];
	    f_collisions = [];
	    f_eq_theories = NoEq;
            f_impl = No_impl;
            f_impl_inv = None }
  in
  let b = Terms.create_binder "!l" Settings.t_bitstring [] in
  let idx = Terms.term_from_binder b in
  let t = Terms.build_term_type Settings.t_bool (FunApp(f, [idx])) in
  let premp = Terms.oproc_from_desc(EventAbort(f)) in
  let count = ref 0 in
  let p' = replace_process count occ premp (Terms.get_process g) in
  if (!count) = 0 then 
    raise (Parsing_helper.Error("Occurrence " ^ (string_of_int occ) ^ " not found. You should use the command show_game occ to determine the desired occurrence.", Parsing_helper.dummy_ext))
  else if (!count > 1) then
    raise (Parsing_helper.Error("Occurrence " ^ (string_of_int occ) ^ " ambiguous. You should use the command show_game occ to determine the desired occurrence.", Parsing_helper.dummy_ext))
  else
    begin
      (* Adding the event to Stringmap.env so that it can be used in the "focus" command *)
      Stringmap.env := Stringmap.StringMap.add f.f_name (Stringmap.EEvent f) (!Stringmap.env);
      Settings.changed := true;
      let g' = Terms.build_transformed_game p' g in
      let q_proof = ref ToProve in
      let pub_vars = Settings.get_public_vars g.current_queries in
      g'.current_queries <- ((QEventQ([false, t], QTerm (Terms.make_false()), pub_vars), g'), q_proof) ::
	 (List.map (fun (q, poptref) -> (q, ref (!poptref))) g.current_queries);
      (g', [SetEvent(f, g', pub_vars, q_proof)], [DInsertEvent(f,occ)])
    end
