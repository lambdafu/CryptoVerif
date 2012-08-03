open Types

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
      Settings.changed := true;
      let g' = { proc = p'; game_number = -1 } in
      Settings.queries := (QEventQ([false, t], QTerm (Terms.make_false())), g') :: (!Settings.queries);
      (g', [SetEvent(f, g')], [DInsertEvent(f,occ)])
    end
