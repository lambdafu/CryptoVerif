open Types
open Parsing_helper

module UpdateFindInfo =
  struct

(* Replace all find[unique] with find[unique to prove] or find in case 
   [Settings.guess_remove_unique] is true *)    
  
type fistate_ty =
    { initial_queries : cur_queries_t;
      all_non_unique_events : funsymb list ref }
      
let upd_notransfo state find_info =
  match find_info with
  | Nothing -> Nothing
  | Unique ->
      if !Settings.guess_remove_unique then
	Nothing
      else
	let e = Terms.create_nonunique_event() in
	state.all_non_unique_events := e :: (!(state.all_non_unique_events));
 	UniqueToProve e
  | UniqueToProve e ->
      if !Settings.guess_remove_unique &&
	not (Terms.has_event_query e state.initial_queries)
	then
	Nothing
      else
	begin
	  Terms.addq_ref state.all_non_unique_events e;
	  UniqueToProve e
	end

let rec upd_t state t =
  match t.t_desc with
  | FindE(l0,p3,find_info) ->
      let find_info' = upd_notransfo state find_info in
      let l0' = List.map (fun (bl, def_list, t1, p2) ->
	let t1' = upd_t state t1 in
	let p2' = upd_t state p2 in
	(bl, def_list, t1', p2')
	  ) l0
      in
      Terms.build_term2 t (FindE(l0',upd_t state p3,find_info'))
  | _ -> Terms.build_term2 t (Terms.map_subterm (upd_t state) (fun def_list -> def_list) (upd_pat state) t)

and upd_pat state pat =
  Terms.map_subpat (upd_t state) (upd_pat state) pat

let rec upd_i state p =
  Terms.iproc_from_desc_at p
    (Terms.map_subiproc (upd_i state) (fun ch pat p ->
    (ch, upd_pat state pat, upd_p state p)) p)

and upd_p state p =
  Terms.oproc_from_desc_at p (
  match p.p_desc with
  | Find(l0,p3,find_info) ->
      let find_info' = upd_notransfo state find_info in
      let l0' = List.map (fun (bl, def_list, t1, p2) ->
	let t1' = upd_t state t1 in
	let p2' = upd_p state p2 in
	(bl, def_list, t1', p2')
	  ) l0
      in
      Find(l0',upd_p state p3,find_info')
  | _ -> Terms.map_suboproc (upd_p state) (upd_t state) (fun def_list -> def_list) (upd_pat state) (upd_i state) p)

  end
  
let selected_guess = ref (GuessOcc(-1, false, dummy_ext))

let ext_command() =
  match !selected_guess with
  | GuessOcc(_,_,ext) | GuessRepl(_,_,ext) | GuessVar(_,_,ext) -> ext


let check_size ty =
  match ty.tsize with
  | Some(_,smax) when smax <= !Settings.tysize_MAX_Guess -> ()
  | _ ->
      raise (Error("The type of the guessed value must have size at most "^
		   (string_of_int (!Settings.tysize_MAX_Guess)), ext_command()))


let get_cst s ty =
  let b_tested = Settings.create_fun (Terms.fresh_id (s ^ "_tested"))
    ([], ty) GuessCst
    (* use the category GuessCst so that the "diffConstants"
       setting does not apply to guessed constants *)
  in
  (* Adding b_tested to Stringmap.env so that it can be used in 
     the "replace" command *)
  Stringmap.env := Stringmap.StringMap.add b_tested.f_name
       (Stringmap.EFunc b_tested) (!Stringmap.env);
  b_tested
	
let found_guess = ref false
let no_test = ref false
    
let guess_card = ref Zero
let guess_cst = ref (Terms.make_true ())
let var_eq_test = ref (Terms.make_true ())
let has_secrecy = ref false
let guess_b_defined = ref None
    
let query_variables = ref []
let events_under_guess = ref []
let events_elsewhere = ref []
let variables_under_guess = ref []
let variables_elsewhere = ref []

let event_accu_ref = ref None
    
let duplicated_vars = ref ([]: (binder * binder) list) (* list of (initial var, image var) *)
let new_pub_vars = ref ([]: (binder * binder) list)
let duplicated_events = ref ([]: (funsymb * funsymb * bool ref * bool ref) list)
    (* list of (initial event, image event, initial event useful?, image event useful?) *)

let fistate = ref { UpdateFindInfo.initial_queries = [];
		    all_non_unique_events = ref [] }
    
let reset() =
  fistate := { UpdateFindInfo.initial_queries = [];
	       all_non_unique_events = ref [] };
  selected_guess := GuessOcc(-1, false, dummy_ext);
  found_guess := false;
  no_test := false;
  guess_card := Zero;
  guess_cst := (Terms.make_true ());
  var_eq_test := (Terms.make_true ());
  has_secrecy := false;
  guess_b_defined := None;
  query_variables := [];
  events_under_guess := [];
  events_elsewhere := [];
  variables_under_guess := [];
  variables_elsewhere := [];
  event_accu_ref := None;
  duplicated_vars := [];
  new_pub_vars := [];
  duplicated_events := []

let update_find_info_notransfo find_info =
  if !has_secrecy then UpdateFindInfo.upd_notransfo (!fistate) find_info else find_info

let update_find_info_t t =
  if !has_secrecy then UpdateFindInfo.upd_t (!fistate) t else t

let update_find_info_pat pat =
  if !has_secrecy then UpdateFindInfo.upd_pat (!fistate) pat else pat
    
let update_find_info_p p =
  if !has_secrecy then UpdateFindInfo.upd_p (!fistate) p else p
      
let update_queries state g' new_queries current_queries =
  let (new_corresp_queries, new_secrecy_queries) =
    List.partition (fun (_,_,q,_) ->
      match q with
      | QEventQ _ -> true
      | QSecret _ -> false
      | _ -> assert false) new_queries
  in
  let proved_ql = List.map (fun (q_orig,_,_,_) -> q_orig) new_corresp_queries in
  let new_corresp_queries' = 
    List.map (fun (q_orig,proof_opt,q, proba) ->
      let proof_opt' = ref ToProve in
      let new_q = ((q,g'), proof_opt') in
      let proof =
	match !selected_guess with
	| GuessVar _ ->
	    assert (proba == []);
	    let full_proba = Mul(!guess_card, Advt(g', true, [])) in
	    Proved(proved_ql, full_proba, state)
	| _ ->
	    let full_proba =
	      Polynom.p_add (Mul(!guess_card, Advt(g', false, [q,proof_opt'])),
			     (Polynom.proba_from_set proba))
	    in
	    Proved([q_orig],full_proba,state)
      in
      proof_opt := proof;
      new_q
	) new_corresp_queries
  in
  let corresp_and_old_queries = new_corresp_queries' @ current_queries in
  let all_pub_vars = Settings.get_public_vars (!fistate.initial_queries) in
  let new_non_unique_queries = ref [] in
  let all_non_unique_queries =
    List.map (fun f ->
      try
	List.find (fun q ->
	  Settings.get_query_status q == ToProve && Terms.is_event_query f q
	    ) corresp_and_old_queries
      with Not_found ->
	let new_q = (Terms.build_event_query f all_pub_vars, g'), ref ToProve in
	new_non_unique_queries := new_q :: (!new_non_unique_queries);
	new_q
	  ) (!(!fistate.all_non_unique_events))
  in
  let new_secrecy_queries' =
    List.map (fun (q_orig,proof_opt,q, proba) ->
      let proof_opt' = ref ToProve in
      let new_q = ((q,g'), proof_opt') in
      let full_proba =
	Polynom.p_add (Mul(!guess_card, Advt(g', false, List.map (fun ((q,_), popt_ref) -> (q, popt_ref)) (new_q :: all_non_unique_queries))),
		       (Polynom.proba_from_set proba))
      in
      proof_opt := Proved([q_orig], full_proba, state);
      new_q
	) new_secrecy_queries
  in
  new_secrecy_queries' @ (!new_non_unique_queries) @ corresp_and_old_queries
						       
(**** Guess value of a variable *)
       
let is_selected_var b =
  match !selected_guess with
  | GuessVar((b',_),_,_) -> b' == b
  | _ -> false
	
let is_guess_var cur_array pp b =
  match !selected_guess with
  | GuessVar((b',l),_,_) when b' == b ->
      if l = [] then
	begin
	  assert (cur_array == []);
	  found_guess := true;
	  true
	end
      else
	begin
	  try 
	    let (facts,_,_,_) = Facts.get_facts_at pp in
	    let simp_facts = Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) facts in
	    let eq = Terms.make_and_list (List.map2 (fun t ri -> Terms.make_equal t (Terms.term_from_repl_index ri)) l cur_array) in
	    let _ = Facts.simplif_add Facts.no_dependency_anal simp_facts eq in
	    if List.for_all2 (fun t ri ->
	      try
		let diff = Terms.make_diff t (Terms.term_from_repl_index ri) in
		let _ = Facts.simplif_add Facts.no_dependency_anal simp_facts diff in
		false
	      with Contradiction ->
	        (* We proved that t = ri *)
		true
		  ) l cur_array
	    then
	      begin
	      (* We proved that l = cur_array *)
		found_guess := true;
		true
	      end
	    else
	      raise (Error("Just before occurrence "^(string_of_int (Terms.occ_from_pp pp))^", cannot determine whether the guessed variable has the desired indices or not", ext_command()))
	  with Contradiction ->
            (* The program point [p] is in fact unreachable
	       or we proved that [eq] is false, so l <> cur_array *)
	    false
	end
  | _ ->
      false
  
let make_test_t t =
  (* Abort when a variable is not guessed correctly *)
  let t_test = Terms.build_term_type t.t_type (TestE(!var_eq_test, update_find_info_t t, Terms.build_term_type t.t_type (EventAbortE (Terms.e_bad_guess())))) in
  match !guess_b_defined with
  | None -> t_test
  | Some b' ->
      Terms.build_term_type t.t_type (LetE(PatVar b', Terms.make_true(), t_test, None))

let make_test_p p =
  (* Abort when a variable is not guessed correctly *)
  let p_test = Terms.oproc_from_desc (Test(!var_eq_test, update_find_info_p p, Terms.oproc_from_desc (EventAbort (Terms.e_bad_guess())))) in
  match !guess_b_defined with
  | None -> p_test
  | Some b' ->
      Terms.oproc_from_desc (Let(PatVar b', Terms.make_true(), p_test,
				 Terms.oproc_from_desc Yield))

	
let rec full_transfo_t cur_array t =
  match t.t_desc with
  | FindE(l0,p3,find_info) ->
      let find_info' = update_find_info_notransfo find_info in
      let l0' = List.map (fun (bl, def_list, t1, p2) ->
	let p2' = 
	  if List.exists (fun (b,_) -> is_guess_var cur_array (DTerm p2) b) bl then
	    begin
	      if (!no_test) then
		raise (Error("guess ... no_test is allowed only for variables defined by let", ext_command()));
	      make_test_t p2
	    end
	  else
	    full_transfo_t cur_array p2
	in
	(bl, def_list, full_transfo_t cur_array t1, p2')
	  ) l0
      in
      Terms.build_term t (FindE(l0',full_transfo_t cur_array p3,find_info'))
  | ResE(b,t1) ->
      let t1' =
	if is_guess_var cur_array (DTerm t1) b then
	  begin
	    if (!no_test) then
	      raise (Error("guess ... no_test is allowed only for variables defined by let", ext_command()));
	    make_test_t t1
	  end
	else
	  full_transfo_t cur_array t1
      in
      Terms.build_term t (ResE(b,t1'))
  | LetE(pat, t1, t2, topt) ->
      let vars_pat = Terms.vars_from_pat [] pat in
      let has_guessed = List.exists (is_guess_var cur_array (DTerm t2)) vars_pat in
      if (!no_test) && has_guessed then
      	begin
	  match pat with
	  | PatVar b ->
	      let branch = Terms.build_term t (LetE(pat, !guess_cst, t2, None)) in
	      if Terms.check_simple_term t1 then
		branch
	      else
		let b_ignore = Terms.create_binder Settings.underscore_var_name t1.t_type cur_array in
		Terms.build_term t (LetE(PatVar b_ignore, t1, branch, None))
	  | _ -> 
	      raise (Error("guess ... no_test is allowed only for variables defined by let x = ...", ext_command()));
	end
      else
	begin
	  let t2' =
	    if has_guessed then
	      make_test_t t2
	    else
	      full_transfo_t cur_array t2
	  in
	  let topt' =
	    match topt with
	    | None -> None
	    | Some t3 -> Some (full_transfo_t cur_array t3)
	  in
	  Terms.build_term t (LetE(full_transfo_pat cur_array pat, full_transfo_t cur_array t1, t2', topt'))
	end
  | GetE _|InsertE _ -> Parsing_helper.internal_error "Get/Insert should not appear here"
  | _ -> Terms.build_term t (Terms.map_subterm (full_transfo_t cur_array) (fun def_list -> def_list) (full_transfo_pat cur_array) t)

and full_transfo_pat cur_array pat =
  Terms.map_subpat (full_transfo_t cur_array) (full_transfo_pat cur_array) pat
	
let rec full_transfo_i cur_array p =
  match p.i_desc with
  | Repl(ri,p1) ->
      let p1' = full_transfo_i (ri::cur_array) p1 in
      Terms.iproc_from_desc_loc p (Repl(ri,p1'))
  | _ -> 
      Terms.iproc_from_desc_loc p
	(Terms.map_subiproc (full_transfo_i cur_array) (fun c pat p1 ->
	  let vars_pat = Terms.vars_from_pat [] pat in
	  let p1' =
	    if List.exists (is_guess_var cur_array (DProcess p1)) vars_pat then
	      make_test_p p1
	    else
	      full_transfo_p cur_array p1
	  in
	  (c,full_transfo_pat cur_array pat, p1')) p) 
	
and full_transfo_p cur_array p =
  match p.p_desc with
  | Find(l0,p3,find_info) ->
      let find_info' = update_find_info_notransfo find_info in
      let l0' =
	List.map (fun (bl, def_list, t1, p2) ->
	  let p2' = 
	    if List.exists (fun (b,_) -> is_guess_var cur_array (DProcess p2) b) bl then
	      begin
		if (!no_test) then
		  raise (Error("guess ... no_test is allowed only for variables defined by let", ext_command()));
		make_test_p p2
	      end
	    else
	      full_transfo_p cur_array p2
	  in
	  (bl, def_list, full_transfo_t cur_array t1, p2')
	    ) l0
      in
      Terms.oproc_from_desc_loc p (Find(l0',full_transfo_p cur_array p3,find_info'))
  | Restr(b,p1) ->
      let p1' =
	if is_guess_var cur_array (DProcess p1) b then
	    begin
	      if (!no_test) then
		raise (Error("guess ... no_test is allowed only for variables defined by let", ext_command()));
	      make_test_p p1
	    end
	else
	  full_transfo_p cur_array p1
      in
      Terms.oproc_from_desc_loc p (Restr(b,p1'))
  | Let(pat, t, p1, p2) ->
      let vars_pat = Terms.vars_from_pat [] pat in
      let has_guessed = List.exists (is_guess_var cur_array (DProcess p1)) vars_pat in
      if (!no_test) && has_guessed then
      	begin
	  match pat with
	  | PatVar b ->
	      let branch = Terms.oproc_from_desc_loc p (Let(pat, !guess_cst, p1, Terms.oproc_from_desc Yield)) in
	      if Terms.check_simple_term t then
		branch
	      else
		let b_ignore = Terms.create_binder Settings.underscore_var_name t.t_type cur_array in
		Terms.oproc_from_desc_loc p (Let(PatVar b_ignore, t, branch, Terms.oproc_from_desc Yield))
	  | _ -> 
	      raise (Error("guess ... no_test is allowed only for variables defined by let x = ...", ext_command()));
	end
      else
	begin
	  let p1' = 
	    if has_guessed then
	      make_test_p p1 
	    else
	      full_transfo_p cur_array p1
	  in
	  Terms.oproc_from_desc_loc p (Let(full_transfo_pat cur_array pat, full_transfo_t cur_array t, p1', full_transfo_p cur_array p2))
	end
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"
  | _ ->
      Terms.oproc_from_desc_loc p
	(Terms.map_suboproc (full_transfo_p cur_array) (full_transfo_t cur_array)
	   (fun def_list -> def_list) (full_transfo_pat cur_array)
	   (full_transfo_i cur_array) p)

let guess_var ((b,l),ext) no_test_arg state g =
  let p = Terms.get_process g in
  check_size b.btype;
  guess_card := Proba.card b.btype;
  no_test := no_test_arg;
  fistate := { initial_queries = g.current_queries;
	       all_non_unique_events = ref [] };
  let b_tested = get_cst b.sname b.btype in
  guess_cst := Terms.app b_tested [];
  var_eq_test :=
     Terms.make_equal
       (Terms.term_from_binder b)
       (!guess_cst);
  let old_proba_zero = !Settings.proba_zero in
  if l != [] then
    begin
    (* We will need facts to prove that the indices are/are not equal to [l] *)
      Depanal.reset [] g;      
      Settings.proba_zero := true;
      Improved_def.improved_def_game None false g
    end;
  let cleanup() =
    if l != [] then
      begin
	Improved_def.empty_improved_def_game false g;
	assert (Depanal.final_add_proba() == []);
	Settings.proba_zero := old_proba_zero
      end
  in    
  try
    (* Check that queries are ok *)
    List.iter (function ((q,_),_) as q_proof ->
      match q with
      | _ when Settings.get_query_status q_proof != ToProve -> () (* I ignore already proved and inactive queries *)
      | QSecret (b,_,_) ->
	  has_secrecy := true;
	  if is_selected_var b then
	    raise (Error("Cannot guess a variable for which we want to prove secrecy", ext_command()));
      | QEventQ _ -> ()
      | _ ->
	  raise (Error("Cannot guess a value when there is an equivalence query to prove, or no query", ext_command()))
	    ) g.current_queries;
    if (!no_test) && (!has_secrecy) then
      raise (Error("guess ... no_test is not allowed in the presence of secrecy queries", ext_command()));
    (* Locate the definitions of guessed variable.
       In particular, raise an error if that variable is defined in a term.
       Also computes the query variables/events found under the guessed value/elsewhere, even though
       we do not use it here: we need it only when we guess a replication index. *)
    if !has_secrecy then
      guess_b_defined := Some (Terms.create_binder ("guess_"^b.sname^"_defined") Settings.t_bool b.args_at_creation);
    
    (* Compute the new queries *)
    (*   Create a new physical place for the proof indication, 
	 so that the proof is carried to the father game only when
	 it is a full proof *)
    let current_queries' = List.map (fun (q, poptref) -> (q, ref (!poptref))) g.current_queries in
    let new_queries = ref [] in
    List.iter (function ((q, g), proof_opt) as q_proof ->
      match q with
      | _ when Settings.get_query_status q_proof != ToProve -> () 
          (* I ignore already proved and inactive queries *)
      | QSecret(b,pub_vars,one_session) ->
	  begin
	    match !guess_b_defined with
	    | None ->
		(* guess_b_defined must be defined when there is a secrecy query *)
                assert false
	    | Some b' ->
		new_queries := (q, proof_opt, QSecret(b,b'::pub_vars,one_session), [])
		   :: (!new_queries)		
	  end
      | QEventQ _ ->
	  new_queries := (q, proof_opt, q, []) :: (!new_queries)
      | _ ->
	  Parsing_helper.internal_error "equivalence queries/absent query should have been eliminated earlier"
	    ) current_queries';

    if (!new_queries) == [] then
      raise (Error("Guess is useless: no query could be modified", ext_command()));
    
    let p' = full_transfo_i [] p in
    if not (!found_guess) then
      raise (Error("Could not find the designated variable", ext_command()));
    let g' = Terms.build_transformed_game p' g in
    g'.current_queries <- update_queries state g' (!new_queries) current_queries';    
    cleanup();
    g'

  with (Error _) as e ->
    cleanup();
    raise e

(****** Guess the tested session *)

let is_selected_repl p =
  match !selected_guess, p.i_desc with
  | GuessOcc(n,_,_), _ -> p.i_occ == n
  | GuessRepl(ri,_,_), Repl(ri',_) -> ri == ri'
  | _ -> false

let and_above() =
  match !selected_guess with
  | GuessOcc(_,and_above,_) | GuessRepl(_,and_above,_) -> and_above
  | _ -> false
	
let add_var under_guess b =
  if List.memq b (!query_variables) then
    let accu = if under_guess then variables_under_guess else variables_elsewhere in
    Terms.addq_ref accu b

let add_event under_guess e =
  let accu = if under_guess then events_under_guess else events_elsewhere in
  Terms.addq_ref accu e

let find_event_find_info under_guess = function
  | UniqueToProve f when (Terms.has_event_query f ((!fistate).initial_queries)) ->
      add_event under_guess f
  | _ -> ()
						   
let rec find_var_event_t under_guess t =
  begin
    match t.t_desc with
    | FindE(l0,t3,find_info) ->
	find_event_find_info under_guess find_info;
	List.iter (fun (bl,def_list,t1,t2) ->
	  List.iter (fun (b,_) -> add_var under_guess b) bl) l0
    | ResE(b,t1) -> add_var under_guess b
    | EventAbortE f 
    | EventE({ t_desc = FunApp(f,_) },_) -> add_event under_guess f
    | EventE _ ->
	Parsing_helper.internal_error "Events should be function applications"
    | GetE _|InsertE _ -> Parsing_helper.internal_error "Get/Insert should not appear here"
    | _ -> ()
  end;
  Terms.iter_subterm (find_var_event_t under_guess) (fun def_list -> ())
    (find_var_event_pat under_guess) t
      
and find_var_event_pat under_guess = function
    PatVar b -> add_var under_guess b
  | pat -> Terms.iter_subpat (find_var_event_t under_guess)
	(find_var_event_pat under_guess) pat

let rec find_var_event_i cur_array under_guess p =
  match p.i_desc with
  | Nil -> ()
  | Par(p1,p2) ->
      find_var_event_i cur_array under_guess p1;
      find_var_event_i cur_array under_guess p2
  | Repl(ri,p1) ->
      let cur_array' = ri::cur_array in
      if is_selected_repl p then
	begin
	  if (!found_guess) then
	    raise (Error("The designated replication is not unique (found a second time at occurrence "^(string_of_int p.i_occ)^")", ext_command()));
	  found_guess := true;
	  if and_above() then
	    begin
	      List.iter (fun ri -> check_size ri.ri_type) cur_array';
	      guess_card := 
		 match p1.i_desc with
		 | Input((c,_),_,_) -> OCount(c,0)
		 | _ -> Polynom.p_prod (List.map (fun ri -> Proba.card ri.ri_type) cur_array')
	    end
	  else
	    begin
	      check_size ri.ri_type;
	      guess_card := Proba.card ri.ri_type;
	    end;
	  find_var_event_i cur_array' true p1
	end
      else
	find_var_event_i cur_array' under_guess p1
  | Input((c,tl), pat, p1) ->
      List.iter (find_var_event_t under_guess) tl;
      find_var_event_pat under_guess pat;
      find_var_event_o cur_array under_guess p1

and find_var_event_o cur_array under_guess p =
  begin
    match p.p_desc with
    | Restr(b,p1) -> add_var under_guess b
    | Find(l0,p3,find_info) ->
	find_event_find_info under_guess find_info;
	List.iter (fun (bl,def_list,t,p1) ->
	  List.iter (fun (b,_) -> add_var under_guess b) bl;
	  ) l0
    | EventAbort f 
    | EventP({ t_desc = FunApp(f,_) },_) ->
	add_event under_guess f
    | EventP _ ->
	Parsing_helper.internal_error "Events should be function applications"
    | Get _| Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"
    | _ -> ()
  end;
  Terms.iter_suboproc (find_var_event_o cur_array under_guess)
    (find_var_event_t under_guess) (fun def_list -> ())
    (find_var_event_pat under_guess) (find_var_event_i cur_array under_guess) p

(* Record which events among those in duplicated_events
   are useful for each query *)
	
let record_useful_ev e =
  ignore (
  List.exists (fun (e1,e2,use1,use2) ->
    if e == e1 then begin use1 := true; true end else
    if e == e2 then begin use2 := true; true end else
    false
      ) (!duplicated_events)
    )

let record_useful_event = function
  | { t_desc = FunApp(e,_)} ->
      record_useful_ev e
  | _ -> 
      Parsing_helper.internal_error "Events should be function applications"
	
let rec record_useful_qterm = function
  | QEvent(_,t) -> record_useful_event t
  | QTerm _ -> ()
  | QAnd(t1,t2) | QOr(t1,t2) ->
      record_useful_qterm t1;
      record_useful_qterm t2

let record_useful_corresp (hyp, concl, pub_vars) =
  List.iter (fun (_, t) ->
    record_useful_event t
      ) hyp;
  record_useful_qterm concl

(* Tests whether a query is injective *)
    
let is_inj hyp =
  List.exists (fun (inj,_) -> inj) hyp

(* Transform correspondence query *)

let rec transform_hyp = function
  | [] -> ([], false)
  | ((inj, t)::rest) ->
      try
	let e,l =
	  match t.t_desc with
	  | FunApp(e,l) -> e,l
	  | _ -> Parsing_helper.internal_error "Events should be function applications"
	in
	let (e1,e2,_,_) =
	  List.find (fun (e1,_,_,_) -> e1 == e) (!duplicated_events)
	in
	(inj, Terms.build_term t (FunApp(e2,l))) :: rest, true
      with Not_found ->
	let rest', changed = transform_hyp rest in
	(inj, t) :: rest', changed

(* Build processes in the branches of the test
   "if i = i_tested" 

then branch:
  transfo (!duplicated_vars) (!duplicated_events) cur_array assigned p
else branch:
  transfo (!new_pub_vars) [] cur_array assigned p
where assigned = variables bound in the pattern [pat] in the input above p
(if [pat] internally defines variables in (!duplicated_vars),
transform into in(c[..], x:T); let pat = x in p
and work on [let pat = x in p]) *)

let rec is_var t =
  match t.t_desc with
  | Var(_,l) -> List.for_all is_var l
  | ReplIndex _ -> true
  | _ -> false

let transfo dup_vars dup_events cur_array assigned p = 

  let update_find_info = function
    | (UniqueToProve e) as find_info when Terms.has_event_query e ((!fistate).initial_queries)->
	begin
	  try
	    let (e1,e2,u1,u2) = List.find (fun (e1,_,_,_) -> e1 == e) dup_events in
	    (* u1 = true cannot happen because non-unique events appear
               only in queries event(e) ==> false,
	       transformed into event(e') ==> false when e
	       is under the guess, so e is no longer used in queries *)
	    assert (!u1 = false && !u2 == true);
	    (* The event is under the guess *)
	    if !has_secrecy then
	      Terms.addq_ref (!fistate).all_non_unique_events e2;
	    UniqueToProve e2
	  with Not_found ->
	    if !has_secrecy then
	      Terms.addq_ref (!fistate).all_non_unique_events e;
	    find_info
	end
    | find_info -> update_find_info_notransfo find_info
  in
  
  let add_assign_t x t =
    try
      let x' = List.assq x dup_vars in
      Terms.build_term t (LetE(PatVar x', Terms.term_from_binder x, t, None)) 
    with Not_found ->
      t
  in
  
  let rec tr_guess_t cur_array t =
    match t.t_desc with
    | Var(b,l) -> Terms.build_term t (Var(b, List.map (tr_guess_t cur_array) l))
    | ReplIndex i -> t
    | FunApp(f,l) -> Terms.build_term t (FunApp(f, List.map (tr_guess_t cur_array) l))
    | TestE(t1,t2,t3) -> Terms.build_term t (TestE(tr_guess_t cur_array t1, tr_guess_t cur_array t2, tr_guess_t cur_array t3))
    | FindE(l0,p3,find_info) ->
	let find_info' = update_find_info find_info in
	let l0' = List.map (fun (bl, def_list, t1, p2) ->
	  let vars = List.map fst bl in
	  let ri = List.map snd bl in
	  let p2' = tr_guess_t cur_array p2 in
	  let p2'' = List.fold_left (fun t b -> add_assign_t b t) p2' vars in
	  let t1' = tr_guess_t (ri @ cur_array) t1 in
	  (bl, def_list, t1', p2'')
	    ) l0
	in
	Terms.build_term t (FindE(l0',tr_guess_t cur_array p3,find_info'))
    | LetE(pat, t1, t2, topt) -> 
	let vars = Terms.vars_from_pat [] pat in
	let t2' = tr_guess_t cur_array t2 in
	let t2'' = List.fold_left (fun t b -> add_assign_t b t) t2' vars in
	let topt' =
	  match topt with
	  | None -> None
	  | Some t3 -> Some (tr_guess_t cur_array t3)
	in
	Terms.build_term t (LetE(tr_guess_pat cur_array pat, tr_guess_t cur_array t1, t2'', topt'))
    | ResE(b,t1) ->
	Terms.build_term t (ResE(b, add_assign_t b (tr_guess_t cur_array t1)))
    | EventAbortE e -> 
	begin
	  try
	    let (e1,e2,u1,u2) = List.find (fun (e1,_,_,_) -> e1 == e) dup_events in
	    match !u1, !u2 with
	    | true, false -> t
	    | false, true -> Terms.build_term t (EventAbortE e2)
	    | true, true ->
		Terms.build_term t (EventE(Terms.app e2 [], t))
	    | false, false ->
	      (* Can happen in case the event was already useless before the transformation *)
		t
	  with Not_found ->
	    t
	end

    | EventE(t1,t2) ->
	begin
	  let t2' = tr_guess_t cur_array t2 in
	  let t1' = tr_guess_t cur_array t1 in
	  match t1'.t_desc with
	  | FunApp(e,idx::tl) ->
	      begin
		try
		  let (e1,e2,u1,u2) = List.find (fun (e1,_,_,_) -> e1 == e) dup_events in
		  match !u1, !u2 with
		  | true, false -> Terms.build_term t (EventE(t1',t2')) 
		  | false, true ->
		    (* Replace e with e2; e is no longer useful *)
		      Terms.build_term t (EventE(Terms.app e2 (idx::tl), t2'))
		  | true, true ->
		    (* Duplicate the event. In case the arguments are not
                       just variables, we store them in variables to avoid
                       duplicating more complex code. *)
		      let binders = ref [] in
		      let tl' = List.map (fun t ->
			if is_var t then
			  t
			else
			  let b = Terms.create_binder "earg" t.t_type cur_array in
			  binders := (PatVar b, t) :: (!binders);
			  Terms.term_from_binder b
			    ) tl
		      in
		      let ev2 = Terms.build_term t (EventE(Terms.app e (idx::tl'), t2')) in
		      let ev1 = Terms.build_term t (EventE(Terms.app e2 (idx::tl'), ev2)) in
		      Terms.put_lets_term (!binders) ev1 None
		  | false, false ->
	            (* Can happen in case the event was already useless before the transformation *)
		      Terms.build_term t (EventE(t1',t2'))
		with Not_found ->
		  Terms.build_term t (EventE(t1',t2'))
	      end
	  | _ ->
	      Parsing_helper.internal_error "Events must be function applications"
	end
	  
    | InsertE _ | GetE _ ->
	Parsing_helper.internal_error "Insert/get should have been expanded"
	  
  and tr_guess_pat cur_array = function
    | PatVar b -> PatVar b
    | PatTuple(f,l) -> PatTuple(f, List.map (tr_guess_pat cur_array) l)
    | PatEqual t -> PatEqual (tr_guess_t cur_array t)
  in
  
  let add_assign_p x p =
    try
      let x' = List.assq x dup_vars in
      Terms.oproc_from_desc_loc p (Let(PatVar x', Terms.term_from_binder x, p,
				       Terms.oproc_from_desc Yield)) 
    with Not_found ->
      p
  in
  
  let rec tr_guess_i cur_array p =
    match p.i_desc with
    | Nil -> p
    | Par(p1,p2) ->
	Terms.iproc_from_desc_loc p
	  (Par(tr_guess_i cur_array p1,
	       tr_guess_i cur_array p2))
    | Repl(i,p1) ->
	Terms.iproc_from_desc_loc p (Repl(i, tr_guess_i (i :: cur_array) p1))
    | Input((c,tl),pat,p1) ->
	Terms.iproc_from_desc_loc p
	  (Input((c, List.map (tr_guess_t cur_array) tl), tr_guess_pat cur_array pat, tr_guess_p cur_array p1))

  and tr_guess_p cur_array p =
    match p.p_desc with
    | Yield -> p
    | EventAbort e ->
	begin
	  try
	    let (e1,e2,u1,u2) = List.find (fun (e1,_,_,_) -> e1 == e) dup_events in
	    match !u1, !u2 with
	    | true, false -> p
	    | false, true -> Terms.oproc_from_desc_loc p (EventAbort e2)
	    | true, true ->
		Terms.oproc_from_desc_loc p (EventP(Terms.app e2 [], p))
	    | false, false ->
	      (* Can happen in case the event was already useless before the transformation *)
		p
	  with Not_found ->
	    p
	end
    | Restr(b,p1) ->
	Terms.oproc_from_desc_loc p (Restr(b, add_assign_p b (tr_guess_p cur_array p1)))
    | Test(t,p1,p2) ->
	Terms.oproc_from_desc_loc p (Test(tr_guess_t cur_array t, tr_guess_p cur_array p1, tr_guess_p cur_array p2))
    | Find(l0,p3,find_info) ->
	let find_info' = update_find_info find_info in
	let l0' = List.map (fun (bl, def_list, t1, p2) ->
	  let vars = List.map fst bl in
	  let ri = List.map snd bl in
	  let p2' = tr_guess_p cur_array p2 in
	  let p2'' = List.fold_left (fun p b -> add_assign_p b p) p2' vars in
	  let t1' = tr_guess_t (ri @ cur_array) t1 in
	  (bl, def_list, t1', p2'')
	    ) l0
	in
	Terms.oproc_from_desc_loc p (Find(l0',tr_guess_p cur_array p3,find_info'))
	  
    | Output((c,tl),t,p1) ->
	Terms.oproc_from_desc_loc p (Output((c, List.map (tr_guess_t cur_array) tl),
					    tr_guess_t cur_array t, tr_guess_i cur_array p1))
    | Let(pat,t,p1,p2) ->
	let vars = Terms.vars_from_pat [] pat in
	let p1' = tr_guess_p cur_array p1 in
	let p1'' = List.fold_left (fun p b -> add_assign_p b p) p1' vars in
	Terms.oproc_from_desc_loc p (Let(tr_guess_pat cur_array pat, tr_guess_t cur_array t, p1'', tr_guess_p cur_array p2))

    | EventP(t,p1) -> 
	begin
	  let p1' = tr_guess_p cur_array p1 in
	  let t' = tr_guess_t cur_array t in
	  match t'.t_desc with
	  | FunApp(e,idx::tl) ->
	      begin
		try
		  let (e1,e2,u1,u2) = List.find (fun (e1,_,_,_) -> e1 == e) dup_events in
		  match !u1, !u2 with
		  | true, false -> Terms.oproc_from_desc_loc p (EventP(t',p1')) 
		  | false, true ->
		    (* Replace e with e2; e is no longer useful *)
		      Terms.oproc_from_desc_loc p (EventP(Terms.app e2 (idx::tl), p1'))
		  | true, true ->
		    (* Duplicate the event. In case the arguments are not
                       just variables, we store them in variables to avoid
                       duplicating more complex code. *)
		      let binders = ref [] in
		      let tl' = List.map (fun t ->
			if is_var t then
			  t
			else
			  let b = Terms.create_binder "earg" t.t_type cur_array in
			  binders := (PatVar b, t) :: (!binders);
			  Terms.term_from_binder b
			    ) tl
		      in
		      let ev2 = Terms.oproc_from_desc_loc p (EventP(Terms.app e (idx::tl'), p1')) in
		      let ev1 = Terms.oproc_from_desc_loc p (EventP(Terms.app e2 (idx::tl'), ev2)) in
		      Terms.put_lets (!binders) ev1 (Terms.oproc_from_desc Yield)
		  | false, false ->
	            (* Can happen in case the event was already useless before the transformation *)
		      Terms.oproc_from_desc_loc p (EventP(t',p1')) 
		with Not_found ->
		  Terms.oproc_from_desc_loc p (EventP(t',p1')) 
	      end
	  | _ ->
	      Parsing_helper.internal_error "Events must be function applications"
	end
	  
    | Insert _ | Get _ ->
	Parsing_helper.internal_error "Insert/get should have been expanded"
  in
  
  let p' = tr_guess_p cur_array p in
  List.fold_left (fun p b -> add_assign_p b p) p' assigned
    

(* [def_dup_var_t t] returns true when [t] defines variable
   that must be duplicated (variable queried for secrecy or one-session secrecy).
   [def_dup_var_pat] is similar for patterns. *)
    
let is_dup_var b =
  try
    let _ = List.assq b (!duplicated_vars) in
    true
  with Not_found ->
    false
    
let rec def_dup_var_t t =
  (match t.t_desc with
  | FindE(l0,p3,find_info) ->
      List.exists (fun (bl, def_list, t1, p2) ->
	List.exists (fun (b,_) -> is_dup_var b) bl
	  ) l0
  | LetE(pat, t1, t2, topt) -> 
      let vars = Terms.vars_from_pat [] pat in
      List.exists is_dup_var vars
  | ResE(b,t1) ->
      is_dup_var b
  | InsertE _ | GetE _ ->
      Parsing_helper.internal_error "Insert/get should have been expanded"
  | _ -> false) ||
    (Terms.exists_subterm def_dup_var_t (fun def_list -> false) def_dup_var_pat t)
      
and def_dup_var_pat pat = Terms.exists_subpat def_dup_var_t def_dup_var_pat pat

(* [transfo_i eq_test cur_array p] transforms the input process [p]
   located just under the replication or variable that we guess.
   [eq_test] is the equality test [i = i_tested] *)

let make_test eq_test cur_array assigned p =
  let p_then = transfo (!duplicated_vars) (!duplicated_events) cur_array assigned p in
  let p_else = transfo (!new_pub_vars) [] cur_array assigned p in
  Terms.oproc_from_desc (Test(eq_test, p_then, p_else))

let transfo_i eq_test cur_array p =
  let rec aux cur_array p =
    match p.i_desc with
    | Nil -> p
    | Par(p1,p2) ->
	Terms.iproc_from_desc_loc p
	  (Par(aux cur_array p1, aux cur_array p2))
    | Repl(i,p1) ->
	Terms.iproc_from_desc_loc p (Repl(i, aux (i :: cur_array) p1))
    | Input((c,tl),pat,p1) ->
	let pat = update_find_info_pat pat in
	if List.exists def_dup_var_t tl then
	  raise (Error("At occurrence "^(string_of_int p.i_occ)^", channel of input should not define a variable that must be duplicated", ext_command()));
	if def_dup_var_pat pat then
	  let b = Terms.create_binder "patv"
	      (Terms.get_type_for_pattern pat) cur_array
	  in
	  let bterm = Terms.term_from_binder b in
	  let p1' = Terms.oproc_from_desc (Let(pat, bterm, p1, Terms.oproc_from_desc Yield)) in
	  Terms.iproc_from_desc_loc p
	    (Input((c,tl), PatVar b, make_test eq_test cur_array [] p1'))
	else
	  let assigned = Terms.vars_from_pat [] pat in
	  Terms.iproc_from_desc_loc p
	    (Input((c,tl), pat, make_test eq_test cur_array assigned p1))

  in
  aux cur_array p


let rec full_transfo_i cur_array p =
  match p.i_desc with
  | Nil -> p
  | Par(p1,p2) ->
      Terms.iproc_from_desc_loc p
	(Par(full_transfo_i cur_array p1,
	     full_transfo_i cur_array p2))
  | Repl(i,p1) ->
      let cur_array' = i :: cur_array in
      let p1' =
	if is_selected_repl p then
	  let i_list =
	    if and_above() then
	      cur_array'
	    else
	      [i]
	  in
	  let ilist_tested =
	    List.map (fun ri -> get_cst ri.ri_sname ri.ri_type) i_list
	  in
	  let eq_test =
	    Terms.make_and_list 
	      (List.map2 (fun ri i_tested ->
		Terms.make_equal
		  (Terms.term_from_repl_index ri)
		  (Terms.app i_tested [])
		  ) i_list ilist_tested)
	  in
	  transfo_i eq_test cur_array' p1
	else
	  full_transfo_i cur_array' p1
      in
      Terms.iproc_from_desc_loc p (Repl(i, p1'))
  | Input(c,pat,p1) ->
      Terms.iproc_from_desc_loc p
	(Input(c,update_find_info_pat pat, full_transfo_p cur_array p1))
	
and full_transfo_p cur_array p =
  match p.p_desc with
  | Find(l0,p3,find_info) ->
      let find_info' = update_find_info_notransfo find_info in
      let l0' =
	List.map (fun (bl, def_list, t1, p2) ->
	  (bl, def_list, update_find_info_t t1, full_transfo_p cur_array p2)
	    ) l0
      in
      Terms.oproc_from_desc_loc p (Find(l0',full_transfo_p cur_array p3,find_info'))	
  | _ ->
      Terms.oproc_from_desc_loc p
	(Terms.map_suboproc (full_transfo_p cur_array) update_find_info_t
	   (fun def_list -> def_list) update_find_info_pat
	   (full_transfo_i cur_array) p)

let get_event_accu g =
  match !event_accu_ref with
  | Some event_accu -> event_accu
  | None ->
      let event_accu = ref [] in
      Improved_def.improved_def_game (Some event_accu) true g;
      event_accu_ref := Some (!event_accu);
      !event_accu

let cleanup_event_accu g =
  match !event_accu_ref with
  | Some event_accu ->
      Improved_def.empty_improved_def_game true g;
      event_accu_ref := None
  | None -> ()
	
let guess_session state g =
  let p = Terms.get_process g in
  (* Compute query_variables: variables on which test secrecy
     or one-session secrecy. Those that occur only under the
     guessed replication will be duplicated *)
  List.iter (function ((q,_),_) as q_proof ->
    match q with
    | _ when Settings.get_query_status q_proof != ToProve -> () (* I ignore already proved and inactive queries *)
    | QSecret (b,_,_) ->
	has_secrecy := true;
	Terms.addq_ref query_variables b
    | QEventQ _ -> ()
    | _ ->
	raise (Error("Cannot guess a value when there is an equivalence query to prove, or no query", ext_command()))
	  ) g.current_queries;
  fistate := { initial_queries = g.current_queries;
	       all_non_unique_events = ref [] };
  (* Compute the variables/events found under the guessed replication/elsewhere *)
  find_var_event_i [] false p;
  if not (!found_guess) then
    raise (Error("Could not find the designated replication", ext_command()));
  
  let dup_vars = 
    List.filter (fun b -> not (List.memq b (!variables_elsewhere))) (!variables_under_guess)
  in
  duplicated_vars := List.map (fun b -> (b, Terms.new_binder b)) dup_vars;
  let dup_events =
    List.filter (fun e -> not (List.memq e (!events_elsewhere))) (!events_under_guess)
  in
  duplicated_events :=
     List.map (fun e ->
       let e' =
	 if e.f_cat == NonUniqueEvent then
	   Terms.create_nonunique_event()
	 else
	   Terms.create_event (Terms.fresh_id e.f_name) (List.tl (fst e.f_type))
       in
       (e, e', ref false, ref false)
	 ) dup_events;

  (* Compute the new queries *)
  (*   Create a new physical place for the proof indication, 
       so that the proof is carried to the father game only when
       it is a full proof *)
  let current_queries' = List.map (fun (q, poptref) -> (q, ref (!poptref))) g.current_queries in
  let new_queries = ref [] in
  List.iter (function ((q, g_q), proof_opt) as q_proof ->
      match q with
      | _ when Settings.get_query_status q_proof != ToProve -> () 
          (* I ignore already proved and inactive queries *)
      | QSecret(b,pub_vars,one_session) ->
	  begin
	    try
	      let b' = List.assq b (!duplicated_vars) in
	      let pub_vars' =
		if one_session then
		  pub_vars
		else
		  let new_pub_var =
		    try
		      List.assq b (!new_pub_vars)
		    with Not_found ->
		      let b'' = Terms.new_binder b in
		      new_pub_vars := (b, b'') :: (!new_pub_vars);
		      b''
		  in
		  new_pub_var :: pub_vars
	      in
	      new_queries := (q, proof_opt, QSecret(b',pub_vars',one_session), []) :: (!new_queries)
	    with Not_found ->
	      ()
	  end
      | QEventQ(hyp,concl,pub_vars) ->
	  let is_inj = List.exists (fun (inj,_) -> inj) hyp in
	  (* Cannot transform injective correspondences *)
	  if is_inj then
	    let _, changed = transform_hyp hyp in
	    if changed then
	      begin
		(* If the query contains a duplicated event
		   in assumption, try to prove injectivity now,
                   and leave a non-injective query to prove *)
		match Check_corresp.remove_inj (get_event_accu g) g q with
		| None -> 
		    record_useful_corresp (hyp, concl, pub_vars)
		| Some(QEventQ(hyp', concl', pub_vars'), proba) ->
		    let hyp'', changed = transform_hyp hyp' in
		    assert changed;
		    record_useful_corresp (hyp'', concl', pub_vars');
		    new_queries := (q, proof_opt, QEventQ(hyp'', concl', pub_vars'), proba) :: (!new_queries)
		| _ -> assert false
	      end
	    else
	      record_useful_corresp (hyp, concl, pub_vars)
	  else
	    let hyp', changed = transform_hyp hyp in
	    record_useful_corresp (hyp', concl, pub_vars);
	    if changed then
	      new_queries := (q, proof_opt, QEventQ(hyp', concl, pub_vars), []) :: (!new_queries)

      | _ ->
	  Parsing_helper.internal_error "equivalence queries/absent query should have been eliminated earlier"
      ) current_queries';

  cleanup_event_accu g;
  if (!new_queries) == [] then
    raise (Error("Guess is useless: no query could be modified", ext_command()));
  
  let p' = full_transfo_i [] p in
  let g' = Terms.build_transformed_game p' g in
  g'.current_queries <- update_queries state g' (!new_queries) current_queries';
  (* Adding the new events to Stringmap.env so that they can be used in the "focus" command *)
  List.iter (fun (_,e2,_,used2) ->
    if !used2 then
      Stringmap.env := Stringmap.StringMap.add e2.f_name (Stringmap.EEvent e2) (!Stringmap.env)
	   ) (!duplicated_events);
  g'


let guess arg state g =
  reset();
  selected_guess := arg;
  try
    let g' =
      match arg with
      | GuessVar((b,l),no_test,ext) ->
	  guess_var ((b,l),ext) no_test state g
      | _ ->
	  guess_session state g
    in
    reset();
    Settings.changed := true;
    (g', [], [DGuess arg])
  with (Error _) as e ->
    reset();
    raise e

(***** Guess a branch *)
      
type state_ty =
    { whole_game : game;
      occ : int;
      no_test : bool;
      ext_o : Parsing_helper.extent;
      mutable to_do : bool;
      branch_num : int;
      has_secrecy : bool;
      mutable guess_br_var : binder option }

exception Finished
      
let may_be_inside state min_occ max_occ =
  if state.to_do then
    (min_occ <= state.occ) && (state.occ <= max_occ)
  else
    begin
      if (min_occ <= state.occ) && (state.occ <= max_occ) then
	Parsing_helper.internal_error "Ambiguous occurrence. That should never happen";
      false
    end

let check_unique_exec state pp cur_array =
  if state.branch_num = 0 && cur_array != [] then
    begin
      (* Check that the branching instruction at [pp] is executed once.
	 For speed, do it only for the first branch *)
      Depanal.reset [] state.whole_game;      
      let old_proba_zero = !Settings.proba_zero in
      Settings.proba_zero := true;
      Improved_def.improved_def_game None false state.whole_game;
      let cleanup() = 
        Improved_def.empty_improved_def_game false state.whole_game;
        assert (Depanal.final_add_proba() == []);
        Settings.proba_zero := old_proba_zero
      in
      try
	(* We create a new copy [cur_array'] of [cur_array] 
	   (when computing [diff_fact] below)
	   and show that: 
	     facts when executing [pp] with indices [cur_array] (this is [facts]/[simp_facts]/[nsimpfacts])
           + facts when executing [pp] with indices [cur_array'] (this is [facts_other_indices])
           + [cur_array <> cur_array'] (this is [diff_fact])
           implies a contradiction.
	   *)
	let (facts,_,_,_) = Facts.get_facts_at pp in
	let simp_facts = Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) facts in
	let nsimpfacts = Facts.true_facts_from_simp_facts simp_facts in 
	let diff_fact = Terms.make_or_list (List.map (fun b ->
	  let b_term = Terms.term_from_repl_index b in
	  let b_term' = Terms.term_from_repl_index (Terms.new_repl_index b) in
	  b.ri_link <- TLink b_term';
	  Terms.make_diff b_term b_term'
	    ) cur_array)
	in
	let facts_other_indices = List.map (Terms.copy_term Terms.Links_RI) nsimpfacts in
	List.iter (fun b -> b.ri_link <- NoLink) cur_array;
	let _ = Facts.simplif_add_list Facts.no_dependency_anal simp_facts (diff_fact::facts_other_indices) in
        cleanup();
        raise (Error("The guessed branching instruction must be executed at most once. I did not manage to prove that at occurrence "^(string_of_int state.occ), state.ext_o)) 
      with Contradiction -> 
        (* OK *)
        cleanup()
    end
  
      
let bad_guess_t() =
  Terms.build_term_type Settings.t_any (EventAbortE (Terms.e_bad_guess()))

let rec guess_t state cur_array t =
  if state.occ == t.t_occ then
    if state.to_do then
      let t' = 
	match t.t_desc with
	| TestE(t0,p1,p2) ->
	    begin
	      if state.no_test then
		begin
		  let branch = 
		    match state.branch_num with
		    | 0 -> p2
		    | 1 -> p1
		    | _ -> raise Finished
		  in
		  if Terms.check_simple_term t0 then
		    branch
		  else
		    let b = Terms.create_binder Settings.underscore_var_name t0.t_type cur_array in
		    Terms.build_term t (LetE(PatVar b, t0, branch, None))
		end
	      else
		match state.branch_num with
		| 0 -> Terms.build_term t (TestE(t0,bad_guess_t(),p2))
		| 1 -> Terms.build_term t (TestE(t0,p1,bad_guess_t()))
		| _ -> raise Finished
	    end
	| _ when state.no_test ->
	    raise (Error("At occurrence "^(string_of_int state.occ)^", guess_branch ... no_test can be applied only to \"if\" instructions", state.ext_o))
	| LetE(pat,t0,p1,popt) ->
	    begin
	      match pat with
	      | PatVar _ -> raise (Error("At occurrence "^(string_of_int state.occ)^", cannot guess branch for let <var> = ...", state.ext_o))
	      | _ -> ()
	    end;
	    begin
	      match state.branch_num with
	      | 0 -> Terms.build_term t (LetE(pat,t0,bad_guess_t(),popt))
	      | 1 -> Terms.build_term t (LetE(pat,t0,p1, Some (bad_guess_t())))
	      | _ -> raise Finished
	    end
	| FindE(l0,p2,find_info) ->
	    begin
	      if l0 == [] then
		raise (Error("At occurrence "^(string_of_int state.occ)^", cannot guess branch for an empty find", state.ext_o));
	      if state.branch_num = 0 then
		Terms.build_term t (FindE(List.map (fun (bl,def_list,t0,p1) ->
		  (bl,def_list,t0,bad_guess_t())
		    ) l0, p2, find_info))
	      else if state.branch_num <= List.length l0 then
		let l0' =
		  List.mapi (fun n (bl,def_list,t0,p1) ->
		    (bl,def_list,t0,
		     if n = state.branch_num-1 then
		       p1
		     else
		       bad_guess_t())
		      ) l0
		in
		Terms.build_term t (FindE(l0', bad_guess_t(),find_info))
	      else
		raise Finished
	    end
	| _ ->
	    raise (Error("At occurrence "^(string_of_int state.occ)^", can guess a branch only for if, let, and find", state.ext_o))
      in
      state.to_do <- false;
      check_unique_exec state (DTerm t) cur_array;
      if state.has_secrecy then
	let b = Terms.create_binder "guess_br_defined" Settings.t_bool cur_array in
	state.guess_br_var <- Some b;
	Terms.build_term_type t.t_type (LetE(PatVar b, Terms.make_true(), t', None))
      else
	t'
    else
      Parsing_helper.internal_error "Ambiguous occurrence. That should never happen"
  else if not (may_be_inside state t.t_occ t.t_max_occ) then
    t
  else
    Terms.build_term t 
      (Terms.map_subterm (guess_t state cur_array) (fun def_list -> def_list)
	 (guess_pat state cur_array) t)

and guess_pat state cur_array pat =
  Terms.map_subpat (guess_t state cur_array) (guess_pat state cur_array) pat


let bad_guess_p() = Terms.oproc_from_desc (EventAbort (Terms.e_bad_guess()))
	
let rec guess_i state cur_array p =
  if not (may_be_inside state p.i_occ p.i_max_occ) then
    p
  else
  let p_desc' =
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) ->
      Par(guess_i state cur_array p1,
	  guess_i state cur_array p2)
  | Repl(b,p) ->
      Repl(b, guess_i state (b::cur_array) p)
  | Input((c,tl),pat, p) ->
      let p' = guess_o state cur_array p in
      let pat' = guess_pat state cur_array pat in
      let tl' = List.map (guess_t state cur_array) tl in
      Input((c,tl'),pat',p')
  in
  Terms.iproc_from_desc_loc p p_desc'

and guess_o state cur_array p =
  if state.occ == p.p_occ then
    if state.to_do then
      let p' = 
	match p.p_desc with
	| Test(t,p1,p2) ->
	    begin
	      if state.no_test then
		begin
		  let branch = 
		    match state.branch_num with
		    | 0 -> p2
		    | 1 -> p1
		    | _ -> raise Finished
		  in
		  if Terms.check_simple_term t then
		    branch
		  else
		    let b = Terms.create_binder Settings.underscore_var_name t.t_type cur_array in
		    Terms.oproc_from_desc (Let(PatVar b, t, branch, Terms.oproc_from_desc Yield))
		end
	      else
		match state.branch_num with
		| 0 -> Terms.oproc_from_desc (Test(t,bad_guess_p(),p2))
		| 1 -> Terms.oproc_from_desc (Test(t,p1,bad_guess_p()))
		| _ -> raise Finished
	    end
	| _ when state.no_test ->
	    raise (Error("At occurrence "^(string_of_int state.occ)^", guess_branch ... no_test can be applied only to \"if\" instructions", state.ext_o))
	| Let(pat,t,p1,p2) ->
	    begin
	      match pat with
	      | PatVar _ -> raise (Error("At occurrence "^(string_of_int state.occ)^", cannot guess branch for let <var> = ...", state.ext_o))
	      | _ -> ()
	    end;
	    begin
	      match state.branch_num with
	      | 0 -> Terms.oproc_from_desc (Let(pat,t,bad_guess_p(),p2))
	      | 1 -> Terms.oproc_from_desc (Let(pat,t, p1,bad_guess_p()))
	      | _ -> raise Finished
	    end
	| Find(l0,p2,find_info) ->
	    begin
	      if l0 == [] then
		raise (Error("At occurrence "^(string_of_int state.occ)^", cannot guess branch for an empty find", state.ext_o));
	      if state.branch_num = 0 then
		Terms.oproc_from_desc (Find(List.map (fun (bl,def_list,t,p1) ->
		  (bl,def_list,t,bad_guess_p())
		    ) l0, p2, find_info))
	      else if state.branch_num <= List.length l0 then
		let l0' =
		  List.mapi (fun n (bl,def_list,t,p1) ->
		    (bl,def_list,t,
		     if n = state.branch_num-1 then
		       p1
		     else
		       bad_guess_p())
		      ) l0
		in
		Terms.oproc_from_desc (Find(l0', bad_guess_p(),find_info))
	      else
		raise Finished
	    end
	| _ ->
	    raise (Error("At occurrence "^(string_of_int state.occ)^", can guess a branch only for if, let, and find", state.ext_o))
      in
      state.to_do <- false;
      check_unique_exec state (DProcess p) cur_array;
      if state.has_secrecy then
	let b = Terms.create_binder "guess_br_defined" Settings.t_bool cur_array in
	state.guess_br_var <- Some b;
	Terms.oproc_from_desc (Let(PatVar b, Terms.make_true(), p',
				   Terms.oproc_from_desc Yield))
      else
	p'
    else
      Parsing_helper.internal_error "Ambiguous occurrence. That should never happen"
  else if not (may_be_inside state p.p_occ p.p_max_occ) then
    p
  else
    Terms.oproc_from_desc_loc p
      (Terms.map_suboproc (guess_o state cur_array) (guess_t state cur_array)
	 (fun def_list -> def_list) (guess_pat state cur_array) (guess_i state cur_array)
	 p)


let update_query v q =
  match q with
  | QSecret(b,pub_vars,one_session) ->
      begin
	match v with
	| None ->
		    (* v must be defined when there is a secrecy query *)
            assert false
	| Some b' ->
	    QSecret(b,b'::pub_vars,one_session)
      end
  | QEventQ _ ->
      q
  | _ ->
      Parsing_helper.internal_error "equivalence queries/absent query should have been eliminated earlier"


let guess_branch occ no_test ext_o state g =
  let p = Terms.get_process g in
  let has_secrecy = ref false in
  List.iter (function ((q,_),_) as q_proof ->
    match q with
    | _ when Settings.get_query_status q_proof != ToProve -> () (* I ignore already proved and inactive queries *)
    | QSecret _ ->
	has_secrecy := true;
    | QEventQ _ -> ()
    | _ ->
	raise (Error("Cannot guess a branch when there is an equivalence query to prove, or no query", ext_o))
	  ) g.current_queries;
  if no_test && (!has_secrecy) then
    raise (Error("guess_branch ... no_test is not allowed in the presence of secrecy queries", ext_o));
  let all_non_unique_events = ref [] in
  let p =
    if !has_secrecy then
      UpdateFindInfo.upd_i
	{ initial_queries = g.current_queries;
	  all_non_unique_events = all_non_unique_events } p
    else
      p
  in
  let g = Terms.build_transformed_game p g in
  let rec gen_case br_num =
    let loc_state =
      { whole_game = g;
        occ = occ;
	no_test = no_test;
	ext_o = ext_o;
	to_do = true;
	branch_num = br_num;
	has_secrecy = !has_secrecy;
	guess_br_var = None }
    in
    let p' = guess_i loc_state [] p in
    if loc_state.to_do then
      raise (Error("Could not find the designated program point (occurrence "^(string_of_int loc_state.occ)^")", ext_o));
    let g' = Terms.build_transformed_game p' g in
    let rest =
      try
	gen_case (br_num + 1)
      with Finished ->
	[]
    in
    (g', loc_state.guess_br_var)::rest
  in
  let g_var_list = gen_case 0 in
  let (g',_) = List.hd g_var_list in
  (* Compute the new queries *)
  (*   Create a new physical place for the proof indication, 
       so that the proof is carried to the father game only when
       it is a full proof *)
  let current_queries' = List.map (fun (q, poptref) -> (q, ref (!poptref))) g.current_queries in
  (* I ignore already proved and inactive queries *)
  let active_queries = List.filter (fun q ->
    Settings.get_query_status q == ToProve) current_queries'
  in
  let all_pub_vars = Settings.get_public_vars active_queries in
  let (corresp_queries, secrecy_queries) =
    List.partition (fun ((q,_),_) ->
      match q with
      | QEventQ _ -> true
      | QSecret _ -> false
      | _ -> assert false) active_queries
  in
  let new_queries = ref current_queries' in
  let proved_ql = List.map (fun ((q,_),_) -> q) corresp_queries in
  List.iter (function ((q, g), proof_opt) ->
      let add_queries =
	List.map (fun (g_new, _) ->
	  let proof_opt' = ref (if g_new == g' then ToProve else Inactive) in
	  ((q, g_new), proof_opt')
	    ) g_var_list
      in
      let full_proba =
	Polynom.p_sum (List.map (fun (g_new, _) -> Advt(g_new, true, [])) g_var_list)
      in
      proof_opt := Proved(proved_ql, full_proba, state);
      new_queries := add_queries @ (!new_queries)
				     ) corresp_queries;
  let corresp_and_old_queries = (!new_queries) in
  let all_non_unique_queries =
    List.map (fun (g_new,_) -> 
      List.map (fun f ->
	try
	  List.find (fun (((_,g_q),_) as q) ->
	    Terms.is_event_query f q && g_new == g_q
	      ) corresp_and_old_queries
	with Not_found ->
	  let new_q =
	    (Terms.build_event_query f all_pub_vars, g_new),
	    ref (if g_new == g' then ToProve else Inactive)
	  in
	  new_queries := new_q :: (!new_queries);
	  new_q
	    ) (!all_non_unique_events)
	) g_var_list
  in

  List.iter (function ((q, g), proof_opt) ->
      let add_queries =
	List.map (fun (g_new, v) ->
	  let q' = update_query v q in
	  let proof_opt' = ref (if g_new == g' then ToProve else Inactive) in
	  ((q', g_new), proof_opt')
	    ) g_var_list 
      in
      let full_proba =
	Polynom.p_sum (List.map2 (fun ((q',g_new),proof_opt') non_unique_queries ->
	  Advt(g_new, false, (q',proof_opt')::(List.map (fun ((q,g_new),proof_opt) -> (q, proof_opt)) non_unique_queries))
	    ) add_queries all_non_unique_queries)
      in
      proof_opt := Proved([q], full_proba, state);
      new_queries := add_queries @ (!new_queries)
				     ) secrecy_queries;

  
  List.iter (fun (g_new,_) -> g_new.current_queries <- (!new_queries)) g_var_list;
  Settings.changed := true;
  (g', [], [DGuessBranch occ])

(* [next_case state] returns 
   - [Some state'] where [state'] is the state to prove the queries in the next case
   (next branch). 
   - [None] in case all branches have already been proved *)

let next_case state =
  let prev_state = 
    match state.prev_state with
    | Some(GuessBranch _,_,_,prev_state) -> prev_state
    | _ -> assert false
  in
  let is_in_prev_state g =
    List.exists (fun ((q, g'), proof_opt) -> 
      g' == g
        ) prev_state.game.current_queries
  in
  try
    let (_,next_g), _ = 
      List.find (fun ((_,g), proof_opt) ->
        !proof_opt = Inactive && not (is_in_prev_state g)
          ) state.game.current_queries
    in
    List.iter (fun ((_,g),proof_opt) ->
      if g == next_g then
        begin
          assert (!proof_opt = Inactive);
          proof_opt := ToProve
        end
          ) state.game.current_queries;
    Some (next_g)
  with Not_found ->
    (* When [next_g] is not found, all cases of the GuessBranch instruction
       have been proved *)
    None
