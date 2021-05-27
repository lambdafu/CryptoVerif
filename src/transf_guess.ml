open Types
open Parsing_helper
  
let selected_repl = ref (GuessOcc(-1, dummy_ext))

let is_selected_repl p =
  match !selected_repl, p.i_desc with
  | GuessOcc(n,_), _ -> p.i_occ == n
  | GuessRepl(ri,_), Repl(ri',_) -> ri == ri'
  | _ -> false

let ext_command() =
  match !selected_repl with
  | GuessOcc(_,ext) | GuessRepl(_,ext) -> ext

	
let found_repl = ref false

let dummy_param = { pname = "?"; psize = 0 }
let repl_param = ref dummy_param
    
let query_variables = ref []
let events_under_repl = ref []
let events_elsewhere = ref []
let variables_under_repl = ref []
let variables_elsewhere = ref []

let duplicated_vars = ref ([]: (binder * binder) list) (* list of (initial var, image var) *)
let new_pub_vars = ref ([]: (binder * binder) list)
let duplicated_events = ref ([]: (funsymb * funsymb * bool ref * bool ref) list)
    (* list of (initial event, image event, initial event useful?, image event useful?) *)

let reset() =
  selected_repl := GuessOcc(-1, dummy_ext);
  found_repl := false;
  repl_param := dummy_param;
  query_variables := [];
  events_under_repl := [];
  events_elsewhere := [];
  variables_under_repl := [];
  variables_elsewhere := [];
  duplicated_vars := [];
  new_pub_vars := [];
  duplicated_events := []
    
let add_var under_repl b =
  if List.memq b (!query_variables) then
    let accu = if under_repl then variables_under_repl else variables_elsewhere in
    if not (List.memq b (!accu)) then accu := b :: (!accu)

let add_event under_repl e =
  let accu = if under_repl then events_under_repl else events_elsewhere in
  if not (List.memq e (!accu)) then accu := e :: (!accu)

let rec find_var_event_t under_repl t =
  match t.t_desc with
    Var(_,l) | FunApp(_,l) ->
      List.iter (find_var_event_t under_repl) l
  | ReplIndex _ -> ()
  | TestE(t1,t2,t3) ->
      find_var_event_t under_repl t1;
      find_var_event_t under_repl t2;
      find_var_event_t under_repl t3
  | FindE(l0,t3,_) ->
      List.iter (fun (bl,def_list,t1,t2) ->
	List.iter (fun (b,_) -> add_var under_repl b) bl;
	find_var_event_t under_repl t1;
	find_var_event_t under_repl t2) l0;
      find_var_event_t under_repl t3
  | ResE(b,t) ->
      add_var under_repl b;
      find_var_event_t under_repl t
  | EventAbortE f ->
      add_event under_repl f
  | LetE(pat, t1, t2, topt) ->
      find_var_event_pat under_repl pat;
      find_var_event_t under_repl t1;
      find_var_event_t under_repl t2;
      begin
      match topt with
	None -> ()
      |	Some t3 -> find_var_event_t under_repl t3
      end
  | EventE(({ t_desc = FunApp(f,_) } as t),p) ->
      add_event under_repl f;
      find_var_event_t under_repl t;
      find_var_event_t under_repl p
  | EventE _ ->
      Parsing_helper.internal_error "Events should be function applications"
  | GetE _|InsertE _ -> Parsing_helper.internal_error "Get/Insert should not appear here"
      
and find_var_event_pat under_repl = function
    PatVar b -> add_var under_repl b
  | PatTuple(_,l) -> List.iter (find_var_event_pat under_repl) l
  | PatEqual t -> find_var_event_t under_repl t

let rec find_var_event_i under_repl p =
  match p.i_desc with
  | Nil -> ()
  | Par(p1,p2) ->
      find_var_event_i under_repl p1;
      find_var_event_i under_repl p2
  | Repl(ri,p1) ->
      if is_selected_repl p then
	begin
	  if !found_repl then
	    raise (Error("The designated replication is not unique", ext_command()));
	  found_repl := true;
	  repl_param := Terms.param_from_type ri.ri_type;
	  find_var_event_i true p1
	end
      else
	find_var_event_i under_repl p1
  | Input((c,tl), pat, p1) ->
      List.iter (find_var_event_t under_repl) tl;
      find_var_event_pat under_repl pat;
      find_var_event_o under_repl p1

and find_var_event_o under_repl p =
  match p.p_desc with
  | Yield -> ()
  | EventAbort e -> add_event under_repl e
  | Restr(b,p1) ->
      add_var under_repl b;
      find_var_event_o under_repl p1
  | Test(t,p1,p2) ->
      find_var_event_t under_repl t;
      find_var_event_o under_repl p1;
      find_var_event_o under_repl p2
  | Find(l0,p3,_) ->
      find_var_event_o under_repl p3;
      List.iter (fun (bl,def_list,t,p1) ->
	List.iter (fun (b,_) -> add_var under_repl b) bl;
	find_var_event_t under_repl t;
	find_var_event_o under_repl p1
	  ) l0
  | Output((c, tl),t2,p1) ->
      List.iter (find_var_event_t under_repl) tl;      
      find_var_event_t under_repl t2;
      find_var_event_i under_repl p1
  | Let(pat, t, p1, p2) ->
      find_var_event_pat under_repl pat;
      find_var_event_t under_repl t;
      find_var_event_o under_repl p1;
      find_var_event_o under_repl p2
  | EventP(({ t_desc = FunApp(f,_) } as t),p) ->
      add_event under_repl f;
      find_var_event_t under_repl t;
      find_var_event_o under_repl p
  | EventP _ ->
      Parsing_helper.internal_error "Events should be function applications"
  | Get _| Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"


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
	let l0' = List.map (fun (bl, def_list, t1, p2) ->
	  let vars = List.map fst bl in
	  let ri = List.map snd bl in
	  let p2' = tr_guess_t cur_array p2 in
	  let p2'' = List.fold_left (fun t b -> add_assign_t b t) p2' vars in
	  let t1' = tr_guess_t (ri @ cur_array) t1 in
	  (bl, def_list, t1', p2'')
	    ) l0
	in
	Terms.build_term t (FindE(l0',tr_guess_t cur_array p3,find_info))
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
	let l0' = List.map (fun (bl, def_list, t1, p2) ->
	  let vars = List.map fst bl in
	  let ri = List.map snd bl in
	  let p2' = tr_guess_p cur_array p2 in
	  let p2'' = List.fold_left (fun p b -> add_assign_p b p) p2' vars in
	  let t1' = tr_guess_t (ri @ cur_array) t1 in
	  (bl, def_list, t1', p2'')
	    ) l0
	in
	Terms.oproc_from_desc_loc p (Find(l0',tr_guess_p cur_array p3,find_info))
	  
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
  match t.t_desc with
  | Var(_,l) | FunApp(_,l) -> List.exists def_dup_var_t l
  | ReplIndex i -> false
  | TestE(t1,t2,t3) -> (def_dup_var_t t1) || (def_dup_var_t t2) || (def_dup_var_t t3)
  | FindE(l0,p3,find_info) ->
      (List.exists (fun (bl, def_list, t1, p2) ->
	let vars = List.map fst bl in
	(def_dup_var_t p2) || (def_dup_var_t t1) ||
	(List.exists is_dup_var vars)
	  ) l0) || (def_dup_var_t p3)
  | LetE(pat, t1, t2, topt) -> 
      let vars = Terms.vars_from_pat [] pat in
      (List.exists is_dup_var vars) ||
      (def_dup_var_pat pat) ||
      (def_dup_var_t t1) ||
      (def_dup_var_t t2) ||
      (match topt with
      | None -> false
      | Some t3 -> def_dup_var_t t3)
  | ResE(b,t1) ->
      (is_dup_var b) || (def_dup_var_t t1)
  | EventAbortE e -> false
  | EventE(t1,t2) ->
      (def_dup_var_t t1) || (def_dup_var_t t2)
  | InsertE _ | GetE _ ->
      Parsing_helper.internal_error "Insert/get should have been expanded"
	  
and def_dup_var_pat  = function
  | PatVar b -> false
  | PatTuple(f,l) -> List.exists def_dup_var_pat l
  | PatEqual t -> def_dup_var_t t

(* [transfo_i eq_test cur_array p] transforms the input process [p]
   located just under the replication that we guess.
   [eq_test] is the equality test [i = i_tested] *)

let transfo_i eq_test cur_array p =
  let make_test cur_array assigned p =
    let p_then = transfo (!duplicated_vars) (!duplicated_events) cur_array assigned p in
    let p_else = transfo (!new_pub_vars) [] cur_array assigned p in
    Terms.oproc_from_desc (Test(eq_test, p_then, p_else))
  in
    
  let rec aux cur_array p =
    match p.i_desc with
    | Nil -> p
    | Par(p1,p2) ->
	Terms.iproc_from_desc_loc p
	  (Par(aux cur_array p1, aux cur_array p2))
    | Repl(i,p1) ->
	Terms.iproc_from_desc_loc p (Repl(i, aux (i :: cur_array) p1))
    | Input((c,tl),pat,p1) ->
	if List.exists def_dup_var_t tl then
	  raise (Error("At "^(string_of_int p.i_occ)^", channel of input should not define a variable that must be duplicated", ext_command()));
	if def_dup_var_pat pat then
	  let b = Terms.create_binder "patv"
	      (Terms.get_type_for_pattern pat) cur_array
	  in
	  let bterm = Terms.term_from_binder b in
	  let p1' = Terms.oproc_from_desc (Let(pat, bterm, p1, Terms.oproc_from_desc Yield)) in
	  Terms.iproc_from_desc_loc p
	    (Input((c,tl), PatVar b, make_test cur_array [] p1'))
	else
	  let assigned = Terms.vars_from_pat [] pat in
	  Terms.iproc_from_desc_loc p
	    (Input((c,tl), pat, make_test cur_array assigned p1))

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
	  let i_tested =
	    Settings.create_fun (Terms.fresh_id (i.ri_sname ^ "_tested"))
	      ([], i.ri_type) Std
	  in
	  (* Adding i_tested to Stringmap.env so that it can be used in 
	     the "replace" command *)
	  Stringmap.env := Stringmap.StringMap.add i_tested.f_name
	       (Stringmap.EFunc i_tested) (!Stringmap.env);
	  let eq_test =
	    Terms.make_equal
	      (Terms.term_from_repl_index i)
	      (Terms.app i_tested [])
	  in
	  transfo_i eq_test cur_array' p1
	else
	  full_transfo_i cur_array' p1
      in
      Terms.iproc_from_desc_loc p (Repl(i, p1'))
  | Input(c,pat,p1) ->
      Terms.iproc_from_desc_loc p
	(Input(c,pat, full_transfo_p cur_array p1))
	
and full_transfo_p cur_array p =
  match p.p_desc with
  | Yield | EventAbort _ -> p
  | Restr(b,p1) ->
      Terms.oproc_from_desc_loc p (Restr(b, full_transfo_p cur_array p1))
  | Test(t,p1,p2) ->
      Terms.oproc_from_desc_loc p (Test(t, full_transfo_p cur_array p1,
					full_transfo_p cur_array p2))
  | Find(l0,p3,find_info) ->
      let l0' =
	List.map (fun (bl, def_list, t1, p2) ->
	  (bl, def_list, t1, full_transfo_p cur_array p2)
	    ) l0
      in
      Terms.oproc_from_desc_loc p (Find(l0',full_transfo_p cur_array p3,find_info))	
  | Output(c,t,p1) ->
      Terms.oproc_from_desc_loc p (Output(c,t, full_transfo_i cur_array p1))
  | Let(pat,t,p1,p2) ->
      Terms.oproc_from_desc_loc p (Let(pat, t, full_transfo_p cur_array p1,
				       full_transfo_p cur_array p2))
  | EventP(t,p1) -> 
      Terms.oproc_from_desc_loc p (EventP(t, full_transfo_p cur_array p1))
  | Insert _ | Get _ ->
      Parsing_helper.internal_error "Insert/get should have been expanded"



let guess_session arg state g =
  reset();
  let p = Terms.get_process g in
  selected_repl := arg;
  (* Compute query_variables: variables on which test secrecy
     or one-session secrecy. Those that occur only under the
     guessed replication will be duplicated *)
  List.iter (function ((q,_),_) as q_proof ->
    match q with
    | _ when Settings.get_query_status q_proof != ToProve -> () (* I ignore already proved and inactive queries *)
    | QSecret (b,_,_) ->
	if not (List.memq b (!query_variables)) then
	  query_variables := b :: (!query_variables)
    | QEventQ _ -> ()
    | _ ->
	raise (Error("Cannot guess the tested session when there is an equivalence query to prove, or no query", ext_command()))
    ) g.current_queries;
  (* Compute the variables/events found under the guessed replication/elsewhere *)
  find_var_event_i false p;
  if not (!found_repl) then
    raise (Error("Could not find the designated replication", ext_command()));
  
  let dup_vars = 
    List.filter (fun b -> not (List.memq b (!variables_elsewhere))) (!variables_under_repl)
  in
  duplicated_vars := List.map (fun b -> (b, Terms.new_binder b)) dup_vars;
  let dup_events =
    List.filter (fun e -> not (List.memq e (!events_elsewhere))) (!events_under_repl)
  in
  duplicated_events :=
     List.map (fun e ->
       (e, Terms.create_event (Terms.fresh_id e.f_name) (List.tl (fst e.f_type)), ref false, ref false)
	 ) dup_events;

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
	      new_queries := (proof_opt, QSecret(b',pub_vars',one_session)) :: (!new_queries)
	    with Not_found ->
	      ()
	  end
      | QEventQ(hyp,concl,pub_vars) ->
	  let is_inj = List.exists (fun (inj,_) -> inj) hyp in
	  (* Cannot transform injective correspondences *)
	  if is_inj then
	    record_useful_corresp (hyp, concl, pub_vars)
	  else
	    let hyp', changed = transform_hyp hyp in
	    record_useful_corresp (hyp', concl, pub_vars);
	    if changed then
	      new_queries := (proof_opt, QEventQ(hyp', concl, pub_vars)) :: (!new_queries)

      | _ ->
	  Parsing_helper.internal_error "equivalence queries/absent query should have been eliminated earlier"
      ) current_queries';

  if (!new_queries) == [] then
    raise (Error("Guess is useless: no query could be modified", ext_command()));
  
  let p' = full_transfo_i [] p in
  let g' = Terms.build_transformed_game p' g in
  let new_queries' =
    List.map (fun (proof_opt,q) ->
      let proof_opt' = ref ToProve in
      proof_opt := Proved(MulQueryProba(!repl_param, (q,g'), proof_opt'), state);
      ((q,g'), proof_opt')
	) (!new_queries)
  in
  g'.current_queries <- new_queries' @ current_queries';
  (* Adding the new events to Stringmap.env so that they can be used in the "focus" command *)
  List.iter (fun (_,e2,_,used2) ->
    if !used2 then
      Stringmap.env := Stringmap.StringMap.add e2.f_name (Stringmap.EEvent e2) (!Stringmap.env)
	   ) (!duplicated_events);
  
  reset();
  Settings.changed := true;
  (g', [], [DGuess arg])

