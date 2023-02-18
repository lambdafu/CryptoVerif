open Types
open Parsing_helper

type pos_t =
  | Occ of int * Parsing_helper.extent * bool ref(*true when found*)
  | Fun of funsymb * Parsing_helper.extent * bool ref(*true when found*)
  
type arg_info_t =
  | Pos of pos_t list
  | Level of int
  | ToTerm of (int * Parsing_helper.extent * bool ref(*true when found*)) list option

type m_state_t =
    { m_arg_info : arg_info_t;
      m_game : game;
      mutable m_changes_done : detailed_instruct option;
      mutable m_changed : bool;
      mutable m_non_expanded : bool;
      mutable m_array_ref_computed : bool}

let add_change_move m_state orig final =
  m_state.m_changes_done <-
    match m_state.m_changes_done with
    | None -> Some (DMoveIf[orig,final])
    | Some(DMoveIf l) -> Some (DMoveIf((orig,final)::l))
    | _ -> assert false

let add_change_to_term m_state occ =
  m_state.m_changes_done <-
    match m_state.m_changes_done with
    | None -> Some (DMoveIfToTerm[occ])
    | Some(DMoveIfToTerm l) -> Some (DMoveIfToTerm(occ::l))
    | _ -> assert false

let check_found m_state =
  match m_state.m_arg_info with
  | ToTerm (Some l) ->
      List.iter (fun (n, ext, found) ->
	if not (!found) then
	  raise (Error("Occurrence "^(string_of_int n)^" not found", ext))
		) l
  | Pos l ->
      List.iter (function
	| Occ(n, ext, found) ->
	    if not (!found) then
	      raise (Error("Occurrence "^(string_of_int n)^" not found", ext))
	| Fun(f, ext, found) ->
	    if not (!found) then
	      raise (Error("No transformable occurrence of function "^f.f_name^" found", ext))	    
	  ) l 
  | _ -> ()

let has_array_ref m_state b =
  if not m_state.m_array_ref_computed then
    begin
      Array_ref.array_ref_process (Terms.get_process m_state.m_game);
      m_state.m_array_ref_computed <- true
    end;
  Array_ref.has_array_ref_q b m_state.m_game.current_queries
	
let rec has_effect m_state t =
  match t.t_desc with
  | Var(_,l) | FunApp(_,l) ->
      List.exists (has_effect m_state) l
  | ReplIndex _ -> false
  | EventAbortE _ | EventE _ -> true
  | TestE(t1,t2,t3) ->
      has_effect m_state t1 || has_effect m_state t2 || has_effect m_state t3
  | ResE(b,t) ->
      has_array_ref m_state b || has_effect m_state t
  | LetE(pat, t1, t2, topt) ->
      has_effect_pat m_state pat || has_effect m_state t1 || has_effect m_state t2 ||
      (match topt with
      | None -> false
      | Some t3 -> has_effect m_state t3)
  | FindE(l0,t3,find_info) ->
      (match l0, find_info with
      | [[],_,_,_], _ | _, Nothing ->
	  false (* unique event cannot happen
		   (no bound variable, single branch, or no unique event) *)
      | _ -> true) ||
	(List.exists (fun (bl,def_list,t1,t2) ->
	  List.exists (fun (b,_) -> has_array_ref m_state b) bl ||
	  has_effect m_state t1 || has_effect m_state t2
		     ) l0) || has_effect m_state t3
  | InsertE _ | GetE _ ->
      Parsing_helper.internal_error "insert/get should have been expanded" 
      
and has_effect_pat m_state = function
  | PatVar b -> has_array_ref m_state b
  | PatTuple(_,l) -> List.exists (has_effect_pat m_state) l
  | PatEqual t -> has_effect m_state t

let convert_to_term curarray m_state t =
  match t.t_desc with
  | FunApp(f, [t1;t2;t3]) when f.f_cat == If ->
      m_state.m_changed <- true;
      m_state.m_non_expanded <- true;
      add_change_to_term m_state t.t_occ;
      if has_effect m_state t2 || has_effect m_state t3 then
	let bcond = Terms.create_binder "bthen" Settings.t_bool curarray in
	let bthen = Terms.create_binder "bthen" t2.t_type curarray in
	let belse = Terms.create_binder "belse" t3.t_type curarray in
	let tf = Terms.build_term t (TestE(Terms.term_from_binder bcond,Terms.term_from_binder bthen,Terms.term_from_binder belse)) in
	let tf2 = Terms.build_term t (LetE(PatVar belse, t3, tf, None)) in
	let tf3 = Terms.build_term t (LetE(PatVar bthen, t2, tf2, None)) in
	Terms.build_term t (LetE(PatVar bcond, t1, tf3, None)) 
      else
	Terms.build_term t (TestE(t1,t2,t3))
  | _ -> raise Not_found

let rec find_if m_state level t =
  match t.t_desc with
  | FunApp(f, [t1;t2;t3]) when f.f_cat == If && (level = None || level = Some 0) ->
      Some (t.t_occ,t1,t2,t3)
  | _ ->
      if level = Some 0 then
	None
      else
	let level' =
	  match level with
	  | None -> None
	  | Some x -> Some (x-1)
	in
	match t.t_desc with
	| Var(b,l) ->
	    begin
	      match find_if_list m_state level' l with
	      | Some (orig_occ,t1,l2,l3) ->
		  Some(orig_occ,t1, Terms.build_term t (Var(b,l2)), Terms.build_term t (Var(b,l3)))
	      | None -> None
	    end
	| FunApp(f,l) ->
	    begin
	      match find_if_list m_state level' l with
	      | Some (orig_occ,t1,l2,l3) ->
		  Some(orig_occ,t1, Terms.build_term t (FunApp(f,l2)), Terms.build_term t (FunApp(f,l3)))
	      | None -> None
	    end
	| ReplIndex _ -> None
	| TestE _ | FindE _ | LetE _ | ResE _ | EventAbortE _ | EventE _ 
	| InsertE _ | GetE _ ->
	    Parsing_helper.internal_error "find_if allowed only for simple terms" 

and find_if_list m_state level = function
  | [] -> None
  | a::l ->
      match find_if m_state level a with
      | Some(orig_occ,t1,t2,t3) ->
	  Some(orig_occ,t1,t2::l,t3::l)
      | None ->
	  match find_if_list m_state level l with
	  | Some(orig_occ,t1,l2,l3) ->
	      Some(orig_occ,t1,a::l2,a::l3)
	  | None -> None
    
let transform_term curarray m_state t =
  match m_state.m_arg_info with
  | ToTerm lopt ->
      begin
	match lopt with
	| None ->
	    begin
	      try
		convert_to_term curarray m_state t
	      with Not_found -> t
	    end
	| Some l ->
	    try
	      let (occ, ext, found) = List.find (fun (occ,_,_) -> occ == t.t_occ) l in
	      try
		let t' = convert_to_term curarray m_state t in
		if !found then
		  Parsing_helper.internal_error "occurrence found twice";
		found := true;
		t'
	      with Not_found -> 
		raise (Error("if_fun function expected at occurrence "^(string_of_int occ), ext))
	    with Not_found ->
	      t
      end

  | Level n ->
      if not (Terms.check_simple_term t) then
	t
      else
	begin
	  match find_if m_state (Some n) t with
	  | None -> t
	  | Some(orig_occ,t1,t2,t3) ->
	      m_state.m_changed <- true;
	      add_change_move m_state orig_occ t.t_occ;
	      let f_if = Settings.get_if_fun t.t_type in
	      Terms.build_term t (FunApp(f_if, [t1;t2;t3]))	      
	end
      
  | Pos l ->
      try
	let triggering_elem =
	  List.find (function
	    | Occ(occ,ext,found) -> occ == t.t_occ
	    | Fun(f,ext,found) ->
		match t.t_desc with
		| FunApp(f',_) -> f == f'
		| _ -> false
		    ) l
	in
	if not (Terms.check_simple_term t) then
	  match triggering_elem with
	  | Occ(_,ext,_) ->
	      raise(Error("if_fun functions can only be moved within simple terms (containing only variables and function applications)", ext))
	  | Fun _ ->
	      t
	else
	  match t.t_desc with
	  | FunApp(f,_) when f.f_cat == If ->
	      begin
		match triggering_elem with
		| Occ(occ,ext,_) ->
		    raise(Error("function at occurrence "^(string_of_int occ)^" is already if_fun, cannot perform the move", ext))
		| Fun _ ->
		    assert false
	      end
	  | _ ->
	  match find_if m_state None t with
	  | None ->
	      begin
		match triggering_elem with
		| Occ(occ,ext,_) ->
		    raise(Error("no if_fun function found inside term at occurrence "^(string_of_int occ), ext))
		| Fun _ ->
		    t
	      end
	  | Some(orig_occ,t1,t2,t3) ->
	      begin
		match triggering_elem with
		| Occ(occ,_,found) ->
		    if !found then
		      Parsing_helper.internal_error "occurrence found twice (2)";
		    found := true
		| Fun(_,_,found) -> found := true
	      end;
	      m_state.m_changed <- true;
	      add_change_move m_state orig_occ t.t_occ;
	      let f_if = Settings.get_if_fun t.t_type in
	      Terms.build_term t (FunApp(f_if, [t1;t2;t3]))
      with Not_found -> t

let rec transfo_t cur_array m_state t =
  let t' = transform_term cur_array m_state t in
  Terms.build_term t' (Terms.map_subterm (transfo_t cur_array m_state) (fun def_list -> def_list) (transfo_pat cur_array m_state) t')

and transfo_pat cur_array m_state pat =
  Terms.map_subpat (transfo_t cur_array m_state) (transfo_pat cur_array m_state) pat

let rec transfo_i cur_array m_state p =
  match p.i_desc with
  | Repl(ri,p1) ->
      let p1' = transfo_i (ri::cur_array) m_state p1 in
      Terms.iproc_from_desc_loc p (Repl(ri,p1'))
  | _ -> Terms.iproc_from_desc_loc p
	(Terms.map_subiproc (transfo_i cur_array m_state) (fun c pat p1 ->
	  (c,transfo_pat cur_array m_state pat, transfo_p cur_array m_state p1)) p) 

and transfo_p cur_array m_state p =
  Terms.oproc_from_desc_loc p
    (Terms.map_suboproc (transfo_p cur_array m_state) (transfo_t cur_array m_state)
	   (fun def_list -> def_list) (transfo_pat cur_array m_state)
	   (transfo_i cur_array m_state) p)
    
let move_if arg g =
  let arg' =
    match arg with
    | MovePos l ->
	Pos(List.map (function
	  | MoveOcc(occ,ext) -> Occ(occ,ext,ref false)
	  | MoveFun(f,ext) -> Fun(f,ext,ref false)) l)
    | MoveLevel n -> Level n
    | MoveToTerm lopt ->
	ToTerm(match lopt with
	| None -> None
	| Some l -> Some (List.map (fun (occ,ext) -> (occ,ext,ref false)) l))
  in
  let m_state =
    { m_arg_info = arg';
      m_game = g;
      m_changes_done = None;
      m_changed = false;
      m_non_expanded = false;
      m_array_ref_computed = false }
  in
  let p = Terms.get_process g in
  let p' = transfo_i [] m_state p in
  check_found m_state;
  if m_state.m_changed then
    Settings.changed := true;
  if m_state.m_array_ref_computed then
    Array_ref.cleanup_array_ref();
  let g' =
    if m_state.m_non_expanded then
      Terms.build_transformed_game ~expanded:false p' g
    else
      Terms.build_transformed_game p' g
  in
  let changes =
    match m_state.m_changes_done with
    | None -> []
    | Some c -> [c]
  in
  (g', [], changes)
