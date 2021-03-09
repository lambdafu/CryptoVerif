open Types

(* Compute the runtime of the context *)

let rec make_length_term accu g t =
  match t.t_desc with
    FunApp(f,l) -> 
      Polynom.add_max accu (Length(f, make_length g l))
  | Var(b,l) ->
      Polynom.add_max accu (Maxlength(g, Terms.term_from_binder b))
  | ReplIndex b ->
      Polynom.add_max accu (Maxlength(g, Terms.term_from_repl_index b))
  | LetE(_,_,t2,t3opt) ->
      begin
	match t3opt with 
	  None -> make_length_term accu g t2
	| Some t3 -> make_length_term accu g t2; make_length_term accu g t3
      end
  | TestE(_, t2, t3) ->
      make_length_term accu g t2; make_length_term accu g t3
  | FindE(l,t,_) ->
      make_length_term accu g t;
      List.iter (fun (bl, def_list, t, t1) -> make_length_term accu g t1) l
  | ResE(_, t) ->
      make_length_term accu g t
  | EventAbortE _ ->
      ()
  | EventE(_,p) ->
      make_length_term accu g p
  | GetE _|InsertE _ -> Parsing_helper.internal_error "Get/Insert should not appear in make_length_term"

and make_length g = function
    [] -> []
  | (t::l) ->
      let l' = make_length g l in
      if t.t_type.toptions land Settings.tyopt_BOUNDED != 0 then
	l'
      else
	let accu = ref Polynom.empty_minmax_accu in
	make_length_term accu g t;
	(Polynom.p_max (!accu))::l'   (*Maxlength(g, t)::l'*)
	  
(* (!Settings.ignore_small_times)>0 when many details should be ignored.*)

let get_time_map = ref ((fun t -> raise Not_found) : term -> term list * int * int * repl_index list * (binder list * term list) list)
let whole_game = ref Terms.empty_game
let names_to_discharge = ref []

let rec time_list f = function
    [] -> Polynom.zero
  | (a::l) -> Polynom.sum (f a) (time_list f l)

let poly1 = Polynom.probaf_to_polynom (Cst 1.0)
	
let rec get_same f = function
  | [] -> raise Not_found
  | [a] -> f a
  | a::l ->
      let x = get_same f l in
      if f a == x then 
	x
      else
	raise Not_found
      
let rec get_oracle_for_node b n =
  match n.definition with
  | DInputProcess({ i_desc = Input((c,tl),_,_) }) ->
       (* Check that the indices of [o] are the same as the indices of [b].
	 That is useful in case [b] is defined in a condition of find. *)
      if (List.length tl == List.length b.args_at_creation) &&
	(Terms.is_args_at_creation b tl) then
	c
      else
	raise Not_found
  | _ ->
      match n.above_node with
      | None -> raise Not_found
      | Some n' -> get_oracle_for_node b n'

let get_oracle b =
  get_same (get_oracle_for_node b) b.def

type state_t =
    { remaining_indices: repl_index list;
      found_oracles: channel list;
      mutable current_candidate: (channel * repl_index list) option }

let rec find_oracles state t =
  match t.t_desc with
  | ReplIndex _ -> ()
  | Var(b,l) -> find_oracles_br state (b,l)
  | FunApp(_,l) -> List.iter (find_oracles state) l
  | _ -> Parsing_helper.internal_error "If/let/find/new unexpected in find_oracles"

and find_oracles_br state (b,l) =
  if List.for_all (fun t ->
    match t.t_desc with
    | ReplIndex _ ->  true
    | _ -> false) l then
    begin
      let li = List.map Terms.repl_index_from_term l in
      let can_improve_current_candidate =
	match state.current_candidate with
	| None -> List.length li > 1
	| Some (_,li') ->
	    (List.length li > List.length li') &&
	    (List.for_all2 (==) (Terms.lsuffix (List.length li') li) li')
      in
      if can_improve_current_candidate &&
	(List.for_all (fun ri -> List.memq ri state.remaining_indices) li)
      then
	try
	  state.current_candidate <- Some (get_oracle b, li)
	with Not_found -> ()
    end
  else
    List.iter (find_oracles state) l

let rec remove_one idx = function
  | [] -> assert false
  | a::l ->
      if a == idx then l else
      a::(remove_one idx l)
      
let rec find_all_oracles state tl =
  if List.length state.remaining_indices <= 1 then state else
  begin
    List.iter (find_oracles state) tl;
    match state.current_candidate with
    | None -> state
    | Some (ch, li) ->
	let new_state =
	  { remaining_indices = List.fold_left (fun accu i -> remove_one i accu) state.remaining_indices li;
	    found_oracles = ch :: state.found_oracles;
	    current_candidate = None }
	in
	find_all_oracles new_state tl
  end

let get_ri_mul indices tl =
  if (not (!Settings.use_oracle_count_in_result)) || (List.length indices <= 1) then
    [], None
  else
    let state =
      { remaining_indices = indices;
	found_oracles = [];
	current_candidate = None }
    in
    let state' = find_all_oracles state tl in
    tl, Some(state'.remaining_indices, Polynom.p_prod (List.map (fun ch -> OCount ch) state'.found_oracles))


let rec find_all_oracles_def_list state def_list =
  if List.length state.remaining_indices <= 1 then state else
  begin
    List.iter (find_oracles_br state) def_list;
    match state.current_candidate with
    | None -> state
    | Some (ch, li) ->
	let new_state =
	  { remaining_indices = List.fold_left (fun accu i -> remove_one i accu) state.remaining_indices li;
	    found_oracles = ch :: state.found_oracles;
	    current_candidate = None }
	in
	find_all_oracles_def_list new_state def_list
  end

let count_find_index bl def_list =
  let indices = List.map snd bl in
  if (not (!Settings.use_oracle_count_in_result)) || (List.length bl <= 1) then
    Polynom.probaf_to_polynom
      (Polynom.p_prod (List.map (fun ri -> Count (Terms.param_from_type ri.ri_type)) indices))
  else
    let state =
      { remaining_indices = indices;
	found_oracles = [];
	current_candidate = None }
    in
    let state' = find_all_oracles_def_list state def_list in
    Polynom.probaf_to_polynom
      (Polynom.p_prod ((List.map (fun ch -> OCount ch) state'.found_oracles) @
		       (List.map (fun ri -> Count (Terms.param_from_type ri.ri_type)) state'.remaining_indices)))
    
	
let rec time_for_term_in_context t (args, il, ik, repl_lhs, indices_exp) =
  let targs = time_list time_term args in
  if (!Settings.ignore_small_times)>0 then
    targs
  else
    let eqindexty = List.map (fun brepl -> Settings.t_interv(*brepl.btype*)) repl_lhs in
    let tupleargs = 
      Terms.app (Settings.get_tuple_fun (List.map (fun t -> t.t_type) args)) args
    in
    let t_context = 
      if (!Settings.front_end) == Settings.Oracles then
	Add(Add(Add(Mul (Cst (float_of_int (ik*il)), ActTime(AFunApp(Settings.f_plus), [])),
		    Mul (Cst (float_of_int (ik*il)), ActTime(AFunApp(Settings.f_mul), []))),
		Mul(Cst (float_of_int (4*ik+5+2*List.length args)), ActTime(AArrayAccess ik, []))),
	    Add(Mul(Cst (float_of_int (2*ik*(ik+1))), ActTime(AReplIndex, [])),
		Mul(Cst 2.0, ActTime(AArrayAccess il, []))))
      else
	Add(Add(Add(ActTime(AOut(eqindexty, t.t_type), make_length (!whole_game) [t]),
		    Add(Mul (Cst (float_of_int (ik*il)), ActTime(AFunApp(Settings.f_plus), [])),
			Mul (Cst (float_of_int (ik*il)), ActTime(AFunApp(Settings.f_mul), [])))),
		Add(Mul(Cst (float_of_int (3*ik)), ActTime(AOut(eqindexty, Settings.t_unit), [])),
		    Mul(Cst 2.0, ActTime(AOut(eqindexty, Settings.t_bitstring), make_length (!whole_game) [tupleargs])))),
	    Add(Add(Mul(Cst (float_of_int (3*ik+3)), ActTime(AIn ik, [])),
		    Mul(Cst (float_of_int (2*ik*(ik+1))), ActTime(AReplIndex, []))),
		Add(ActTime(AArrayAccess il, []), ActTime(AArrayAccess ik, []))))
    in
    let t_indexes = time_list (fun (_,tl) -> time_list time_term tl) indices_exp in
    Polynom.sum targs (Polynom.sum t_indexes (Polynom.probaf_to_polynom t_context))

and time_term t =
  try
    (* The term is transformed; compute the time of the context,
       not the time of t itself *)
    time_for_term_in_context t ((!get_time_map) t)
  with Not_found -> 
    (* The term is not transformed; simply compute the time of t *)
  match t.t_desc with
    ReplIndex b ->
      if (!Settings.ignore_small_times)>0 then
	Polynom.zero
      else
	Polynom.probaf_to_polynom (ActTime(AReplIndex, []))
  | Var(b,l) ->
      let tl = time_list time_term l in
      if (!Settings.ignore_small_times)>0 then
	tl
      else
	Polynom.sum tl (Polynom.probaf_to_polynom (ActTime(AArrayAccess (List.length l), [])))
  | FunApp(f,l) ->
      let tl = time_list time_term l in
      if (!Settings.ignore_small_times)>1 && 
	((f==Settings.f_and) || (f==Settings.f_or) || (f==Settings.f_not) ||
	(f==Settings.empty_tuple) ||
	(f.f_cat == Event) ||
	 ((l == []) && (Terms.equal_terms t (Stringmap.cst_for_type (snd f.f_type)))))
      then
	(* Ignore &&, ||, not, (), events, cst_ty 
	   when (!Settings.ignore_small_times)>1 *)
	tl
      else if (!Settings.ignore_small_times)>2  && 
	(match f.f_cat with
	  Equal | Diff -> true 
	| _ -> false) && 
	((List.hd l).t_type.toptions land Settings.tyopt_BOUNDED != 0)
      then
	(* Ignore the time for equality tests 
	   when (!Settings.ignore_small_times)>2 *)
	tl
      else if (!Settings.ignore_small_times)>2  && (l == []) 
      then
	tl
      else
	Polynom.sum tl (Polynom.probaf_to_polynom (ActTime(AFunApp f, make_length (!whole_game) l)))
  | ResE(b,t) ->
      let tt = time_term t in
      if (!Settings.ignore_small_times)>0 then
	tt
      else
	begin
	  (* When b is in names_to_discharge, "new b" is replaced with
	     "let b = cst" in the context *)
	  if List.memq b (!names_to_discharge) then
	    Polynom.sum tt (Polynom.sum 
	      (Polynom.probaf_to_polynom (ActTime(AArrayAccess (List.length b.args_at_creation), [])))
              (time_term (Stringmap.cst_for_type b.btype)))
	  else
	    Polynom.sum tt (Polynom.probaf_to_polynom 
	      (Add(ActTime(AArrayAccess (List.length b.args_at_creation), []), ActTime(ANew b.btype, []))))
	end
  | EventAbortE(f) ->
      Polynom.zero
  | TestE(t,t1,t2) ->
      let tp = Polynom.sum (time_term t) (Polynom.max (time_term t1) (time_term t2)) in
      if (!Settings.ignore_small_times)>0 then
	tp
      else
	Polynom.sum tp (Polynom.probaf_to_polynom (ActTime(AIf, [])))
  | FindE(l0,t3, _) ->
      let rec t_proc = function
	  [] -> time_term t3
	| (_,_,_,t2)::l -> Polynom.max (time_term t2) (t_proc l)
      in
      let tp = t_proc l0 in
      let max_blen = ref 0 in
      let args_at_creation = ref 0 in
      let rec t_test = function
	  [] -> tp
	| (bl, def_list, t, _)::l ->
	    let t_test1 = 
	      Polynom.sum (time_list time_binderref def_list)
	     (Polynom.sum (time_term t) 
	     (if (!Settings.ignore_small_times)>0 then 
	       Polynom.zero
	     else
	       Polynom.probaf_to_polynom (
	       match bl with
		 [] -> ActTime(AFind 0, [])
	       | ((b,_)::_) ->
		   let blen = List.length bl in
		   let argslen = List.length b.args_at_creation in
		   if blen > !max_blen then
		     begin
		       max_blen := blen;
		       args_at_creation := argslen
		     end;
		   ActTime(AFind blen, [])
		     )))
	    in
	    Polynom.sum (t_test l) (Polynom.product t_test1 (count_find_index bl def_list))
      in
      let tt = t_test l0 in
      if (!Settings.ignore_small_times)>0 then 
	tt
      else
	Polynom.sum tt (Polynom.probaf_to_polynom (Mul (Cst(float_of_int (!max_blen)), ActTime(AArrayAccess (!args_at_creation), []))))
  | LetE(pat, t, t1, topt) ->
      Polynom.sum (time_pat pat) (Polynom.sum (time_term t) 
	(Polynom.max (time_term t1) 
	   (match topt with
	     None -> Polynom.zero 
	   | Some t2 -> time_term t2)))
  | EventE(t,p) ->
      Polynom.sum (time_term t) (time_term p)
  | GetE _|InsertE _ -> Parsing_helper.internal_error "Get/Insert should not appear in time_term"
	
and time_pat = function
    PatVar b -> 
      if (!Settings.ignore_small_times)>0 then
	Polynom.zero
      else
	Polynom.probaf_to_polynom (ActTime(AArrayAccess (List.length b.args_at_creation), []))
  | PatTuple(f,l) ->
      let tl = time_list time_pat l in
      if (!Settings.ignore_small_times)>1 && 
	(f == Settings.empty_tuple) then
	(* Ignore let () when (!Settings.ignore_small_times)>1 *)
	tl
      else
	Polynom.sum tl (Polynom.probaf_to_polynom (ActTime(APatFunApp f, make_length (!whole_game) (List.map Terms.term_from_pat l))))
  | PatEqual t ->
      if (!Settings.ignore_small_times)>2 &&
	(t.t_type.toptions land Settings.tyopt_BOUNDED != 0)
      then
	time_term t 
      else
	Polynom.sum (time_term t) (Polynom.probaf_to_polynom (ActTime(AFunApp (Settings.f_comp Equal t.t_type t.t_type), make_length (!whole_game) [t])))

and time_binderref (b,l) = 
  let tl = time_list time_term l in
  if (!Settings.ignore_small_times)>0 then
    tl
  else
    Polynom.sum tl (Polynom.probaf_to_polynom (ActTime(AArrayAccess (List.length l), [])))

let rec time_term_ignore_tuple t =
  match t.t_desc with
    FunApp(f,l) when f.f_cat == Tuple ->
      time_list time_term_ignore_tuple l
  | _ -> time_term t

let time_term_ignore_top_tuple t =
  match t.t_desc with
    FunApp(f,l) when f.f_cat == Tuple ->
      time_list time_term l
  | _ -> time_term t

let rec time_pat_ignore_tuple = function
    PatTuple(f,l) when f.f_cat == Tuple ->
      time_list time_pat_ignore_tuple l
  | pat -> time_pat pat

let time_pat_ignore_top_tuple = function
    PatTuple(f,l) when f.f_cat == Tuple ->
      time_list time_pat l
  | pat -> time_pat pat

let rec time_process multiplier p =
  match p.i_desc with
    Nil -> Polynom.zero
  | Par(p1,p2) -> Polynom.sum (time_process multiplier p1) (time_process multiplier p2)
  | Repl(b,p) -> time_process (Polynom.product multiplier (Polynom.probaf_to_polynom (Count (Terms.param_from_type b.ri_type)))) p
  | Input((c,tl),pat,p) ->
      let ttl = Polynom.sum (time_list time_term tl) 
	 ((if (!Settings.ignore_small_times)>1 then time_pat_ignore_tuple else 
	 if (!Settings.front_end) == Settings.Oracles then time_pat_ignore_top_tuple else time_pat) pat) in
      let tt = 
	if ((!Settings.ignore_small_times)>0) || 
        ((!Settings.front_end) == Settings.Oracles) then
	  ttl
	else
	  Polynom.sum ttl (Polynom.probaf_to_polynom (ActTime(AIn(List.length tl), [])))
      in
      let multiplier =
	if (!Settings.use_oracle_count_in_result) &&
	  (match Polynom.polynom_to_probaf multiplier with
	  | Cst _ | Count _ -> false (* constant or single parameter: leave as it is *)
	  | _ -> true (* other, ie product of parameters: use the #c instead *)) then
	  Polynom.probaf_to_polynom (OCount c)
	else
	  multiplier
      in
      Polynom.sum (Polynom.product multiplier tt) (time_oprocess multiplier p)
	
and time_oprocess multiplier p = 
  match p.p_desc with
    Yield -> 
      if ((!Settings.ignore_small_times)>0) || 
         ((!Settings.front_end) == Settings.Oracles) then
	Polynom.zero
      else
	Polynom.product multiplier (Polynom.probaf_to_polynom (ActTime(AOut([], Settings.t_unit), [])))
  | EventAbort _ -> Polynom.zero
  | Restr(b,p) ->
      let tp = time_oprocess multiplier p in
      if (!Settings.ignore_small_times)>0 then
	tp
      else
	let tres = 
	  (* When b is in names_to_discharge, "new b" is replaced with
	     "let b = cst" in the context *)
	  if List.memq b (!names_to_discharge) then
	    Polynom.sum 
	      (Polynom.probaf_to_polynom (ActTime(AArrayAccess (List.length b.args_at_creation), [])))
              (time_term (Stringmap.cst_for_type b.btype))
	  else
	    Polynom.probaf_to_polynom 
			      (Add(ActTime(AArrayAccess (List.length b.args_at_creation), []), ActTime(ANew b.btype, [])))
	in
	Polynom.sum tp (Polynom.product multiplier tres)
  | Test(t,p1,p2) ->
      let ttest = 
	if (!Settings.ignore_small_times)>0 then
	  time_term t
	else
	  Polynom.sum (time_term t) (Polynom.probaf_to_polynom (ActTime(AIf, [])))
      in
      Polynom.sum (Polynom.product multiplier ttest)
	(Polynom.max (time_oprocess multiplier p1) (time_oprocess multiplier p2))
  | Find(l0,p2, _) ->
      let rec t_proc = function
	  [] -> time_oprocess multiplier p2
	| (_,_,_,p1)::l -> Polynom.max (time_oprocess multiplier p1) (t_proc l)
      in
      let tp = t_proc l0 in
      let max_blen = ref 0 in
      let args_at_creation = ref 0 in
      let rec t_test = function
	  [] -> Polynom.zero
	| (bl, def_list, t, _)::l ->
	    let t_test1 = 
	      Polynom.sum (time_list time_binderref def_list)
	     (Polynom.sum (time_term t) 
	     (if (!Settings.ignore_small_times)>0 then 
	       Polynom.zero
	     else
	       Polynom.probaf_to_polynom (
	       match bl with
		 [] -> ActTime(AFind 0, [])
	       | ((b,_)::_) ->
		   let blen = List.length bl in
		   let argslen = List.length b.args_at_creation in
		   if blen > !max_blen then
		     begin
		       max_blen := blen;
		       args_at_creation := argslen
		     end;
		   ActTime(AFind blen, [])
		     )))
	    in
	    Polynom.sum (t_test l) (Polynom.product t_test1 (count_find_index bl def_list))
      in
      let tt = t_test l0 in
      let tt2 = 
	if (!Settings.ignore_small_times)>0 then 
	  tt
	else
	  Polynom.sum tt (Polynom.probaf_to_polynom (Mul (Cst(float_of_int (!max_blen)), ActTime(AArrayAccess (!args_at_creation), []))))
      in
      Polynom.sum (Polynom.product multiplier tt2) tp
  | Output((c,tl),t2,p) ->
      let tp = Polynom.sum (time_list time_term tl) 
	  ((if (!Settings.ignore_small_times)>1 then time_term_ignore_tuple else
	  if (!Settings.front_end) == Settings.Oracles then time_term_ignore_top_tuple else time_term) t2)
      in
      let tout = 
	if ((!Settings.ignore_small_times)>0) ||
        ((!Settings.front_end) == Settings.Oracles) then
	  tp
	else
	  Polynom.sum tp (Polynom.probaf_to_polynom (ActTime(AOut(List.map (fun t -> t.t_type) tl, t2.t_type), make_length (!whole_game) (tl @ [t2]))))
      in
      Polynom.sum (Polynom.product multiplier tout) (time_process multiplier p)
  | Let(pat, t, p1, p2) ->
      Polynom.sum 
	(Polynom.product multiplier (Polynom.sum (time_pat pat) (time_term t)))
	(Polynom.max (time_oprocess multiplier p1) (time_oprocess multiplier p2))
  | EventP(t,p) ->
      Polynom.sum (Polynom.product multiplier (time_term t)) (time_oprocess multiplier p)
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

let compute_runtime_for_context g equiv map_fun names_discharge =
  whole_game := g;
  get_time_map := map_fun;
  names_to_discharge := names_discharge;
  let tp = time_process poly1 (Terms.get_process g) in
  let t = 
    if (!Settings.ignore_small_times)>0 then
      tp
    else
      let ((_,lm, _,_,_,_),_) = equiv in
      let rec countfuns = function
	  [] -> 0
	| (a::l) -> countfuns_fg a + countfuns l
      and countfuns_fg = function
	  ReplRestr(_,_,fgl) -> 1 + countfuns fgl
	| Fun _ -> 1
      in
      let nnewchannel = 2*(countfuns (List.map fst lm)) in
      Polynom.sum tp (Polynom.probaf_to_polynom (Mul(Cst (float_of_int nnewchannel), ActTime(ANewChannel, []))))
  in
  let r = Polynom.polynom_to_probaf t in
  whole_game := Terms.empty_game;
  get_time_map := (fun t -> raise Not_found);
  names_to_discharge := [];
  r

let compute_runtime_for g = 
  whole_game := g;
  get_time_map := (fun t -> raise Not_found);
  names_to_discharge := [];
  let r = Polynom.polynom_to_probaf (time_process poly1 (Terms.get_process g)) in
  whole_game := Terms.empty_game;
  r

(* [add_restr restr_list t] adds to time [t] the time needed to
   choose random numbers in [restr_list]. ([t] and the result
   are polynoms.) *)
    
let add_restr restr_list t =
  if (!Settings.ignore_small_times)>0 then
    t
  else
    Polynom.sum t
      (time_list (fun (b,_) ->
	Polynom.probaf_to_polynom 
	  (Add(ActTime(AArrayAccess (List.length b.args_at_creation), []),
	       ActTime(ANew b.btype, [])))) restr_list)

(* [product_repl_opt repl_opt t] multiplies [t] by
   the number of repetitions specified by [repl_opt]. 
   ([t] and the result are polynoms.)*)
      
let product_repl_opt repl_opt t =
  match repl_opt with
  | None -> t
  | Some b ->
      Polynom.product t (Polynom.probaf_to_polynom (Count (Terms.param_from_type b.ri_type)))
    
let rec time_fungroup = function
  | Fun(_,_,t,_) -> time_term t
  | ReplRestr(repl_opt, restr_list, fun_list) ->
      let tfun = time_list time_fungroup fun_list in
      let tfun_restr = add_restr restr_list tfun in
      product_repl_opt repl_opt tfun_restr
	 
let compute_runtime_for_fungroup g fg =
  whole_game := g; (* The game does not matter here,
		      it will be instantiated when we 
		      apply the crypto transformation *)
  get_time_map := (fun t -> raise Not_found);
  names_to_discharge := [];
  let res = Polynom.polynom_to_probaf (time_fungroup fg) in
  whole_game := Terms.empty_game;
  res

let max t t' = 
  match t, t' with
  | Zero, _ -> t'
  | _, Zero -> t
  | _ -> Max [ t; t' ]
    
let compute_add_time lhs rhs mul_param opt2 =
  let time_add1 =
    match opt2 with
    | Decisional ->
	let lhs_time = compute_runtime_for_fungroup Terms.lhs_game lhs in
	let rhs_time = compute_runtime_for_fungroup Terms.rhs_game rhs in
	max lhs_time rhs_time
    | Computational -> compute_runtime_for_fungroup Terms.lhs_game lhs
  in
  Polynom.p_mul((Sub(Count(mul_param),Cst 1.0)), time_add1)

(* Second version of compute_runtime_for_fungroup using #O *)

let rec time_list2 f = function
    [] -> ([], Polynom.zero)
  | (a::l) ->
      let (t1,t2) = f a in
      let (t1',t2') = time_list2 f l in
      (t1 @ t1',
       Polynom.sum t2 t2')

(* [time_fungroup fg] returns [tfun, time_restr]
   where [fg] calls oracle [oname] at most [count] times and 
   one execution of [oname] takes at most time [time], 
   for each [(count, oname, time)] in the list [tfun].
   [time_restr] is the time needed to evaluate random number
   generations not directly associated to oracles. *)
	
let rec time_fungroup = function
  | Fun(oname,_,t,_) ->
      ([Polynom.probaf_to_polynom (Cst 1.0), oname, time_term t],
       Polynom.zero)
  | ReplRestr(repl_opt, restr_list, [Fun (oname,_,t,_)]) ->
      ([ product_repl_opt repl_opt (Polynom.probaf_to_polynom (Cst 1.0)),
	 oname, add_restr restr_list (time_term t) ],
       Polynom.zero)
  | ReplRestr(repl_opt, restr_list, fun_list) ->
      let (tfun, totherrestr) = time_list2 time_fungroup fun_list in
      let t_restr = add_restr restr_list totherrestr in
      let t_restr_tot = product_repl_opt repl_opt t_restr in
      let tfun' =
	List.map (fun (count, oname, time) ->
	  (product_repl_opt repl_opt count, oname, time)) tfun
      in
      (tfun', t_restr_tot)
	
let compute_runtime_for_fungroup_totcount g fg =
  whole_game := g; (* The game does not matter here,
		      it will be instantiated when we 
		      apply the crypto transformation *)
  get_time_map := (fun t -> raise Not_found);
  names_to_discharge := [];
  let (tfun, trestr) = time_fungroup fg in
  let res =
    List.map (fun (count, oname, t) ->
      (Polynom.polynom_to_probaf count, oname, Polynom.polynom_to_probaf t)) tfun,
    Polynom.polynom_to_probaf trestr
  in
  whole_game := Terms.empty_game;
  res

let max2 (t1,t2) (t1',t2') =
  (List.map2 (fun (count, oname, t) (_, _, t') ->
    (count, oname, max t t')) t1 t1',
   max t2 t2')
    
let compute_add_time_totcount lhs rhs mul_param opt2 =
  let tfun, restr_time_add1 =
    match opt2 with
    | Decisional ->
	let lhs_time = compute_runtime_for_fungroup_totcount Terms.lhs_game lhs in
	let rhs_time = compute_runtime_for_fungroup_totcount Terms.rhs_game rhs in
	max2 lhs_time rhs_time
    | Computational -> compute_runtime_for_fungroup_totcount Terms.lhs_game lhs
  in
  let fun_time_add1 =
    Polynom.p_sum
      (List.map (fun (count, oname, t) ->
	let count1 = Polynom.p_mul((Sub(Count(mul_param),Cst 1.0)), count) in
	Polynom.p_mul(OptimIf(OCProbaFun("<=", [ count1; OCount oname ]),
			      count1, OCount oname),
		      t)
	  ) tfun)
  in
  Polynom.p_add (fun_time_add1, Polynom.p_mul((Sub(Count(mul_param),Cst 1.0)), restr_time_add1))
    
let compute_runtime_for_term g t =
  whole_game := g;
  get_time_map := (fun t -> raise Not_found);
  names_to_discharge := [];
  let res = Polynom.polynom_to_probaf (time_term t) in
  whole_game := Terms.empty_game;
  res
