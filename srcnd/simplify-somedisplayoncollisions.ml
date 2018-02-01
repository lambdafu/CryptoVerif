open Types

let whole_game = ref { proc = Terms.nil_proc; game_number = -1 }

let success_check_all_deps = ref [] 
let failure_check_all_deps = ref []

(* Priorities for orienting equalities into rewrite rules *)
let current_max_priority = ref 0
let priority_list = ref []

(* Create fresh replication indices *)

let repl_index_counter = ref 0
(* mapping from terms to fresh repl indexes *)
let repl_index_list = ref []

let new_repl_index_term t =
  let rec find_repl_index = function
      [] ->
	incr repl_index_counter;
	let b' = Terms.create_binder "!2" (!repl_index_counter) t.t_type [] in
	let rec node = { above_node = node;
			 binders = [b'];
			 true_facts_at_def = [];
			 def_vars_at_def = [];
			 future_binders = []; future_true_facts = [];
			 future_def_vars = [];
			 definition = DFunRepl }
	in
	b'.def <- [node];
	repl_index_list := (t,b') :: (!repl_index_list);
	b'
    | ((a,b')::l) ->
	if Terms.equal_terms a t then b' else
	find_repl_index l
  in
  find_repl_index (!repl_index_list)

let new_repl_index b = new_repl_index_term (Terms.term_from_binder b)

let rec map_find_indices = function
    [] -> []
  | (b::l) ->
      let l' = map_find_indices l in
      if Terms.is_repl b then 
	l' 
      else
	(b, Terms.term_from_binder (new_repl_index b)) :: l'

let get_binder t =
  match t.t_desc with
    Var(b,_) -> b
  | _ -> Parsing_helper.internal_error "Unexpected repl index in get_binder"

let true_facts_from_simp_facts (facts, subst, else_find) =
  subst @ facts

(* An element (t1, t2, b, lopt, T) in term_collisions means that
the equality t1 = t2 was considered impossible; it has
negligible probability because t1 depends on b[lopt] by decompos followed
by compos functions, the types T are the types obtained after applying
the decompos functions (they are large types), and t2 does not depend 
on b *)

let term_collisions = ref []

let any_term_name = "?"
let any_term_binder t = 
  let b' = Terms.create_binder any_term_name 0 t [] in
  let rec node = { above_node = node;
		   binders = [b'];
		   true_facts_at_def = [];
		   def_vars_at_def = [];
		   future_binders = []; future_true_facts = [];
		   future_def_vars = [];
		   definition = DNone }
  in
  b'.def <- [node];
  b'

let any_term t = Terms.term_from_binder (any_term_binder t.t_type)

let any_term_pat pat = 
  Terms.term_from_binder (any_term_binder (Terms.get_type_for_pattern pat))

let rec match_term3 next_f t t' = 
  match t.t_desc, t'.t_desc with
    Var (v,[]), _ when v.sname==any_term_name -> next_f()
  | Var (v,[]), _ when Terms.is_repl v -> 
    (* Check that types match *)
      if t'.t_type != v.btype then
	raise NoMatch;
      begin
	match v.link with
	  NoLink -> Terms.link v (TLink t')
	| TLink t -> if not (Terms.equal_terms t t') then raise NoMatch;
      end;
      next_f()
  | Var(b,l), Var(b',l') when b == b' -> 
      match_term_list3 next_f l l'
  | FunApp(f,[t1;t2]), FunApp(f',[t1';t2']) when f.f_options land Settings.fopt_COMMUT != 0 && f == f' ->
      (* Commutative function symbols *)
      begin
        try
          Terms.auto_cleanup (fun () ->
	    match_term3 (fun () -> match_term3 next_f t2 t2') t1 t1')
        with NoMatch ->
          match_term3 (fun () -> match_term3 next_f t2 t1') t1 t2'
      end
  | FunApp(f,l), FunApp(f',l') when f == f' ->
      match_term_list3 next_f l l'
  | _ -> raise NoMatch

and match_term_list3 next_f l l' = 
  match l,l' with
    [],[] -> next_f()
  | a::l,a'::l' ->
      match_term3 (fun () -> match_term_list3 next_f l l') a a'
  | _ -> Parsing_helper.internal_error "Different lengths in match_term_list"

let matches_pair t1 t2 t1' t2' =
  try
    Terms.auto_cleanup (fun () ->
      match_term3 (fun () -> match_term3 (fun () -> ()) t2 t2') t1 t1');
    true
  with NoMatch -> false

let rec cleanup_until l l' = 
  if l' == l then () else
  match l' with
    [] -> Parsing_helper.internal_error "cleanup_until"
  | (v::r) -> 
      v.link <- NoLink;
      cleanup_until l r

let eq_terms3 t1 t2 =
  let cur_bound_vars = !Terms.current_bound_vars in
  try
    match_term3 (fun () -> ()) t1 t2;
    true
  with NoMatch ->
    cleanup_until cur_bound_vars (!Terms.current_bound_vars);
    Terms.current_bound_vars := cur_bound_vars;
    false

let is_noninteractive b =
  match b.btype.tcat with
    Interv p -> p.poptions land Settings.popt_NONINTERACTIVE != 0
  | BitString -> Parsing_helper.internal_error "I would expect indices to have interval type in is_noninteractive"

(* Filter out the indices that are unique knowing other indices 
   (useful for reducing the probabilities of collision) 

   true_facts must not contain if/let/find/new. 
   if the initial indices contain "noninteractive" indices, we try
   to eliminate them, even by adding "interactive" indices, as follows: 
   we start from a list (initial_indices) of indices that consists of
   (1) the "noninteractive" indices in the initial useful indices
   (2) the "interactive" indices that occur in all_indices but not in the 
      initial useful indices
   (3) the "interactive" indices that occur in the initial indices
   and try to eliminate the indices in order. At each step, we check that all
   indices in the initial useful indices (used_indices) are uniquely 
   determined. 
   *)


let filter_indices_coll true_facts used_indices initial_indices =
  (* Filter the indices *)
  let useful_indices = ref [] in
  let useless_indices = ref [] in
  let used_indices_term = List.map Terms.term_from_binder used_indices in
  let rec filter_indices_rec = function
      [] -> ()
    | first_index::rest_indices ->
	List.iter (fun b -> 
	  let b' = new_repl_index b in
	  Terms.link b (TLink (Terms.term_from_binder b')))
	  (first_index::(!useless_indices));
	let true_facts' = List.map Terms.copy_term3 true_facts in
	let used_indices_term' = List.map Terms.copy_term3 used_indices_term in 
	Terms.cleanup();
	let diff_fact = Terms.make_or_list (List.map2 Terms.make_diff used_indices_term used_indices_term') in
	let facts = diff_fact :: (true_facts' @ true_facts) in
	try
	  ignore (Terms.auto_cleanup (fun () -> Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) facts));
	  (* The index cannot be removed *)
	  useful_indices := (!useful_indices) @ [first_index];
	  filter_indices_rec rest_indices
	with Contradiction ->
	  (* The index can be removed *)
	  useless_indices := first_index :: (!useless_indices);
	  filter_indices_rec rest_indices
  in
  filter_indices_rec initial_indices;
  if (!useless_indices) == [] then
    (* Removed no index, return the initial list physically, to facilitate
       testing that the list of index was unchanged *)
    initial_indices
  else    
    (!useful_indices)

(* Collision t1 = t2 means: for all indices in t1, t2 such that true_facts holds, eliminate collision t1 = t2.
   Collision t1' = t2' means: for all indices in t1', t2' such that true_facts' holds, eliminate collision t1' = t2'.
There is a substitution sigma such that
 * t1' = sigma t1', t2' = sigma t2
 * There is a subset common_facts of true_facts suchthat
   true_facts' contains at least sigma common_facts 
 * The same indices can be removed using common_facts as
   using true_facts, so that the used indices at t1 = t2 with common_facts
   are still really_used_indices.
Then we replace both calls with
  for all indices in t1, t2 and common_facts such that common_facts holds, 
  eliminate collision t1 = t2
This is more general than the two collisions and yields the same cardinal 
as t1 = t2. *)

let matches 
    (true_facts, used_indices, initial_indices, really_used_indices, t1, t2, b, lopt, tl)
    (true_facts', used_indices', initial_indices', really_used_indices', t1', t2', b', lopt', tl') =
  Terms.auto_cleanup(fun () ->
    if matches_pair t1 t2 t1' t2' then
      let common_facts = List.filter (fun f -> List.exists (fun f' -> eq_terms3 f f') true_facts') true_facts in
      Terms.cleanup();
      (* Check that we can remove the same indices using common_facts as with all facts *)
      if initial_indices == really_used_indices then
	(* If we removed no index, this is certainly true *)
	Some(common_facts, used_indices, initial_indices, really_used_indices, t1, t2, b, lopt, tl)
      else
      let really_used_indices'' = filter_indices_coll common_facts used_indices initial_indices in
      if Terms.equal_lists (==) really_used_indices really_used_indices'' then
	begin
	  (*
	  print_string "Simplify.matches ";
	  Display.display_term [] t1;
	  print_string " with ";
	  Display.display_term [] t2;
	  print_string " succeeds\n";
	  print_string "Common facts:\n";
	  List.iter (fun t ->
	    Display.display_term [] t; print_newline()) common_facts; *)
	  Some(common_facts,  used_indices, initial_indices, really_used_indices, t1, t2, b, lopt, tl)
	end
      else
	begin
	  (*
	  print_string "Simplify.matches ";
	  Display.display_term [] t1;
	  print_string " with ";
	  Display.display_term [] t2;
	  print_string " fails\n";
	  print_string "True facts:\n";
	  List.iter (fun t ->
	    Display.display_term [] t; print_newline()) true_facts;
	  print_string "True facts':\n";
	  List.iter (fun t ->
	    Display.display_term [] t; print_newline()) true_facts';
	  print_string "Common facts:\n";
	  List.iter (fun t ->
	    Display.display_term [] t; print_newline()) common_facts;
	  print_string "used_indices\n";
	  Display.display_list Display.display_binder used_indices;
	  print_newline();
	  print_string "initial_indices\n";
	  Display.display_list Display.display_binder initial_indices;
	  print_newline();
	  print_string "really_used_indices\n";
	  Display.display_list Display.display_binder really_used_indices;
	  print_newline();
	  print_string "really_used_indices''\n";
	  Display.display_list Display.display_binder really_used_indices'';
	  print_newline();*)
	  None
	end
    else
      None)

let add_term_collisions (all_indices, map_find_indices, true_facts) t1 t2 b lopt tl =
  (* If no type is a "password" type, the term will be small anyway, no need to worry *)
  let must_optimize = List.exists Proba.is_passwd tl in
  (* Map everything with map_find_indices, to replace indices of find with fresh
     replication indices.
     For some calls, some parts have already been mapped by map_find_indices,
     but not all (in particular the true_facts) *)
  let true_facts = if must_optimize then List.map (Terms.subst3 map_find_indices) true_facts else [] in
  let t1 = Terms.subst3 map_find_indices t1 in
  let t2 = Terms.subst3 map_find_indices t2 in
  let lopt = match lopt with
    None -> None
  | Some l -> Some (List.map (Terms.subst3 map_find_indices) l) 
  in
  let all_indices_ref = ref (List.map (fun b ->
    try
      get_binder (List.assq b map_find_indices)
    with Not_found ->
      b) all_indices)
  in
  (* Add the indices of t1,t2 to all_indices; some of them may be missing
     initially because array indices in t1,t2 that depend on "bad" variables
     are replaced with fresh indices, and these indices are not included in
     all_indices initially (all_indices contains the replication and find
     indices above the considered terms) *)
  Proba.collect_array_indexes all_indices_ref t1;
  Proba.collect_array_indexes all_indices_ref t2;
  let all_indices = !all_indices_ref in
  (* Compute the used indices *)
  let used_indices_ref = ref [] in
  Proba.collect_array_indexes used_indices_ref t1;
  Proba.collect_array_indexes used_indices_ref t2;
  let used_indices = !used_indices_ref in
  let collision_info = 
    if not must_optimize then 
      ([], used_indices, used_indices, used_indices, t1, t2, b, lopt, tl)
    else
  (* Try to reduce the list of used indices. 
     Compute the initial list of indices to start with.
     - if all indices in used_indices_ref are "interactive",
       then we start from used_indices_ref
     - otherwise, we add "interactive" indices from all_indices;
       the goal is to try to remove "non-interactive" indices
       of used_indices_ref, perhaps at the cost of adding more
       "interactive" indices (because interactive indices are
       expected to be much smaller than non-interactive indices) *)
      let initial_indices =
	if not (List.exists is_noninteractive used_indices) then
	  used_indices
	else
	  (List.filter is_noninteractive used_indices) @
	  (List.filter (fun b -> not (is_noninteractive b || List.memq b used_indices)) all_indices) @
	  (List.filter (fun b -> not (is_noninteractive b)) used_indices)
      in
      let really_used_indices = filter_indices_coll true_facts used_indices initial_indices in
      (
      (* I can forget the facts without losing precision when I removed no index *)
      (if initial_indices == really_used_indices then [] else true_facts), 
      used_indices, initial_indices, really_used_indices, t1, t2, b, lopt, tl) 
  in
    (* I remove an entry when another entry is an instance of it,
       obtained by substituting terms for replication indexes *)
  let rec find_more_general_coll = function
      [] -> raise Not_found
    | (collision_info' :: rest) ->
	match matches collision_info' collision_info with
	  Some collision_info'' -> collision_info'' :: rest
	| None -> collision_info' :: (find_more_general_coll rest)
  in
  try
    term_collisions := find_more_general_coll (!term_collisions)
  with Not_found ->
    let new_coll = ref collision_info in
    let term_collisions' = List.filter (fun collision_info' -> 
      match matches (!new_coll) collision_info' with
	None -> true
      |	Some collision_info'' -> new_coll := collision_info''; false) (!term_collisions)
    in
    term_collisions := (!new_coll) :: term_collisions'

let proba_for_term_collision (_, _, _, really_used_indices, t1, t2, b, lopt, tl) =
  print_string "Eliminated collisions between ";
  Display.display_term [] t1;
  print_string " and ";
  Display.display_term [] t2;
  print_string " Probability: ";  
  let nindex = Proba.prod (List.map (fun array_idx -> Proba.card array_idx.btype) really_used_indices) in
  let p = 
    match tl with
      [t] -> Div(nindex, Proba.card t)
    | _ -> Proba.sum (List.map (fun t -> Div(nindex, Proba.card t)) tl)
  in
  Display.display_proba 0 p;
  print_newline();
  print_string "(";
  Display.display_term [] t1;
  print_string " characterizes a part of ";
  begin
  match lopt with
    None ->   Display.display_binder b; print_string "[...]"
  | Some l -> Display.display_var [] b l 
  end;
  print_string " of type(s) ";
  Display.display_list (fun t -> print_string t.tname) tl;
  print_string ";\n ";
  Display.display_term [] t2;
  print_string " does not depend on ";
  begin
  match lopt with
    None ->   Display.display_binder b; print_string "[...]"
  | Some l -> Display.display_var [] b l 
  end;
  print_string ")\n";
  p
  

(* Initialization of probability counting *)  

let partial_reset g = 
  whole_game := g;
  success_check_all_deps := [];
  failure_check_all_deps := [];
  current_max_priority := 0;
  List.iter (fun b -> b.priority <- 0) (!priority_list);
  priority_list := []

let reset coll_elim internal_info g =
  partial_reset g;
  Proba.reset coll_elim internal_info g;
  term_collisions := [];
  repl_index_list := []

(* Final addition of probabilities *)

let final_add_proba() =
  Proba.final_add_proba (List.map proba_for_term_collision (!term_collisions))

(* Dependency analysis
   When M1 characterizes a part of x of a large type T
   and M2 does not depend on x, then M1 = M2 fails up to
   negligible probability.
   The module FindCompos defines "characterize"
   The modules DepAnal1 and DepAnal2 perform dependency analyses
   Function dependency_collision concludes *)

module FindCompos : sig

type status = Compos | Decompos | Any

type charac_type =
    CharacType of typet
  | CharacTypeOfVar of binder

type 'a depinfo =
   (binder * (status * 'a)) list option * term list
      (* The dependency information has two components (dep, nodep):
	 If dep = Some l where l is a list of (variable, ...), such that it 
	 is guaranteed only variables in this list depend on the considered 
	 variable x[l].
	 If dep = None, we have no information of this kind; any variable 
	 may depend on x.
	 nodep is a list of terms that are guaranteed not to depend on x[l].
	 *)

val init_elem : 'a depinfo

val depends : (binder * 'a depinfo) -> term -> bool

  (* is_indep (b, depinfo) t returns a term independent of b
     in which some array indexes in t may have been replaced with
     fresh replication indexes. When t depends on b by variables
     that are not array indexes, raise Not_found *)
val is_indep : (binder * 'a depinfo) -> term -> term

val remove_dep_array_index : (binder * 'a depinfo) -> term -> term
val remove_array_index : term -> term

val find_compos : ((binder * (status * 'a)) -> term list -> (status * charac_type) option) -> 'a depinfo -> (binder * (status * 'a)) -> term -> (status * charac_type * term) option

val find_compos_list : ((binder * (status * 'a)) -> term list -> (status * charac_type) option) -> 'a depinfo -> (binder * (status * 'a)) list -> term -> (status * charac_type * term * binder * 'a) option

end
=
struct

let init_elem = (None, [])

let rec depends ((b, (dep,nodep)) as bdepinfo) t = 
  match t.t_desc with
    FunApp(f,l) -> List.exists (depends bdepinfo) l
  | Var(b',[]) when Terms.is_repl b' -> false
  | Var(b',l) ->
      (not (List.exists (Terms.equal_terms t) nodep)) && 
      ((
       ((b == b') || (not (Terms.is_restr b'))) &&
       (match dep with
	 None -> true
       | Some dl -> List.exists (fun (b'',_) -> b'' == b') dl
	  )) || (List.exists (depends bdepinfo) l))
  | _ -> true (*Rough overapproximation of the dependency analysis when
       if/let/find/new occur.
       Parsing_helper.internal_error "If/let/find/new unexpected in DepAnal1.depends"*)

let rec is_indep ((b0, (dep,nodep)) as bdepinfo) t =
  Terms.build_term2 t
     (match t.t_desc with
	FunApp(f,l) -> FunApp(f, List.map (is_indep bdepinfo) l)
      | Var(b,[]) when Terms.is_repl b -> t.t_desc
      |	Var(b,l) ->
	  if (List.exists (Terms.equal_terms t) nodep) then
	    t.t_desc 
	  else if (b != b0 && Terms.is_restr b) || (match dep with
	      None -> false
	    | Some dl -> not (List.exists (fun (b',_) -> b' == b) dl))
	  then
	    Var(b, List.map (fun t' ->
	      try
		is_indep bdepinfo t'
	      with Not_found ->
		Terms.term_from_binder (new_repl_index_term t')) l)
	  else
	    raise Not_found
      | _ -> Parsing_helper.internal_error "If/let/find/new unexpected in is_indep")

let rec remove_dep_array_index ((b0, (dep,nodep)) as bdepinfo) t =
  Terms.build_term2 t 
     (match t.t_desc with
	FunApp(f,l) -> FunApp(f, List.map (remove_dep_array_index bdepinfo) l)
      | Var(b,[]) when Terms.is_repl b -> t.t_desc
      |	Var(b,l) ->
	  if (List.exists (Terms.equal_terms t) nodep) then
	    t.t_desc 
	  else 
	    Var(b, List.map (fun t' -> 
	      if depends bdepinfo t' then
		Terms.term_from_binder (new_repl_index_term t')
	      else
		t') l)
      | _ -> Parsing_helper.internal_error "If/let/find/new unexpected in remove_dep_array_index")

let rec remove_array_index t =
  Terms.build_term2 t 
     (match t.t_desc with
	FunApp(f,l) -> FunApp(f, List.map remove_array_index l)
      | Var(b,[]) when Terms.is_repl b -> t.t_desc
      |	Var(b,l) ->
	  Var(b, List.map (fun t' ->
	    match t'.t_desc with
	      Var(b',[]) when Terms.is_repl b' -> t'
	    | _ -> Terms.term_from_binder (new_repl_index_term t')
		  ) l)
      | _ -> Parsing_helper.internal_error "If/let/find/new unexpected in remove_dep_array_index")

let reduced = ref false

(* Same as apply_reds but do not apply collisions, and apply statements
   only at the root of the term *)
let apply_statement2 t t_state =
  match t_state.t_desc, t.t_desc with
    FunApp(f1, [redl;redr]), FunApp(f,l) when f1.f_cat == Equal ->
      begin
	try
	  Facts.match_term (fun () -> 
	    let t' = Terms.copy_term redr in
	    Terms.cleanup();
	    reduced := true;
	    t'
	      ) ([],[],[]) [] redl t
	with NoMatch ->
	  Terms.cleanup();
	  t
      end
  | _ -> t

let rec apply_all_red2 t = function
    [] -> t
  | ((_,t_state)::l) ->
      let t' = apply_statement2 t t_state in
      if !reduced then t' else apply_all_red2 t l

let rec apply_statements t =
  reduced := false;
  let t' = apply_all_red2 t (!Transform.statements) in
  if !reduced then 
    apply_statements t' 
  else
    t


(* find_compos b t returns true when t characterizes b: only one
value of b can yield a certain value of t *)

type status = Compos | Decompos | Any

type charac_type =
    CharacType of typet
  | CharacTypeOfVar of binder

type 'a depinfo =
  (binder * (status * 'a)) list option * term list

let rec find_decompos_bin check ((b,_) as b_st) b' t t' =
  (Proba.is_large_term t || Proba.is_large_term t') && (t'.t_type == t.t_type) &&
  (match t.t_desc, t'.t_desc with
    Var(b1,l), Var(b1',l') when 
    (b == b1 && b' == b1') || (b == b1' && b' == b1) -> 
      (check b_st l != None) && (check b_st l' != None)
  | FunApp(f,l), FunApp(f',l') when 
      (f.f_options land Settings.fopt_UNIFORM) != 0  && (f == f') ->
      List.exists2 (find_decompos_bin check b_st b') l l'
  | _ -> false)
  
let rec find_compos_bin check ((b,(st,_)) as b_st) b' fact =
  match fact.t_desc with
   FunApp(f,[t1;t2]) when f.f_cat == Equal ->
      begin
      match (t1.t_desc, t2.t_desc) with
      	Var(b1,l1), Var(b2,l2) when (b1 == b && b2 == b') ->
	  if check b_st l2 != None then check b_st l1 else None
      |	Var(b1,l1), Var(b2,l2) when (b1 == b' && b2 == b) -> 
	  if check b_st l1 != None then check b_st l2 else None
      |	(FunApp(f1,l1), FunApp(f2,l2)) when
	(f1.f_options land Settings.fopt_COMPOS) != 0 && f1 == f2 -> 
	  find_compos_bin_l check b_st b' l1 l2
      |	(FunApp(f1,l1), FunApp(f2,l2)) when
	(f1.f_options land Settings.fopt_UNIFORM) != 0  && f1 == f2 ->
	  if (Proba.is_large_term t1 || Proba.is_large_term t2) && (st = Decompos) && 
	    (List.exists2 (find_decompos_bin check b_st b') l1 l2)
	  then Some (Decompos, CharacType t1.t_type)  else None
      |	_ -> None
      end
  | FunApp(f,[t1;t2]) when f == Settings.f_and ->
      begin
	match find_compos_bin check b_st b' t1 with
	  None -> find_compos_bin check b_st b' t2
	| x -> x
      end
  | _ -> None
    
and find_compos_bin_l check b_st b' l1 l2 =
  match (l1,l2) with
    [],[] -> None
  | (a1::l1,a2::l2) ->
      begin
      match find_compos_bin check b_st b' (apply_statements (Terms.make_equal a1 a2)) with
	None -> find_compos_bin_l check b_st b' l1 l2
      |	Some(_, charac_type) -> Some(Compos,charac_type)
      end
  | _ -> Parsing_helper.internal_error "Lists of different lengths in find_compos_bin_l"
      
let rec subst depinfo assql t =
  Terms.build_term2 t 
     (match t.t_desc with
	Var(b,l) -> Var(
	  (try List.assq b (!assql) with Not_found ->
            (* Do not rename variables that do not depend on the
	       variable argument of find_compos *)
	    if (Terms.is_restr b) || (Terms.is_repl b) ||
	       (match depinfo with
	         (Some dl,tl) ->
		   (not (List.exists (fun (b',_) -> b' == b) dl)) ||
		   (List.exists (Terms.equal_terms t) tl)
	       | (None, tl) -> List.exists (Terms.equal_terms t) tl)
	    then b else 
	    let r = Terms.new_binder b in
	    assql := (b,r)::(!assql);
	    r), List.map (subst depinfo assql) l)
      | FunApp(f,l) -> FunApp(f, List.map (subst depinfo assql) l)
      |	_ -> Parsing_helper.internal_error "If, find, let, and new should not occur in subst")

let rec find_decompos check ((b, _) as b_st) t =
  (Proba.is_large_term t) && 
  (match t.t_desc with
    Var(b',l) when b == b' -> 
      check b_st l != None
  | FunApp(f,l) when (f.f_options land Settings.fopt_UNIFORM) != 0 ->
      List.exists (find_decompos check b_st) l
  | _ -> false)

let rec find_compos check depinfo ((b,(st,_)) as b_st) t =
  if st = Any then None else
  match t.t_desc with
    Var(b',l) when b == b' -> 
      begin
	match check b_st l with
	  None -> None
	| Some(st, ch_ty) -> Some(st, ch_ty, t)
      end
  | FunApp(f,l) when (f.f_options land Settings.fopt_COMPOS) != 0 ->
      begin
	match find_compos_l check depinfo b_st l with
	  None -> None
	| Some(st, ch_ty, l') -> 
	    Some(st, ch_ty, Terms.build_term2 t (FunApp(f,l')))
      end
  | FunApp(f,l) when (f.f_options land Settings.fopt_UNIFORM) != 0 ->
      if (Proba.is_large_term t) && (st = Decompos) && 
	(List.exists (find_decompos check b_st) l)
      then Some (Decompos, CharacType t.t_type, t)  else None
  | Var _ -> None
  | _ -> 
      (* In a simpler version, we would remove 
	 find_compos_bin, find_compos_bin_l, find_decompos_bin, subst,
	 apply_statement2, apply_all_red2, apply_statements
	 and replace this case with None
	 *)
      let vcounter = !Terms.vcounter in
      let b' = Terms.new_binder b in
      let t' = subst depinfo (ref [(b, b')]) t in
      let f1 = apply_statements (Terms.make_equal t t') in
      let r = 
	match find_compos_bin check b_st b' f1 with
	  None -> None
	| Some(st,ch_ty) -> Some(st, ch_ty, t)
      in
      Terms.vcounter := vcounter; (* Forget created variables *)
      r

and find_compos_l check depinfo b_st = function
    [] -> None
  | (a::l) ->
      match find_compos check depinfo b_st a with
	None -> 
	  begin
	    match find_compos_l check depinfo b_st l with
	      None -> None
	    | Some(st, charac_type, l') -> Some(st, charac_type, (any_term a)::l')
	  end
      |	Some(_, charac_type, a') -> Some(Compos,charac_type, a'::List.map any_term l)

let find_compos_list check depinfo seen_list t =
  let rec test_l = function
    [] -> None
  | (((b, (st, x)) as b_st)::l) -> 
      match find_compos check depinfo b_st t with
	None -> test_l l
      |	Some(st,charac_type,t') -> Some(st,charac_type,t',b,x)
  in
  test_l seen_list

end

module DepAnal1 :
sig
  exception BadDep
  val check_all_deps : binder -> binder list * ((binder list * (binder * term) list * term list) * (term * term * typet list)) list
  val find_compos_glob : binder -> term list -> term -> (typet * term) option
end
=
struct

(* Find all variables that depend on a certain variable, provided
   these variables are not output (raises BadDep when some
   of these variables may be output)

   When tests depend on these variables, they must always yield
   the same result up to a negligible probability.

(1) Activate advice? (See comments and display of "Manual advice:" below)
Guesses some useful SArename, but makes the proof of 
event endB(x, y, na, nb) ==> beginA(x, y, na, nb) fail for 
needham-schroeder-pkcorr3BlockAuth
7/7/2008 Now, this problem seems to have disappeared

TO DO (2) The dependency analysis tends to be too sensitive to the syntax.
For example, the test let (..., =M, =A) = r always fails when M is a 
large type and A is a small type, both not depending on r, and r is random.
However, the other test let (...., x, =A) = r in if x = M then...
yields a bad dependency (comparison with the small type A).
*)

open FindCompos

type branch = OnlyThen | OnlyElse | BothDepB | BothIndepB

let collisions_for_current_check_dependency = ref []

let equal_charac_type c1 c2 =
  match (c1,c2) with
    CharacType t1, CharacType t2 -> t1 == t2
  | CharacTypeOfVar b1, CharacTypeOfVar b2 -> b1 == b2
  | _ -> false

let add_collisions_for_current_check_dependency (all_indices, map_find_indices, true_facts, facts_info) ((t1,t2,c) as proba_info) =
  (* For speed, when the type is not a password, we need not optimize the indices, so we can remove the facts *)
  match c with
    CharacType t when not (Proba.is_passwd t) ->
      if not (List.exists (fun ((all_indices', map_find_indices',true_facts''),(t1',t2',c')) ->
	(Terms.equal_lists (==) all_indices all_indices') &&
	(Terms.equal_lists (fun (b,t) (b',t') -> b == b' && Terms.equal_terms t t') map_find_indices map_find_indices') &&
	(true_facts'' == []) && 
	(Terms.equal_terms t1 t1') && 
	(Terms.equal_terms t2 t2') && 
	(equal_charac_type c c'))
                (!collisions_for_current_check_dependency)) then
        collisions_for_current_check_dependency :=
           ((all_indices, map_find_indices, []), proba_info) ::
           (!collisions_for_current_check_dependency)
  | _ ->
  try
    let true_facts' = true_facts @ (Facts.get_facts_at facts_info) in
    if not (List.exists (fun ((all_indices', map_find_indices',true_facts''),(t1',t2',c')) ->
      (Terms.equal_lists (==) all_indices all_indices') &&
      (Terms.equal_lists (fun (b,t) (b',t') -> b == b' && Terms.equal_terms t t') map_find_indices map_find_indices') &&
      (Terms.equal_term_lists true_facts' true_facts'') &&
      (Terms.equal_terms t1 t1') && 
      (Terms.equal_terms t2 t2') && 
      (equal_charac_type c c'))
          (!collisions_for_current_check_dependency)) then
      collisions_for_current_check_dependency := 
        ((all_indices, map_find_indices, true_facts'), proba_info) ::
        (!collisions_for_current_check_dependency)
  with Contradiction -> ()

exception BadDep

let depends seen_list t = 
  List.exists (fun (b, _) -> Terms.refers_to b t) seen_list

(* find_compos b t returns true when t characterizes b: only one
value of b can yield a certain value of t *)

let find_compos_list seen_list l =
  let check (b, (st, _)) l =
    if List.exists (depends seen_list) l then
      None
    else
      Some (st, CharacTypeOfVar b)
  in
  FindCompos.find_compos_list check (Some seen_list, []) seen_list l

let get_std_charac_type b = function
    CharacType t -> t
  | CharacTypeOfVar b' -> 
      if b != b' then Parsing_helper.internal_error "should be b";
      b.btype

let find_compos_glob b l' t =
  let check (b, (st, _)) l = 
    if List.for_all2 Terms.equal_terms l l' then
      Some (st, CharacTypeOfVar b) 
    else
      None
  in
  match FindCompos.find_compos check (None, []) (b,(Decompos, ref [CharacType b.btype])) t with
    Some(_, charac_type, t') -> Some(get_std_charac_type b charac_type, t')
  | None -> None

(* almost_indep_test seen_list t checks that the result of test t does not
depend on variables in seen_list, up to negligible probability.
Raises BadDep when the result may depend on variables in seen_list.
Returns Some true when the test is true with overwhelming probability
Returns Some false when the test is false with overwhelming probability
Returns None when the result cannot be evaluated. *)

let rec almost_indep_test all_indices map_find_indices true_facts seen_list t =
  match t.t_desc with
    FunApp(f,[t1;t2]) when f == Settings.f_and ->
      begin
	let t2res = almost_indep_test all_indices map_find_indices (t1::true_facts) seen_list t2 in
	let t1res = match t2res with
	  OnlyElse | OnlyThen -> 
	    (* I have eliminated a collision in t2 using the fact that t1 is true,
	       I won't assume t2 when analyzing t1 *)
	    almost_indep_test all_indices map_find_indices true_facts seen_list t1
	| BothDepB | BothIndepB ->
	    (* I did not eliminate any collision when analyzing t2,
	       I can swap the "and" and assume t2 when analyzing t1 *)
	    almost_indep_test all_indices map_find_indices (t2::true_facts) seen_list t1
	in
	match (t1res, t2res) with
	  (OnlyElse, _) | (_, OnlyElse) -> OnlyElse
	| (OnlyThen, x) -> x
	| (x, OnlyThen) -> x
	| (BothDepB, _) | (_, BothDepB) -> BothDepB
	| (BothIndepB, BothIndepB) -> BothIndepB
      end
  | FunApp(f,[t1;t2]) when f == Settings.f_or ->
      begin
	let t2res = almost_indep_test all_indices map_find_indices ((Terms.make_not t1)::true_facts) seen_list t2 in
	let t1res = match t2res with
	  OnlyElse | OnlyThen -> 
	    (* I have eliminated a collision in t2 using the fact that t1 is false,
	       I won't assume t2 when analyzing t1 *)
	    almost_indep_test all_indices map_find_indices true_facts seen_list t1
	| BothDepB | BothIndepB ->
	    (* I did not eliminate any collision when analyzing t2,
	       I can swap the "or" and assume (not t2) when analyzing t1 *)
	    almost_indep_test all_indices map_find_indices ((Terms.make_not t2)::true_facts) seen_list t1
	in
	match (t1res, t2res) with
	  (OnlyThen, _) | (_, OnlyThen) -> OnlyThen
	| (OnlyElse, x) -> x
	| (x, OnlyElse) -> x
	| (BothDepB, _) | (_, BothDepB) -> BothDepB
	| (BothIndepB, BothIndepB) -> BothIndepB
      end
  | FunApp(f,[t1]) when f == Settings.f_not ->
      begin
	match almost_indep_test all_indices map_find_indices true_facts seen_list t1 with
	  OnlyThen -> OnlyElse
	| OnlyElse -> OnlyThen
	| x -> x
      end
(* Be careful: do not use or-patterns with when: 
   If both patterns of the or succeed but the when clause fails for the 
   first one and succeeds for the second one, Caml considers that the
   match fails.
*)
  | FunApp(f,[t1;t2]) 
    when ((f.f_cat == Equal) || (f.f_cat == Diff)) && (Proba.is_large_term t1 || Proba.is_large_term t2) ->
      begin
	match find_compos_list seen_list t1 with
	  Some(_, charac_type,t1',_,_) ->
	    if depends seen_list t2 then
	      BothDepB
	    else 
	      begin
                (* add probability *)
		print_string "almost_indep_test1 knowing ";
		Display.display_list (Display.display_term []) true_facts;
		print_string " ";
		Display.display_term [] t1';
		print_string " = ";
		Display.display_term [] t2;
		print_newline();
		add_collisions_for_current_check_dependency (all_indices, map_find_indices, true_facts, t.t_facts) (t1', t2, charac_type);
		if (f.f_cat == Diff) then OnlyThen else OnlyElse
	      end
	| None -> match find_compos_list seen_list t2 with
	    Some(_,charac_type,t2',_,_) ->
	    if depends seen_list t1 then
	      BothDepB
	    else 
	      begin
                (* add probability *)
		print_string "almost_indep_test2 knowing ";
		Display.display_list (Display.display_term []) true_facts;
		print_string " ";
		Display.display_term [] t2';
		print_string " = ";
		Display.display_term [] t1;
		print_newline();
		add_collisions_for_current_check_dependency (all_indices, map_find_indices, true_facts, t.t_facts) (t2', t1, charac_type);
		if (f.f_cat == Diff) then OnlyThen else OnlyElse
	      end
	  | None ->
	      if depends seen_list t then 
		BothDepB
	      else
		BothIndepB
      end
  | _ -> 
      if depends seen_list t then 
	BothDepB
      else
	BothIndepB

(* checkassign1 is called when the assigned term characterizes b
   Returns false when the let is always going to take the else branch
   up to negligible probability.
   Returns true when the let can take both branches
   tmp_bad_dep is set to true when there is a bad dependency except when
   the let always takes the else branch. *)
let rec check_assign1 cur_array ((t1, t2, charac_type) as proba_info) vars_to_add tmp_bad_dep seen_list st = function
    PatVar b ->
      begin
	let charac_type' = 
	  if st = Decompos then CharacType b.btype else charac_type 
	in
	try 
	  let (st',proba_info_list) = List.assq b (!seen_list) in
	  if st != st' then
	    tmp_bad_dep := true
	  else if not (List.exists (fun (t1', t2', charac_type'') ->
	    (matches_pair t1' t2' t1 t2) &&
	    (equal_charac_type charac_type' charac_type'')) (!proba_info_list))
	  then
	    begin
	      (* Above, I use "matches_pair" to check that t1 = t2 is
                 a particular case of the assignment t1' = t2' seen before.
                 If this is true, I have nothing to add.
                 (Testing equality (t1,t2) = (t1',t2') is not exactly 
		 what we want because these terms may contain wildcards "?")
	      Display.display_binder b;
	      print_newline();
	      print_string " Already present: ";
	      List.iter (fun (t1', t2', charac_type'') ->
		Display.display_term [] t1';
		print_string ", ";
		Display.display_term [] t2';
		print_string ", ";
		begin
		match charac_type'' with
		  CharacType t -> print_string t.tname
		| CharacTypeOfVar b -> Display.display_binder b
		end;
		print_newline()) (!proba_info_list);
	      print_string "Adding: ";
	      Display.display_term [] t1;
	      print_string ", ";
	      Display.display_term [] t2;
	      print_string ", ";
	      begin
		match charac_type' with
		  CharacType t -> print_string t.tname
		| CharacTypeOfVar b -> Display.display_binder b
	      end;
	      print_newline();
	      *)
	      proba_info_list := (t1, t2, charac_type') :: (!proba_info_list)
	    end
	with Not_found ->
	  vars_to_add := (b,(st, ref [t1, t2, charac_type'])) :: (!vars_to_add)
      end;
      true
  | PatTuple(f,l) ->
      if st != Decompos then tmp_bad_dep := true;
      List.for_all (check_assign1 cur_array proba_info vars_to_add tmp_bad_dep seen_list st) l
  | PatEqual t ->
      if (depends (!seen_list) t) || 
        (not (Proba.is_large_term t)) then
	begin
	  tmp_bad_dep := true;
	  true
	end
      else
	begin
	  (* add probability *)
	  add_collisions_for_current_check_dependency (cur_array, [], [], t.t_facts) proba_info;
	  false
	end

(* check_assign2 is called when the assigned term does not depend on b
   Returns Some(charac_type, t') when the let is always going to take the 
   else branch up to negligible probability. t' is the term with which
   the collision is eliminated and charac_type the type of the part of 
   t' characterized by the value of the pattern.
   Returns None when the let can take both branches 
   tmp_bad_dep is set to true when there is a bad dependency except when
   the let always takes the else branch. *)
let rec check_assign2 seen_list to_advise tmp_bad_dep = function
    PatVar b ->
      if List.exists (fun (b',_) -> b == b') (!seen_list) then
	begin
	  to_advise := Terms.add_eq (SArenaming b) (!to_advise);
	  tmp_bad_dep := true
	end;
      None
  | PatTuple(f,l) ->
      begin
        match check_assign2_list seen_list to_advise tmp_bad_dep l with
	  None -> None
	| Some(charac_type, l') ->
	    Some (charac_type, Terms.build_term_type (snd f.f_type) (FunApp(f,l')))
      end
  | PatEqual t ->
      match find_compos_list (!seen_list) t with
	Some (status, charac_type,t',_,_) when Proba.is_large_term t ->
	  Some(charac_type, t')
      |	_ ->
	begin
	  if depends (!seen_list) t then
	    tmp_bad_dep := true;
	  None
	end

and check_assign2_list seen_list to_advise tmp_bad_dep = function
    [] -> None
  | (a::l) ->
      match check_assign2 seen_list to_advise tmp_bad_dep a with
	None -> 
	  begin
	    match check_assign2_list seen_list to_advise tmp_bad_dep l with
	      None -> None
	    | Some(charac_type, l') -> Some(charac_type, (any_term_pat a)::l')
	  end
      |	Some(charac_type, a') -> Some(charac_type, a'::(List.map any_term_pat l))

let rec check_depend_process cur_array seen_list p' =
  match p'.i_desc with
    Nil -> ()
  | Par(p1,p2) -> 
      check_depend_process cur_array seen_list p1;
      check_depend_process cur_array seen_list p2
  | Repl(b,p) -> check_depend_process (b::cur_array) seen_list p
  | Input((c,tl),pat,p) -> 
      if List.exists (depends (!seen_list)) tl then raise BadDep;
      (* Create a dummy variable for the input message *)
      let b = Terms.create_binder "dummy_input" (Terms.new_vname())
		(Terms.term_from_pat pat).t_type
		(List.map Terms.term_from_binder cur_array)
      in
      let t2 = Terms.term_from_binder b in
      let tmp_bad_dep = ref false in
      let to_advise = ref [] in
      match check_assign2 seen_list to_advise tmp_bad_dep pat with
	Some(charac_type, t1) -> 
	  add_collisions_for_current_check_dependency (cur_array, [], [], p'.i_facts) (t1, t2, charac_type);
      |	None ->
	begin
	  if (!tmp_bad_dep) then
	    begin
	      if (!to_advise) != [] then
		begin
                  if !Settings.no_advice_simplify then 
                    begin
		      print_string "Manual advice: ";
		      Display.display_list Display.display_instruct (!to_advise);
		      print_newline()
                    end
                  else
		    List.iter (fun x -> Transform.advise := Terms.add_eq x (!Transform.advise)) (!to_advise)
		end;
	      raise BadDep
	    end;
	  check_depend_oprocess cur_array seen_list p
	end

and check_depend_oprocess cur_array seen_list p = 
  match p.p_desc with
    Yield -> ()
  | Restr(b,p) -> check_depend_oprocess cur_array seen_list p
  | Test(t,p1,p2) -> 
      begin
	match almost_indep_test cur_array [] [] (!seen_list) t with
	  BothDepB -> raise BadDep
	| BothIndepB -> 
	    check_depend_oprocess cur_array seen_list p1;
	    check_depend_oprocess cur_array seen_list p2
	| OnlyThen -> 
	    check_depend_oprocess cur_array seen_list p1
	| OnlyElse -> 
	    check_depend_oprocess cur_array seen_list p2
      end
  | Find(l0,p2,_) ->
      let always_then = ref false in
      let check_br (b,l) = 
	if List.exists (depends (!seen_list)) l then raise BadDep 
      in
      List.iter (fun (bl,def_list,t,p1) ->
	List.iter check_br def_list;
	(* Compute the probability that the test fails.
	   For that, replace bl' with new replication indexes, since the
	   test fails only when it fails for _all_ values of bl' *)
	let mapping_find_indices = map_find_indices bl in
	let t' = Terms.subst3 mapping_find_indices t in
        match almost_indep_test (bl @ cur_array) mapping_find_indices [] (!seen_list) t' with
	  BothDepB -> raise BadDep
	| OnlyThen ->
	    if def_list == [] then always_then := true;
	    check_depend_oprocess cur_array seen_list p1
	| BothIndepB ->
            check_depend_oprocess cur_array seen_list p1
	| OnlyElse -> ()) l0;
      if not (!always_then) then
	check_depend_oprocess cur_array seen_list p2
  | Output((c,tl),t2,p) ->
      if (List.exists (depends (!seen_list)) tl) || (depends (!seen_list) t2) then raise BadDep;
      check_depend_process cur_array seen_list p
  | Let(pat,t,p1,p2) ->
      begin
	match find_compos_list (!seen_list) t with
	  Some (st, charac_type,t',_,_) ->
	    begin
	      let vars_to_add = ref [] in
	      let tmp_bad_dep = ref false in
	      if check_assign1 cur_array (t', Terms.term_from_pat pat, charac_type) vars_to_add tmp_bad_dep seen_list st pat then
		begin
		  if (!tmp_bad_dep) || (match pat with PatVar _ -> false | _ -> true) then raise BadDep;
		  List.iter (function ((b,_) as b_st) ->
                    (*print_string "Adding ";
                      Display.display_binder b0;
                      print_newline();*)
		    if not (Terms.is_assign b) then
		      raise BadDep;
		    seen_list := b_st :: (!seen_list)) (!vars_to_add);
		  check_depend_oprocess cur_array seen_list p1;
		end
	    end
	| None ->
	    if depends (!seen_list) t then
	      raise BadDep
	    else
	      begin
		let to_advise = ref [] in
		let tmp_bad_dep = ref false in
		match check_assign2 seen_list to_advise tmp_bad_dep pat with
		  Some(charac_type, t1) ->
		    (* add probability *)
		    add_collisions_for_current_check_dependency (cur_array, [], [], p.p_facts) (t1, t, charac_type)
		| None ->
		  begin
		    if (!tmp_bad_dep) then
		      begin
			if (!to_advise) != [] then
			  begin
			    if !Settings.no_advice_simplify then 
			      begin
				print_string "Manual advice: ";
				Display.display_list Display.display_instruct (!to_advise);
				print_newline()
			      end
			    else
			       List.iter (fun x -> Transform.advise := Terms.add_eq x (!Transform.advise)) (!to_advise)
			  end;
			raise BadDep
		      end;
		    check_depend_oprocess cur_array seen_list p1
		  end;
	      end;
      end;
      check_depend_oprocess cur_array seen_list p2
  | EventP(t,p) ->
      check_depend_oprocess cur_array seen_list p
      
let rec check_depend_iter seen_list =
  if List.exists (fun (b0, _) -> Transform.occurs_in_queries b0) (!seen_list) then
    raise BadDep;
  let old_seen_list = !seen_list in
  check_depend_process [] seen_list (!whole_game).proc;
  if (!seen_list) != old_seen_list then check_depend_iter seen_list

let rec get_type_from_charac seen_list vlist = function
    CharacType t -> [t]
  | CharacTypeOfVar b -> 
      if List.memq b seen_list then
	raise BadDep;
      let (st, proba_info_list) = List.assq b vlist in
      List.concat (List.map (fun (_,_,charac_type) -> get_type_from_charac (b::seen_list) vlist charac_type) (!proba_info_list))

let check_all_deps b0 =
  (*print_string "Doing check_all_deps ";
  Display.display_binder b0;
  print_newline();*)
  collisions_for_current_check_dependency := [];
  let dummy_term = Terms.term_from_binder b0 in
  let b0st = (b0, (Decompos, ref [dummy_term, dummy_term, CharacType b0.btype])) in
  let seen_vars = ref [b0st] in
  check_depend_iter seen_vars;
  (*print_string "Success\n";*)
  let vars_charac_type = 
    List.map (fun (b, (st, proba_info_list)) -> (b, List.concat (List.map (fun (_,_,charac_type) -> get_type_from_charac [b] (!seen_vars) charac_type) (!proba_info_list)))) (!seen_vars)
  in
  let proba_info = List.map (fun (info,(t1, t2, c)) ->
    (info,(t1, t2, match c with
      CharacType t -> [t]
    | CharacTypeOfVar b -> List.assq b vars_charac_type))) (!collisions_for_current_check_dependency)
  in
  (List.map fst (!seen_vars), proba_info)

(* Memoizing version of check_all_deps *)

let check_all_deps b0 =
  try 
    List.assq b0 (!success_check_all_deps)
  with Not_found -> 
    if List.memq b0 (!failure_check_all_deps) then raise BadDep
    else
      try 
	let res = check_all_deps b0 in
	success_check_all_deps := (b0, res) :: (!success_check_all_deps);
	res
      with BadDep ->
	failure_check_all_deps := b0 :: (!failure_check_all_deps);
	raise BadDep

end (* module DepAnal1 *)

module DepAnal2 :
sig
  type dep_info 
  type elem_dep_info = (typet * term) FindCompos.depinfo

  val init : dep_info

  (* find_compos_glob depinfo b t   returns Some ty when
     t characterizes a part of b of type ty, knowing the dependency
     information given in depinfo. Otherwise, returns None. *)
  val find_compos_glob : elem_dep_info -> binder -> term -> (typet * term) option

  val update_dep_info : binder list -> dep_info -> simp_facts -> inputprocess -> dep_info
  val update_dep_infoo : binder list -> dep_info -> simp_facts -> process -> process * dep_info list 

  val get_dep_info : dep_info -> binder -> elem_dep_info

  (* is_indep (b, depinfo) t returns a term independent of b
     in which some array indexes in t may have been replaced with
     fresh replication indexes. When t depends on b by variables
     that are not array indexes, raise Not_found *)
  val is_indep : (binder * elem_dep_info) -> term -> term
end
= 
struct

(* Second dependency analysis: take into account the freshness
   of the random number b to determine precisely which expressions depend on b
   for expressions defined before the first output that follows the choice
   of b
   dep = List of variables that may depend on b, with their associated
         "find_compos" status
   nodep:term list = List of terms that do not depend on b
   under_b:bool = True when we are under the "new" that chooses b
   res_accu: term list option ref = List of terms that do not depend on b
   in the whole protocol. Initialized to None.
 *)

open FindCompos

type elem_dep_info = (typet * term) FindCompos.depinfo
type dep_info = (binder * elem_dep_info) list
      (* list of (b, (dep, nodep)), where 
	 dep is either Some l, where l is a list variables that depend on b, 
	 with their associated status and a term that describes how to 
	 compute this variable from b;
         nodep is a list of terms that do not depend on b[b.args_at_creation]
	 *)

let init = []

let depends = FindCompos.depends

let is_indep = FindCompos.is_indep
    
(* find_compos b t returns true when t characterizes b: only one
value of b can yield a certain value of t *)

let check (b, (st, (bct, _))) l =
  if List.for_all2 Terms.equal_terms l b.args_at_creation then
    Some (st, CharacType bct)
  else
    None

let find_compos_list (b, ((dep, nodep) as depinfo)) t =
  let seen_list' = match dep with
    Some seen_list -> seen_list
  | None -> [(b,(Decompos, (b.btype, Terms.term_from_binder b)))]
  in
  match FindCompos.find_compos_list check depinfo seen_list' t with
    Some(st, CharacType charac_type, t', b', (_,assign)) -> Some(st, charac_type, t', b', assign)
  | Some _ -> Parsing_helper.internal_error "CharacTypeOfVar should not be used in DepAnal2"
  | None -> None

let find_compos_glob depinfo b t =
  match FindCompos.find_compos check depinfo (b,(Decompos, (b.btype, Terms.term_from_binder b))) t with
    Some(_, CharacType charac_type, t') -> Some(charac_type, t')
  | Some _ -> Parsing_helper.internal_error "CharacTypeOfVar should not be used in DepAnal2"
  | None -> None

let subst b t t' =
  Terms.auto_cleanup (fun () ->
    Terms.link b (TLink t);
    Terms.copy_term3 t')

exception Else

(* checkassign1 is called when the assigned term depends on b with status st
   Raises Else when only the else branch of the let may be taken *)
let rec check_assign1 cur_array true_facts ((t1, t2, b, charac_type) as proba_info) bdep_info st pat =
  match pat with
    PatVar b -> ()
  | PatTuple(f,l) ->
      let st' = if st != Decompos then Any else st in
      List.iter (check_assign1 cur_array true_facts proba_info bdep_info st') l
  | PatEqual t ->
      if (depends bdep_info t) || 
        (not (Proba.is_large_term t)) || (st == Any) then
	()
      else
	begin
	  (* add probability *)
	  add_term_collisions (cur_array, [], true_facts_from_simp_facts true_facts) t1 t2 b (Some b.args_at_creation) [charac_type];
	  raise Else
	end

(* check_assign2 is called when the assigned term does not depend on b
   Return None when both branches may be taken and
          Some(charac_type, t') when only the else branch of the let
          may be taken. t' is the term with which the collision is
          eliminated and charac_type is the type of the part of t'
          characterized by the value of t' *)
let rec check_assign2 bdepinfo = function
    PatVar _ ->
      None
  | PatTuple(f,l) ->
      begin
        match check_assign2_list bdepinfo l with
	  None -> None
	| Some(charac_type, l') ->
	    Some(charac_type, Terms.build_term_type (snd f.f_type) (FunApp(f,l')))
      end
  | PatEqual t ->
      match find_compos_list bdepinfo t with
	Some (status, charac_type, t', b2, b2fromb) when Proba.is_large_term t ->
	  Some (charac_type, subst b2 b2fromb t')
      |	_ ->
	  None

and check_assign2_list bdepinfo = function
    [] -> None
  | (a::l) ->
      match check_assign2 bdepinfo a with
	None -> 
	  begin
	    match check_assign2_list bdepinfo l with
	      None -> None
	    | Some(charac_type, l') -> Some(charac_type, (any_term_pat a)::l')
	  end
      |	Some(charac_type, a') -> Some(charac_type, a'::(List.map any_term_pat l))
      
let rec remove_dep_array_index_pat bdepinfo = function
    PatVar b -> PatVar b
  | PatTuple(f,l) ->
      PatTuple(f, List.map (remove_dep_array_index_pat bdepinfo) l)
  | PatEqual t ->
      PatEqual (FindCompos.remove_dep_array_index bdepinfo t)

let rec depends_pat bdepinfo = function
    PatVar _ ->
      false
  | PatTuple(f,l) ->
      List.exists (depends_pat bdepinfo) l
  | PatEqual t ->
      depends bdepinfo t

let rec simplify_term all_indices dep_info true_facts t =
  match t.t_desc with
    FunApp(f,[t1;t2]) when f == Settings.f_and ->
      (* We simplify t2 knowing t1 and t1 knowing t2, by swapping the "and"
         after the simplification of t2 *)
      begin
	try
	  let true_facts2 = Facts.simplif_add Facts.no_dependency_anal true_facts t1 in
	  let t2' = simplify_term all_indices dep_info true_facts2 t2 in
	  let true_facts1 = Facts.simplif_add Facts.no_dependency_anal true_facts t2' in
	  Terms.make_and (simplify_term all_indices dep_info true_facts1 t1)  t2'
	with Contradiction ->
	  Terms.make_false()
      end
  | FunApp(f,[t1;t2]) when f == Settings.f_or ->
      (* We simplify t2 knowing (not t1) and t1 knowing (not t2), 
	 by swapping the "or" after the simplification of t2 *)
      begin
	try
	  let true_facts2 = Facts.simplif_add Facts.no_dependency_anal true_facts (Terms.make_not t1) in
	  let t2' = simplify_term all_indices dep_info true_facts2 t2 in
	  let true_facts1 = Facts.simplif_add Facts.no_dependency_anal true_facts (Terms.make_not t2') in
	  Terms.make_or (simplify_term all_indices dep_info true_facts1 t1) t2' 
	with Contradiction ->
	  Terms.make_true()
      end
  | FunApp(f,[t1]) when f == Settings.f_not ->
      let t' = simplify_term all_indices dep_info true_facts t1 in
      if Terms.is_false t' then Terms.make_true() else
      if Terms.is_true t' then Terms.make_false() else
      Terms.make_not t'
  | FunApp(f,[t1;t2]) 
    when ((f.f_cat == Equal) || (f.f_cat == Diff)) && (Proba.is_large_term t1 || Proba.is_large_term t2) ->
      begin
	let mapping_find_indices = map_find_indices all_indices in
	let t1' = Terms.subst3 mapping_find_indices t1 in
	let t2' = Terms.subst3 mapping_find_indices t2 in
	let rec try_dep_info = function
	    [] -> t
	  | ((b, _) as bdepinfo)::restl ->
	      let t1'' = remove_dep_array_index bdepinfo t1' in
	      match find_compos_list bdepinfo t1'' with
		Some(_, charac_type, t1''', b2, b2fromb) ->
		  begin
		    try 
		      let t2'' = is_indep bdepinfo t2' in
                      (* add probability *)
		      add_term_collisions (all_indices, map_find_indices all_indices, true_facts_from_simp_facts true_facts) (subst b2 b2fromb t1''') t2'' b (Some b.args_at_creation) [charac_type];
		      if (f.f_cat == Diff) then Terms.make_true() else Terms.make_false()
		    with Not_found ->
		      try_dep_info restl
		  end
	      | None -> 
		  let t2'' = remove_dep_array_index bdepinfo t2' in
		  match find_compos_list bdepinfo t2'' with
		  Some(_,charac_type, t2''', b2, b2fromb) ->
		    begin
		      try 
			let t1'' = is_indep bdepinfo t1' in
                        (* add probability *)
			add_term_collisions (all_indices, map_find_indices all_indices, true_facts_from_simp_facts true_facts) (subst b2 b2fromb t2''') t1'' b (Some b.args_at_creation) [charac_type];
			if (f.f_cat == Diff) then Terms.make_true() else Terms.make_false()
		      with Not_found ->
			try_dep_info restl
		    end
		| None ->
		    try_dep_info restl
	in
	try_dep_info dep_info
      end
  | _ -> t

(* Takes a dep_info as input and returns the new dep_info for the subprocesses
   of the input process p *)

let update_dep_info cur_array dep_info true_facts p = dep_info

(* Takes a dep_info as input and returns a simplified process and
   the list of new dep_info's for the subprocesses *)

let rec update_dep_infoo cur_array dep_info true_facts p' = 
  match p'.p_desc with
    Yield -> (Terms.oproc_from_desc2 p' Yield, [])
  | Restr(b,p) ->
      let b_term = Terms.term_from_binder b in
      let dep_info' = List.map (fun (b', (dep, nodep)) -> (b', (dep, b_term::nodep))) dep_info in
      if Proba.is_large b.btype then
	try 
	  let def_vars = Facts.get_def_vars_at p'.p_facts in
	  (Terms.oproc_from_desc (Restr(b,p)), 
	   [(b, (Some [b, (Decompos, (b.btype, Terms.term_from_binder b))], 
		 (List.map Terms.term_from_binderref def_vars))) :: dep_info' ])
	with Contradiction ->
	  (* The current program point is unreachable, because it requires the definition
	     of a variable that is never defined *)
	  (Terms.oproc_from_desc2 p' Yield, [])
      else
	(Terms.oproc_from_desc2 p' (Restr(b,p)), [dep_info'])
  | Test(t,p1,p2) ->
      let t' = simplify_term cur_array dep_info true_facts t in
      if Terms.is_true t' then
	begin
	  Transform.changed := true;
	  update_dep_infoo cur_array dep_info true_facts p1
	end
      else if Terms.is_false t' then
	begin
	  Transform.changed := true;
	  update_dep_infoo cur_array dep_info true_facts p2
	end
      else
	let r = List.map (function ((b, (dep, nodep)) as bdepinfo) ->
	  if depends bdepinfo t' then
	    (b, (None, nodep))
	  else
	    bdepinfo) dep_info
	in
	if not (Terms.equal_terms t t') then Transform.changed := true;
	(Terms.oproc_from_desc2 p' (Test(t',p1,p2)), [r])
  | Find(l0,p2,find_info) ->
       let always_then = ref false in
       let rec simplify_find = function
          [] -> []
        | (bl, def_list, t, p1)::l ->
            let l' = simplify_find l in
            let t' = simplify_term (bl @ cur_array) dep_info true_facts t
            in
            if Terms.is_false t' then 
	      begin
		Transform.changed := true;
		l'
	      end 
	    else 
	      begin
		if Terms.is_true t' && def_list == [] then always_then := true;
		if not (Terms.equal_terms t t') then Transform.changed := true;
		(bl, def_list, t', p1)::l'
	      end
       in
       let l0' = simplify_find l0 in
       begin
	 match l0' with
	   [] -> 
	     Transform.changed := true;
             update_dep_infoo cur_array dep_info true_facts p2
	 | [([],[],t, p1)] when Terms.is_true t ->
	     Transform.changed := true;
	     update_dep_infoo cur_array dep_info true_facts p1
	 | _ ->
         (* For each b in dep_info.in_progress, does the branch taken
            depend on b? *)
         let dep_b = List.map (fun bdepinfo ->
	   let tmp_bad_dep = ref false in
	   let check_br (b, l) = 
	     if List.exists (depends bdepinfo) l then tmp_bad_dep := true
	   in
	   List.iter (fun (bl, def_list, t, p1) ->
	     List.iter check_br def_list;
	     if depends bdepinfo t then tmp_bad_dep := true;
		  ) l0';
           !tmp_bad_dep) dep_info 
	 in

         (* Dependence info for the "then" branches *)
         let dep_info_list = List.map (fun (bl, def_list, _, _) ->
	   let this_branch_node = Facts.get_node_for_find_branch p'.p_facts bl in
	   let nodep_add = List.map Terms.term_from_binderref 
	     (try
	       Facts.def_vars_from_defined this_branch_node bl def_list
	     with Contradiction -> 
	       (* For simplicity, I ignore when a variable can in fact not be defined. 
		  I could remove that branch of the find to be more precise *)
	       def_list)
	       (* I add variables by closing recursively variables
	          that must be defined *)
	   in
	   List.map2 (fun dep1 ((b, (dep, nodep)) as bdepinfo) ->
	     if dep1 then
	       (b, (None, nodep))
	     else
	       (b, (dep, (List.filter (fun t -> not (depends bdepinfo t)) nodep_add) @ nodep))
		 ) dep_b dep_info
             ) l0' 
	 in
         (* Dependence info for the else branch *)
	 let dep_info_else = List.map2 
	     (fun dep1 ((b, (dep, nodep)) as bdepinfo) ->
	       if dep1 then
		 (b, (None, nodep))
	       else
		 bdepinfo) dep_b dep_info
	 in
         (Terms.oproc_from_desc2 p' (Find(l0',(if !always_then then Terms.yield_proc else p2), find_info)), dep_info_else :: dep_info_list)
       end
  | Let(pat, t, p1, p2) ->
      begin
        match pat with
          PatVar b' -> 
            let dep_info' = 
              List.map (fun ((b, (dep, nodep)) as bdepinfo) ->
		if depends bdepinfo t then
		  match dep with
		    None -> bdepinfo
		  | Some dl ->
                      match find_compos_list bdepinfo t with
	                Some (st, charac_type, t', b2, b2fromb) -> 
			  (b, (Some ((b',(st, (charac_type, subst b2 b2fromb t')))::dl), nodep))
                      | None -> 
			  let rec find_dep = function
			      [] -> 
				Parsing_helper.internal_error "t does not depend on b; this should have been detected by depends before"
                                (*(b, (dep, (Terms.term_from_binder b')::nodep))*)
			    | (b2, (_, (_, b2fromb)))::dep' ->
				if Terms.refers_to b2 t then
				  (b, (Some ((b', (Any, (b.btype, subst b2 b2fromb t)))::dl), nodep))
				else
				  find_dep dep'
			  in
			  find_dep dl
		else
		  (b, (dep, (Terms.term_from_binder b')::nodep))
                 ) dep_info 
            in
	    if p2.p_desc != Yield then Transform.changed := true;
            (Terms.oproc_from_desc2 p' (Let(pat, t, p1, Terms.yield_proc)), [dep_info'])
        | _ -> 
            let bl = Terms.vars_from_pat [] pat in
            let bl_terms = List.map Terms.term_from_binder bl in
	    try        
	      (* status is true when the chosen branch may depend on b *)
              let status ((b, _) as bdepinfo) =
		let t' = FindCompos.remove_dep_array_index bdepinfo t in
		let pat' = remove_dep_array_index_pat bdepinfo pat in
		match find_compos_list bdepinfo t' with
		  Some (st, charac_type, t'', b2, b2fromb) ->
		    check_assign1 cur_array true_facts (subst b2 b2fromb t'', Terms.term_from_pat pat', b, charac_type) bdepinfo st pat';
		    true
		| None ->
		    begin
		      if depends bdepinfo t' then () else
		      match check_assign2 bdepinfo pat' with
			None -> ()
		      |	Some(charac_type, t1') ->
			  (* Add probability *)
			  add_term_collisions (cur_array, [], true_facts_from_simp_facts true_facts) t1' t' b (Some b.args_at_creation) [charac_type];
			  raise Else
		    end;
		    (depends bdepinfo t) || (depends_pat bdepinfo pat)
	      in
	      (* dependency information for the "in" and "else" branches *)
	      let dep_info' = List.map (fun ((b, (dep, nodep)) as bdepinfo) ->
		if status bdepinfo then
		  (b, (None, nodep)), (b, (None, nodep))
		else
		  (b, (dep, bl_terms @ nodep)), bdepinfo
		    ) dep_info
	      in
	      let dep_info1, dep_info2 = List.split dep_info' in
              (Terms.oproc_from_desc2 p' (Let(pat, t, p1, p2)), [dep_info1; dep_info2])
	    with Else ->         
	      Transform.changed := true;
	      update_dep_infoo cur_array dep_info true_facts p2
      end
  | Output _ ->
      (p', [List.map (fun (b, (dep, nodep)) -> (b, (None, nodep))) dep_info])
  | EventP _ ->
      (p', [dep_info])

  let get_dep_info dep_info b =
    try 
      List.assq b dep_info
    with Not_found ->
      (None, []) (* Not found *)

end (* Module DepAnal2 *)

let rec try_no_var_rec simp_facts t =
  let t' = Facts.try_no_var simp_facts t in(* Risk of non-termination? *)
  match t'.t_desc with
    FunApp(f,l) -> 
      Terms.build_term2 t' (FunApp(f, List.map (try_no_var_rec simp_facts) l))
  | _ -> t'

let rec dependency_collision_rec1 all_indices map_find_indices true_facts t1 t2 t =
  match t.t_desc with
    Var(b,l) when (Terms.is_restr b) && (Proba.is_large_term t) && (not (Terms.refers_to b t2)) ->
      begin
	match DepAnal1.find_compos_glob b l t1 with
	  None -> false
	| Some(charac_type, t1') -> 
	    try 
	      let (vlist, collision_info) = DepAnal1.check_all_deps b in
	      if not (List.exists (fun b' -> Terms.refers_to b' t2 || List.exists (Terms.refers_to b') l) vlist) then
		begin
		  (* add probability *)
		print_string "dependency_collision_rec1 knowing ";
		Display.display_list (Display.display_term []) true_facts;
		print_string " ";
		Display.display_term [] t1';
		print_string " = ";
		Display.display_term [] t2;
		print_newline();
		  
		  List.iter (fun (info,(t1,t2,tl)) -> add_term_collisions info t1 t2 b None tl)
		    (((all_indices, map_find_indices, true_facts), (t1', t2, [charac_type])) :: collision_info);
		  true
		end
	      else
		false
	    with DepAnal1.BadDep ->
	      false
      end
  | FunApp(f,l) ->
      List.exists (dependency_collision_rec1 all_indices map_find_indices true_facts t1 t2) l
  | _ -> false

let rec dependency_collision_rec2 all_indices map_find_indices true_facts dep_info t1 t2 t =
  match t.t_desc with
    Var(b,l) when (Terms.is_restr b) && (Proba.is_large_term t) && (not (Terms.refers_to b t2)) ->
      begin
	(List.for_all2 Terms.equal_terms l b.args_at_creation) &&
	(let depinfo = DepAnal2.get_dep_info dep_info b in
	 let t1' = FindCompos.remove_dep_array_index (b,depinfo) t1 in
	 match DepAnal2.find_compos_glob depinfo b t1' with
	   None -> false
	 | Some(charac_type, t1'') ->
	    try 
	      let t2' = DepAnal2.is_indep (b,depinfo) t2 in
	      (* add probability *)
	      add_term_collisions (all_indices, map_find_indices, true_facts) t1'' t2' b (Some b.args_at_creation) [charac_type];
	      true
	    with Not_found -> false)
      end 
  | FunApp(f,l) ->
      List.exists (dependency_collision_rec2 all_indices map_find_indices true_facts dep_info t1 t2) l
  | _ -> false

let rec dependency_collision_rec3 all_indices map_find_indices true_facts t1 t2 t =
  match t.t_desc with
    Var(b,l) when (Terms.is_restr b) && (Proba.is_large_term t) && (not (Terms.refers_to b t2)) ->
      begin
	let check (b, (st, _)) tl =
	  if List.for_all2 Terms.equal_terms tl l then
	    Some (st, FindCompos.CharacType b.btype) 
	  else 
	    None
	in
	match FindCompos.find_compos check FindCompos.init_elem (b, (FindCompos.Decompos, b.btype)) t1 with
	  Some(_, FindCompos.CharacType charac_type, t1') -> 
	    begin
	      try 
		let t2' = FindCompos.is_indep (b,FindCompos.init_elem) t2  in
	        (* add probability *)
		add_term_collisions (all_indices, map_find_indices, true_facts) t1' t2' b (Some l) [charac_type];
		true
	      with Not_found -> 
		false
	    end
       | _ -> false
      end 
  | FunApp(f,l) ->
      List.exists (dependency_collision_rec3 all_indices map_find_indices true_facts t1 t2) l
  | _ -> false

let dependency_collision all_indices dep_info simp_facts t1 t2 = 
  let t1' = try_no_var_rec simp_facts t1 in
  let t2' = try_no_var_rec simp_facts t2 in
  let map_find_indices = map_find_indices all_indices in
  let true_facts = true_facts_from_simp_facts simp_facts in
  (dependency_collision_rec2 all_indices map_find_indices true_facts dep_info t1' t2' t1') ||
  (dependency_collision_rec2 all_indices map_find_indices true_facts dep_info t2' t1' t2') ||
  (repl_index_list := [];
   let t1'' = FindCompos.remove_array_index t1' in
   let t2'' = FindCompos.remove_array_index t2' in
   (dependency_collision_rec3 all_indices map_find_indices true_facts t1'' t2'' t1'') ||
   (dependency_collision_rec3 all_indices map_find_indices true_facts t2'' t1'' t2'')) ||
  (dependency_collision_rec1 all_indices map_find_indices true_facts t1' t2' t1') ||
  (dependency_collision_rec1 all_indices map_find_indices true_facts t2' t1' t2')

(* Note on the elimination of collisions in find conditions:
   The find indices are replaced with fresh replication indices
   (by new_repl_index), so that we correctly take into account that
   the condition of find is executed for every value of the indices.

   However, the variables created in conditions of find do not
   have as indices the indices of find, so those indices might be 
   forgotten. This problem does not happen because:
   - DepAnal1 raises BadDep as soon as the considered variable b
   occurs in a condition of find that contains if/let/find/new,
   so the terms modified using DepAnal1 cannot contain variables
   defined in conditions of find.
   - DepAnal2 similarly leaves conditions of find that contain
   if/let/find/new unchanged. The dependency information for DepAnal2
   is forgotten in simplify_term_w_find.
   - In the remaining cases, the referenced variables must be restrictions,
   but restrictions cannot occur in conditions of find, so this case
   does not happen.
*)

(* Simplify a term knowing some true facts *)

let rec simplify_term_rec dep_info simp_facts t =
  let t' = Facts.try_no_var simp_facts t in
  match t'.t_desc with
    FunApp(f, [t1;t2]) when f == Settings.f_and ->
      begin
	try
          (* We simplify t2 knowing t1 (t2 is evaluated only when t1 is true) *)
	  let simp_facts2 = Facts.simplif_add dep_info simp_facts t1 in
	  let t2' = simplify_term_rec dep_info simp_facts2 t2 in
          (* we can swap the "and" to evaluate t1 before t2 *)
	  let simp_facts1 = Facts.simplif_add dep_info simp_facts t2' in
	  Terms.make_and (simplify_term_rec dep_info simp_facts1 t1) t2'
	with Contradiction -> 
	  (* Adding t1 or t2' raised a Contradiction *)
	  Terms.make_false()
      end
  | FunApp(f, [t1;t2]) when f == Settings.f_or ->
      begin
	try 
          (* We simplify t2 knowing (not t1) (t2 is evaluated only when t1 is false) *)
	  let simp_facts2 = Facts.simplif_add dep_info simp_facts (Terms.make_not t1) in
	  let t2' = simplify_term_rec dep_info simp_facts2 t2 in
          (* we can swap the "or" to evaluate t1 before t2 *)
	  let simp_facts1 = Facts.simplif_add dep_info simp_facts (Terms.make_not t2') in
	  Terms.make_or (simplify_term_rec dep_info simp_facts1 t1) t2'
	with Contradiction ->
	  (* Adding (not t1) or (not t2') raised a Contradiction, t1 or t2' is always true *)
	  Terms.make_true()
      end
  | FunApp(f, [t1;t2]) when f.f_cat == Equal ->
      let t1' = Facts.try_no_var simp_facts t1 in
      let t2' = Facts.try_no_var simp_facts t2 in
      begin
	match t1'.t_desc, t2'.t_desc with
	  (FunApp(f1,l1), FunApp(f2,l2)) when
	  (f1.f_options land Settings.fopt_COMPOS) != 0 && f1 == f2 -> 
	    simplify_term_rec dep_info simp_facts (Terms.make_and_list (List.map2 Terms.make_equal l1 l2))
	| (Var(b1,l1), Var(b2,l2)) when
	  (Terms.is_restr b1) &&
	  (Proba.is_large_term t1' || Proba.is_large_term t2') && b1 == b2 ->
	    Proba.add_elim_collisions b1 b1;
          (* add_proba (Div(Cst 1, Card b1.btype)); * number applications *)
	    simplify_term_rec dep_info simp_facts (Terms.make_and_list (List.map2 Terms.make_equal l1 l2))
	| _ ->
	    try
	      let _ = Facts.simplif_add dep_info simp_facts t' in
	      t
	    with Contradiction -> 
	      Terms.make_false()
      end
  | FunApp(f, [t1;t2]) when f.f_cat == Diff ->
      let t1' = Facts.try_no_var simp_facts t1 in
      let t2' = Facts.try_no_var simp_facts t2 in
      begin
	match t1'.t_desc, t2'.t_desc with
	  (FunApp(f1,l1), FunApp(f2,l2)) when
	  (f1.f_options land Settings.fopt_COMPOS) != 0 && f1 == f2 -> 
	    simplify_term_rec dep_info simp_facts (Terms.make_or_list (List.map2 Terms.make_diff l1 l2))

	| (Var(b1,l1), Var(b2,l2)) when
	  (Terms.is_restr b1) &&
	  (Proba.is_large_term t1' || Proba.is_large_term t2') && b1 == b2 ->
	    Proba.add_elim_collisions b1 b1;
      (* add_proba (Div(Cst 1, Card b1.btype)); * number applications *)
	    simplify_term_rec dep_info simp_facts (Terms.make_or_list (List.map2 Terms.make_diff l1 l2))
	| _ -> 
	    try
	      let _ = Facts.simplif_add dep_info simp_facts (Terms.make_not t') in
	      t
	    with Contradiction -> 
	      Terms.make_true()
      end
  | _ -> t

let simplify_term all_indices dep_info keep_tuple ((subst2, facts, elsefind) as simp_facts) t = 
  let t' = 
    if keep_tuple then 
      Facts.try_no_var simp_facts t 
    else
      t
  in
  let t'' = Facts.apply_reds simp_facts t' in
  let t''' = 
    if t''.t_type == Settings.t_bool then
      simplify_term_rec (dependency_collision all_indices dep_info) simp_facts t''
    else
      t''
  in
  if !Settings.minimal_simplifications then
    begin
      if Terms.is_true t''' || Terms.is_false t''' || (not (Terms.equal_terms t' t''')) ||
         (keep_tuple && Terms.is_tuple t''' && not (Terms.is_tuple t)) then
	begin
	  if not (Terms.is_true t || Terms.is_false t) then Transform.changed := true;
	  t'''
	end
      else
	(* The change is not really useful, don't do it *)
	t
    end
  else
    begin
      if not (Terms.equal_terms t t''') then Transform.changed := true;
      t'''
    end

(*
let simplify_term all_indices dep_info k s t =
  let res = simplify_term all_indices dep_info k s t in
  if not (Terms.equal_terms t res) then
    begin
      print_string "Simplifying "; Display.display_term [] t;
      print_string " knowing\n";
      display_facts s; 
      print_string "Simplify done "; Display.display_term [] res;
      print_newline();
      print_newline()
    end;
  res
*)

(* Simplify pattern *)

let rec simplify_pat all_indices dep_info true_facts = function
    (PatVar b) as pat -> pat
  | PatTuple (f,l) -> PatTuple (f,List.map (simplify_pat all_indices dep_info true_facts) l)
  | PatEqual t -> PatEqual (simplify_term all_indices dep_info false true_facts t)

(* Facts.facts_from_defined def_list: 
       for each (b,l) in def_list,
       look for definitions n of binders b,
       substitute l for b.args_at_creation in n.true_facts_at_def and
       add these facts to the returned list 
       substitute l for b.args_at_creation in n.def_vars_at_def and
       continue recursively with these definitions 
       If there are several definitions of b, take the intersection
       of lists of facts/defined vars. ("or" would be more precise
       but difficult to implement) 
       Do not reconsider an already seen pair (b,l), to avoid loops.*)


let rec filter_def_list bl accu = function
    [] -> accu
  | (br::l) ->
      let implied_br = Facts.def_vars_from_defined None bl [br] in
      let accu' = Terms.setminus_binderref accu implied_br in
      let l' = Terms.setminus_binderref l implied_br in
      filter_def_list bl (br::accu') l'

let rec remove_subterms accu = function
    [] -> accu
  | (br::l) ->
      let subterms = ref [] in
      Terms.close_def_subterm subterms br;
      let accu' = Terms.setminus_binderref accu (!subterms) in
      let l' = Terms.setminus_binderref l (!subterms) in
      remove_subterms (br::accu') l' 


let rec match_term2 next_f simp_facts bl t t' =
  match t.t_desc with
    Var(v,l) when (List.memq v bl) && (List.for_all2 Terms.equal_terms l v.args_at_creation) ->
      begin
	if t'.t_type != v.btype then
	  raise NoMatch;
	match v.link with
	  NoLink -> Terms.link v (TLink t')
	| TLink t -> ignore (Facts.unify_terms simp_facts t t')
      end;
      next_f ()
  | Var(v,l) ->
      begin
	match t'.t_desc with
	  Var(v',l') when v == v' ->
	    match_term_list2 next_f simp_facts bl l l'
	| _ -> raise NoMatch
      end
  | FunApp(f,[t1;t2]) when f.f_options land Settings.fopt_COMMUT != 0 ->
      (* Commutative function symbols *)
      begin
	match t'.t_desc with
	  FunApp(f',[t1';t2']) when f == f' ->
	    begin
	      try
		Terms.auto_cleanup (fun () ->
		  match_term2 (fun () -> match_term2 next_f simp_facts bl t2 t2') simp_facts bl t1 t1')
	      with NoMatch ->
		match_term2 (fun () -> match_term2 next_f simp_facts bl t2 t1') simp_facts bl t1 t2'
	    end
	| _ -> raise NoMatch
      end
  | FunApp(f,l) ->
      begin
	match t'.t_desc with
	  FunApp(f',l') when f == f' ->
	    match_term_list2 next_f simp_facts bl l l'
	| _ -> raise NoMatch
      end
  | _ -> Parsing_helper.internal_error "If, find, let, and new should not occur in match_term2"

and match_term_list2 next_f simp_facts bl l l' = 
  match l,l' with
    [],[] -> next_f()
  | a::l,a'::l' ->
      match_term2 (fun () -> match_term_list2 next_f simp_facts bl l l') 
	simp_facts bl a a'
  | _ -> Parsing_helper.internal_error "Different lengths in match_term_list2"


let match_binderref2 next_f simp_facts bl (b,l) (b',l') =
  if b != b' then raise NoMatch;
  match_term_list2 next_f simp_facts bl l l'

let rec match_among next_match simp_facts bl br = function
    [] -> raise NoMatch
  | (br1::brl) ->
      try 
	Terms.auto_cleanup (fun () ->
	  match_binderref2 next_match simp_facts bl br br1)
      with NoMatch ->
	match_among next_match simp_facts bl br brl

let rec match_among_list next_match simp_facts bl def_vars = function
    [] -> next_match()
  | (br1::brl) ->
      match_among (fun () -> 
	match_among_list next_match simp_facts bl def_vars brl) 
	simp_facts bl br1 def_vars
  

let final_next dep_info bl true_facts t () =
  let t' = Terms.copy_term3 t in
  (* Cleanup links, with possibility to restore *)
  let tmp_list = List.map (fun b -> b.link) bl in
  List.iter (fun b -> b.link <- NoLink) bl;
  (* Raise Contradiction when t implied *)
  Terms.auto_cleanup (fun () -> 
    (* TO DO It would be possible to improve this when t' is the conjunction
       of terms in tl:
       replace true_facts := Facts.simplif_add (!true_facts) (Terms.make_not t') with
       if List.for_all (fun t -> 
         try
           ignore(Facts.simplif_add true_facts (Terms.make_not t));
           false
         with Contradiction -> true) tl then raise Contradiction *)
    (* print_string "Adding ";
    Display.display_term [] (Terms.make_not t');
    print_newline();*)
    true_facts := Facts.simplif_add dep_info (!true_facts) (Terms.make_not t'));
  (* Restore links *)
  List.iter2 (fun b l -> b.link <- l) bl tmp_list;
  (* Backtrack *)
  raise NoMatch

let always_true_def_list_t dep_info bl simp_facts t def_vars def_list =
  try
    match_among_list (final_next dep_info bl simp_facts t) (!simp_facts) bl def_vars def_list
  with NoMatch -> ()

(* Test if a branch of find always succeeds *)

exception SuccessBranch of (binder * term) list * binder list

let final_next2 dep_info bl true_facts t1 () =
  let t1' = Terms.copy_term3 t1 in
  (* Cleanup links, with possibility to restore *)
  let tmp_list = List.map (fun b -> b.link) bl in
  List.iter (fun b -> b.link <- NoLink) bl;
  (* Raise Contradiction when t1 implied *)
  begin
    try 
      Terms.auto_cleanup (fun () -> 
	ignore (Facts.simplif_add dep_info true_facts (Terms.make_not t1')))
    with Contradiction ->
      (* For the value of bl computed in the links, t1 is true;
	 furthermore match_among_list has checked that all variables
	 in def_list are defined, so this branch of find succeeds *)
      (* print_string "Proved ";
         Display.display_term [] t1';
         print_newline();*)
      let subst = ref [] in
      let keep_bl = ref [] in
      List.iter2 (fun b l -> 
	match l with
	  TLink b_im -> subst := (b,b_im) :: (!subst)
	| NoLink -> keep_bl := b :: (!keep_bl)) bl tmp_list;
      raise (SuccessBranch(!subst, !keep_bl))
  end;
  (* Restore links *)
  List.iter2 (fun b l -> b.link <- l) bl tmp_list;
  (* Backtrack *)
  raise NoMatch

(* Raises SuccessBranch when the branch is proved to succeed for some
   value of the indices. These values are stored in the argument of SuccessBranch *)

let branch_succeeds (bl, def_list, t1, _) dep_info true_facts def_vars =
  try
    match_among_list (final_next2 dep_info bl true_facts t1) true_facts bl def_vars def_list
  with NoMatch -> ()

(* Treatment of elsefind facts *)

let rec add_elsefind dep_info def_vars ((subst, facts, elsefind) as simp_facts) = function
    [] -> simp_facts
  | ((bl, def_list, t1,_)::l) -> 
      (* When the condition t1 contains if/let/find/new, we simply ignore it when adding elsefind facts. *)
      let simp_facts' = 
	match (bl, def_list, t1.t_desc) with
	  [],[],(Var _ | FunApp _) -> Facts.simplif_add dep_info simp_facts (Terms.make_not t1)
	| _,[],_ -> simp_facts
	| _,_,(Var _ | FunApp _) -> 
	    let simp_facts_ref = ref (subst, facts, (bl, def_list, t1)::elsefind) in
	    always_true_def_list_t dep_info bl simp_facts_ref t1 def_vars def_list;
	    !simp_facts_ref
	| _ -> simp_facts
      in
      add_elsefind dep_info def_vars simp_facts' l

let not_deflist b (_, def_list, _) =
  List.for_all (fun (b',l) ->
    (b != b') && (not (List.exists (Terms.refers_to b) l))) def_list

let not_deflist_l bl elsefind =
  List.for_all (fun b -> not_deflist b elsefind) bl

let rec filter_elsefind f (subst, facts, elsefind) =
  (subst, facts, List.filter f elsefind)

let convert_elsefind dep_info def_vars ((subst, facts, elsefind) as simp_facts) =
  let simp_facts_ref = ref simp_facts in
  List.iter (fun (bl, def_list, t1) ->
    always_true_def_list_t dep_info bl simp_facts_ref t1 def_vars def_list
      ) elsefind;
  !simp_facts_ref



(* Try to determine when a defined condition is always false
   b = variable
   pp = program point, at which we test whether b is defined
   lcp = length of the longest common prefix between the current replication
   indexes at pp and the indexes of b
   cur_array = current replication indexes at pp
   is_comp: bool ref, set to true when b may be defined at pp

   check_compatible ... p returns a pair (has_b,has_pp) where
   has_b is true when b is defined in p
   has_pp is true when pp is a branch in a subprocess of p
 *)

module CompatibleDefs
=
struct

exception Compatible

let rec check_compatiblefc lcp b pp def_node_opt t' =
  match t'.t_desc with
  | ResE(b',t) ->
      let (has_b, has_pp) = check_compatiblefc lcp b pp def_node_opt t in
      if (b' == b) && has_pp then
	raise Compatible;
      (has_b || (b' == b), has_pp)
  | TestE(_, p1, p2) -> 
      let (has_b1, has_pp1) = check_compatiblefc lcp b pp def_node_opt p1 in
      let (has_b2, has_pp2) = check_compatiblefc lcp b pp def_node_opt p2 in
      (has_b1 || has_b2, has_pp1 || has_pp2)
  | FindE(l0, p2, _) ->
      let (has_b2, has_pp2) = check_compatiblefc lcp b pp def_node_opt p2 in
      let rec check_l = function
	  [] -> (false, false)
	| ((bl,def_list,t,p1)::l) ->
	    let (has_br, has_ppr) = check_l l in
	    let (_, has_ppt) = check_compatiblefc lcp b pp def_node_opt t in
	    let (has_b1, has_pp1) = check_compatiblefc lcp b pp def_node_opt p1 in
	    let has_b0 = List.memq b bl in
	    if has_b0 && (has_ppt || has_pp1 || (def_list == pp)) then
	      raise Compatible;
	    (has_br || has_b1 || has_b0, has_ppr || has_ppt || has_pp1 || (def_list == pp))
      in
      let (has_bl, has_ppl) = check_l l0 in
      (has_bl || has_b2, has_ppl || has_pp2)
  | LetE(pat, _, p1, topt) ->
      let (has_b1, has_pp1) = check_compatiblefc lcp b pp def_node_opt p1 in
      let (has_b2, has_pp2) = 
	match topt with
	  None -> (false, false)
	| Some p2 -> check_compatiblefc lcp b pp def_node_opt p2 
      in
      let has_b3 = Terms.occurs_in_pat b pat in
      if has_b3 && has_pp1 then 
	raise Compatible;
      (has_b1 || has_b2 || has_b3, has_pp1 || has_pp2)
  | Var _ | FunApp _ -> (false, false) (* Will not contain any find or variable definition *)
  | EventE _ -> Parsing_helper.internal_error "Event should have been expanded"

let rec check_compatible lcp b pp def_node_opt p' = 
  match p'.i_desc with
    Nil -> (false, false)
  | Par(p1,p2) ->
      let (has_b1, has_pp1) = check_compatible lcp b pp def_node_opt p1 in
      let (has_b2, has_pp2) = check_compatible lcp b pp def_node_opt p2 in
      if (has_b1 && has_pp2) || (has_b2 && has_pp1) then
	raise Compatible;
      (has_b1 || has_b2, has_pp1 || has_pp2)
  | Repl(b',p) ->
      if lcp <= 0 then
	(* When lcp <= 0, we have Compatible as soon as b is defined in p and pp occurs in p,
           and this can be tested very efficiently using definition nodes *)
	let (has_b, has_pp) =
	  match def_node_opt with
	    None -> check_compatible (lcp-1) b pp def_node_opt p
	  | Some (_,_,pp_node) ->
	      (* Returns true when p' is above node n *)
	      let rec find p' n =
		match n.definition with
		  DInputProcess p'' when p'' == p' -> true
		| _ -> if n.above_node == n then false else find p' n.above_node
	      in
	      (List.exists (find p') b.def, find p' pp_node)
	in
	if (has_b || (b' == b)) && has_pp then
	  raise Compatible;
	(has_b || (b' == b), has_pp)
      else
	let (has_b, has_pp) = check_compatible (lcp-1) b pp def_node_opt p in
	if (b' == b) && has_pp then
	  raise Compatible;
	(has_b || (b' == b), has_pp)
  | Input(_,pat, p) ->
      let (has_b, has_pp) = check_compatibleo lcp b pp def_node_opt p in
      let has_b2 = Terms.occurs_in_pat b pat in
      if has_b2 && has_pp then
	raise Compatible;
      (has_b || has_b2, has_pp)

and check_compatibleo lcp b pp def_node_opt p =
  match p.p_desc with
    Yield -> (false, false)
  | Restr(b',p) ->
      let (has_b, has_pp) = check_compatibleo lcp b pp def_node_opt p in
      if (b' == b) && has_pp then
	raise Compatible;
      (has_b || (b' == b), has_pp)
  | Test(_, p1, p2) -> 
      let (has_b1, has_pp1) = check_compatibleo lcp b pp def_node_opt p1 in
      let (has_b2, has_pp2) = check_compatibleo lcp b pp def_node_opt p2 in
      (has_b1 || has_b2, has_pp1 || has_pp2)
  | Find(l0, p2, _) ->
      let (has_b2, has_pp2) = check_compatibleo lcp b pp def_node_opt p2 in
      let rec check_l = function
	  [] -> (false, false)
	| ((bl,def_list,t,p1)::l) ->
	    let (has_br, has_ppr) = check_l l in
	    let (_, has_ppt) = check_compatiblefc lcp b pp def_node_opt t in
	    let (has_b1, has_pp1) = check_compatibleo lcp b pp def_node_opt p1 in
	    let has_b0 = List.memq b bl in
	    if has_b0 && (has_ppt || has_pp1 || (def_list == pp)) then
	      raise Compatible;
	    (has_br || has_b1 || has_b0, has_ppr || has_ppt || has_pp1 || (def_list == pp))
      in
      let (has_bl, has_ppl) = check_l l0 in
      (has_bl || has_b2, has_ppl || has_pp2)
  | Let(pat, _, p1, p2) ->
      let (has_b1, has_pp1) = check_compatibleo lcp b pp def_node_opt p1 in
      let (has_b2, has_pp2) = check_compatibleo lcp b pp def_node_opt p2 in
      let has_b3 = Terms.occurs_in_pat b pat in
      if has_b3 && has_pp1 then 
	raise Compatible;
      (has_b1 || has_b2 || has_b3, has_pp1 || has_pp2)
  | Output(_,_,p) ->
      check_compatible lcp b pp def_node_opt p 
  | EventP(_,p) ->
      check_compatibleo lcp b pp def_node_opt p 


let check_compatible_main b args pp cur_array simp_facts def_node_opt =
  let rec get_lcp l1 l2 = 
    match (l1,l2) with
      ({ t_desc = Var(b1,[]) }::l1',b2::l2') when b1 == b2 ->
	1 + get_lcp l1' l2' 
    | (t::l1',b2::l2') ->
	begin
	  match Facts.try_no_var simp_facts t with
	    { t_desc = Var(b1,[]) } when b1 == b2 ->
	      1 + get_lcp l1' l2' 
	  | _ -> 0
	end
    | _ -> 0
  in
  let lcp = get_lcp (List.rev args) (List.rev cur_array) in
  try
    let (has_b, has_pp) = check_compatible lcp b pp def_node_opt (!whole_game).proc in
    if not has_pp then
      Parsing_helper.internal_error "Program point not found in check_compatible_deflist; deflist probably altered since whole_game was set";
    false
  with Compatible ->
    true


let rec check_compatible_deflist pp cur_array simp_facts def_node_opt def_list =
  List.for_all (fun (b,l) -> check_compatible_main b l pp cur_array simp_facts def_node_opt) def_list

end


(* check_compatible2_deflist checks that all pairs of variables that must 
   be defined can be simultaneously defined.
   Uses the field "compatible" set by Terms.build_compatible_defs
 *)


module CompatibleDefs2
=
struct

let rec check_compatible2_main = function
    [] -> true
  | (a::l) -> 
      (List.for_all (Terms.is_compatible a) l) &&
      (check_compatible2_main l)

let rec check_compatible2_deflist simp_facts old_def_list def_list =
  (* First simplify the terms in the list of defined variables *)
  let old_def_list = List.map (fun (b,l) -> (b, List.map (Facts.try_no_var simp_facts) l)) old_def_list in
  let def_list = List.map (fun (b,l) -> (b, List.map (Facts.try_no_var simp_facts) l)) def_list in
  (* Then remove the already defined variables from the new def_list *)
  let new_def_list = List.filter (fun br -> not (Terms.mem_binderref br old_def_list)) def_list in
  (* Check that the newly defined variables are compatible with each other *)
  (check_compatible2_main new_def_list) && 
  (* ... and with all the previously defined variables *)
  (List.for_all (fun br -> List.for_all (Terms.is_compatible br) new_def_list) old_def_list)

end


let needed_vars vars = List.exists Transform.has_array_ref vars

let needed_vars_in_pat pat =
  needed_vars (Terms.vars_from_pat [] pat)

(* Return true when b has an array reference in t with
   indexes different from the indexes at creation *)

let rec has_array_access b t =
  match t.t_desc with
    Var(b',l) -> 
      ((b == b') && not (List.for_all2 Terms.equal_terms l b.args_at_creation)) ||
      (List.exists (has_array_access b) l)
  | FunApp(f,l) ->
      List.exists (has_array_access b) l
  | ResE(b',t) -> has_array_access b t
  | TestE(t1,t2,t3) -> 
      (has_array_access b t1) || (has_array_access b t2) || (has_array_access b t3)
  | FindE(l0,t3,_) ->
      (List.exists (fun (bl,def_list,t1,t2) ->
	(List.exists (has_array_access_br b) def_list) ||
	(has_array_access b t1) || (has_array_access b t2)
	) l0) || (has_array_access b t3)
  | LetE(pat,t1,t2,topt) ->
      (has_array_access_pat b pat) ||
      (has_array_access b t1) || 
      (has_array_access b t2) || 
      (match topt with
	None -> false
      |	Some t3 -> has_array_access b t3)
  | EventE _ ->
     Parsing_helper.internal_error "Event should have been expanded"

and has_array_access_br b (b',l) =
  ((b == b') && not (List.for_all2 Terms.equal_terms l b.args_at_creation)) ||
  (List.exists (has_array_access b) l)

and has_array_access_pat b = function
    PatVar _ -> false
  | PatTuple(_,l) -> List.exists (has_array_access_pat b) l
  | PatEqual t -> has_array_access b t

(* Simplification of terms with if/let/find/res *)

exception OneBranchTerm of (binder list * binderref list * term * term)

let rec simplify_term_w_find find_indices cur_array true_facts t =
  match t.t_desc with
    Var _ | FunApp _ ->     
      simplify_term (find_indices @ cur_array) DepAnal2.init false true_facts t
  | TestE(t1,t2,t3) ->
      begin
	(* If p1 and p2 are equal, we can remove the test *)
      if (!Settings.merge_branches) && 
	 (Mergebranches.equal_term_with_find true_facts t2 t3) then
	begin
	  Transform.changed := true;
	  simplify_term_w_find find_indices cur_array true_facts t3
	end
      else
      let t1' = simplify_term (find_indices @ cur_array) DepAnal2.init false true_facts t1 in
      let t_or_and = Terms.or_and_form t1' in
      try
	let t3' = simplify_term_w_find find_indices cur_array (Facts.simplif_add (dependency_collision (find_indices @ cur_array) DepAnal2.init) true_facts (Terms.make_not t1')) t3 in
	simplify_term_if find_indices cur_array true_facts t2 t3' t_or_and
      with Contradiction ->
	Transform.changed := true;
	simplify_term_w_find find_indices cur_array true_facts t2
      end

  | FindE(l0,t3,find_info) -> 
      begin
	(* If the processes in all branches are equal and the variables
	   defined by the find are not needed (no array reference, do not occur
	   in queries), we can remove the find *)
      if (!Settings.merge_branches) && (find_info != Unique) &&
	(Mergebranches.can_merge_all_branches_findE t true_facts l0 t3) then
	begin
	  Transform.changed := true;
	  simplify_term_w_find find_indices cur_array true_facts t3
	end
      else	

      (* Expand find in conditions of find when both finds are "unique" *)
      let l0' = 
	if (!Settings.unique_branch) && (find_info == Unique) then
	  let rec expand_find seen = function
	      [] -> l0
	    | (((bl, def_list, t, t2) as br1)::r) ->
		match t.t_desc with
		  FindE(l2, t4, Unique) when Terms.is_false t4 ->
		    List.rev_append seen ((List.map (fun (bl3, def_list3, t5, t6) ->
		      (bl @ bl3, def_list @ def_list3, Terms.make_and t5 t6, t2)) l2) @ r)
		| _ -> expand_find (br1::seen) r
	  in
	  expand_find [] l0
	else
	  l0
      in
      if l0' != l0 then
	begin
	  Transform.changed := true;
	  Terms.build_term_type t3.t_type (FindE(l0', t3, find_info))
	end
      else

      (* Expand find in branch of find when both finds are "unique" *)
      let l0', t3' = 
	if (!Settings.unique_branch) && (find_info == Unique) then
	  let rec expand_find seen = function
	      [] -> l0, t3
	    | (((bl, def_list, t, t2) as br1)::r) ->
		match t2.t_desc with
		  FindE(l3, t4, Unique) ->
		    List.iter (fun b ->
		      Transform.advise := Terms.add_eq (SArenaming b) (!Transform.advise)) bl;
		    (List.rev_append seen ((List.map (fun (bl3, def_list3, t5, t6) ->
		      (bl @ bl3, def_list @ def_list3, Terms.make_and t t5, t6)) l3) @ r)),
		    (Terms.build_term_type t3.t_type (FindE([bl, def_list, t, t4], t3, Nothing)))
		| _ -> expand_find (br1::seen) r
	  in
	  expand_find [] l0
	else
	  l0, t3
      in
      if l0' != l0 then
	begin
	  Transform.changed := true;
	  Terms.build_term_type t3.t_type (FindE(l0', t3', find_info))
	end
      else

      let l0 =
	if (!Settings.merge_branches) && (find_info == Unique) then
	  List.filter (fun br ->
	    let r = 
	      not (Mergebranches.can_merge_one_branch_findE t true_facts br t3)
	    in
	    if not r then Transform.changed := true;
	    r
	      ) l0
	else
	  l0
      in

      match l0 with
	[] ->
	  simplify_term_w_find find_indices cur_array true_facts t3
      |	[([],def_list,t1,t2)] when Facts.reduced_def_list t.t_facts def_list = [] && 
	                              (match t1.t_desc with Var _ | FunApp _ -> true | _ -> false) -> 
	  Transform.changed := true;
	   simplify_term_w_find find_indices cur_array true_facts (Terms.build_term_type t3.t_type (TestE(t1,t2,t3)))
      |	_ -> 
      let def_vars = Facts.get_def_vars_at t.t_facts in
      let t3' = 
	try
	  simplify_term_w_find find_indices cur_array (add_elsefind (dependency_collision (find_indices @ cur_array) DepAnal2.init) def_vars true_facts l0) t3
	with Contradiction ->
	  (* Transform.changed := true;
	  TO DO in fact, the else branch of the find will never be executed *)
	  t3
      in
      let rec simplify_findl = function
	  [] -> []
	| (bl, def_list, t1, t2)::l ->
	    begin
	    let l' = simplify_findl l in
	    try
	      let this_branch_node = Facts.get_node_for_find_branch t.t_facts bl in 
	      let true_facts = filter_elsefind (not_deflist_l bl) true_facts in
	      let facts_def_list = Facts.facts_from_defined this_branch_node bl def_list in
	      let true_facts' = Facts.simplif_add_list (dependency_collision (find_indices @ cur_array) DepAnal2.init) true_facts facts_def_list in
	      let def_list' = Facts.reduced_def_list t.t_facts def_list in
	      (* Set priorities of variables defined by this find, 
	         to orient rewrite rules preferably in the direction
	         b[..] -> t where b \in bl *)
	      incr current_max_priority;
	      List.iter (fun b -> 
		b.priority <- (!current_max_priority); 
		priority_list := b :: (!priority_list)) bl;
	      let (t1',tf') =
		match t1.t_desc with
		  Var _ | FunApp _ ->
		    let t1' = simplify_term (bl @ find_indices @ cur_array) DepAnal2.init false true_facts' t1 in
		    let tf' = Facts.simplif_add (dependency_collision (bl @ find_indices @ cur_array) DepAnal2.init) true_facts' t1' in
		    (t1',tf')
		| _ -> 
		    let t1' = simplify_term_w_find (bl @ find_indices) cur_array true_facts' t1 in
		    (t1', true_facts')
	      in

	      (* The "defined" conditions cannot hold
		 Using def_list as a marker for the program point.
		 It is important that def_list still has physically the same value as
		 in the initial process; in particular, that it is not modified by
		 DepAnal2.update_dep_infoo. *)
	      let def_vars_accu = Facts.def_vars_from_defined this_branch_node bl def_list' in
	      (* check_compatible_deflist checks that the variables in def_vars_accu can be defined
	         at the current program point *)
	      if not (CompatibleDefs.check_compatible_deflist def_list cur_array tf' t.t_facts def_vars_accu) then
		raise Contradiction;
	      (* check_compatible2_deflist checks that all pairs of variables 
		 that must be defined can be simultaneously defined. 
		 Useful in some examples, but costly! *)
	      if !Settings.detect_incompatible_defined_cond then
		begin
		  if not (CompatibleDefs2.check_compatible2_deflist tf' def_vars def_vars_accu) then
		    raise Contradiction
		end;
	      let def_vars' = 
		(* Using def_vars_accu instead of def_list' is more precise *)
	        def_vars_accu @ def_vars
	      in
	      let tf' = convert_elsefind (dependency_collision (find_indices @ cur_array) DepAnal2.init) def_vars' tf' in
	      let t2' = simplify_term_w_find find_indices cur_array tf' t2 in
	      let accu_def_list = ref def_list' in 
	      List.iter (Terms.get_deflist_subterms accu_def_list) facts_def_list;
	      let accu_def_list_subterm = ref [] in
	      List.iter (Terms.close_def_subterm accu_def_list_subterm) (!accu_def_list);
	      let accu_needed = ref [] in
	      Terms.get_deflist_subterms accu_needed t1';
	      Terms.get_deflist_subterms accu_needed t2';
	      let accu_needed_subterm = ref [] in
	      List.iter (Terms.close_def_subterm accu_needed_subterm) (!accu_needed);
	      let needed_occur = 
		(Facts.reduced_def_list t.t_facts 
		   (Terms.inter_binderref (!accu_needed_subterm) (!accu_def_list_subterm))) in
	      let implied_needed_occur = Facts.def_vars_from_defined None bl needed_occur in
	      let def_list'' = Terms.setminus_binderref def_list' implied_needed_occur in
	      let def_list3 = remove_subterms [] (needed_occur @ (filter_def_list bl [] def_list'')) in

	      (* When i = M implied by def_list & t, remove i from bl
		 and substitute M for i *)
	      let keep_bl = ref [] in
	      let subst = ref [] in
	      List.iter (fun b -> 
		let b_im = Facts.try_no_var tf' (Terms.term_from_binder b) in
		if (has_array_access b t1') ||
		   (List.exists (fun (b', b_im') -> Terms.refers_to b b_im') (!subst)) ||
		   (List.exists (has_array_access_br b) def_list') ||
		   (Terms.refers_to b b_im)
		then
		  keep_bl := b :: (!keep_bl)
		else
		  subst := (b, b_im) :: (List.filter (fun (b',_) -> 
		    if Terms.refers_to b' b_im then 
		      begin
			keep_bl := b' :: (!keep_bl);
			false
		      end
		    else
		      true
			) (!subst));
					  ) bl;
	      let bl = !keep_bl in
	      if (!subst) != [] then Transform.changed := true;
	      let def_list_tmp = ref [] in
	      List.iter (fun br ->
		Terms.get_deflist_subterms def_list_tmp 
		  (Terms.subst3 (!subst) (Terms.term_from_binderref br))) def_list3;
	      let def_list3 = !def_list_tmp in 
	      let t1' = Terms.subst3 (!subst) t1' in
	      let rec add_let p = function
		  [] -> p
		| ((b, b_im)::l) ->
		    Terms.build_term_type p.t_type (LetE(PatVar b, b_im, add_let p l, None))
	      in
	      let t2' = add_let (Terms.subst3 (!subst) t2') (!subst) in
	      (* End of "When i = M implied by def_list & t, remove i from bl
		 and substitute M for i"*)

              let find_branch = (bl, def_list3, t1', t2') in

              (* If the find is marked "unique", and we can prove that
	         the current branch succeeds, keep only that branch *)
              if (find_info == Unique) && (!Settings.unique_branch) &&
		(match t1'.t_desc with
		  Var _ | FunApp _ -> true
		| _ -> false)
	      then 
		try 
		  branch_succeeds find_branch (dependency_collision (find_indices @ cur_array) DepAnal2.init) true_facts def_vars;
		  find_branch :: l'
		with SuccessBranch(subst, keep_bl) ->
		  if List.exists (fun (b, b_im) -> 
		    (has_array_access b t1') ||
		    (List.exists (fun (b', b_im') -> Terms.refers_to b b_im') subst) ||
		    (List.exists (has_array_access_br b) def_list3)
					  ) subst
		  then raise (OneBranchTerm(find_branch));
		  if subst != [] then Transform.changed := true;
		  let def_list_tmp = ref [] in
		  List.iter (fun br ->
		    Terms.get_deflist_subterms def_list_tmp 
		      (Terms.subst3 subst (Terms.term_from_binderref br))) def_list3;
		  let def_list3 = !def_list_tmp in 
		  let t1' = Terms.subst3 subst t1' in
		  let rec add_let p = function
		      [] -> p
		    | ((b, b_im)::l) ->
			Terms.build_term_type p.t_type (LetE(PatVar b, b_im, add_let p l, None))
		  in
		  let t2' = add_let (Terms.subst3 subst t2') subst in
		  raise (OneBranchTerm(keep_bl, def_list3, t1', t2'))
	      else
		find_branch :: l'

	      (*let t_or_and = Terms.or_and_form t' in
	      simplify_find true_facts' l' bl def_list' t_or_and p1 *)
	    with Contradiction ->
	      Transform.changed := true;
	      l'
	    end
      in
      try 
	let l0' = simplify_findl l0 in
	if l0' == [] then
	  begin
	    Transform.changed := true;
	    t3'
	  end
	else
	  Terms.build_term_type t3'.t_type (FindE(l0', t3',find_info))
      with OneBranchTerm(find_branch) ->
	match find_branch with
	  ([],[],_,t2) -> 
	    Transform.changed := true;
	    t2
	| _ ->
	    (* TO DO in fact, the else branch of the find will never be executed *)
	    if List.length l0 > 1 then Transform.changed := true;
	    Terms.build_term_type t3'.t_type (FindE([find_branch], t3',find_info))
      end

  | LetE(pat,t1,t2,topt) ->
      begin
	(* If p1 and p2 are equal and the variables in the pattern pat are
           not needed (no array reference, do not occur in queries), 
	   we can remove the let *)
      if (!Settings.merge_branches) && 
	 (match topt with
	   None -> false
	 | Some t3 -> Mergebranches.equal_term_with_find true_facts t2 t3) &&
         (not (needed_vars_in_pat pat)) then
	begin
	  Transform.changed := true;
	  simplify_term_w_find find_indices cur_array true_facts t2
	end
      else
      let true_facts' = filter_elsefind (not_deflist_l (Terms.vars_from_pat [] pat)) true_facts in
      let t1' = simplify_term (find_indices @ cur_array) DepAnal2.init (Terms.is_pat_tuple pat) true_facts t1 in
      simplify_term_let find_indices true_facts cur_array true_facts' t2 topt t1' pat
      end

  | ResE(b,t) ->
      let true_facts = filter_elsefind (not_deflist b) true_facts in
      let t' = simplify_term_w_find find_indices cur_array true_facts t in
      if not ((Transform.has_array_ref b) || (Terms.refers_to b t)) then
	begin
	  Transform.changed := true;
	  t'
	end
      else
	Terms.build_term_type t'.t_type (ResE(b, t'))

  | EventE _ ->
      Parsing_helper.internal_error "Event should have been expanded"

and simplify_term_if find_indices cur_array true_facts ttrue tfalse t' =
  match t'.t_desc with
    FunApp(f, []) when f == Settings.c_false -> 
      Transform.changed := true;
      tfalse
  | FunApp(f, []) when f == Settings.c_true -> 
      Transform.changed := true;
      simplify_term_w_find find_indices cur_array true_facts ttrue
  | FunApp(f, [t1; t2]) when f == Settings.f_or ->
      Transform.changed := true;
      simplify_term_if find_indices cur_array true_facts ttrue (simplify_term_if find_indices cur_array true_facts ttrue tfalse t2) t1
  | _ -> 
      try
	let ttrue' = simplify_term_w_find find_indices cur_array (Facts.simplif_add (dependency_collision (find_indices @ cur_array) DepAnal2.init) true_facts t') ttrue in
	Terms.build_term_type tfalse.t_type (TestE(t', ttrue', tfalse))
      with Contradiction ->
	Transform.changed := true;
	tfalse

and simplify_term_let find_indices true_facts_else cur_array true_facts ttrue tfalse t' = function
    (PatVar b) as pat -> 
      if tfalse != None then Transform.changed := true;
      Terms.build_term_type ttrue.t_type (LetE(pat, t', simplify_term_w_find find_indices cur_array (Facts.simplif_add (dependency_collision (find_indices @ cur_array) DepAnal2.init) true_facts (Terms.make_let_equal 
	(Terms.term_from_binder b) t')) ttrue, None))
  | PatEqual t ->
      Transform.changed := true;
      begin
	match tfalse with
	  None -> Parsing_helper.internal_error "missing else branch of let"
	| Some t3 ->
	    simplify_term_w_find find_indices cur_array true_facts (Terms.build_term_type t3.t_type (TestE(Terms.make_equal t t', ttrue, t3)))
      end
  | (PatTuple (f,l)) as pat ->
      begin
	match tfalse with
	  None -> Parsing_helper.internal_error "missing else branch of let"
	| Some t3 ->
	try 
	  let res = simplify_term_w_find find_indices cur_array true_facts 
	      (Terms.put_lets_term l (Terms.split_term f t') ttrue tfalse)
	  in
	  Transform.changed := true;
	  res
	with 
	  Not_found -> 
	    begin
	      try
		let ttrue' = simplify_term_w_find find_indices cur_array (Facts.simplif_add (dependency_collision (find_indices @ cur_array) DepAnal2.init) true_facts 
		   (Terms.make_equal (Terms.term_from_pat pat) t')) ttrue
		in
		Terms.build_term_type ttrue.t_type (LetE(pat, t', ttrue', Some (simplify_term_w_find find_indices cur_array true_facts_else t3)))
	      with Contradiction ->
		Transform.changed := true;
		simplify_term_w_find find_indices cur_array true_facts_else t3
	    end
	| Terms.Impossible -> 
	    Transform.changed := true;
	    simplify_term_w_find find_indices cur_array true_facts_else t3
      end


(* Simplification of processes *)

exception OneBranchProcess of (binder list * binderref list * term * process)

let rec simplify_process cur_array dep_info true_facts p = 
  let dep_info' = DepAnal2.update_dep_info cur_array dep_info true_facts p in
  Terms.iproc_from_desc (
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) -> Par(simplify_process cur_array dep_info' true_facts p1,
		      simplify_process cur_array dep_info' true_facts p2)
  | Repl(b,p) -> Repl(b, simplify_process (b::cur_array) dep_info' true_facts p)
  | Input((c,tl), pat, p) ->
      begin
	match true_facts with
	  (_,_,[]) -> ()
	| _ -> Parsing_helper.internal_error "There should be no elsefind facts at inputs"
      end;
      Input((c, List.map (fun t -> simplify_term cur_array dep_info false true_facts t) tl), 
	    simplify_pat cur_array dep_info true_facts pat, 
	    simplify_oprocess cur_array dep_info' true_facts p))


and simplify_oprocess cur_array dep_info true_facts p =
  let (p', dep_info_list') = DepAnal2.update_dep_infoo cur_array dep_info true_facts p in
  match p'.p_desc with
    Yield -> Terms.yield_proc
  | Restr(b,p) -> 
      let true_facts = filter_elsefind (not_deflist b) true_facts in
      let p' = simplify_oprocess cur_array (List.hd dep_info_list') true_facts p in
      if not ((Transform.has_array_ref b) || (Terms.refers_to_oprocess b p)) then
	begin
	  Transform.changed := true;
	  p'
	end
      else
	Terms.oproc_from_desc (Restr(b, p'))
  | Test(t, p1, p2) ->
      begin
	(* If p1 and p2 are equal, we can remove the test *)
      if (!Settings.merge_branches) && 
	 (Mergebranches.equal_oprocess true_facts p1 p2) then
	begin
	  Transform.changed := true;
	  simplify_oprocess cur_array dep_info true_facts p2
	end
      else
      let t' = simplify_term cur_array dep_info false true_facts t in
      let t_or_and = Terms.or_and_form t' in
      try
	let p2' = simplify_oprocess cur_array (List.hd dep_info_list') (Facts.simplif_add (dependency_collision cur_array dep_info) true_facts (Terms.make_not t')) p2 in
	simplify_if (List.hd dep_info_list') cur_array true_facts p1 p2' t_or_and
      with Contradiction ->
	Transform.changed := true;
	simplify_oprocess cur_array (List.hd dep_info_list') true_facts p1
      end
  | Find(l0, p2, find_info) ->
      begin
	(* If the processes in all branches are equal and the variables
	   defined by the find are not needed (no array reference, do not occur
	   in queries), we can remove the find *)
      if (!Settings.merge_branches) && (find_info != Unique) &&
	(Mergebranches.can_merge_all_branches_find p' true_facts l0 p2) then
	begin
	  Transform.changed := true;
	  simplify_oprocess cur_array dep_info true_facts p2
	end
      else

      match dep_info_list' with
	[] -> Parsing_helper.internal_error "Non empty dep_info_list' needed"
      |	dep_info_else :: dep_info_then ->

      (* Expand find in conditions of find when both finds are "unique" *)
      let l0' = 
	if (!Settings.unique_branch) && (find_info == Unique) then
	  let rec expand_find seen = function
	      [] -> l0
	    | (((bl, def_list, t, p1) as br1)::r) ->
		match t.t_desc with
		  FindE(l2, t2, Unique) when Terms.is_false t2 ->
		    List.rev_append seen ((List.map (fun (bl3, def_list3, t3, t4) ->
		      (bl @ bl3, def_list @ def_list3, Terms.make_and t3 t4, p1)) l2) @ r)
		| _ -> expand_find (br1::seen) r
	  in
	  expand_find [] l0
	else
	  l0
      in
      if l0' != l0 then
	begin
	  Transform.changed := true;
	  Terms.oproc_from_desc (Find(l0', p2, find_info))
	end
      else

      (* Expand find in branch of find when both finds are "unique" *)
      let l0', p2' = 
	if (!Settings.unique_branch) && (find_info == Unique) then
	  let rec expand_find seen = function
	      [] -> l0, p2
	    | (((bl, def_list, t, p1) as br1)::r) ->
		match p1.p_desc with
		  Find(l3, p3, Unique) ->
		    List.iter (fun b ->
		      Transform.advise := Terms.add_eq (SArenaming b) (!Transform.advise)) bl;
		    (List.rev_append seen ((List.map (fun (bl3, def_list3, t3, p4) ->
		      (bl @ bl3, def_list @ def_list3, Terms.make_and t t3, p4)) l3) @ r)),
		    (Terms.oproc_from_desc (Find([bl, def_list, t, p3], p2, Nothing)))
		| _ -> expand_find (br1::seen) r
	  in
	  expand_find [] l0
	else
	  l0, p2
      in
      if l0' != l0 then
	begin
	  Transform.changed := true;
	  Terms.oproc_from_desc (Find(l0', p2', find_info))
	end
      else


      let l0, dep_info_then =
	if (!Settings.merge_branches) && (find_info == Unique) then
	  let rec filter2 l1 l2 =
	    match (l1,l2) with
	      [],[] -> [],[]
	    | a1::r1, a2::r2 ->
		let r1',r2' = filter2 r1 r2 in
		let r = 
		  not (Mergebranches.can_merge_one_branch_find p' true_facts a1 p2)
		in
		if not r then Transform.changed := true;
		if r then (a1::r1',a2::r2') else (r1',r2')
	    | _ -> Parsing_helper.internal_error "Lists of different lengths in filter2"
	  in 
	  filter2 l0 dep_info_then
	else
	  l0, dep_info_then
      in

      match l0 with
	[] ->
	  simplify_oprocess cur_array dep_info true_facts p2
      |	[([],def_list,t1,p1)] when (Facts.reduced_def_list p'.p_facts def_list = []) && 
	                              (match t1.t_desc with Var _ | FunApp _ -> true | _ -> false) -> 
	  Transform.changed := true;
	  simplify_oprocess cur_array dep_info true_facts (Terms.oproc_from_desc  (Test(t1,p1,p2)))
      |	_ -> 

      let def_vars = Facts.get_def_vars_at p'.p_facts in
      let p2' = 
	if p2.p_desc == Yield then Terms.yield_proc else
	try
	  simplify_oprocess cur_array dep_info_else (add_elsefind (dependency_collision cur_array dep_info_else) def_vars true_facts l0) p2
	with Contradiction ->
	  Transform.changed := true;
	  Terms.yield_proc
      in
      let rec simplify_findl dep_info_l1 l1 = 
	match (dep_info_l1,l1) with
	  [],[] -> []
	| (dep_infoi::dep_info_l),((bl, def_list, t, p1)::l) ->
	    begin
	    let l' = simplify_findl dep_info_l l in
	    try
	      let this_branch_node = Facts.get_node_for_find_branch p'.p_facts bl in 
	      let true_facts = filter_elsefind (not_deflist_l bl) true_facts in
	      let facts_def_list = Facts.facts_from_defined this_branch_node bl def_list in
	      let true_facts' = Facts.simplif_add_list (dependency_collision cur_array dep_infoi) true_facts facts_def_list in
	      let def_list' = Facts.reduced_def_list p'.p_facts def_list in
	      (* Set priorities of variables defined by this find, 
	         to orient rewrite rules preferably in the direction
	         b[..] -> t where b \in bl *)
	      incr current_max_priority;
	      List.iter (fun b -> 
		b.priority <- (!current_max_priority);
		priority_list := b :: (!priority_list)) bl;
	      let (t',tf') =
		match t.t_desc with
		  Var _ | FunApp _ ->
		    let t' = simplify_term (bl @ cur_array) dep_infoi false true_facts' t in
		    let tf' = Facts.simplif_add (dependency_collision (bl @ cur_array) dep_infoi) true_facts' t' in
		    (t',tf')
		| _ -> 
		    let t' = simplify_term_w_find bl cur_array true_facts' t in
		    (t', true_facts')
	      in

	      (* The "defined" conditions cannot hold
		 Using def_list as a marker for the program point.
		 It is important that def_list still has physically the same value as
		 in the initial process; in particular, that it is not modified by
		 DepAnal2.update_dep_infoo. *)
	      let def_vars_accu = Facts.def_vars_from_defined this_branch_node bl def_list' in
	      (* check_compatible_deflist checks that the variables in def_vars_accu can be defined
	         at the current program point *)
	      if not (CompatibleDefs.check_compatible_deflist def_list cur_array tf' p'.p_facts def_vars_accu) then
		raise Contradiction;
	      (* check_compatible2_deflist checks that all pairs of variables 
		 that must be defined can be simultaneously defined. 
		 Useful in some examples, but costly! *)
	      if !Settings.detect_incompatible_defined_cond then
		begin
		  if not (CompatibleDefs2.check_compatible2_deflist tf' def_vars def_vars_accu) then
		    raise Contradiction
		end;
	      let def_vars' = 
		(* Using def_vars_accu instead of def_list' is more precise *)
		def_vars_accu @ def_vars
	      in
	      let tf' = convert_elsefind (dependency_collision cur_array dep_infoi) def_vars' tf' in
	      let p1' = simplify_oprocess cur_array dep_infoi tf' p1 in
	      let accu_def_list = ref def_list' in 
	      List.iter (Terms.get_deflist_subterms accu_def_list) facts_def_list;
	      let accu_def_list_subterm = ref [] in
	      List.iter (Terms.close_def_subterm accu_def_list_subterm) (!accu_def_list);
	      let accu_needed = ref [] in
	      Terms.get_deflist_subterms accu_needed t';
	      Terms.get_deflist_oprocess accu_needed p1';
	      let accu_needed_subterm = ref [] in
	      List.iter (Terms.close_def_subterm accu_needed_subterm) (!accu_needed);
	      let needed_occur = 
		(Facts.reduced_def_list p'.p_facts 
		   (Terms.inter_binderref (!accu_needed_subterm) (!accu_def_list_subterm))) in
	      let implied_needed_occur = Facts.def_vars_from_defined None bl needed_occur in
	      let def_list'' = Terms.setminus_binderref def_list' implied_needed_occur in
	      let def_list3 = remove_subterms [] (needed_occur @ (filter_def_list bl [] def_list'')) in

	      (* When i = M implied by def_list & t, remove i from bl
		 and substitute M for i *)
	      let keep_bl = ref [] in
	      let subst = ref [] in
	      List.iter (fun b -> 
		let b_im = Facts.try_no_var tf' (Terms.term_from_binder b) in
		if (has_array_access b t') ||
		   (List.exists (fun (b', b_im') -> Terms.refers_to b b_im') (!subst)) ||
		   (List.exists (has_array_access_br b) def_list') ||
		   (Terms.refers_to b b_im)
		then
		  keep_bl := b :: (!keep_bl)
		else
		  subst := (b, b_im) :: (List.filter (fun (b',_) -> 
		    if Terms.refers_to b' b_im then 
		      begin
			keep_bl := b' :: (!keep_bl);
			false
		      end
		    else
		      true
			) (!subst))
					  ) bl;
	      let bl = !keep_bl in
	      if (!subst) != [] then Transform.changed := true;
	      let def_list_tmp = ref [] in
	      List.iter (fun br ->
		Terms.get_deflist_subterms def_list_tmp 
		  (Terms.subst3 (!subst) (Terms.term_from_binderref br))) def_list3;
	      let def_list3 = !def_list_tmp in 
	      let t' = Terms.subst3 (!subst) t' in
	      let rec add_let p = function
		  [] -> p
		| ((b, b_im)::l) ->
		    Terms.oproc_from_desc (Let(PatVar b, b_im, add_let p l, Terms.yield_proc))
	      in
	      let p1' = add_let (Terms.subst_oprocess3 (!subst) p1') (!subst) in
	      (* End of "When i = M implied by def_list & t, remove i from bl
		 and substitute M for i"*)

              let find_branch = (bl, def_list3, t', p1') in

              (* If the find is marked "unique", and we can prove that
	         the current branch succeeds, keep only that branch *)
              if (find_info == Unique) &&  (!Settings.unique_branch) &&
		(match t'.t_desc with
		  Var _ | FunApp _ -> true
		| _ -> false)
	      then 
		try 
		  branch_succeeds find_branch (dependency_collision cur_array dep_infoi) true_facts def_vars;
		  find_branch :: l'
		with SuccessBranch(subst, keep_bl) ->
		  if List.exists (fun (b, b_im) -> 
		    (has_array_access b t') ||
		    (List.exists (fun (b', b_im') -> Terms.refers_to b b_im') subst) ||
		    (List.exists (has_array_access_br b) def_list3)
					  ) subst
		  then raise (OneBranchProcess(find_branch));
		  if subst != [] then Transform.changed := true;
		  let def_list_tmp = ref [] in
		  List.iter (fun br ->
		    Terms.get_deflist_subterms def_list_tmp 
		      (Terms.subst3 subst (Terms.term_from_binderref br))) def_list3;
		  let def_list3 = !def_list_tmp in 
		  let t' = Terms.subst3 subst t' in
		  let rec add_let p = function
		      [] -> p
		    | ((b, b_im)::l) ->
			Terms.oproc_from_desc (Let(PatVar b, b_im, add_let p l, Terms.yield_proc))
		  in
		  let p1' = add_let (Terms.subst_oprocess3 subst p1') subst in
		  raise (OneBranchProcess(keep_bl, def_list3, t', p1'))
	      else
		find_branch :: l'

	      (*let t_or_and = Terms.or_and_form t' in
	      simplify_find true_facts' l' bl def_list' t_or_and p1 *)
	    with Contradiction ->
	      Transform.changed := true;
	      l'
	    end
	| _ -> Parsing_helper.internal_error "Different lengths in simplify/Find"
      in
      try
	let l0' = simplify_findl dep_info_then l0 in
	if l0' == [] then
	  begin
	    Transform.changed := true;
	    p2'
	  end
	else
	  begin
	    if (p2'.p_desc == Yield) && (List.for_all (fun (bl,_,t,p1) ->
	      (p1.p_desc == Yield) && (not (List.exists Transform.has_array_ref bl))
		) l0') then
	      begin
		Transform.changed := true;
		Terms.yield_proc
	      end
	    else
	      Terms.oproc_from_desc (Find(l0', p2', find_info))
	  end
      with OneBranchProcess(find_branch) ->
	match find_branch with
	  ([],[],_,p1) -> 
	    Transform.changed := true;
	    p1
	| _ ->
	    (* the else branch of the find will never be executed *)
	    if (List.length l0 > 1) || (p2.p_desc != Yield) then Transform.changed := true;
	    Terms.oproc_from_desc (Find([find_branch], Terms.yield_proc, find_info))
	
      end
  | Let(pat, t, p1, p2) ->
      begin
	(* If p1 and p2 are equal and the variables in the pattern pat are
           not needed (no array reference, do not occur in queries), 
	   we can remove the let *)
      if (!Settings.merge_branches) && 
	 (Mergebranches.equal_oprocess true_facts p1 p2) &&
         (not (needed_vars_in_pat pat)) then
	begin
	  Transform.changed := true;
	  simplify_oprocess cur_array dep_info true_facts p2
	end
      else
      let true_facts' = filter_elsefind (not_deflist_l (Terms.vars_from_pat [] pat)) true_facts in
      match dep_info_list' with
	[dep_info_in; dep_info_else] ->
	  let t' = simplify_term cur_array dep_info (Terms.is_pat_tuple pat) true_facts t in
	  simplify_let dep_info_else true_facts dep_info dep_info_in cur_array true_facts' p1 p2 t' pat
      |	[dep_info_in] -> 
	  let t' = simplify_term cur_array dep_info (Terms.is_pat_tuple pat) true_facts t in
	  simplify_let dep_info true_facts dep_info dep_info_in cur_array true_facts' p1 Terms.yield_proc t' pat 
      |	_ -> Parsing_helper.internal_error "Bad dep_info_list' in case Let"
      end
  | Output((c,tl),t2,p) ->
      (* Remove all "Elsefind" facts since variables may be defined 
         between the output and the following input *)
      let (subst, facts, _) = true_facts in
      let true_facts' = (subst, facts, []) in
      Terms.oproc_from_desc 
	(Output((c, List.map (fun t -> simplify_term cur_array dep_info false true_facts t) tl), 
	     simplify_term cur_array dep_info false true_facts t2,
	     simplify_process cur_array (List.hd dep_info_list') true_facts' p))
  | EventP(t,p) ->
      match t.t_desc with
	FunApp(f,_) ->
	  if not (Transform.event_occurs_in_queries f) then
	    simplify_oprocess cur_array (List.hd dep_info_list') true_facts p
	  else
	    Terms.oproc_from_desc (EventP(simplify_term cur_array dep_info false true_facts t,
					  simplify_oprocess cur_array (List.hd dep_info_list') true_facts p))
      |	_ ->
	  Parsing_helper.internal_error "Events must be function applications"

and simplify_if dep_info cur_array true_facts ptrue pfalse t' =
  match t'.t_desc with
    FunApp(f, []) when f == Settings.c_false -> 
      Transform.changed := true;
      pfalse
  | FunApp(f, []) when f == Settings.c_true -> 
      Transform.changed := true;
      simplify_oprocess cur_array dep_info true_facts ptrue
  | FunApp(f, [t1; t2]) when f == Settings.f_or ->
      Transform.changed := true;
      simplify_if dep_info cur_array true_facts ptrue (simplify_if dep_info cur_array true_facts ptrue pfalse t2) t1
  | _ -> 
      try
	let ptrue' =  simplify_oprocess cur_array dep_info (Facts.simplif_add (dependency_collision cur_array dep_info) true_facts t') ptrue in
	if (ptrue'.p_desc == Yield) && (pfalse.p_desc == Yield) then 
	  begin
	    Transform.changed := true;
	    Terms.yield_proc
	  end
	else
	  Terms.oproc_from_desc (Test(t', ptrue', pfalse))
      with Contradiction ->
	Transform.changed := true;
	pfalse

(*
and simplify_find true_facts accu bl def_list t' ptrue = 
  match t'.t_desc with
    FunApp(f, []) when f == Settings.c_false -> 
      Transform.changed := true;
      accu
  | FunApp(f, [t1; t2]) when f == Settings.f_or ->
      Transform.changed := true;
      simplify_find true_facts (simplify_find true_facts accu bl def_list t2 ptrue) bl def_list t1 ptrue
  | _ -> 
      try
	let tf' = Facts.simplif_add true_facts t' in
	(bl, def_list, t', simplify_oprocess tf' ptrue) :: accu
      with Contradiction ->
	Transform.changed := true;
	accu
*)

and simplify_let dep_info_else true_facts_else dep_info dep_info_in cur_array true_facts ptrue pfalse t' = function
    (PatVar b) as pat -> 
      if pfalse.p_desc != Yield then Transform.changed := true;
      Terms.oproc_from_desc 
	(Let(pat, t', simplify_oprocess cur_array dep_info_in 
	       (Facts.simplif_add (dependency_collision cur_array dep_info_in) true_facts 
		  (Terms.make_let_equal (Terms.term_from_binder b) t')) ptrue, Terms.yield_proc))
  | PatEqual t ->
      Transform.changed := true;
      simplify_oprocess cur_array dep_info true_facts 
	(Terms.oproc_from_desc (Test(Terms.make_equal t t', ptrue, pfalse)))
  | (PatTuple (f,l)) as pat ->
      begin
	try 
	  let res = simplify_oprocess cur_array dep_info true_facts 
	      (Terms.put_lets l (Terms.split_term f t') ptrue pfalse)
	  in
	  Transform.changed := true;
	  res
	with 
	  Not_found -> 
	    begin
	      try
		let ptrue' = simplify_oprocess cur_array dep_info_in (Facts.simplif_add (dependency_collision cur_array dep_info_in) true_facts 
		   (Terms.make_equal (Terms.term_from_pat pat) t')) ptrue
		in
		if (ptrue'.p_desc == Yield) && (pfalse.p_desc == Yield) &&
		  (not (needed_vars_in_pat pat)) then
		  begin
		    Transform.changed := true;
		    Terms.yield_proc
		  end
		else
		  Terms.oproc_from_desc (Let(pat, t', ptrue', simplify_oprocess cur_array dep_info_else true_facts_else pfalse))
	      with Contradiction ->
		Transform.changed := true;
		simplify_oprocess cur_array dep_info_else true_facts_else pfalse
	    end
	| Terms.Impossible -> 
	    Transform.changed := true;
	    simplify_oprocess cur_array dep_info_else true_facts_else pfalse
      end

let rec simplify_main1 iter g =
  let tmp_changed = !Transform.changed in
  partial_reset g;
  Transform.changed := false;
  Terms.array_ref_process g.proc;
  Terms.build_def_process None g.proc;
  if !Settings.detect_incompatible_defined_cond then
    Terms.build_compatible_defs g.proc;
  let p' = simplify_process [] DepAnal2.init ([],[],[]) g.proc in
  let g' = { proc = p'; game_number = -1 } in
  let res = 
    if (!Transform.changed) && (iter != 1) then 
      simplify_main1 (iter-1) g'
    else
      begin
	print_string ("Run simplify " ^ (string_of_int ((!Settings.max_iter_simplif) - iter + 1)));
	if !Transform.changed then 
	  print_string " time(s). Maximum reached.\n"
	else
	  print_string " time(s). Fixpoint reached.\n";
	g'
      end
  in
  Transform.changed := (!Transform.changed) || tmp_changed;
  Terms.cleanup_array_ref();
  if !Settings.detect_incompatible_defined_cond then
    Terms.empty_comp_process g.proc;
  res


let simplify_main coll_elim internal_info g =
  reset coll_elim internal_info g;
  let res_game = simplify_main1 (!Settings.max_iter_simplif) g in
  (* Add probability for eliminated collisions *)
  let proba = final_add_proba() in
  let internal_info' = Proba.final_internal_info() in
  (res_game, proba, internal_info', None)



(***** Filter out the indices that are unique knowing other indices *****
       (useful for reducing the probabilities in the crypto transformation) 
       Terms.build_def_process must have been called so that t.t_facts has 
       been filled. For use from cryptotransf.ml.
*)

type compat_info_elem = term * term list * binder list(* all indices *) * binder list (* initial indices *) 
      * binder list (* used indices *) * binder list (* really used indices *)

(* true_facts0 must not contain if/let/find/new. 
   if the initial indices contain "noninteractive" indices, we try
   to eliminate them, even by adding "interactive" indices, as follows: 
   start from a list of indices that consists of
   (1) the "noninteractive" indices in the initial useful indices
   (2) the "interactive" indices that occur in all_indices but not in the 
      initial useful indices
   (3) the "interactive" indices that occur in the initial indices
   and try to eliminate the indices in order. At each step, we check that all
   indices in the initial useful indices are uniquely determined. 
   *)

let filter_indices internal_info g t true_facts0 all_indices used_indices =
  reset [] internal_info g;
  (* Collect all facts that are known to be true *)
  let true_facts' = 
    try
      true_facts0 @ (Facts.get_facts_at t.t_facts)
    with Contradiction ->
      [Terms.make_false()]
  in
  (* Substitute fresh replication indices for find indices *)
  if (!Terms.current_bound_vars) != [] then
    Parsing_helper.internal_error "current_bound_vars should be cleaned up (simplify, filter_indices)";
  let map_find_indices = map_find_indices all_indices in
  let all_indices' = List.map (fun b ->
    try
      get_binder (List.assq b map_find_indices)
    with Not_found ->
      b) all_indices
  in
  let t' = Terms.subst3 map_find_indices t in
  let true_facts'' = List.map (Terms.subst3 map_find_indices) true_facts' in
  let used_indices' = List.map (fun t -> get_binder (Terms.subst3 map_find_indices t)) used_indices in
  (* Try to reduce the list of used indices. 
     Compute the initial list of indices to start with.
     - if all indices in used_indices_ref are "interactive",
       then we start from used_indices_ref
     - otherwise, we add "interactive" indices from all_indices;
       the goal is to try to remove "non-interactive" indices
       of used_indices_ref, perhaps at the cost of adding more
       "interactive" indices (because interactive indices are
       expected to be much smaller than non-interactive indices) *)
  let initial_indices =
    if not (List.exists is_noninteractive used_indices') then
      used_indices'
    else
      (List.filter is_noninteractive used_indices') @
      (List.filter (fun b -> not (is_noninteractive b || List.memq b used_indices')) all_indices') @
      (List.filter (fun b -> not (is_noninteractive b)) used_indices')
  in
  (* Try to remove useless indices using true_facts' *)
  let really_used_indices = filter_indices_coll true_facts'' used_indices' initial_indices in
  (* Add probability for eliminated collisions *)
  let proba = final_add_proba() in
  let internal_info' = Proba.final_internal_info() in
  if really_used_indices == initial_indices then
    (* I removed no index, I can just leave things as they were *)
    (used_indices, (t', true_facts'', all_indices', initial_indices, used_indices', used_indices'), [], internal_info)
  else
    (List.map (fun b -> 
      let rec find_in_map_indices = function
	  [] -> Terms.term_from_binder b
	| ((b',t')::l) ->
	    if get_binder t' == b then Terms.term_from_binder b' else find_in_map_indices l
      in
      find_in_map_indices map_find_indices) really_used_indices, 
     (t', true_facts'', all_indices', initial_indices, used_indices', really_used_indices), proba, internal_info')

(***** Test if two expressions can be evaluated with the same value of *****
       certain indices. 
       (useful for reducing the probabilities in the crypto transformation) 
       For use from cryptotransf.ml.
*)

(* TO DO Also exploit defined variables using CompatibleDefs2.check_compatible2_deflist *)

let rec find_same_type b = function
    [] -> raise Not_found 
  | b''::r ->
      if b''.btype == b.btype then
	(* relate b to b'' *)
	(b'', r)
      else
	let (bim, rest_r) = find_same_type b r in
	(bim, b''::rest_r)

let is_compatible_indices internal_info g 
    (t1, true_facts1, all_indices1, _, _, really_used_indices1) 
    (t2, true_facts2, all_indices2, _, _, really_used_indices2) =
  (*
  print_string "Simplify.is_compatible_indices ";
  Display.display_term [] t1;
  print_string " with ";
  Display.display_term [] t2;
  *)
  reset [] internal_info g;
  (* Substitute fresh replication indices for find indices *)
  if (!Terms.current_bound_vars) != [] then
    Parsing_helper.internal_error "current_bound_vars should be cleaned up (simplify, filter_indices)";
  List.iter (fun b -> 
    let b' = new_repl_index b in
    Terms.link b (TLink (Terms.term_from_binder b'))) all_indices1;
  let true_facts1' = List.map Terms.copy_term3 true_facts1 in
  let really_used_indices1' = ref (List.map (fun b -> match b.link with 
    NoLink -> b
  | TLink t -> get_binder t) really_used_indices1) in
  Terms.cleanup();
  List.iter (fun b -> 
    (* Find a relation between really_used_indices1 and really_used_indices2 that
       respect types. *)
    if List.memq b really_used_indices2 then
      try
	let (b', rest_really_used_indices1) = find_same_type b (!really_used_indices1') in
	really_used_indices1' := rest_really_used_indices1;
	Terms.link b (TLink (Terms.term_from_binder b'))
      with Not_found -> 
	let b' = new_repl_index b in
	Terms.link b (TLink (Terms.term_from_binder b'))
    else
      let b' = new_repl_index b in
      Terms.link b (TLink (Terms.term_from_binder b'))
	) all_indices2;
  let true_facts2' = List.map Terms.copy_term3 true_facts2 in
  Terms.cleanup();
  try
    ignore (Terms.auto_cleanup (fun () -> 
      Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) (true_facts1' @ true_facts2')));
    (* The terms t1 and t2 are compatible: they may occur for the same indices *)
    (* print_string " true\n";  *)
    (true, [], internal_info)
  with Contradiction ->
    (* The terms t1 and t2 are not compatible *)
    (* Add probability for eliminated collisions *)
    let proba = final_add_proba() in
    let internal_info' = Proba.final_internal_info() in
    (* print_string " false\n"; *)
    (false, proba, internal_info')


(* Test if two terms represent in fact calls to the same oracle
   (and so should be counted only once when computing probabilities) 
   For use from cryptotransf.ml.
*)

(*
TO DO I should use a form of antiunification: when t1 and t2
are not exactly equal, I can replace subterms at the same
occurrence of t1 and t2 with the same fresh variable.
When I see the same pair of subterms in the computation of
common facts, I reuse the same variable.
I must then check that the common facts imply that this variable has
a unique value for each value of the really_used_indices.

Remark: since the desired result of filter_indices is known,
I could be faster and avoid trying to remove indices in
really_used_indices.
*)

(* Oracle call t1 means: for all indices in t1 and true_facts1 such that true_facts1 holds, call t1.
   Oracle call t2 means: for all indices in t2 and true_facts2 such that true_facts2 holds, call t2.
There is a substitution sigma such that
 * t2 = sigma t1
 * There is a subset common_facts of true_facts1 suchthat
   true_facts2 contains at least sigma common_facts 
 * The same indices can be removed using common_facts as
   using true_facts1, so that the used indices at t1 with common_facts
   are still really_used_indices1.
Then we replace both calls with
  for all indices in t1 and common_facts such that common_facts holds, call t1
This is more general than t1 and t2 and yields the same cardinal as t1. *)

let match_oracle_call internal_info g
    (t1, true_facts1, all_indices1, initial_indices1, used_indices1, really_used_indices1) 
    (t2, true_facts2, all_indices2, initial_indices2, used_indices2, really_used_indices2) =
  (*
  print_string "Simplify.same_oracle_call ";
  Display.display_term [] t1;
  print_string " with ";
  Display.display_term [] t2;
    *)
  Terms.auto_cleanup(fun () ->
    if eq_terms3 t1 t2 then
      let common_facts = List.filter (fun f1 -> List.exists (fun f2 -> eq_terms3 f1 f2) true_facts2) true_facts1 in
      Terms.cleanup();
      reset [] internal_info g;
      (* Check that we can remove the same indices using common_facts as with all facts *)
      let really_used_indices1' = filter_indices_coll common_facts used_indices1 initial_indices1 in
      let r1 = Terms.equal_lists (==) really_used_indices1 really_used_indices1' in
      (* Add probability for eliminated collisions *)
      let proba = final_add_proba() in
      let internal_info' = Proba.final_internal_info() in

      if r1 then
	begin
	  (*
	  print_string "Simplify.same_oracle_call ";
	  Display.display_term [] t1;
	  print_string " with ";
	  Display.display_term [] t2;
	  print_string " succeeds\n";
	  print_string "Common facts:\n";
	  List.iter (fun t ->
	    Display.display_term [] t; print_newline()) common_facts;
	  *)
	  (Some (t1, common_facts, all_indices1, initial_indices1, used_indices1, really_used_indices1), proba, internal_info')
	end
      else
	begin
	  (*
	  print_string "Simplify.same_oracle_call ";
	  Display.display_term [] t1;
	  print_string " with ";
	  Display.display_term [] t2;
	  print_string " fails\n";
	  print_string "True facts 1:\n";
	  List.iter (fun t ->
	    Display.display_term [] t; print_newline()) true_facts1;
	  print_string "True facts 2:\n";
	  List.iter (fun t ->
	    Display.display_term [] t; print_newline()) true_facts2;
	  print_string "Common facts:\n";
	  List.iter (fun t ->
	    Display.display_term [] t; print_newline()) common_facts;
	  print_string "used_indices_map1\n";
	  Display.display_list (fun (t,t') ->
	    print_string "("; Display.display_term [] t; print_string ", "; Display.display_term [] t'; print_string ")") used_indices_map1;
	  print_newline();
	  print_string "used_indices_map1'\n";
	  Display.display_list (fun (t,t') ->
	    print_string "("; Display.display_term [] t; print_string ", "; Display.display_term [] t'; print_string ")") used_indices_map1';
	  print_newline();
	  print_string "used_indices1\n";
	  Display.display_list (Display.display_term []) used_indices1;
	  print_newline();*)
	  (None, [], internal_info)
	end
    else
      begin
	(*
	  print_string "Simplify.same_oracle_call ";
	  Display.display_term [] t1;
	  print_string " with ";
	  Display.display_term [] t2;
	  print_string " fails\n";*)
	(None, [], internal_info)
      end
    )

let same_oracle_call internal_info g call1 call2 =
  let (r, _, _) as res = match_oracle_call internal_info g call1 call2 in
  if r == None then
    match_oracle_call internal_info g call2 call1
  else
    res
