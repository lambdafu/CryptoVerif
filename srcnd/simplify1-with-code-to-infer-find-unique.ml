open Types

(* Create fresh replication indices *)

let repl_index_counter = ref 0
(* mapping from terms to fresh repl indexes *)
let repl_index_list = ref []

let new_repl_index_term t =
  let rec find_repl_index = function
      [] ->
	incr repl_index_counter;
	let b' = Terms.create_repl_index "!2" (!repl_index_counter) t.t_type in
	repl_index_list := (t,b') :: (!repl_index_list);
	b'
    | ((a,b')::l) ->
	if Terms.equal_terms a t then b' else
	find_repl_index l
  in
  find_repl_index (!repl_index_list)

let new_repl_index b = new_repl_index_term (Terms.term_from_replindex b)

(* TO DO I am trying to remove these functions
let rec map_find_indices = function
    [] -> []
  | (b::l) ->
      let l' = map_find_indices l in
      if Terms.is_repl b then 
	l' 
      else
	(b, Terms.term_from_binder (new_repl_index b)) :: l'
*)

(* An element (t1, t2, b, lopt, T) in term_collisions means that
the equality t1 = t2 was considered impossible; it has
negligible probability because t1 depends on b[lopt] by decompos followed
by compos functions, the types T are the types obtained after applying
the decompos functions (they are large types), and t2 does not depend 
on b *)

let term_collisions = ref []

let reset coll_elim g =
  Proba.reset coll_elim g;
  term_collisions := [];
  repl_index_list := []


let any_term_name = "?"
let any_term_binder t = 
  let b' = Terms.create_binder any_term_name 0 t [] in
  let rec node = { above_node = node;
		   binders = [b'];
		   true_facts_at_def = [];
		   def_vars_at_def = [];
		   elsefind_facts_at_def = [];
		   future_binders = []; future_true_facts = [];
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
  | ReplIndex (v), _ -> 
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

let matches_pair_with_order_ass order_assumptions t1 t2 order_assumptions' t1' t2' =
  try
    if (order_assumptions != []) && (order_assumptions' == []) then
      false 
    else
      begin
	Terms.auto_cleanup (fun () ->
	  match_term3 (fun () -> match_term3 (fun () -> 
	    let order_assumptions_instance = List.map (fun (br1,br2) ->
	      (Terms.copy_term3 (Terms.term_from_binderref br1),
	       Terms.copy_term3 (Terms.term_from_binderref br2))) order_assumptions
	    in
	    let order_assumptions' = List.map (fun (br1, br2) ->
	      (Terms.term_from_binderref br1,
	       Terms.term_from_binderref br2)) order_assumptions'
	    in
	    if not 
		(List.for_all (fun (br1,br2) ->
		  List.exists (fun (br1',br2') ->
		    (Terms.equal_terms br1 br1') && (Terms.equal_terms br2 br2')) order_assumptions') order_assumptions_instance)
	    then raise NoMatch
		) t2 t2') t1 t1');
	true
      end
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

let get_index_size b =
  match b.btype.tcat with
    Interv p -> p.psize
  | BitString -> Parsing_helper.internal_error "I would expect indices to have interval type in get_index_size"

let greater_size b1 b2 = compare (get_index_size b2) (get_index_size b1)

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
  (*print_string "Filter_indices_coll\nKnowing\n";
  List.iter (fun f -> Display.display_term f; print_newline()) true_facts;
  print_string "used_indices: ";
  Display.display_list Display.display_binder used_indices;
  print_string "\ninitial_indices: ";
  Display.display_list Display.display_binder initial_indices;
  print_string "\n";*)
  let useful_indices = ref [] in
  let useless_indices = ref [] in
  (* Remove all indices that are before the first used index.
     Indeed, if we remove those, all used indices are still present,
     so that's clearly sufficient. *)
  let rec remove_first_indices = function
      [] -> []
    | (b::l) -> 
	if not (List.memq b used_indices) then 
	  begin
	    useless_indices := b :: (!useless_indices);
	    remove_first_indices l
	  end
	else
	  b::l
  in
  let initial_indices' = remove_first_indices initial_indices in
  let used_indices_term = List.map Terms.term_from_replindex used_indices in
  let rec filter_indices_rec = function
      [] -> ()
    | first_index::rest_indices ->
	List.iter (fun b -> 
	  let b' = new_repl_index b in
	  Terms.link b (TLink (Terms.term_from_replindex b')))
	  (first_index::(!useless_indices));
	let true_facts' = List.map Terms.copy_term3 true_facts in
	let used_indices_term' = List.map Terms.copy_term3 used_indices_term in 
	Terms.cleanup();
	let diff_fact = Terms.make_or_list (List.map2 Terms.make_diff used_indices_term used_indices_term') in
	let facts = diff_fact :: (true_facts' @ true_facts) in
	try
	  (*print_string "index: "; Display.display_binder first_index; *)
	  ignore (Terms.auto_cleanup (fun () -> Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) facts));
	  (* The index cannot be removed *)
	  (*print_string " kept\n";*)
	  useful_indices := (!useful_indices) @ [first_index];
	  filter_indices_rec rest_indices
	with Contradiction ->
	  (* The index can be removed *)
	  (*print_string " removed\n";*)
	  useless_indices := first_index :: (!useless_indices);
	  filter_indices_rec rest_indices
  in
  filter_indices_rec initial_indices';
  (*print_string "Result: "; Display.display_list Display.display_binder (!useful_indices); print_newline();*)
  if (!useless_indices) == [] then
    (* Removed no index, return the initial list physically, to facilitate
       testing that the list of indices was unchanged *)
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
    (order_assumptions, true_facts, used_indices, initial_indices, really_used_indices, t1, t2, b, lopt, tl)
    (order_assumptions', true_facts', used_indices', initial_indices', really_used_indices', t1', t2', b', lopt', tl') =
  Terms.auto_cleanup(fun () ->
    if matches_pair_with_order_ass order_assumptions t1 t2 order_assumptions' t1' t2' then
      let common_facts = List.filter (fun f -> List.exists (fun f' -> eq_terms3 f f') true_facts') true_facts in
      Terms.cleanup();
      (* Check that we can remove the same indices using common_facts as with all facts *)
      if initial_indices == really_used_indices then
	(* If we removed no index, this is certainly true *)
	Some(order_assumptions, common_facts, used_indices, initial_indices, really_used_indices, t1, t2, b, lopt, tl)
      else
      let really_used_indices'' = filter_indices_coll common_facts used_indices initial_indices in
      if Terms.equal_lists (==) really_used_indices really_used_indices'' then
	begin
	  (*
	  print_string "Simplify.matches ";
	  Display.display_term t1;
	  print_string " with ";
	  Display.display_term t2;
	  print_string " succeeds\n";
	  print_string "Common facts:\n";
	  List.iter (fun t ->
	    Display.display_term t; print_newline()) common_facts; *)
	  Some(order_assumptions, common_facts, used_indices, initial_indices, really_used_indices, t1, t2, b, lopt, tl)
	end
      else
	begin
	  (*
	  print_string "Simplify.matches ";
	  Display.display_term t1;
	  print_string " with ";
	  Display.display_term t2;
	  print_string " fails\n";
	  print_string "True facts:\n";
	  List.iter (fun t ->
	    Display.display_term t; print_newline()) true_facts;
	  print_string "True facts':\n";
	  List.iter (fun t ->
	    Display.display_term t; print_newline()) true_facts';
	  print_string "Common facts:\n";
	  List.iter (fun t ->
	    Display.display_term t; print_newline()) common_facts;
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

let add_term_collisions (all_indices, map_find_indices, true_facts, order_assumptions) t1 t2 b lopt tl =
  (* Map everything with map_find_indices, to replace indices of find with fresh
     replication indices.
     For some calls, some parts have already been mapped by map_find_indices,
     but not all (in particular the true_facts) *)
  let t1 = Terms.subst3 map_find_indices t1 in
  let t2 = Terms.subst3 map_find_indices t2 in
  let lopt = match lopt with
    None -> None
  | Some l -> Some (List.map (Terms.subst3 map_find_indices) l) 
  in
  let all_indices_ref = ref (List.map (fun b ->
    try
      Terms.binder_from_term (List.assq b map_find_indices)
    with Not_found ->
      b) all_indices)
  in
  let order_assumptions = List.map (fun (br1,br2) ->
    (Terms.binderref_from_term (Terms.subst3 map_find_indices (Terms.term_from_binderref br1)), 
     Terms.binderref_from_term (Terms.subst3 map_find_indices (Terms.term_from_binderref br2)))
    ) order_assumptions
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
  try
  let collision_info = 
    (* If the probability used_indices/t for t in tl is small enough to eliminate collisions, return that probability.
       Otherwise, try to optimize to reduce the factor used_indices *)
    if List.for_all (fun t -> 
      Proba.is_small_enough_coll_elim (List.map (fun array_idx -> Proba.card array_idx.btype) used_indices, Proba.card t)
	) tl then 
      (order_assumptions, [], used_indices, used_indices, used_indices, t1, t2, b, lopt, tl)
    else
      let true_facts = List.map (Terms.subst3 map_find_indices) true_facts in
      (* Try to reduce the list of used indices. 
	 The initial list of indices is a reordering of the list of all indices.
	 We start with the larger indices (to eliminate them first) and among
	 the indices of the same size, with those that are not in used_indices
	 (also to eliminate them first).
	 The goal is to try to remove large indices
	 of used_indices, perhaps at the cost of adding more
         smaller indices of all_indices. *)
      let initial_indices =
	  (* Sort used_indices and all_indices in decreasing size *)
	  let used_indices_sort = List.sort greater_size used_indices in
	  let all_indices_sort = List.sort greater_size all_indices in
	  (* Remove elements of all_indices that are in used_indices *)
	  let all_indices_sort_minus_used_indices = List.filter (fun b -> not (List.memq b used_indices_sort)) all_indices_sort in
	  (* Build a list by merging indices from all_indices and used_indices.
	     When indices are of the same size, we put elements of all_indices first,
	     so that they will be eliminated, except if they are now necessary
	     because they replace some larger index eliminated before. *)
	  List.merge greater_size all_indices_sort_minus_used_indices used_indices_sort 
      in
      let really_used_indices = filter_indices_coll true_facts used_indices initial_indices in
      (* OLD: I can forget the facts without losing precision when I removed no index
	 (initial_indices == really_used_indices);
	 Now, if I removed no index, the probability will be too large to eliminate collisions. *)
      if List.for_all (fun t -> 
	Proba.is_small_enough_coll_elim (List.map (fun array_idx -> Proba.card array_idx.btype) really_used_indices, Proba.card t)
	  ) tl then 
	(order_assumptions, true_facts, used_indices, initial_indices, really_used_indices, t1, t2, b, lopt, tl) 
      else
	(* Raises NoMatch when the probability is too large to be accepted *)
	raise NoMatch
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
  begin
    try
      term_collisions := find_more_general_coll (!term_collisions)
    with Not_found ->
      let new_coll = ref collision_info in
      let term_collisions' = List.filter (fun collision_info' -> 
	match matches (!new_coll) collision_info' with
	  None -> true
	| Some collision_info'' -> new_coll := collision_info''; false) (!term_collisions)
      in
      term_collisions := (!new_coll) :: term_collisions'
  end;
  true
  with NoMatch -> 
    false

let proba_for_term_collision (order_assumptions, _, _, _, really_used_indices, t1, t2, b, lopt, tl) =
  print_string "Eliminated collisions between ";
  Display.display_term t1;
  print_string " and ";
  Display.display_term t2;
  print_string " Probability: ";  
  let nindex = Polynom.p_prod (List.map (fun array_idx -> Proba.card array_idx.btype) really_used_indices) in
  let p = 
    match tl with
      [t] -> Div(nindex, Proba.card t)
    | _ -> Polynom.p_sum (List.map (fun t -> Div(nindex, Proba.card t)) tl)
  in
  Display.display_proba 0 p;
  print_newline();
  print_string "(";
  if order_assumptions != [] then
    begin
      print_string "assuming ";
      Display.display_list (fun ((b1, l1), (b2, l2)) ->
	Display.display_var b2 l2;
	print_string " is defined before ";
	Display.display_var b1 l1
	  ) order_assumptions;
      print_string ", ";
    end;
  Display.display_term t1;
  print_string " characterizes a part of ";
  begin
  match lopt with
    None ->   Display.display_binder b; print_string "[...]"
  | Some l -> Display.display_var b l 
  end;
  print_string " of type(s) ";
  Display.display_list (fun t -> print_string t.tname) tl;
  print_string ";\n ";
  Display.display_term t2;
  print_string " does not depend on ";
  begin
  match lopt with
    None ->   Display.display_binder b; print_string "[...]"
  | Some l -> Display.display_var b l 
  end;
  print_string ")\n";
  p
  

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
	 variable x[...].
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
  | ReplIndex(b') -> false
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
      | ReplIndex(b) -> t.t_desc
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
		Terms.term_from_replindex (new_repl_index_term t')) l)
	  else
	    raise Not_found
      | _ -> Parsing_helper.internal_error "If/let/find/new unexpected in is_indep")

let rec remove_dep_array_index ((b0, (dep,nodep)) as bdepinfo) t =
  Terms.build_term2 t 
     (match t.t_desc with
	FunApp(f,l) -> FunApp(f, List.map (remove_dep_array_index bdepinfo) l)
      | ReplIndex(b) -> t.t_desc
      |	Var(b,l) ->
	  if (List.exists (Terms.equal_terms t) nodep) then
	    t.t_desc 
	  else 
	    Var(b, List.map (fun t' -> 
	      if depends bdepinfo t' then
		Terms.term_from_replindex (new_repl_index_term t')
	      else
		t') l)
      | _ -> Parsing_helper.internal_error "If/let/find/new unexpected in remove_dep_array_index")

let rec remove_array_index t =
  Terms.build_term2 t 
     (match t.t_desc with
	FunApp(f,l) -> FunApp(f, List.map remove_array_index l)
      | ReplIndex(b) -> t.t_desc
      |	Var(b,l) ->
	  Var(b, List.map (fun t' ->
	    match t'.t_desc with
	      ReplIndex(b') -> t'
	    | _ -> Terms.term_from_replindex (new_repl_index_term t')
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
        ReplIndex(b) -> ReplIndex(b)
      | Var(b,l) -> Var(
	  (try List.assq b (!assql) with Not_found ->
            (* Do not rename variables that do not depend on the
	       variable argument of find_compos *)
	    if (Terms.is_restr b) ||
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
  if (!Settings.debug_simplif_add_facts) then
    begin
      print_string "find_compos:t=";
      Display.display_term t;
      print_newline ()
    end;

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
      if (!Settings.debug_simplif_add_facts) then
        begin
          print_string "_->b'=";
          Display.display_binder b';
          print_string ", t'=";
          Display.display_term t';
          print_string ", depinfo=";
          print_newline ()
        end;

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
    Display.display_term (Terms.make_not t');
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
         Display.display_term t1';
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

let filter_elsefind f (subst, facts, elsefind) =
  (subst, facts, List.filter f elsefind)

let convert_elsefind dep_info def_vars ((subst, facts, elsefind) as simp_facts) =
  let simp_facts_ref = ref simp_facts in
  List.iter (fun (bl, def_list, t1) ->
    always_true_def_list_t dep_info bl simp_facts_ref t1 def_vars def_list
      ) elsefind;
  !simp_facts_ref


let true_facts_from_simp_facts (facts, subst, else_find) =
  subst @ facts

let rec try_no_var_rec simp_facts t =
  let t' = Facts.try_no_var simp_facts t in(* Risk of non-termination? *)
  match t'.t_desc with
    FunApp(f,l) -> 
      Terms.build_term2 t' (FunApp(f, List.map (try_no_var_rec simp_facts) l))
  | _ -> t'


(* Reasoning that depends on assumptions on the order of definition
   of variables. *)

(* [is_in_bl bl t] returns true when the term [t] is equal to some
   variable in the list [bl] *)

let is_in_bl bl t =
  match t.t_desc with
    Var(b,l) ->
      (List.memq b bl) && (List.for_all2 Terms.equal_terms b.args_at_creation l)
  | _ -> false

(* Dependency analysis that takes into account assumption on the
   definition order

   dep_info = (array ref defined later; list of array ref defined before)
 *)

let rec remove_dep_array_index all_indices ((b0, (dep,nodep)) as bdepinfo) t =
  Terms.build_term2 t 
     (match t.t_desc with
	FunApp(f,l) -> FunApp(f, List.map (remove_dep_array_index all_indices bdepinfo) l)
      | Var(b,l) ->
	  if (is_in_bl all_indices t) || (List.exists (Terms.equal_terms t) nodep) then
	    t.t_desc 
	  else 
	    Var(b, List.map (fun t' -> 
	      if is_in_bl all_indices t' then
		t'
	      else if FindCompos.depends bdepinfo t' then
		Terms.term_from_replindex (new_repl_index_term t')
	      else
		t') l)
      | _ -> Parsing_helper.internal_error "If/let/find/new unexpected in remove_dep_array_index")

let rec dependency_collision_rec2bis all_indices map_find_indices true_facts order_assumptions (((b_after, l_after), defl_before) as dep_info) t1 t2 t =
  match t.t_desc with
    Var(b,l) when (Terms.is_restr b) && (b == b_after) && (List.for_all2 Terms.equal_terms l l_after) && (Proba.is_large_term t) ->
      begin
        let t = Terms.subst3 map_find_indices t in
        let t1 = Terms.subst3 map_find_indices t1 in
        let t2 = Terms.subst3 map_find_indices t2 in
        let defl_before = List.map (Terms.subst3 map_find_indices) defl_before in
          if (!Settings.debug_elsefind_facts) then
            begin
              print_string "t t1 t2="; 
	      Display.display_term t;print_string ", "; 
	      Display.display_term t1;print_string ", ";
	      Display.display_term t2;
            end;
          

        let t' = FindCompos.remove_dep_array_index (*all_indices*) (b,(None, defl_before)) t in
        let l_after' = 
	  match t'.t_desc with
	    Var (_,l_after') -> l_after'
	  | _ -> Parsing_helper.internal_error "t' must be a variable in dependency_collision_rec2bis"
	in
          if (!Settings.debug_elsefind_facts) then
            begin
              Display.display_term t;print_string " is restriction.";
	      print_newline ();
            end;
	let t1' = FindCompos.remove_dep_array_index (*all_indices*) (b,(None, defl_before)) t1 in
          if (!Settings.debug_elsefind_facts) then
            begin
              print_string "remove_dep_array_index t1=";
	      Display.display_term t1';print_newline ()
            end;
	let check (b, (st, _)) l =
          if (!Settings.debug_elsefind_facts) then
            begin
              print_string "check: b="; Display.display_binder b; 
	      print_string ", l=";Display.display_list Display.display_term l;
	      print_string ", l_after'=";Display.display_list Display.display_term l_after';
	      print_newline ()
            end;
	  if List.for_all2 Terms.equal_terms l l_after' then
	    Some (st, FindCompos.CharacType b.btype)
	  else
	    None
	in
	match FindCompos.find_compos check (None, defl_before) (b,(FindCompos.Decompos, b.btype)) t1' with
	  Some(_, FindCompos.CharacType charac_type, t1'') -> 
	    begin
	    try 
              if (!Settings.debug_elsefind_facts) then
                begin
                  print_string "FindCompos ok";print_newline ()
                end;
	      let t2' = FindCompos.is_indep (b, (None, defl_before)) t2 in
	      (* add probability, if small enough. returns true if proba small enough, false otherwise *)
	      add_term_collisions (all_indices, map_find_indices, true_facts, order_assumptions) t1'' t2' b (Some l_after') [charac_type]
	    with Not_found -> false
	    end
	| Some _ -> Parsing_helper.internal_error "CharacTypeOfVar should not be used in DepAnal2"
	| None -> false
      end 
  | FunApp(f,l) ->
      List.exists (dependency_collision_rec2bis all_indices map_find_indices true_facts order_assumptions dep_info t1 t2) l
  | _ -> false

let dependency_collision_order_hyp all_indices order_assumptions dep_info simp_facts t1 t2 = 
  let t1' = try_no_var_rec simp_facts t1 in
  let t2' = try_no_var_rec simp_facts t2 in
    if (!Settings.debug_elsefind_facts) then
      begin
        print_string "simplified t1,t2=";
        Display.display_term t1'; print_string ", ";
        Display.display_term t2'; print_newline ();
      end;
  let map_find_indices = map_find_indices all_indices in
  let true_facts = true_facts_from_simp_facts simp_facts in
  (dependency_collision_rec2bis all_indices map_find_indices true_facts order_assumptions dep_info t1' t2' t1') ||
  (dependency_collision_rec2bis all_indices map_find_indices true_facts order_assumptions dep_info t2' t1' t2')


(* Dependency analysis taking into account the order of definition of the variables. Here dep_info is a list of array ref defined after and a list of array ref defined before *)

let dependency_collision_order_hyp' all_indices order_assumptions (defl_after, defl_before) simp_facts t1 t2 =
  if (!Settings.debug_elsefind_facts) then
    begin
      print_string "dependency_collision_order_hyp': ";
      Display.display_term t1; print_string ", ";
      Display.display_term t2; print_newline ();
    end;
  let b = List.exists (fun def_after -> dependency_collision_order_hyp all_indices order_assumptions (def_after, defl_before) simp_facts t1 t2) defl_after in
    if (!Settings.debug_elsefind_facts) then
      begin
        print_string (if b then "Result: true" else "Result: false");
	print_newline ()
      end;
    b

(* [above_input_node n] returns the first node corresponding to
   an input above [n]. *)

let rec above_input_node n =
  if n.above_node == n then
    Parsing_helper.internal_error "reached beginning of program without seeing an input";
  match n.definition with
    DInputProcess _ -> n
  | _ -> above_input_node n.above_node
    
(* COMMENTED OUT

(* Prove unicity of find branches. 
   This code applies both to find and findE because it just deals with 
   the find conditions *)

(* [same_input_node br defl] returns true when [br] is defined in the
same input...output block as variables in [defl]. When [defl] contains
several elements, they are already supposed to be defined in the same
input...output block, so that we need only compare with the
first element of [defl]. *) 

let same_input_node (b,_) defl =
  let (b',_) = List.hd defl in
  match b.def with
    n::r -> 
      let input_node = above_input_node n in
      (List.for_all (fun n' -> input_node == above_input_node n') r) &&
      (List.for_all (fun n' -> input_node == above_input_node n') b'.def)
  | _ -> false

(* analyzed contains a list of pairs (list of indices used, list of
   variable references in defined condition that use those indices and
   are in the same input...output block).
   This input...output block is chosen to be as late as possible. *)

let rec add_in_analyzed ((b,l) as br) = function
    [] -> [(List.map Terms.binder_from_term l, [br])]
  | (bl, defl)::rest ->
      let l' = List.map Terms.binder_from_term l in
      if List.exists (fun b' -> List.memq b' bl) l' then
	let lenl' = List.length l' in
	let lenbl = List.length bl in
	if lenl' > lenbl then 
	  (l',[br])::rest
	else if lenl' < lenbl then
	  (bl, defl)::rest
	else (* lenl' == lenbl *) 
	  if (List.for_all2 (==) l' bl) && (same_input_node br defl) then
	    (* Most frequent case *)
	    (bl, br::defl)::rest
	  else if List.for_all (fun (b',_) ->
	    List.for_all (fun n -> List.exists (fun n' -> Facts.is_reachable n' n) b'.def) b.def) defl then
	    (* b defined after b', b is better *)
	    (l', [br])::rest
	  else
	    (bl, defl)::rest
      else
	(bl, defl)::(add_in_analyzed br rest)

let rec analyze_def_br analyzed bl ((b,l) as br) =
  if List.for_all (is_in_bl bl) l then
    analyzed := add_in_analyzed br (!analyzed)
  else
    List.iter (analyze_def_term analyzed bl) l

and analyze_def_term analyzed bl t =
  match t.t_desc with
    Var(b,l) -> analyze_def_br analyzed bl (b,l)
  | FunApp(f,l) -> List.iter (analyze_def_term analyzed bl) l
  | _ -> Parsing_helper.internal_error "If/Let/Find/Res/Event not allowed in def list"

(* Rename an elsefind fact according to renaming subst *)

let rec rename_term_except bl subst t =
  match t.t_desc with
    Var(b,l) -> 
      let (b',l') = rename_br_except bl subst (b,l) in
      Terms.build_term2 t (Var(b',l'))
  | FunApp(f,l) ->
       Terms.build_term2 t (FunApp(f, List.map (rename_term_except bl subst) l))
  | _ -> Parsing_helper.internal_error "If/Let/Find/Res/Event not allowed in elsefind facts"

and rename_br_except bl subst (b,l) =
  if List.for_all2 Terms.equal_terms b.args_at_creation l then
    if List.memq b bl  then
      (b,l)
    else
      try
	let b' = Terms.binder_from_term (List.assq b subst) in
	(b', b'.args_at_creation)
      with Not_found ->
	(b, List.map (rename_term_except bl subst) l)
  else
    (b, List.map (rename_term_except bl subst) l)

let rename_elsefind subst (bl, def_list, t) =
  (bl, List.map (rename_br_except bl subst) def_list, 
   rename_term_except bl subst t)

(* branch_unique proves that the given branch can succeed only for one 
   choice of indices in bl 
cur_array = all indices above the current find (replication indices, and 
  find indices if the current find occurs in a find condition)
the_facts = p.p_facts for processes, t.t_facts for terms
true_facts0 = the facts that are true at the find.
*)

let branch_unique cur_array the_facts true_facts0 (bl, def_list, t, _) =
  let bl1 = List.map Terms.new_binder bl in
  let bl2 = List.map Terms.new_binder bl in
  let subst1 = List.map2 (fun b b' -> (b, Terms.term_from_binder b')) bl bl1 in
  let subst2 = List.map2 (fun b b' -> (b, Terms.term_from_binder b')) bl bl2 in
  let def_list1 = Terms.subst_def_list3 subst1 def_list in
  let t1 = Terms.subst3 subst1 t in
  let def_list2 = Terms.subst_def_list3 subst2 def_list in
  let t2 = Terms.subst3 subst2 t in
  try
    let this_branch_node = Facts.get_node_for_find_branch the_facts bl in 
    let facts_def_list1 = Facts.facts_from_defined this_branch_node bl1 def_list1 in
    let true_facts1 = Facts.simplif_add_list Facts.no_dependency_anal true_facts0 facts_def_list1 in
    let true_facts2 = Facts.simplif_add_find_cond Facts.no_dependency_anal true_facts1 t1 in
    let facts_def_list2 = Facts.facts_from_defined this_branch_node bl2 def_list2 in
    let true_facts3 = Facts.simplif_add_list Facts.no_dependency_anal true_facts2 facts_def_list2 in
    let true_facts4 = Facts.simplif_add_find_cond Facts.no_dependency_anal true_facts3 t2 in
    let diff_fact = Terms.make_or_list (List.map2 (fun (_,b1) (_,b2) -> Terms.make_diff b1 b2) subst1 subst2) in
    let true_facts5 = Facts.simplif_add Facts.no_dependency_anal true_facts4 diff_fact in

    let analyzed = ref [] in
    List.iter (analyze_def_br analyzed bl) def_list;
    (* Check that all elements of bl are in some sub-bl list of analyzed.
       Otherwise, we cannot apply the case distinction. *)
    (List.for_all (fun b -> List.exists (fun (sub_bl,_) -> List.memq b sub_bl) (!analyzed)) bl) &&
    ((* Since all elements of bl are in some sub_bl list, and bl1 <> bl2,
	there exists some sub_bl list such that sub_bl1 <> sub_bl2 *)
    List.for_all (fun (sub_bl, defl) ->
      if !Settings.debug_find_unique then
	begin
	  print_string "Discriminating variables: "; Display.display_list (fun (bx,_) -> Display.display_binder bx) defl; print_newline()
	end;
      try
	let diff_fact2 = Terms.make_or_list 
	    (List.map (fun b -> Terms.make_diff (List.assq b subst1) (List.assq b subst2)) sub_bl) 
	in
	let true_facts6 = Facts.simplif_add Facts.no_dependency_anal true_facts5 diff_fact2 in
	(* Distinguish cases depending on whether the variable bx has 
	   been defined first with indices sub_bl1 or sub_bl2.
	   Suppose sub_bl1 comes first. (The other case is symmetric.)
	   Then bx[sub_bl2] defined afterwards, and we can exploit some
	   "elsefind" facts at definition of bx[sub_bl2]

	   When bx[sub_bl2] is defined, I know that bx[sub_bl1] is defined.
	   Infer other defined variables by Facts.def_vars_from_defined
	   *)
	let sub_bl1 = List.map (fun b -> List.assq b subst1) sub_bl in
	let def_vars = Facts.def_vars_from_defined None bl (List.map (fun (bx, _) -> (bx, sub_bl1)) defl) in
	let (subst6, facts6, _) = true_facts6 in 
	(* TO DO Would it be better to collect elsefind_facts for each
	   node n, take the intersection, then take the union on all
	   variables bx, and look for a contradiction from the
	   obtained facts? *) 
	List.exists (fun (bx, _) -> List.for_all
	   (fun n -> try
	    (* convert indices of bx to sub_bl2 *)
	      let renaming = List.map2 (fun t b -> (Terms.binder_from_term t, List.assq b subst2)) bx.args_at_creation sub_bl in
	      let elsefind_facts = List.map (rename_elsefind renaming) n.elsefind_facts_at_def in
	      if !Settings.debug_find_unique then Facts.display_facts (subst6,facts6, elsefind_facts);
	      let _ = convert_elsefind Facts.no_dependency_anal def_vars (subst6,facts6, elsefind_facts) in
	      if !Settings.debug_find_unique then print_string "Could not get a contradiction\n";
	      false
	    with Contradiction ->
	      true) bx.def
	    ) defl
      with Contradiction ->
	true
	  ) (!analyzed)
      )
  with Contradiction -> 
    true

(* incompatible branches proves that the two branches cannot 
   simultaneously succeed *)

let incompatible_branches cur_array the_facts true_facts0 (bl1, def_list1, t1, _) (bl2, def_list2, t2, _) =
  let bl1' = List.map Terms.new_binder bl1 in
  let bl2' = List.map Terms.new_binder bl2 in
  let all_indices = bl1' @ bl2' @ cur_array in
  let subst1 = List.map2 (fun b b' -> (b, Terms.term_from_binder b')) bl1 bl1' in
  let subst2 = List.map2 (fun b b' -> (b, Terms.term_from_binder b')) bl2 bl2' in
  let def_list1' = Terms.subst_def_list3 subst1 def_list1 in
  let t1' = Terms.subst3 subst1 t1 in
  let def_list2' = Terms.subst_def_list3 subst2 def_list2 in
  let t2' = Terms.subst3 subst2 t2 in
  try
    let this_branch_node1 = Facts.get_node_for_find_branch the_facts bl1 in 
    let facts_def_list1 = Facts.facts_from_defined this_branch_node1 bl1' def_list1' in
    let true_facts1 = Facts.simplif_add_list Facts.no_dependency_anal true_facts0 facts_def_list1 in
    let true_facts2 = Facts.simplif_add_find_cond Facts.no_dependency_anal true_facts1 t1' in
    let this_branch_node2 = Facts.get_node_for_find_branch the_facts bl2 in 
    let facts_def_list2 = Facts.facts_from_defined this_branch_node2 bl2' def_list2' in
    let true_facts3 = Facts.simplif_add_list Facts.no_dependency_anal true_facts2 facts_def_list2 in
    let true_facts4 = Facts.simplif_add_find_cond Facts.no_dependency_anal true_facts3 t2' in
    let (subst4, facts4, _) = true_facts4 in 

    let analyzed1 = ref [] in
    List.iter (analyze_def_br analyzed1 bl1) def_list1;
    let analyzed2 = ref [] in
    List.iter (analyze_def_br analyzed2 bl2) def_list2;

    (* TO DO When the variables in defl1 are defined in a different
       input...output block than the variables of defl2, I could make the
       stronger assumption that either all variables of defl1 are defined
       before all variables of defl2, or all variables of defl2 are
       defined before all variables of defl1 *)

    List.exists (fun (sub_bl1, defl1) ->
      List.exists (fun (bx1, _) ->
	List.exists (fun (sub_bl2, defl2) ->
	  List.exists (fun (bx2, _) ->
	(List.for_all (fun n -> not (List.memq n bx2.def)) bx1.def) &&
	(* bx1 and bx2 are defined in different nodes (checked on the above line), so 
	   bx1[sub_bl1'] and bx2[sub_bl2'] are not defined simultaneously, 
	   one is defined before the other.
	   First case: bx1[sub_bl1'] is defined before bx2[sub_bl2']  *)
	(
	if !Settings.debug_find_unique then 
	  begin
	    print_string "Discriminating variables: "; Display.display_binder bx1; print_string " before "; Display.display_binder bx2; print_newline()
	  end;
	try
	  let def_before = (bx1, List.map (fun b -> List.assq b subst1) sub_bl1) in
	  let def_after = (bx2, List.map (fun b -> List.assq b subst2) sub_bl2) in
	  let order_assumptions = [def_after, def_before] in
	  let def_vars = Facts.def_vars_from_defined None bl1 [def_before] in
	  if !Settings.debug_find_unique then
	    begin
	      print_string "Def vars = "; Display.display_list (fun (b,l) -> Display.display_var b l) def_vars; print_newline()
	    end;
	  let dep_info =
	    (def_after,
	     List.map Terms.term_from_binderref def_vars)
	  in
	  List.for_all (fun n ->   
	    try
	    (* convert indices of bx2 to sub_bl2' *)
	      let renaming = List.map2 (fun t b -> (Terms.binder_from_term t, List.assq b subst2)) bx2.args_at_creation sub_bl2 in
	      let elsefind_facts = List.map (rename_elsefind renaming) n.elsefind_facts_at_def in
	      if !Settings.debug_find_unique then Facts.display_facts (subst4,facts4, elsefind_facts);
	      let (subst4, facts4, _) = Facts.simplif_add_list (dependency_collision_order_hyp all_indices order_assumptions dep_info) ([],[],[]) (subst4 @ facts4) in
	      let _ = convert_elsefind (dependency_collision_order_hyp all_indices order_assumptions dep_info) def_vars (subst4,facts4, elsefind_facts) in
	      if !Settings.debug_find_unique then print_string "Could not get a contradiction\n";
	      false
	    with Contradiction ->
	      true) bx2.def
	with Contradiction ->
	  true
	) && 
	(* Second case:  bx2[sub_bl2'] is defined before bx1[sub_bl1'] *)
	(
	if !Settings.debug_find_unique then
	  begin
	    print_string "Discriminating variables: "; Display.display_binder bx1; print_string " after "; Display.display_binder bx2; print_newline()
	  end;
	try
	  let def_before = (bx2, List.map (fun b -> List.assq b subst2) sub_bl2) in
	  let def_after = (bx1, List.map (fun b -> List.assq b subst1) sub_bl1) in
	  let order_assumptions = [def_after, def_before] in
	  let def_vars = Facts.def_vars_from_defined None bl2 [def_before] in
	  if !Settings.debug_find_unique then 
	    begin
	      print_string "Def vars = "; Display.display_list (fun (b,l) -> Display.display_var b l) def_vars; print_newline()
	    end;
	  let dep_info =
	    (def_after,
	     List.map Terms.term_from_binderref def_vars)
	  in
	  List.for_all (fun n ->   
	    try
	    (* convert indices of bx2 to sub_bl2' *)
	      let renaming = List.map2 (fun t b -> (Terms.binder_from_term t, List.assq b subst1)) bx1.args_at_creation sub_bl1 in
	      let elsefind_facts = List.map (rename_elsefind renaming) n.elsefind_facts_at_def in
	      if !Settings.debug_find_unique then Facts.display_facts (subst4,facts4, elsefind_facts);
	      let (subst4, facts4, _) = Facts.simplif_add_list (dependency_collision_order_hyp all_indices order_assumptions dep_info) ([],[],[]) (subst4 @ facts4) in
	      let _ = convert_elsefind (dependency_collision_order_hyp all_indices order_assumptions dep_info) def_vars (subst4,facts4, elsefind_facts) in
	      if !Settings.debug_find_unique then print_string "Could not get a contradiction\n";
	      false
	    with Contradiction ->
	      true) bx1.def
	with Contradiction -> 
	  true
	)
	      ) defl2
	    ) (!analyzed2)
	  ) defl1
	) (!analyzed1)
  with Contradiction -> 
    true

(* prove unicity of find *)

let is_find_unique cur_array the_facts simp_facts find_branches =
  (List.for_all (branch_unique cur_array the_facts simp_facts) find_branches) &&
  (let rec incomp_branches = function
      [] -> true
    | (br::rest_br) -> 
	(List.for_all (incompatible_branches cur_array the_facts simp_facts br) rest_br) &&
	(incomp_branches rest_br)
  in
  incomp_branches find_branches)

END COMMENTED OUT *)

(* get_elsefind_facts *)

(* this function returns the list of all the binderref that are defined before the node `node' after transformation through the rename_br transformation, and stops if it encounters a binder from stop_binders or if the node is stop_node *)

let rec add_vars_until_binder_or_node node stop_binders stop_node acc =
  if (node == node.above_node) then
    (
      if (!Settings.debug_elsefind_facts) then
        begin
          print_string "Bug ?";
          print_newline ()
        end;
      acc
    )
  else
  if (node == stop_node) then
    (
      if (!Settings.debug_elsefind_facts) then
        begin
          print_string "Elsefind_fact add_vars stopped at input_node";
          print_newline ()
        end;
      acc
    )
  else if (List.exists (fun b -> List.mem b node.binders) stop_binders) then
      (
        if (!Settings.debug_elsefind_facts) then
          begin
            print_string "Elsefind_fact add_vars stopped because var b or br found";
            print_newline ()
          end;
        acc
      )
  else
    (add_vars_until_binder_or_node node.above_node stop_binders stop_node (node.binders @ acc))
  

(* this function is used as the final function for match_among_list *)
let final_next3 bl def_list t result () =
  Terms. auto_cleanup (fun () ->
    let t' = Terms.copy_term3 t in
    let def_list' = Terms.copy_def_list3 def_list in
    result := (def_list', t')::(!result));
  (* Backtrack *)
  raise NoMatch

(* [get_fact_of_elsefind_fact] collects terms that are true, where
   - the variable b[tl] is known to be defined at the current program point (due to some defined condition of find)
   - the variable b is defined in the else branch of a find, so that 
     [elsefind_fact = (bl,def_list,t1)], which means [forall bl, not (defined(def_list) && t1)] 
     holds at the definition of b
   - [all_indices] corresponds to the current [cur_array] plus possibly find indices when we are in a condition of find.
   - [def_vars] are variables known to be defined at the current program point.
   - [simp_facts] are facts known to be true at the current program point.

   - [proba_accu] stores the negligible probability that the proved terms do not hold
   - [term_accu] stores the proved terms
   - [g] is the current game

   [get_fact_of_elsefind_fact] uses the following reasoning:
   * we substitute tl for b.args_at_creation in the [elsefind_fact], and choose the variables bl such that
   the elements of def_list are defined at the current program point.
   * then, we know that not (defined(def_list) && t1) holds at the definition of b[tl].
   * if the elements of def_list are defined before b[tl], we obtain not(t1).
   * otherwise, we try to show that, if an element of def_list is defined after b[tl], then
   t1 leads to a contradiction.
   * if this succeeds, we can conclude that not(t1) holds in all cases.
*)

let get_fact_of_elsefind_fact proba_accu term_accu g all_indices def_vars simp_facts (b,tl) ((bl,def_list,t1) as elsefind_fact) =
  if (!Settings.debug_elsefind_facts) then
    begin
      print_string "-----------------\nElsefind_fact (before renaming):\n";
      Display.display_term (Terms.term_from_binderref (b,tl));
      print_newline ();
      Facts.display_facts ([],[],[elsefind_fact])
    end;

  let vcounter = !Terms.vcounter in

  (* rename the bl to fresh variables in the elsefind fact (the variables in bl are universally quantified) *)
  let bl' = List.map (fun b -> Terms.create_binder "@t" (Terms.new_vname ()) b.btype []) bl in
  let subst = List.map2 (fun b b' -> (b,Terms.term_from_binder b')) bl bl' in
  let def_list = Terms.subst_def_list3 subst def_list in
  let t1 = Terms.subst3 subst t1 in

  (* decompose def_list into subterms: all *subterms* of def_list must
     be defined before the find so that we can conclude not(t1) from
     the elsefind fact. *)
  let def_list_subterms = ref [] in
  List.iter (Terms.close_def_subterm def_list_subterms) def_list;
  let def_list = Terms.setminus_binderref (!def_list_subterms) (List.map (fun b' -> (b', [])) bl') in

  (* Optimization: if we know that an element br1 is defined before br2 = (b2,tl2) in deflist', 
     we can remove br1. Indeed, assuming that br2 is defined before (b,tl) implies that
     br1 is defined before (b,tl), so that is enough to apply the elsefind fact. 
     This optimization does not seem to affect much the speed of the system. *)
  let rec filter_def_list already_seen = function
      [] -> List.rev already_seen
    | ((b2,tl2)::l) ->
	let rename_b2 = List.map2 (fun t b -> (Terms.binder_from_term t, b)) b2.args_at_creation tl2 in
	let before_br2 = 
	  try 
            Terms.subst_def_list3 rename_b2 (Terms.setminus_binderref (Facts.def_vars_from_defined None [] [(b2, b2.args_at_creation)]) (List.map Terms.binderref_from_term b2.args_at_creation))
	  with Contradiction -> 
	    (* Contradiction may be raised when b2 can in fact not be defined. *)
	    []	
	in
	let already_seen' = Terms.setminus_binderref already_seen before_br2 in
	let l' = Terms.setminus_binderref l before_br2 in
	filter_def_list ((b2,tl2)::already_seen') l'
  in
  let def_list = filter_def_list [] def_list in

  (* transform the elsefind fact such that the variable (b,b.args_at_creation) 
     for the original fact corresponds to our variable (b,tl):
     substitute b.args_at_creation with tl *)
  let subst' = List.map2 (fun t t' -> (Terms.binder_from_term t, t')) b.args_at_creation tl in
  let def_list = Terms.subst_def_list3 subst' def_list in
  let t1 = Terms.subst3 subst' t1 in

  if (!Settings.debug_elsefind_facts) then
    begin
      print_string "Elsefind_fact (after renaming):\n";
      Display.display_term (Terms.term_from_binderref (b,tl));
      print_newline ();
      Facts.display_facts ([],[],[(bl',def_list,t1)])
    end;

  (* We have [elsefind_fact = (bl,def_list,t1)], which means [forall bl, not (defined(def_list) && t1)].
     We collect in variable [result] the pairs (def_list', t') instances of (def_list, t1) such that
     the elements of [def_list'] are defined at the current program point. (They are in [def_vars].) *)
  let result = ref [] in
  begin
    try 
      match_among_list (final_next3 bl' def_list t1 result) simp_facts bl' def_vars def_list
    with NoMatch -> ()
  end;
    
  Terms.vcounter := vcounter; (* Forget created variables *)

  List.iter (fun (def_list',t') ->
      if (!Settings.debug_elsefind_facts) then
        begin
          print_string "Elsefind_fact_try:\n";
          Display.display_term t';
          print_newline ();
          print_string "And the def_list':\n";
          Display.display_list Display.display_term (List.map Terms.term_from_binderref def_list');
          print_newline ()
        end;

      (* If \forall br \in def_list', br is defined strictly before (b,tl), then it is defined before the find that gives the elsefind_fact, and so (not t') is true, since the "else" branch of that find has been taken.
         In the other case, we must prove that \forall br \in def_list', if br is defined after or at (b,tl), t' => Contradiction. *)

    (* Variables defined before (b,tl) *)
    let rename_b = List.map2 (fun t b -> (Terms.binder_from_term t, b)) b.args_at_creation tl in
    let def_vars = 
      try 
        Terms.subst_def_list3 rename_b (Terms.setminus_binderref (Facts.def_vars_from_defined None [] [(b, b.args_at_creation)]) (List.map Terms.binderref_from_term b.args_at_creation))
      with Contradiction -> 
	(* Contradiction may be raised when b can in fact not be defined. *)
	[]
    in
      if (!Settings.debug_elsefind_facts) then
        begin
          print_string "Elsefind_fact_vars_before:\n";
          Display.display_list Display.display_term (List.map Terms.term_from_binderref def_vars);
          print_newline ()
        end;
      if proba_accu != None then reset [] g;
      if (
        List.for_all (fun br ->
          (* Let us suppose that br has been defined after or at (b,tl) *)
          if (!Settings.debug_elsefind_facts) then
            begin
              print_string "Let's assume that ";
	      Display.display_term (Terms.term_from_binderref br);
	      print_string " is defined after or simultaneously ";
	      Display.display_term (Terms.term_from_binderref (b,tl));
              print_newline ()
            end;

	  (* If the variable of br is defined at the definition of b, 
	     remove the variables defined at the same time as (b,tl) and br
	     from def_vars. (We are not sure that they are defined before br.) *)
	  let vars_at_b = List.concat (List.map (fun n -> n.binders) b.def) in
	  let def_vars = 
	    if List.memq (fst br) vars_at_b then
	      Terms.setminus_binderref def_vars (List.map (fun b' -> (b', tl)) vars_at_b)
	    else
	      def_vars
	  in

	  (* If br is in def_vars, br is defined before (b,tl), so the assumption 
	     that br is defined after (b,tl) never holds. *)
	  (Terms.mem_binderref br def_vars) || (
          let order_assumptions = [br,(b,tl)] in
          List.for_all (fun n -> (* for each definition def_node of br *)
            try
              let rename_br = List.map2 (fun t b -> (Terms.binder_from_term t, b)) (fst br).args_at_creation (snd br) in
                (* Compute variables that are defined after (b,tl):
		   add to the future variables of br the variables defined between the previous input 
		   point and the definition of br and after another definition of (b,_). *)
              let future_binders = add_vars_until_binder_or_node n [b] (above_input_node n) n.future_binders in
	      let future_vars = Terms.subst_def_list3 rename_br (List.map (fun b -> (b, b.args_at_creation)) future_binders) in
                if (!Settings.debug_elsefind_facts) then
                  begin
                    print_string "Elsefind_fact_future_vars:\n";
                    Display.display_list Display.display_term (List.map Terms.term_from_binderref future_vars);
                    print_newline ()
                  end;

	      (* Elements of future_vars are defined after those of def_vars;
	         If they are in def_vars, that's a contradiction *)
	      if List.exists (fun future_br -> Terms.mem_binderref future_br def_vars) future_vars then
		raise Contradiction;

	      (* Since br is defined after (b,tl), all elements of future_vars are defined after (b,tl).
		 The elements of def_vars are defined before (b,tl), so before the elements
		 of future_vars. 
		 Therefore, the elements of def_vars are independent of the elements of future_vars
		 that are randomly chosen. *)
              let dep_info = (future_vars, List.map Terms.term_from_binderref def_vars) in
     
                if (!Settings.debug_elsefind_facts) then
                  begin
                    print_string "--Args to dependency_collision:\n";
                    print_string "All indices=";
                    Display.display_list Display.display_binder all_indices;
                    print_string "\nOrder assumptions=";
                    Display.display_list (fun (br,br') -> 
		      print_string "(";
                      Display.display_list Display.display_term (List.map Terms.term_from_binderref [br;br']); 
		      print_string ")"
			) order_assumptions;
                    print_string "\nDepinfo=previous lists";
                    print_string "\nFacts=\n";
                    Facts.display_facts simp_facts;
                    print_string "\nt'=";
                    Display.display_term t';
                    print_string "\n--End of args"; print_newline ();
                    Settings.debug_simplif_add_facts := true;
                  end;
           
              let (subst, facts, _) = simp_facts in
              let (_,_,_) = Facts.simplif_add_list (dependency_collision_order_hyp' all_indices order_assumptions dep_info) ([],[],[]) (t'::(subst@facts)) in
                if (!Settings.debug_elsefind_facts) then
                  begin
                    Settings.debug_simplif_add_facts := false;
                    print_string "Failed to obtain a contradiction.";
                    print_newline ()
                  end;
                false
            with Contradiction -> 
              if (!Settings.debug_elsefind_facts) then
                begin
                  Settings.debug_simplif_add_facts := false;
                  print_string "Obtained a contradiction.";
                  print_newline ()
                end;
              true
                ) (fst br).def
	    )
            ) def_list'; 
      )
      then
        begin
          (* The term (not t') is true, add it *)
          let t = Terms.make_not t' in
          term_accu := t :: (!term_accu);
	  match proba_accu with
	    None -> 
              if (!Settings.debug_elsefind_facts) then
		begin
		  print_string "Found a usable term: ";
		  Display.display_term t;
		  print_newline ()
		end
	  | Some proba_ref ->
              let proba = final_add_proba() in
              if (!Settings.debug_elsefind_facts) then
		begin
		  print_string "Found a usable term: ";
		  Display.display_term t;
		  print_string " with probability ";
		  Display.display_set proba;
		  print_newline ()
		end;
	      proba_ref := proba @ (!proba_ref)
        end
      else
        begin
          if (!Settings.debug_elsefind_facts) then
            begin
              print_string "Found no usable terms.";
              print_newline ()
            end
	end
	  ) (!result)


let defined_after b b1 =
  List.for_all (fun n -> List.memq b1 (Terms.add_def_vars_node [] n)) b.def

let rec add_latest ((b,tl) as br) elsefind = function
    [] -> [(br,elsefind)]
  | ((b', tl') as br',elsefind')::l ->
      if (Terms.equal_elsefind_facts elsefind elsefind') && (Terms.equal_term_lists tl tl') then
	if defined_after b b' then
	  (br,elsefind)::l
	else
	  (br',elsefind')::l
      else
	(br',elsefind')::(add_latest br elsefind l)

let rec collect_eff = function
    [] -> []
  | br::l ->
      let last_effl = collect_eff l in
      let new_effl = 
	try 
          Terms.intersect_list Terms.equal_elsefind_facts (List.map (fun n -> n.elsefind_facts_at_def) (fst br).def)
	with Contradiction -> []
      in
      List.fold_right (add_latest br) new_effl last_effl

let get_facts_of_elsefind_facts g cur_array return_proba simp_facts def_vars_orig (bl,def_list,_,_) =
  if (!Settings.debug_elsefind_facts) then
    begin
      print_string "__________________\n";
      print_string "Elsefind begin\n";
      print_newline ()
    end; 
  let def_vars = 
    try 
      Terms.setminus_binderref (Facts.def_vars_from_defined None bl def_list) def_vars_orig
    with Contradiction ->
      (* A contradiction may happen when the variables in def_list can in fact not be defined *)
      []
  in
  let def_vars_current = def_vars_orig @ def_vars in
  let all_indices = bl @ cur_array in
  let proba_accu = if return_proba then Some (ref []) else None in
  let term_accu = ref [] in
  let effl = collect_eff def_vars in
  List.iter (fun (br, eff) -> get_fact_of_elsefind_fact proba_accu term_accu g all_indices def_vars_current simp_facts br eff) effl;
(*List.iter (fun br -> 
    let effl =
      try 
        Terms.intersect_list Terms.equal_elsefind_facts (List.map (fun n -> n.elsefind_facts_at_def) (fst br).def)
      with Contradiction -> []
    in
    List.iter (get_fact_of_elsefind_fact proba_accu term_accu g all_indices def_vars_current simp_facts br) effl
      ) def_vars;*)
  if (!Settings.debug_elsefind_facts) then
    begin
      print_string "__________________\n";
      print_string "Elsefind summary: these terms are true:\n";
      Display.display_list Display.display_term (!term_accu);
      print_newline ()
    end;
  (!term_accu),(match proba_accu with None -> [] | Some proba_ref -> !proba_ref)


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

let filter_indices t true_facts0 all_indices used_indices =
  let proba_state = Proba.get_current_state() in
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
      Terms.binder_from_term (List.assq b map_find_indices)
    with Not_found ->
      b) all_indices
  in
  let t' = Terms.subst3 map_find_indices t in
  let true_facts'' = List.map (Terms.subst3 map_find_indices) true_facts' in
  let used_indices' = List.map (fun t -> Terms.binder_from_term (Terms.subst3 map_find_indices t)) used_indices in
  (* Try to reduce the list of used indices. 
     The initial list of indices is a reordering of the list of all indices.
     We start with the larger indices (to eliminate them first) and among
     the indices of the same size, with those that are not in used_indices
     (also to eliminate them first).
     The goal is to try to remove large indices
     of used_indices, perhaps at the cost of adding more
     smaller indices of all_indices. *)
  let initial_indices =
      (* Sort used_indices and all_indices in decreasing size *)
      let used_indices_sort = List.sort greater_size used_indices' in
      let all_indices_sort = List.sort greater_size all_indices' in
      (* Remove elements of all_indices that are in used_indices *)
      let all_indices_sort_minus_used_indices = List.filter (fun b -> not (List.memq b used_indices_sort)) all_indices_sort in
      (* Build a list by merging indices from all_indices and used_indices.
	 When indices are of the same size, we put elements of all_indices first,
	 so that they will be eliminated, except if they are now necessary
	 because they replace some larger index eliminated before. *)
      List.merge greater_size all_indices_sort_minus_used_indices used_indices_sort 
  in
  (* Try to remove useless indices using true_facts' *)
  let really_used_indices = filter_indices_coll true_facts'' used_indices' initial_indices in
  if really_used_indices == initial_indices then
    begin
      (* I removed no index, I can just leave things as they were *)
      Proba.restore_state proba_state;
      (used_indices, (t', true_facts'', all_indices', initial_indices, used_indices', used_indices'))
    end
  else
    (List.map (fun b -> 
      let rec find_in_map_indices = function
	  [] -> Terms.term_from_binder b
	| ((b',t')::l) ->
	    if Terms.binder_from_term t' == b then Terms.term_from_binder b' else find_in_map_indices l
      in
      find_in_map_indices map_find_indices) really_used_indices, 
     (t', true_facts'', all_indices', initial_indices, used_indices', really_used_indices))

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

let is_compatible_indices 
    (t1, true_facts1, all_indices1, _, _, really_used_indices1) 
    (t2, true_facts2, all_indices2, _, _, really_used_indices2) =
  (*
  print_string "Simplify.is_compatible_indices ";
  Display.display_term t1;
  print_string " with ";
  Display.display_term t2;
  *)
  let proba_state = Proba.get_current_state() in
  (* Substitute fresh replication indices for find indices *)
  if (!Terms.current_bound_vars) != [] then
    Parsing_helper.internal_error "current_bound_vars should be cleaned up (simplify, filter_indices)";
  List.iter (fun b -> 
    let b' = new_repl_index b in
    Terms.link b (TLink (Terms.term_from_binder b'))) all_indices1;
  let true_facts1' = List.map Terms.copy_term3 true_facts1 in
  let really_used_indices1' = ref (List.map (fun b -> match b.link with 
    NoLink -> b
  | TLink t -> Terms.binder_from_term t) really_used_indices1) in
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
    Proba.restore_state proba_state;
    true
  with Contradiction ->
    (* The terms t1 and t2 are not compatible *)
    (* print_string " false\n"; *)
    false


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

let match_oracle_call 
    (t1, true_facts1, all_indices1, initial_indices1, used_indices1, really_used_indices1) 
    (t2, true_facts2, all_indices2, initial_indices2, used_indices2, really_used_indices2) =
  (*
  print_string "Simplify.same_oracle_call ";
  Display.display_term t1;
  print_string " with ";
  Display.display_term t2;
    *)
  Terms.auto_cleanup(fun () ->
    if eq_terms3 t1 t2 then
      let common_facts = List.filter (fun f1 -> List.exists (fun f2 -> eq_terms3 f1 f2) true_facts2) true_facts1 in
      Terms.cleanup();
      let proba_state = Proba.get_current_state() in
      (* Check that we can remove the same indices using common_facts as with all facts *)
      let really_used_indices1' = filter_indices_coll common_facts used_indices1 initial_indices1 in
      let r1 = Terms.equal_lists (==) really_used_indices1 really_used_indices1' in
      if r1 then
	begin
	  (*
	  print_string "Simplify.same_oracle_call ";
	  Display.display_term t1;
	  print_string " with ";
	  Display.display_term t2;
	  print_string " succeeds\n";
	  print_string "Common facts:\n";
	  List.iter (fun t ->
	    Display.display_term t; print_newline()) common_facts;
	  *)
	  Some (t1, common_facts, all_indices1, initial_indices1, used_indices1, really_used_indices1)
	end
      else
	begin
	  (*
	  print_string "Simplify.same_oracle_call ";
	  Display.display_term t1;
	  print_string " with ";
	  Display.display_term t2;
	  print_string " fails\n";
	  print_string "True facts 1:\n";
	  List.iter (fun t ->
	    Display.display_term t; print_newline()) true_facts1;
	  print_string "True facts 2:\n";
	  List.iter (fun t ->
	    Display.display_term t; print_newline()) true_facts2;
	  print_string "Common facts:\n";
	  List.iter (fun t ->
	    Display.display_term t; print_newline()) common_facts;
	  print_string "used_indices_map1\n";
	  Display.display_list (fun (t,t') ->
	    print_string "("; Display.display_term t; print_string ", "; Display.display_term t'; print_string ")") used_indices_map1;
	  print_newline();
	  print_string "used_indices_map1'\n";
	  Display.display_list (fun (t,t') ->
	    print_string "("; Display.display_term t; print_string ", "; Display.display_term t'; print_string ")") used_indices_map1';
	  print_newline();
	  print_string "used_indices1\n";
	  Display.display_list Display.display_term used_indices1;
	  print_newline();*)
	  Proba.restore_state proba_state;
	  None
	end
    else
      begin
	(*
	  print_string "Simplify.same_oracle_call ";
	  Display.display_term t1;
	  print_string " with ";
	  Display.display_term t2;
	  print_string " fails\n";*)
	None
      end
    )

let same_oracle_call call1 call2 =
  match match_oracle_call call1 call2 with
    None -> match_oracle_call call2 call1
  | r -> r
