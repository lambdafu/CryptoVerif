open Types

(* Generate a fresh variable, independent of [b0] *)
    
let any_term_name = "?"
let any_term_from_type t = 
  let b' = Terms.create_binder0 any_term_name t [] in
  let rec node = { above_node = node;
		   binders = [b'];
		   true_facts_at_def = [];
		   def_vars_at_def = [];
		   elsefind_facts_at_def = [];
		   future_binders = []; future_true_facts = []; 
		   definition = DNone; definition_success = DNone }
  in
  b'.def <- [node];
  Terms.term_from_binder b'

let any_term t = any_term_from_type t.t_type

let any_term_pat pat = 
  any_term_from_type (Terms.get_type_for_pattern pat)

let fresh_indep_term t =
  match t.t_type.tcat with
  | BitString -> (any_term t, [t.t_type], Some [])
  | Interv _ -> (Terms.term_from_repl_index (Facts.new_repl_index_term t), [], Some [t.t_type])

(* An element (order_assumptions, side_cond, true_facts, used_indices, 
initial_indices, t1, t2, b, lopt, probaf_mul_types) in term_collisions means that
the equality [t1 = t2] was considered impossible, assuming that
[order_assumptions] are satisfied: 
For each (br1, br2) in [order_assumptions], br2 is defined before br1,
[side_cond] is true, and the facts in [true_facts] hold; it has
negligible probability because t1 depends on b[lopt] by 
[decompos]/[projection] functions followed
by [compos]/[data] functions and t2 does not depend on b[lopt].
[probaf_mul_types] represents the probability of the collision.
[used_indices] are indices that occur in [t1] and [t2].
[initial_indices] are the indices at the program point of the collision. *)

let term_collisions = ref ([]: collision_state)

let reset coll_elim g =
  Proba.reset coll_elim g;
  term_collisions := [];
  Facts.reset_repl_index_list()

(* [get_var_link] function associated to [match_term3].
   See the interface of [Terms.match_funapp] for the 
   specification of [get_var_link]. *)

let get_var_link t () =
  match t.t_desc with
    Var (v,[]) when v.sname==any_term_name -> Some(v.link, true)
  | ReplIndex (v) -> Some(v.ri_link, false)
  | _ -> None

(* [match_term3 next_f t t' ()] Calls [next_f()] when [t']
   is an instance of [t], with any value for the [?] variables,
   and values stored in links for replication indices.
   It raises [NoMatch] when [t'] is not an instance of [t]. *)
	
let rec match_term3 next_f t t' () = 
  Terms.ri_auto_cleanup_failure (fun () ->
    match t.t_desc, t'.t_desc with
      Var (v,[]), _ when v.sname==any_term_name -> next_f()
    | ReplIndex (v), _ -> 
      (* Check that types match *)
	if t'.t_type != v.ri_type then
	  raise NoMatch;
	begin
	  match v.ri_link with
	    NoLink -> Terms.ri_link v (TLink t')
	  | TLink t -> if not (Terms.equal_terms t t') then raise NoMatch;
	end;
	next_f()
    | Var(b,l), Var(b',l') when b == b' -> 
	Match_eq.match_term_list match_term3 next_f l l' ()
    | FunApp(f,l), FunApp(f',l') when f == f' ->
	Match_eq.match_funapp match_term3 get_var_link Match_eq.default_match_error Terms.simp_facts_id next_f t t' ()
    | _ -> raise NoMatch
	  )

(* The functions [instantiate_*] replace indices with their
   value stored in links, inside probabilities *)
    
let rec instantiate_ri_list accu = function
  | [] -> accu
  | ri::ri_list ->
      match ri.ri_link with
      | NoLink -> instantiate_ri_list (ri::accu) ri_list
      | TLink t ->
	  let l = ref accu in
	  Proba.collect_array_indexes l t;
	  instantiate_ri_list (!l) ri_list

let rec instantiate_probaf = function
  | Time(g,x) -> Time(g, instantiate_probaf x)
  | (AttTime | Cst _ | Count _ | OCount _ | Zero | Card _ | TypeMaxlength _
     | EpsFind | EpsRand _ | PColl1Rand _ | PColl2Rand _) as x -> x
  | Proba(p,l) -> Proba(p, List.map instantiate_probaf l)
  | ActTime(f,l) -> ActTime(f, List.map instantiate_probaf l)
  | Maxlength(g,t) -> Maxlength(g, Terms.copy_term Terms.Links_RI t)
  | Length(f,l) -> Length(f, List.map instantiate_probaf l)
  | Mul(x,y) -> Mul(instantiate_probaf x, instantiate_probaf y)
  | Add(x,y) -> Add(instantiate_probaf x, instantiate_probaf y)
  | Sub(x,y) -> Sub(instantiate_probaf x, instantiate_probaf y)
  | Div(x,y) -> Div(instantiate_probaf x, instantiate_probaf y)
  | Max(l) -> Max(List.map instantiate_probaf l)
	    
let instantiate_probaf_mul_types (ri_list, probaf, dep_types, full_type, opt_indep_types) =
  (* Note: in case probaf refers to terms (via maxlength), we
     might need to instantiate probaf as well. That is not
     common for collisions, but I do it for safety. *)
  (instantiate_ri_list [] ri_list, instantiate_probaf probaf, dep_types, full_type, opt_indep_types)

let instantiate_term_coll = function
  | Fixed probaf_mul_types ->
      Fixed (instantiate_probaf_mul_types probaf_mul_types)
  | ProbaIndepCollOfVar(b,args,ri_list) ->
      ProbaIndepCollOfVar(b, List.map (Terms.copy_term Terms.Links_RI) args,
			  instantiate_ri_list [] ri_list)

let instantiate_red_proba (t1,t2,side_cond,probaf_mul_types) =
  (Terms.copy_term Terms.Links_RI t1,
   Terms.copy_term Terms.Links_RI t2,
   Terms.copy_term Terms.Links_RI side_cond,
   instantiate_probaf_mul_types probaf_mul_types)

let instantiate_find_compos_probaf (ri_arg, (term_coll, var_coll, red_proba)) =
  (ri_arg, (List.map instantiate_term_coll term_coll, var_coll,
	    List.map instantiate_red_proba red_proba))

(* [addq_list accu l] adds [l] to [accu], removing duplicate elements *)
    
let addq_list accu l =
  List.fold_left Terms.addq accu l

(* [check_no_index idx (b1,b2)] verifies that [idx]
   is not a replication index at creation of [b1] or [b2]. *)
    
let check_no_index idx (b1,b2) =
  assert (not (List.memq idx b1.args_at_creation ||
               List.memq idx b2.args_at_creation))

(* The functions [subst_idx_* idx image ...] replace 
   [idx] with its image [image = (ri_list,dep_types, full_type, indep_types_opt)]
   corresponding to all indices [ri_list] and types of [?] variables [dep_types] in a term,
   inside a probability.
   When [indep_types_opt = Some indep_types], 
   \prod_{T \in dep_types} |T| <= |full_type|/\prod{T \in indep_types} |T|. *)

let rec subst_idx idx ri_list' = function
  | [] -> []
  | (idx1::ri_list) ->
      if idx1 == idx then
	begin
	  assert (not (List.memq idx ri_list));
	  addq_list ri_list ri_list'
	end
      else
	idx1::(subst_idx idx ri_list' ri_list)
    
let subst_idx_entry idx (ri_list',dep_types', full_type', indep_types')
    (ri_list,probaf,dep_types, full_type, indep_types) =
  assert (dep_types == []);
  (subst_idx idx ri_list' ri_list,probaf,dep_types', full_type', indep_types')

let subst_idx_term_coll_entry idx image = function
  | Fixed probaf_mul_types -> Fixed (subst_idx_entry idx image probaf_mul_types)
  | ProbaIndepCollOfVar(b, args, ri_list) ->
      let (ri_list',dep_types', full_type', indep_types') = image in
      assert(dep_types' == []);
      let ri_list'' = subst_idx idx ri_list' ri_list in
      ProbaIndepCollOfVar(b, args, ri_list'')
    
let subst_idx_red_proba_entry idx image
    (t1,t2,side_cond,probaf_mul_types) =
  let probaf_mul_types' = subst_idx_entry idx image probaf_mul_types in
  (t1,t2,side_cond,probaf_mul_types')

let subst_idx_proba idx image (ac_term_coll, ac_coll, ac_red_proba) =
  List.iter (check_no_index idx) ac_coll;
  let ac_term_coll' = List.map (subst_idx_term_coll_entry idx image) ac_term_coll in
  let ac_red_proba' = List.map (subst_idx_red_proba_entry idx image) ac_red_proba in
  (ac_term_coll', ac_coll, ac_red_proba')

(* [equal_find_compos_probaf probaf1 probaf2] returns true when 
   [probaf1] is equal to [probaf2] (of type [find_compos_probaf]).
   [equal_term_coll] helps by computing equality on type [term_coll_t]. *)
    
let equal_term_coll term_coll1 term_coll2 =
  match term_coll1, term_coll2 with
  | Fixed probaf_mul_types1, Fixed probaf_mul_types2 ->
      Proba.equal_probaf_mul_types probaf_mul_types1 probaf_mul_types2
  | ProbaIndepCollOfVar(b1, args1, ri_list1), ProbaIndepCollOfVar(b2, args2, ri_list2) ->
      (b1 == b2) &&
      (Terms.equal_term_lists args1 args2) &&
      (Terms.equal_lists_sets_q ri_list1 ri_list2)
  | _ -> false
      	
let equal_find_compos_probaf
    (idx1, (ac_term_coll1, ac_coll1, ac_red_proba1))
    (idx2, all_coll2) =
  let image_idx2 = ([idx1], [], Settings.t_bitstring (*dummy type*), None) in
  let (ac_term_coll2', ac_coll2', ac_red_proba2') =
    subst_idx_proba idx2 image_idx2 all_coll2
  in
  (Terms.equal_lists_sets Proba.equal_coll ac_coll1 ac_coll2') &&
  (Terms.equal_lists_sets equal_term_coll ac_term_coll1 ac_term_coll2') &&
  (Terms.equal_lists_sets Proba.equal_red ac_red_proba1 ac_red_proba2')

(* [matches_proba_info (t1, t2, probaf) (t1', t2', probaf')]
   returns true when [(t1', t2', probaf')] is instance of 
   [(t1, t2, probaf)]. Then [(t1', t2', probaf')] does not 
   need to be added if [(t1, t2, probaf)] is already present.
   Used for various definitions of a variable with their
   find_compos probability in Transf.global_dep_anal. *)
	
let matches_proba_info (t1, t2, probaf) (t1', t2', probaf') =
  try
    let probaf_inst = 
      Terms.ri_auto_cleanup (match_term3 (match_term3 (fun () ->
	instantiate_find_compos_probaf probaf
	  ) t2 t2') t1 t1')
    in
    (* We do not instantiate terms that may occur in probaf
       when they are not fully instantiated by the match on
       [t1,t2]. 
       That should be ok because all variable indices that
       depend on [b0] are replaced with fresh indices before
       [find_compos], so no further index is replaced by a fresh
       index inside the simplifications made in [find_compos]. 
       Hence all fresh indices should occur in [t1,t2]. *)
    equal_find_compos_probaf probaf_inst probaf'
  with NoMatch -> false

(* [matches_term_coll coll1 coll2] returns the true facts of [coll1]
   whose instance appear in [coll2], when [coll2] is an instance
   of [coll1].
   Otherwise, raises NoMatch

   The functions [lookup] and [find_common] help computing the
   commun true facts. 
   [lookup next_f t l] calls [next_f true] when an instance of
   [t] occurs in [l]. Otherwise, it calls [next_f false].
   [find_common next_f [] l1 l2] calls [next_f common]
   where [common] is the list of elements of [l1]
   whose instance occurs in [l2]. *)

let rec lookup next_f t = function
  | [] -> (* Not found *) next_f false
  | a::l ->
      try 
	match_term3 (fun () -> (* Found *) next_f true) t a ()
      with NoMatch ->
	lookup next_f t l

let rec find_common next_f accu l1 l2 =
  match l1 with
  | [] -> next_f accu
  | t::l ->
      lookup (fun found ->
	let accu' = if found then t::accu else accu in
	find_common next_f accu' l l2
	  ) t l2
	
      
let matches_term_coll
    (order_assumptions, side_condition, true_facts, used_indices, initial_indices, t1, t2, b, lopt, probaf_mul_types)
    (order_assumptions', side_condition', true_facts', used_indices', initial_indices', t1', t2', b', lopt', probaf_mul_types') =
  try 
    if (order_assumptions != []) && (order_assumptions' == []) then
      raise Not_found
    else
      begin
	match_term3 (match_term3 (match_term3 (fun () -> 
	  let order_assumptions_instance = List.map (fun (br1,br2) ->
	    (Terms.copy_term Terms.Links_RI (Terms.term_from_binderref br1),
	     Terms.copy_term Terms.Links_RI (Terms.term_from_binderref br2))) order_assumptions
	  in
	  let order_assumptions' = List.map (fun (br1, br2) ->
	    (Terms.term_from_binderref br1,
	     Terms.term_from_binderref br2)) order_assumptions'
	  in
	  if not 
	      (List.for_all (fun (br1,br2) ->
		List.exists (fun (br1',br2') ->
		  (Terms.equal_terms br1 br1') && (Terms.equal_terms br2 br2')) order_assumptions') order_assumptions_instance)
	  then raise NoMatch;
	  let probaf_mul_types_inst = instantiate_probaf_mul_types probaf_mul_types in
	  if not (Proba.equal_probaf_mul_types probaf_mul_types_inst probaf_mul_types') then
	    (* For speed, we do not reconsider other ways to match the 3 terms,
	       so we raise Not_found rather than NoMatch *)
	    raise Not_found;
	  find_common (fun common_facts -> common_facts) [] true_facts true_facts'
	      ) side_condition side_condition') t2 t2') t1 t1' ();
      end
  with NoMatch -> raise Not_found

let get_index_size b =
  (Terms.param_from_type b.ri_type).psize

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
  let used_indices_term = List.map Terms.term_from_repl_index used_indices in
  let rec filter_indices_rec = function
      [] -> ()
    | first_index::rest_indices ->
	List.iter (fun b -> 
	  let b' = Facts.new_repl_index b in
	  Terms.ri_link b (TLink (Terms.term_from_repl_index b')))
	  (first_index::(!useless_indices));
	let true_facts' = List.map (Terms.copy_term Terms.Links_RI) true_facts in
	let used_indices_term' = List.map (Terms.copy_term Terms.Links_RI) used_indices_term in 
	Terms.ri_cleanup();
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
as t1 = t2. 

In principle, the variables in t1, t2 might have different definitions
for different indices, yielding different collision probabilities.
In this case, we should take the maximum of the probabilities
when we merge several collisions. 
In practice:
- in DepAnal2, the variables are replaced with their value.
So equal terms implies same probabibility.
- in global_dep_anal, in case a variable has several definitions
in the whole game, this was taken care of in its status using
ProbaIndepCollOfVar and in Transf_globaldepanal.compute_probas.
However, now these cases are registered as several collisions,
so we could have different probabilities with the same terms.

I compare the probabilities by [equal_probaf_mul_types]
and avoid merging in case they are different.
   *)

let matches 
    ((order_assumptions, side_condition, true_facts,
      used_indices, initial_indices, t1, t2, b, lopt,
      ((really_used_indices, _,_,_,_) as probaf_mul_types)) as coll)
    coll' =
  Terms.ri_auto_cleanup (fun () ->
    try 
      let common_facts = matches_term_coll coll coll' in
      Terms.ri_cleanup();
      (* Check that we can remove the same indices using common_facts as with all facts *)
      if initial_indices == really_used_indices then
	(* If we removed no index, this is certainly true *)
	Some(order_assumptions, side_condition, common_facts, used_indices, initial_indices, t1, t2, b, lopt, probaf_mul_types)
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
	    Some(order_assumptions, side_condition, common_facts, used_indices, initial_indices, t1, t2, b, lopt, probaf_mul_types)
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
  with Not_found -> None)

let add_term_collision (cur_array, true_facts, order_assumptions, side_condition) t1 t2 b lopt ((used_indices, probaf, dep_types, full_type, indep_types_opt) as probaf_mul_types) =
  (* Add the indices of t1,t2 to all_indices; some of them may be missing
     initially because array indices in t1,t2 that depend on "bad" variables
     are replaced with fresh indices, and these indices are not included in
     cur_array initially (cur_array contains the replication and find
     indices above the considered terms) *)
  let all_indices = addq_list cur_array used_indices in
  try
  let collision_info = 
    (* If the probability used_indices * probaf is small enough to eliminate collisions, return that probability.
       Otherwise, try to optimize to reduce the factor used_indices *)
    if Proba.is_small_enough_coll_elim probaf_mul_types then 
      (order_assumptions, side_condition, [], used_indices, used_indices, t1, t2, b, lopt, probaf_mul_types)
    else
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
      let probaf_mul_types' = (really_used_indices, probaf, dep_types, full_type, indep_types_opt) in
      if Proba.is_small_enough_coll_elim probaf_mul_types' then 
	(order_assumptions, side_condition, true_facts, used_indices, initial_indices, t1, t2, b, lopt, probaf_mul_types') 
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

      
let add_term_collisions current_state t1 t2 b lopt ((idx, all_coll), dep_types, full_type, indep_types) =
  match dep_types with
  | [ty] when ty == full_type -> false (* Quickly eliminate a case in which the probability will always be too large: the term [t2] can take any value depending of [b] *) 
  | _ ->
      let idx_t2 = ref [] in
      Proba.collect_array_indexes idx_t2 t2;
      let image_idx = (!idx_t2, dep_types, full_type, indep_types) in
      let (proba_term_collisions', proba_var_coll', proba_collision') =
	subst_idx_proba idx image_idx all_coll
      in
      let old_proba_state = (!term_collisions, Proba.get_current_state()) in
      if List.for_all (fun (b1,b2) -> Proba.add_elim_collisions b1 b2) proba_var_coll' &&
	List.for_all Proba.add_proba_red_inside proba_collision' &&
	List.for_all (function
	  | Fixed probaf_mul_types -> add_term_collision current_state t1 t2 b lopt probaf_mul_types
	  | ProbaIndepCollOfVar _ -> Parsing_helper.internal_error "ProbaIndepCollOfVar should have been instantiated"
		) proba_term_collisions' then
	true
      else
	begin
	  term_collisions := fst old_proba_state;
	  Proba.restore_state (snd old_proba_state);
	  false
	end

let proba_for_term_collision (order_assumptions, side_condition, _, _, _, t1, t2, b, lopt, ((really_used_indices, probaf, dep_types, _, _) as probaf_mul_types)) =
  print_string "Eliminated collisions between ";
  Display.display_term t1;
  print_string " and ";
  Display.display_term t2;
  let p = Proba.proba_for probaf_mul_types in
  print_string "(";
  if order_assumptions != [] then
    begin
      print_string "assuming ";
      Display.display_list (fun ((b1, l1), (b2, l2)) ->
	Display.display_var b2 l2;
	print_string " is defined before ";
	Display.display_var b1 l1
	  ) order_assumptions;
      print_string ", "
    end;
  if not (Terms.is_true side_condition) then
    begin
      if order_assumptions != [] then print_string "and " else print_string "assuming ";
      Display.display_term side_condition;
      print_string ", "
    end;
  Display.display_term t1;
  print_string " collides with a value independent of ";
  begin
    match lopt with
      None ->   Display.display_binder b; print_string "[...]"
    | Some l -> Display.display_var b l 
  end;
  print_string " with probability at most ";
  Display.display_proba 0 probaf;
  print_string ";\n ";
  Display.display_term t2;
  print_string " does not depend on ";
  begin
  match lopt with
    None ->   Display.display_binder b; print_string "[...]"
  | Some l -> Display.display_var b l 
  end;
  if dep_types != [] then
    begin
      print_string " but takes at most ";
      Display.display_proba 0 (Polynom.p_prod (List.map (fun ty -> Card ty) dep_types));
      print_string " values"
    end;
  print_string ")\n";
  p
  

(* Final addition of probabilities *)

let final_add_proba() =
  Proba.final_add_proba (List.map proba_for_term_collision (!term_collisions))

    
let rec depends ((b, depinfo) as bdepinfo) t = 
  match t.t_desc with
  | FunApp(f,l) -> List.exists (depends bdepinfo) l
  | ReplIndex(b') -> false
  | Var(b',l) ->
      (not (List.exists (Terms.equal_terms t) depinfo.nodep)) && 
      ((
       ((b == b') || (not (Terms.is_restr b'))) &&
       (depinfo.other_variables ||
       (List.exists (fun (b'',_) -> b'' == b') depinfo.dep))
	 ) || (List.exists (depends bdepinfo) l))
  | _ -> true (*Rough overapproximation of the dependency analysis when
		if/let/find/new occur.
		Parsing_helper.internal_error "If/let/find/new unexpected in DepAnal1.depends"*)

let rec depends_pat f_depends = function
  | PatVar _ ->
      false
  | PatTuple(f,l) ->
      List.exists (depends_pat f_depends) l
  | PatEqual t ->
      f_depends t

let rec is_indep simp_facts ((b0, depinfo) as bdepinfo) t =
  match t.t_desc with
  | FunApp(f,l) ->
      let (l_indep, l_dep_types, l_indep_types) = is_indep_list simp_facts bdepinfo l in
      if l_dep_types = [] || f.f_cat == Tuple ||
      ((!Settings.trust_size_estimates) && t.t_type.tcat == BitString &&
       Terms.sum_list Terms.get_size_high l_dep_types <= Terms.get_size_high t.t_type) then
	Terms.build_term2 t (FunApp(f, l_indep)), l_dep_types,
	(if l_dep_types = [] then Some [t.t_type] else
	if f.f_cat == Tuple then l_indep_types else
	None)
      else
	fresh_indep_term t
  | ReplIndex(b) -> (t, [], Some [t.t_type])
  | Var(b,l) ->
      if (List.exists (Terms.equal_terms t) depinfo.nodep) then
	(t, [], Some [t.t_type]) 
      else if (b != b0 && Terms.is_restr b) ||
      ((not depinfo.other_variables) &&
       (not (List.exists (fun (b',_) -> b' == b) depinfo.dep)))
      then
	(Terms.build_term2 t (Var(b, List.map (fun t' ->
	  let (t'_indep, _, _) = is_indep simp_facts bdepinfo t' in
	  t'_indep) l)), [], Some [t.t_type])
      else
        let t' = Terms.try_no_var simp_facts t in
	(* The next test aims to avoid a loop. 
           In particular, it avoids looping when t is a subterm of t' or t = t' *)
        if Terms.refers_to b t' (*Terms.equal_terms t t'*) then
	  fresh_indep_term t
        else
          is_indep simp_facts bdepinfo t'
  | _ -> Parsing_helper.internal_error "If/let/find/new unexpected in is_indep"

and is_indep_list simp_facts bdepinfo = function
  | [] -> ([], [], Some [])
  | (a::l) ->
      let (a_indep, a_dep_types, a_indep_types) = is_indep simp_facts bdepinfo a in
      let (l_indep, l_dep_types, l_indep_types) = is_indep_list simp_facts bdepinfo l in
      (a_indep::l_indep, a_dep_types @ l_dep_types,
       match a_indep_types, l_indep_types with
       | None, _ | _, None -> None
       | Some a_i, Some l_i -> Some (a_i @ l_i))

let rec is_indep_pat simp_facts bdepinfo = function
  | PatVar b -> (any_term_from_type b.btype, [b.btype], Some [])
  | PatEqual t -> is_indep simp_facts bdepinfo t
  | PatTuple(f,l) ->
      let (l_indep, l_dep_types, l_indep_types) = is_indep_pat_list simp_facts bdepinfo l in
      Terms.build_term_type (snd f.f_type) (FunApp(f, l_indep)), l_dep_types,
      (if l_dep_types = [] then Some [snd f.f_type] else l_indep_types)
	
and is_indep_pat_list simp_facts bdepinfo = function
  | [] -> ([], [], Some [])
  | (a::l) ->
      let (a_indep, a_dep_types, a_indep_types) = is_indep_pat simp_facts bdepinfo a in
      let (l_indep, l_dep_types, l_indep_types) = is_indep_pat_list simp_facts bdepinfo l in
      (a_indep::l_indep, a_dep_types @ l_dep_types,
       match a_indep_types, l_indep_types with
       | None, _ | _, None -> None
       | Some a_i, Some l_i -> Some (a_i @ l_i))


let rec remove_dep_array_index ((b0, depinfo) as bdepinfo) t =
  match t.t_desc with
  | FunApp(f,l) -> Terms.build_term2 t (FunApp(f, List.map (remove_dep_array_index bdepinfo) l))
  | ReplIndex(b) -> t
  | Var(b,l) ->
      if (List.exists (Terms.equal_terms t) depinfo.nodep) then
	t 
      else 
	Terms.build_term2 t (Var(b, List.map (fun t' -> 
	  if depends bdepinfo t' then
	    Terms.term_from_repl_index (Facts.new_repl_index_term t')
	  else
	    t') l))
  | _ -> Parsing_helper.internal_error "If/let/find/new unexpected in remove_dep_array_index"

let rec remove_array_index t =
  Terms.build_term2 t 
     (match t.t_desc with
	FunApp(f,l) -> FunApp(f, List.map remove_array_index l)
      | ReplIndex(b) -> t.t_desc
      |	Var(b,l) ->
	  Var(b, List.map (fun t' ->
	    match t'.t_desc with
	      ReplIndex(b') -> t'
	    | _ -> Terms.term_from_repl_index (Facts.new_repl_index_term t')
		  ) l)
      | _ -> Parsing_helper.internal_error "If/let/find/new unexpected in remove_dep_array_index")

(* [is_indep_collect_args simp_facts ((b0,l0,depinfo,collect_bargs,collect_bargs_sc) as bdepinfo) t] 
   returns a quadruple [(t_indep, t_eq, dep_types, indep_types)]:
   - [t_eq] is a term equal to [t] using the equalities in [simp_facts]
   - [t_indep] is a term independent of [b0[l0]] in which some array indices in [t_eq] 
   may have been replaced with fresh replication indices, and some other subterms of [t_eq] 
   may have been replaced with variables [?]. 
   - [dep_types] is the list of types of subterms of [t_eq]
   replaced with variables [?], so that the number of values
   that [t_eq] can take depending on [b] is at most 
   the product of |T| for T \in dep_types (ignoring replication
   indices).
   - [indep_types] is the list of types of subterms of [t_eq]
   not replaced with variables [?]. This list is valid only
   when [trust_size_estimates] is not set. In this case, 
   subterms of [t_eq] are replaced only under [data] functions,
   so that 
   product of |T| for T \in dep_types <= |type(t_eq)|/product of |T| for T \in indep_types

   [depinfo] is the dependency information (see the type ['a depinfo] in types.ml)
   [collect_bargs] collects the indices of [b0] (different from [l0]) on which [t] depends
   [collect_bargs_sc] is a modified version of [collect_bargs] in which  
   array indices that depend on [b0] are replaced with fresh replication indices
   (as in the transformation from [t_eq] to [t_indep]). *)

let fresh_indep_term2 t =
  let (t_indep, t_dep_types, t_indep_types) = fresh_indep_term t in
  (t_indep, t, t_dep_types, t_indep_types)

	
let rec is_indep_collect_args simp_facts ((b0,l0,depinfo,collect_bargs,collect_bargs_sc) as bdepinfo) t =
  match t.t_desc with
  | FunApp(f,l) ->
      let (l_indep, l_eq, l_dep_types, l_indep_types) = is_indep_list simp_facts bdepinfo l in
      if l_dep_types = [] || f.f_cat == Tuple ||
      ((!Settings.trust_size_estimates) && t.t_type.tcat == BitString &&
       Terms.sum_list Terms.get_size_high l_dep_types <= Terms.get_size_high t.t_type) then
	Terms.build_term2 t (FunApp(f, l_indep)),
	Terms.build_term2 t (FunApp(f, l_eq)), l_dep_types,
	(if l_dep_types = [] then Some [t.t_type] else
	if f.f_cat == Tuple then l_indep_types else None)
      else
	fresh_indep_term2 t
  | ReplIndex(b) -> t, t, [], Some [t.t_type]
  | Var(b,l) ->
      if (List.exists (Terms.equal_terms t) depinfo.nodep) then
	t, t, [], Some [t.t_type]
      else if (b != b0 && Terms.is_restr b) ||
      ((not depinfo.other_variables) &&
       (not (List.exists (fun (b',_) -> b' == b) depinfo.dep)))
      then
	let (l_indep, l_eq, _, _) = is_indep_list simp_facts bdepinfo l in
	Terms.build_term2 t (Var(b, l_indep)), Terms.build_term2 t (Var(b, l_eq)), [], Some [t.t_type]
      else if b == b0 then
	if List.for_all2 Terms.equal_terms l0 l then
	  fresh_indep_term2 t
	else 
	  begin
	    let (l_indep, l_eq, _, _) = is_indep_list simp_facts bdepinfo l in
	    if not (List.exists (List.for_all2 Terms.equal_terms l_eq) (!collect_bargs)) then
	      begin
		collect_bargs := l_eq :: (!collect_bargs);
		collect_bargs_sc := l_indep :: (!collect_bargs_sc)
	      end;
	    Terms.build_term2 t (Var(b, l_indep)), Terms.build_term2 t (Var(b, l_eq)), [], Some [t.t_type]
	  end
      else
        let t' = Terms.try_no_var simp_facts t in
	(* The next test aims to avoid a loop. 
           In particular, it avoids looping when t is a subterm of t' or t = t' *)
        if Terms.refers_to b t' (*Terms.equal_terms t t'*) then
	  fresh_indep_term2 t
        else
          is_indep_collect_args simp_facts bdepinfo t'
  | _ -> Parsing_helper.internal_error "If/let/find/new unexpected in is_indep"

and is_indep_list simp_facts bdepinfo = function
  | [] -> ([], [], [], Some [])
  | (a::l) ->
      let (a_indep, a_eq, a_dep_types, a_indep_types) = is_indep_collect_args simp_facts bdepinfo a in
      let (l_indep, l_eq, l_dep_types, l_indep_types) = is_indep_list simp_facts bdepinfo l in
      (a_indep::l_indep, a_eq::l_eq, a_dep_types @ l_dep_types,
       match a_indep_types, l_indep_types with
       | None, _ | _, None -> None
       | Some a_i, Some l_i -> Some (a_i @ l_i))

let fresh_repl_index() =
  { ri_sname = "arg-idx";
    ri_vname = 0;
    ri_type = Settings.t_empty_idx;
    ri_link = NoLink }
    
let find_compos_probaf_from_term t =
  let ri = fresh_repl_index() in
  let t_idx = ref [] in
  Proba.collect_array_indexes t_idx t;
  (ri, ([Fixed(ri::(!t_idx),Proba.pcoll1rand t.t_type,[],t.t_type,None)],[],[]))
    
let extract_from_status t = function
  | Any -> None
  | Compos(probaf, t_1, l0opt') -> Some(probaf, t_1, l0opt')
  | Decompos(l0opt') -> Some(find_compos_probaf_from_term t, t, l0opt')

let indep_counter = ref 0
	
let indep_term t b idx =
  let b' = Terms.create_binder_internal (b.sname ^ "-indep") (!indep_counter) b.btype [idx] in
  incr indep_counter;
  let rec node = { above_node = node;
		   binders = [b'];
		   true_facts_at_def = [];
		   def_vars_at_def = [];
		   elsefind_facts_at_def = [];
		   future_binders = []; future_true_facts = []; 
		   definition = DNone; definition_success = DNone }
  in
  b'.def <- [node];
  Terms.build_term2 t (Var(b', [Terms.term_from_repl_index idx]))

let rec assoc_eq t = function
  | [] -> raise Not_found
  | ((t',res)::l) ->
      if Terms.equal_terms t t' then
	res
      else
	assoc_eq t l
    
let rec subst ((main_var, depinfo) as var_depinfo) assql idx new_indep_terms t =
  match t.t_desc with
  | ReplIndex(b) -> t
  | Var(b,l) -> 
      (try
	assoc_eq t (!assql) 
      with Not_found ->
        (* Do not rename variables that do not depend on the
	   variable argument of find_compos *)
	if ((Terms.is_restr b) && (b != main_var))(* Restrictions (other than main_var) do not depend on main_var *) ||
	((not depinfo.other_variables) &&
	 (not (List.exists (fun (b',_) -> b' == b) depinfo.dep)))
	then
	  Terms.build_term2 t (Var(b, List.map (subst var_depinfo assql idx new_indep_terms) l))
	else if List.exists (Terms.equal_terms t) depinfo.nodep then
	  t
	else 
	  let res = indep_term t b idx in
	  assql := (t,res)::(!assql);
	  new_indep_terms := res :: (!new_indep_terms);
	  res)
  | FunApp(f,l) -> Terms.build_term2 t (FunApp(f, List.map (subst var_depinfo assql idx new_indep_terms) l))
  | _ -> Parsing_helper.internal_error "If, find, let, and new should not occur in subst"

let ok_l0opt l0opt l0opt' = 
  match l0opt, l0opt' with
  | None,_ -> true
  | Some l0, Some l0' ->
      if Terms.equal_term_lists l0 l0' then
	true
      else
	false
  | Some _, None -> false

let subst_l0opt b l l0opt =
  match l0opt with
  | None -> None
  | Some l0 -> Some (List.map (Terms.subst b.args_at_creation l) l0)

(* The functions [subst_args_* b l ...] replace b.args_at_creation with l (or indices in l) in a probability *)

let subst_args_ri_list b l ri_list =
  List.fold_left2 (fun ri_list idx t ->
    let ri_list' = ref [] in
    Proba.collect_array_indexes ri_list' t;
    subst_idx idx (!ri_list') ri_list
      ) ri_list b.args_at_creation l 
	
let subst_args_probaf_mul_types b l (ri_list, probaf, dep_types, full_type, indep_types_opt) =
  (subst_args_ri_list b l ri_list, probaf, dep_types, full_type, indep_types_opt)

let subst_args_term_coll b l = function
  | Fixed probaf_mul_types ->
      Fixed(subst_args_probaf_mul_types b l probaf_mul_types)
  | ProbaIndepCollOfVar(b',args,ri_list) ->
      ProbaIndepCollOfVar(b',List.map (Terms.subst b.args_at_creation l) args,
			  subst_args_ri_list b l ri_list)
  
let subst_args_red_proba b l (t1,t2,side_cond,probaf_mul_types) =
  (t1,t2,side_cond,subst_args_probaf_mul_types b l probaf_mul_types)
	
let subst_args_proba b l (ri_arg, (term_coll, var_coll, red_proba)) =
  let term_coll' = List.map (subst_args_term_coll b l) term_coll in
  let red_proba' = List.map (subst_args_red_proba b l) red_proba in
  (ri_arg, (term_coll', var_coll, red_proba'))
	
let rec find_compos_gen decompos_only allow_bin ((main_var, depinfo) as var_depinfo) simp_facts l0opt t =
  if (!Settings.debug_simplif_add_facts) then
    begin
      print_string "find_compos:t=";
      Display.display_term t;
      print_newline ()
    end;

  match t.t_desc with
  | Var(b',l) when b' == main_var -> 
      begin
	match l0opt with
	| Some l0 ->
	    if Terms.equal_term_lists l l0 then
	      Decompos(l0opt)
	    else
	      Any
	| None ->
	    Decompos(Some l)
      end
  | Var(b',l) (* b' != main_var *) ->
      begin
	try
	  let (st, _,_) = List.assq b' depinfo.dep in
	  if depinfo.args_at_creation_only then
	    if Terms.is_args_at_creation b' l then
	      match st with
	      | Any -> Any
	      | Decompos(l0opt') ->
		  if ok_l0opt l0opt l0opt' then Decompos(l0opt') else Any
	      | Compos(proba, t_1, l0opt') ->
		  if (not decompos_only) && (ok_l0opt l0opt l0opt') then Compos(proba, t_1, l0opt') else Any
	    else Any
	  else
	    match st with
	    | Any -> Any
	    | Decompos(l0opt') ->
		let l0opt' = subst_l0opt b' l l0opt' in
		if ok_l0opt l0opt l0opt' then Decompos(l0opt') else Any
	    | Compos(proba, t_1, l0opt') ->
		if decompos_only then Any else
		let l0opt' = subst_l0opt b' l l0opt' in
		let proba' = subst_args_proba b' l proba in
		if ok_l0opt l0opt l0opt' then Compos(proba', Terms.subst b'.args_at_creation l t_1, l0opt') else Any
	with Not_found -> Any
      end
  | FunApp(f,l) when (f.f_options land Settings.fopt_COMPOS) != 0 ->
      begin
	if decompos_only then Any else
	match find_compos_l allow_bin var_depinfo simp_facts l0opt l with
	| None -> Any
	| Some(probaf, l', l0opt') -> 
	    Compos(probaf, Terms.build_term2 t (FunApp(f,l')), l0opt')
      end
  | FunApp(f,[t']) when (f.f_options land Settings.fopt_UNIFORM) != 0 ->
      if Proba.is_large_term t then
	find_compos_gen true allow_bin var_depinfo simp_facts l0opt t'
      else Any
  | _ ->
      if decompos_only || (not allow_bin) then Any else
      (* In a simpler version, we would remove 
	 find_compos_bin, find_compos_bin_l, find_decompos_bin, subst,
	 apply_statement2, apply_all_red2, apply_statements
	 and replace this case with Any
	 *)
      let vcounter = Terms.get_var_num_state() in
      indep_counter := 0;
      let idx = fresh_repl_index() in
      let new_indep_terms = ref depinfo.nodep in
      let t' = subst var_depinfo (ref []) idx new_indep_terms t in
      let new_depinfo =
	{ depinfo with
          nodep = (!new_indep_terms) }
      in
      if (!Settings.debug_simplif_add_facts) then
        begin
          print_string "_->t'=";
          Display.display_term t';
          print_string ", depinfo=";
          print_newline ()
        end;
      let idx_t' = ref [] in
      Proba.collect_array_indexes idx_t' t';
      let old_proba_state = Proba.get_and_empty_state() in
      let old_reduced = !Facts.reduced in
      let dependency_anal =
	let indep_test simp_facts t (b,l) =
	  let dep_info =
	    if (b == main_var) &&
	      (match l0opt with
	      | None -> true
	      | Some l0 -> Terms.equal_term_lists l0 l)
	    then
	      new_depinfo
	    else
	      Facts.nodepinfo
	  in
	  Facts.default_indep_test dep_info simp_facts t (b,l)
	in
	(indep_test, Facts.no_collision_test)
      in
      let f1 = Facts.apply_reds dependency_anal simp_facts (Terms.make_equal t t') in
      let (ac_coll, ac_red_proba) = Proba.get_current_state() in
      Proba.restore_state old_proba_state;
      Facts.reduced := old_reduced;
      let r =
	if Terms.is_false f1 then
	  Compos((idx, ([], ac_coll, ac_red_proba)), t, l0opt)
	else
	match find_compos_bin (main_var, new_depinfo) simp_facts l0opt f1 with
	  None -> Any
	| Some((idx', (proba', ac_coll', ac_red_proba')), _, l0opt') ->
	    let image_idx' = (!idx_t', [], t.t_type, None) in
	    let (proba'', ac_coll'', ac_red_proba'') = 
	      subst_idx_proba idx' image_idx'
		(proba', ac_coll', ac_red_proba')
	    in
	    (* Even if [l0opt'] is more precise than [l0opt], i.e.,
	       [l0opt = None] and [l0opt' = Some(...)], I cannot
	       exploit this information because I may have used that
	       terms are independent of all [b0[...]] in 
	       [Facts.apply_reds] above *)
	    Compos((idx, (proba'', ac_coll @ ac_coll'', ac_red_proba @ ac_red_proba'')), t, l0opt)
      in
      Terms.set_var_num_state vcounter; (* Forget created variables *)
      r

and find_compos_l (* decompos_only = false *) allow_bin var_depinfo simp_facts l0opt = function
    [] -> None
  | (a::l) ->
      match extract_from_status a (find_compos_gen false allow_bin var_depinfo simp_facts l0opt a) with
      |	None -> 
	  begin
	    match find_compos_l allow_bin var_depinfo simp_facts l0opt l with
	      None -> None
	    | Some(probaf, l', l0opt') -> Some(probaf, (any_term a)::l', l0opt')
	  end
      |	Some(probaf, a', l0opt') -> Some(probaf, a'::List.map any_term l, l0opt')

and find_compos_bin var_depinfo simp_facts l0opt fact =
  match fact.t_desc with
  | FunApp(f,[t1;t2]) when f.f_cat == Equal ->
      if not (depends var_depinfo t2) then
	extract_from_status t1 (find_compos_gen false false var_depinfo simp_facts l0opt t1)
      else if not (depends var_depinfo t1) then
	extract_from_status t2 (find_compos_gen false false var_depinfo simp_facts l0opt t2)
      else None
  | FunApp(f,[t1;t2]) when f == Settings.f_and ->
      begin
	match find_compos_bin var_depinfo simp_facts l0opt t1 with
	  None -> find_compos_bin var_depinfo simp_facts l0opt t2
	| x -> x
      end
  | _ -> None
    
let find_compos simp_facts var_depinfo l0opt t = find_compos_gen false true var_depinfo simp_facts l0opt t

let rec find_compos_pat f_find_compos = function
  | PatVar _ -> None
  | PatTuple(f,l) -> find_compos_pat_list f_find_compos f [] l
  | PatEqual t ->
      if Proba.is_large_term t then
	snd (f_find_compos t)
      else
	None

and find_compos_pat_list f_find_compos f seen = function
    [] -> None
  | (a::l) ->
      match find_compos_pat f_find_compos a with
      |	None -> 
	  find_compos_pat_list f_find_compos f (a::seen) l 
      |	Some(probaf, a', l0opt) ->
	  let l' = List.rev_append (List.map any_term_pat seen) (a'::(List.map any_term_pat l)) in
	  let t' = Terms.build_term_type (snd f.f_type) (FunApp(f,l')) in
	  Some(probaf, t', l0opt)

    
let rec dependency_collision_rec3 cur_array simp_facts t1 t2 t =
  let t_simp_ind = remove_array_index t in
  match t_simp_ind.t_desc, t.t_desc with
    Var(b,l_simp_ind), Var(b',l) when (Terms.is_restr b) && (Proba.is_large_term t) ->
      assert (b == b');
      begin
	let t1_simp_ind = remove_array_index t1 in
	match extract_from_status t1_simp_ind (find_compos simp_facts (b,Facts.nodepinfo) (Some l_simp_ind) t1_simp_ind) with
	  Some(probaf, t1', _) -> 
	    begin
	      try 
		let collect_bargs = ref [] in
		let collect_bargs_sc = ref [] in
		let (t2', t2_eq, dep_types, indep_types) = is_indep_collect_args simp_facts (b,l,Facts.nodepinfo,collect_bargs,collect_bargs_sc) t2 in
		let side_condition = 
		  Terms.make_and_list (List.map (fun l' ->
		    Terms.make_or_list (List.map2 Terms.make_diff l l')
		      ) (!collect_bargs_sc))
		in
	        (* add probability; returns true if small enough to eliminate collisions, false otherwise. *)
		if add_term_collisions (cur_array, Facts.true_facts_from_simp_facts simp_facts, [], side_condition) t1' t2' b (Some l) (probaf, dep_types, t2.t_type, indep_types) then
		  Some (Terms.make_or_list (List.map (fun l' ->   
		    let t2'' = Terms.replace l' l t2_eq in
		      Terms.make_and (Terms.make_and_list (List.map2 Terms.make_equal l l')) (Terms.make_equal t1 t2'')
		      ) (!collect_bargs)))
		else
		  None
	      with Not_found -> 
		None
	    end
       | _ -> None
      end 
  | _, FunApp(f,l) ->
      Terms.find_some (dependency_collision_rec3 cur_array simp_facts t1 t2) l
  | _ -> None

(* [try_two_directions f t1 t2] *)
	
let try_two_directions f t1 t2 =
  match f t1 t2 t1 with
    None -> f t2 t1 t2
  | x -> x

(***** Filter out the indices that are unique knowing other indices *****
       (useful for reducing the probabilities in the crypto transformation) 
       Terms.build_def_process must have been called so that t.t_facts has 
       been filled. For use from cryptotransf.ml.
*)

type compat_info_elem = term * term list * 
      repl_index list(* all indices *) * 
      repl_index list(* initial indices *) * 
      repl_index list(* used indices *) * 
      repl_index list(* really used indices *)

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
  let true_facts = 
    try
      true_facts0 @ (Facts.get_facts_at (DTerm t))
    with Contradiction ->
      [Terms.make_false()]
  in
  let used_indices' = List.map Terms.repl_index_from_term used_indices in
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
      let all_indices_sort = List.sort greater_size all_indices in
      (* Remove elements of all_indices that are in used_indices *)
      let all_indices_sort_minus_used_indices = List.filter (fun b -> not (List.memq b used_indices_sort)) all_indices_sort in
      (* Build a list by merging indices from all_indices and used_indices.
	 When indices are of the same size, we put elements of all_indices first,
	 so that they will be eliminated, except if they are now necessary
	 because they replace some larger index eliminated before. *)
      List.merge greater_size all_indices_sort_minus_used_indices used_indices_sort 
  in
  (* Try to remove useless indices using true_facts *)
  let really_used_indices = filter_indices_coll true_facts used_indices' initial_indices in
  if really_used_indices == initial_indices then
    begin
      (* I removed no index, I can just leave things as they were *)
      Proba.restore_state proba_state;
      (used_indices, (t, true_facts, all_indices, initial_indices, used_indices', used_indices'))
    end
  else
    (List.map Terms.term_from_repl_index really_used_indices, 
     (t, true_facts, all_indices, initial_indices, used_indices', really_used_indices))

(***** Test if two expressions can be evaluated with the same value of *****
       certain indices. 
       (useful for reducing the probabilities in the crypto transformation) 
       For use from cryptotransf.ml.
*)

(* TO DO Also exploit defined variables using CompatibleDefs2.check_compatible2_deflist *)

let rec find_same_type b = function
    [] -> raise Not_found 
  | b''::r ->
      if b''.ri_type == b.ri_type then
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
    (* Find a relation between really_used_indices1 and really_used_indices2 that
       respect types. *)
  if (!Terms.current_bound_ri) != [] then
    Parsing_helper.internal_error "current_bound_ri should be cleaned up (simplify, filter_indices)";
  let really_used_indices1' = ref really_used_indices1 in
  List.iter (fun b -> 
    if List.memq b really_used_indices2 then
      try
	let (b', rest_really_used_indices1) = find_same_type b (!really_used_indices1') in
	really_used_indices1' := rest_really_used_indices1;
	Terms.ri_link b (TLink (Terms.term_from_repl_index b'))
      with Not_found -> 
	let b' = Facts.new_repl_index b in
	Terms.ri_link b (TLink (Terms.term_from_repl_index b'))
    else
      let b' = Facts.new_repl_index b in
      Terms.ri_link b (TLink (Terms.term_from_repl_index b'))
	) all_indices2;
  let true_facts2' = List.map (Terms.copy_term Terms.Links_RI) true_facts2 in
  Terms.ri_cleanup();
  try
    ignore (Terms.auto_cleanup (fun () -> 
      Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) (true_facts1 @ true_facts2')));
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
    try
      match_term3 (fun () -> 
	let common_facts = find_common (fun common_facts -> common_facts) [] true_facts1 true_facts2 in
	Terms.ri_cleanup();
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
	  ) t1 t2 ()
    with NoMatch ->
      (*
	print_string "Simplify.same_oracle_call ";
	Display.display_term t1;
	print_string " with ";
	Display.display_term t2;
	print_string " fails\n";*)
      None
    )

let same_oracle_call call1 call2 =
  match match_oracle_call call1 call2 with
    None -> match_oracle_call call2 call1
  | r -> r

