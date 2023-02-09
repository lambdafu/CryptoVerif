open Types

(* Generate a fresh variable, independent of [b0] *)

let any_term_name = Proba.any_term_name
let any_term_from_type t =
  (* It is important to make sure that [b'.sname] is physically 
     equal to [any_term_name], as this is tested by matching in
     [Proba.match_term_any_var]. That works with 
     [create_binder_internal] or [create_binder0]. *)
  let b' = Terms.create_binder_internal any_term_name 0 t [] in
  ignore (Terms.set_def [b'] DNone DNone None);
  Terms.term_from_binder b'

let any_term t = any_term_from_type t.t_type

let any_term_pat pat = 
  any_term_from_type (Terms.get_type_for_pattern pat)

let fresh_indep_term t =
  match t.t_type.tcat with
  | BitString -> (any_term t, [t.t_type], Some [])
  | Interv _ -> (Terms.term_from_repl_index (Facts.new_repl_index_term t), [], Some [t.t_type])

(* An element (side_cond, true_facts, used_indices, 
initial_indices, t1, t2, b, lopt, probaf_mul_types) in term_collisions 
means that the equality [t1 = t2] was considered impossible: 
[side_cond] is true, and the facts in [true_facts] hold; it has
negligible probability because t1 depends on b[lopt] by 
[decompos]/[projection] functions followed
by [compos]/[data] functions and t2 does not depend on b[lopt].
[probaf_mul_types] represents the probability of the collision.
[used_indices] are indices that occur in [t1] and [t2].
[initial_indices] are the indices at the program point of the collision. *)

let term_collisions = ref ([]: term_coll_t list)

let reset coll_elim g =
  Proba.reset coll_elim g;
  term_collisions := [];
  Facts.reset_repl_index_list()

let get_current_state() =
  (!term_collisions, Proba.get_current_state())

let final_empty_state() =
  term_collisions := [];
  Proba.final_empty_state()
    
let restore_state (term_coll, prob_state) =
  term_collisions := term_coll;
  Proba.restore_state prob_state

let empty_proba_state = ([], Proba.empty_proba_state)

let get_and_final_empty_state() =
  let res = get_current_state() in
  final_empty_state();
  res
    
(* The functions [instantiate_*] replace indices with their
   value stored in links, inside probabilities *)
    
let instantiate_term_coll_proba = function
  | Fixed probaf_mul_types ->
      Fixed (Proba.copy_probaf_mul_types Terms.Links_RI  probaf_mul_types)
  | ProbaIndepCollOfVar(b,args,ri_list,known_def) ->
      ProbaIndepCollOfVar(b, List.map (Terms.copy_term Terms.Links_RI) args,
			  Proba.instantiate_ri_list [] ri_list, [])

let instantiate_find_compos_probaf (ri_arg, (term_coll_proba, var_coll, red_proba)) =
  (ri_arg, (List.map instantiate_term_coll_proba term_coll_proba, var_coll,
	    List.map (Proba.copy_red_proba Terms.Links_RI) red_proba))

(* [addq_list accu l] adds [l] to [accu], removing duplicate elements *)
    
let addq_list accu l =
  List.fold_left Terms.addq accu l

(* [check_no_index idx (b1,b2)] verifies that [idx]
   is not a replication index at creation of [b1] or [b2]. *)
    
let check_no_index idx (b1,b2,_) =
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
	Terms.addq (subst_idx idx ri_list' ri_list) idx1

let subst_idx_entry idx (ri_list',known_def', dep_types', full_type', indep_types') p =
  assert (p.p_dep_types == []);
  if List.memq idx p.p_ri_list then
    let (known_def, _) = p.p_ri_mul in
    { p_ri_list = subst_idx idx ri_list' p.p_ri_list;
      p_ri_mul = known_def' @ known_def, None;
      p_proba = p.p_proba;
      p_dep_types = dep_types';
      p_full_type = full_type';
      p_indep_types_option = indep_types' }
  else
    p

let subst_idx_term_coll_proba_entry idx image = function
  | Fixed probaf_mul_types -> Fixed (subst_idx_entry idx image probaf_mul_types)
  | ProbaIndepCollOfVar(b, args, ri_list, known_def) as x ->
      if List.memq idx ri_list then
	let (ri_list', known_def', dep_types', full_type', indep_types') = image in
	assert(dep_types' == []);
	let ri_list'' = subst_idx idx ri_list' ri_list in
	ProbaIndepCollOfVar(b, args, ri_list'', known_def' @ known_def)
      else
	x
    
let subst_idx_red_proba_entry idx image r =
  { r with r_proba = subst_idx_entry idx image r.r_proba }

let subst_idx_proba idx image (ac_term_coll_proba, ac_coll, ac_red_proba) =
  List.iter (check_no_index idx) ac_coll;
  let ac_term_coll_proba' = List.map (subst_idx_term_coll_proba_entry idx image) ac_term_coll_proba in
  let ac_red_proba' = List.map (subst_idx_red_proba_entry idx image) ac_red_proba in
  (ac_term_coll_proba', ac_coll, ac_red_proba')

(* [equal_find_compos_probaf probaf1 probaf2] returns true when 
   [probaf1] is equal to [probaf2] (of type [find_compos_probaf]).
   [equal_term_coll_proba] helps by computing equality on type [term_coll_proba_t]. *)
    
let equal_term_coll_proba term_coll_proba1 term_coll_proba2 =
  match term_coll_proba1, term_coll_proba2 with
  | Fixed probaf_mul_types1, Fixed probaf_mul_types2 ->
      Proba.equal_probaf_mul_types probaf_mul_types1 probaf_mul_types2
  | ProbaIndepCollOfVar(b1, args1, ri_list1, _), ProbaIndepCollOfVar(b2, args2, ri_list2, _) ->
      (b1 == b2) &&
      (Terms.equal_term_lists args1 args2) &&
      (Terms.equal_lists_sets_q ri_list1 ri_list2)
  | _ -> false
      	
let equal_find_compos_probaf
    (idx1, (ac_term_coll_proba1, ac_coll1, ac_red_proba1))
    (idx2, all_coll2) =
  let image_idx2 = ([idx1], [], [], Settings.t_bitstring (*dummy type*), None) in
  let (ac_term_coll_proba2', ac_coll2', ac_red_proba2') =
    subst_idx_proba idx2 image_idx2 all_coll2
  in
  (Terms.equal_lists_sets Proba.equal_coll ac_coll1 ac_coll2') &&
  (Terms.equal_lists_sets equal_term_coll_proba ac_term_coll_proba1 ac_term_coll_proba2') &&
  (Terms.equal_lists_sets Proba.equal_red ac_red_proba1 ac_red_proba2')

(* [matches_proba_info (t1, t2, probaf) (t1', t2', probaf')]
   returns true when [(t1', t2', probaf')] is instance of 
   [(t1, t2, probaf)]. Then [(t1', t2', probaf')] does not 
   need to be added if [(t1, t2, probaf)] is already present.
   Used for various definitions of a variable with their
   find_compos probability in Transf.global_dep_anal. *)

let match_term_any_var next_f t t' () = Proba.match_term_any_var None next_f t t' ()
    
let matches_proba_info (t1, t2, probaf) (t1', t2', probaf') =
  try
    let probaf_inst = 
      Terms.ri_auto_cleanup (match_term_any_var (match_term_any_var  (fun () ->
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
   [lookup match_fun next_f t l] calls [next_f true] when an instance of
   [t] occurs in [l]. Otherwise, it calls [next_f false].
   [find_common_aux match_fun next_f [] l1 l2] calls [next_f common]
   where [common] is the list of elements of [l1]
   whose instance occurs in [l2].
   [find_common match_fun l1 l2] returns the list of elements of [l1]
   whose instance occurs in [l2].
 *)

let rec lookup match_fun next_f t = function
  | [] -> (* Not found *) next_f false
  | a::l ->
      try 
	match_fun (fun () -> (* Found *) next_f true) t a ()
      with NoMatch ->
	lookup match_fun next_f t l

let rec find_common_aux match_fun next_f accu l1 l2 =
  match l1 with
  | [] -> next_f accu
  | t::l ->
      lookup match_fun (fun found ->
	let accu' = if found then t::accu else accu in
	find_common_aux match_fun next_f accu' l l2
	  ) t l2

let find_common match_fun l1 l2 =
  find_common_aux match_fun (fun accu -> accu) [] l1 l2

    
let matches_term_coll c c' = 
  try 
    if c.t_var != c'.t_var then
      raise Not_found
    else
      begin
	let match_lopt next_f () =
	  match c.t_lopt,c'.t_lopt with
	  | None, None -> next_f ()
	  | Some l, Some l' ->
	      Match_eq.match_term_list match_term_any_var next_f l l' ()
	  | _ -> raise NoMatch
	in
	match_lopt (match_term_any_var (match_term_any_var (match_term_any_var (fun () -> 
	  let proba_inst = Proba.copy_probaf_mul_types Terms.Links_RI c.t_proba in
	  if not (Proba.equal_probaf_mul_types proba_inst c'.t_proba) then
	    (* For speed, we do not reconsider other ways to match the 3 terms,
	       so we raise Not_found rather than NoMatch *)
	    raise Not_found;
	  find_common match_term_any_var c.t_true_facts c'.t_true_facts
	      ) c.t_side_cond c'.t_side_cond) c.t_indep c'.t_indep) c.t_charac c'.t_charac) ();
      end
  with NoMatch -> raise Not_found

let get_index_size b =
  (Terms.param_from_type b.ri_type).psize

let greater_size b1 b2 = compare (get_index_size b2) (get_index_size b1)

(* [order_indices] prepares the initial list of indices for [filter_indices_coll] 
   The initial list of indices is a reordering of the list of all indices.
   We start with the larger indices (to eliminate them first) and among
   the indices of the same size, with those that are not in [used_indices]
   (also to eliminate them first).
   The goal is to try to remove large indices
   of [used_indices], perhaps at the cost of adding more
   smaller indices of [all_indices]. *)
let order_indices all_indices used_indices =
  (* Sort used_indices and all_indices in decreasing size *)
  let used_indices_sort = List.sort greater_size used_indices in
  let all_indices_sort = List.sort greater_size all_indices in
  (* Remove elements of all_indices that are in used_indices *)
  let all_indices_sort_minus_used_indices = List.filter (fun b -> not (List.memq b used_indices_sort)) all_indices_sort in
  (* Build a list by merging indices from [all_indices] and [used_indices].
     When indices are of the same size, we put elements of all_indices first,
     so that they will be eliminated, except if they are now necessary
     because they replace some larger index eliminated before. *)
  List.merge greater_size all_indices_sort_minus_used_indices used_indices_sort 

    
(* [filter_indices_coll] filter out the indices that are unique knowing other indices 
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


   - [call_terms] represents the oracle call or collision test that is performed.
   - [above_indices] represents indices that are fixed because they determine
   random variables above the replication index with want to bound: we bound
   the number of calls for the same value of [above_indices].
   
   We show that, assuming the indices in [above_indices] are fixed and the
   counted indices are fixed, we get the same [call_terms] even if the other indices vary.
   To do that, we create a second copy of the other indices, and write ren(t) for
   the term obtained by replacing the other indices with their second copy.
   We show that [above_indices = ren(above_indices)], [true_facts], (ren(true_facts)]
   imply [call_terms = ren(call_terms)], by assuming [call_terms <> ren(call_terms)]
   and deriving a contradiction.
   *)


let filter_indices_coll above_indices call_terms true_facts used_indices initial_indices =
  (* Filter the indices *)
  (*print_string "Filter_indices_coll ";
  Display.display_list Display.display_term call_terms;
  print_string " above indices ";
  Display.display_list Display.display_term above_indices;
  print_string "\nKnowing\n";
  List.iter (fun f -> Display.display_term f; print_newline()) true_facts;
  print_string "used_indices: ";
  Display.display_list Display.display_repl_index used_indices;
  print_string "\ninitial_indices: ";
  Display.display_list Display.display_repl_index initial_indices;
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
  let rec filter_indices_rec = function
      [] -> ()
    | first_index::rest_indices ->
	List.iter (fun b ->
	  if not (List.exists (Terms.is_repl_index b) above_indices) then
	    let b' = Facts.new_repl_index b in
	    Terms.ri_link b (TLink (Terms.term_from_repl_index b')))
	  (first_index::(!useless_indices));
	let true_facts' = List.map (Terms.copy_term Terms.Links_RI) true_facts in
	let call_terms' = List.map (Terms.copy_term Terms.Links_RI) call_terms in
	let above_indices' = List.map (Terms.copy_term Terms.Links_RI) above_indices in
	Terms.ri_cleanup();
	let diff_fact = Terms.make_or_list (List.map2 Terms.make_diff call_terms call_terms') in
	let eq_facts = List.map2 Terms.make_equal above_indices above_indices' in
	let facts = diff_fact :: eq_facts @ (true_facts' @ true_facts) in
	try
	  (*print_string "index: "; Display.display_repl_index first_index; *)
	  let proba_state = Proba.get_current_state() in
	  ignore (Terms.auto_cleanup (fun () ->
	    Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) facts));
	  (* The index cannot be removed *)
	  Proba.restore_state proba_state;
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
  (*print_string "Result: "; Display.display_list Display.display_repl_index (!useful_indices); print_newline();*)
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

let get_terms_opt = function
  | None -> []
  | Some l -> l
      
let matches coll coll' =
  Terms.ri_auto_cleanup (fun () ->
    try 
      let common_facts = matches_term_coll coll coll' in
      Terms.ri_cleanup();
      (* Check that we can remove the same indices using common_facts as with all facts *)
      if coll.t_initial_indices == coll.t_proba.p_ri_list then
	(* If we removed no index, this is certainly true *)
	Some { coll with t_true_facts = common_facts }
      else
	let really_used_indices'' = filter_indices_coll [] (coll.t_indep :: coll.t_charac :: coll.t_side_cond :: (get_terms_opt coll.t_lopt)) common_facts coll.t_used_indices coll.t_initial_indices in
	if Terms.equal_lists (==) coll.t_proba.p_ri_list really_used_indices'' then
	  begin
	  (*
	  print_string "Depanal.matches ";
	  Display.display_term coll.t_charac;
	  print_string " with ";
	  Display.display_term coll.t_indep;
	  print_string " succeeds\n";
	  print_string "Common facts:\n";
	  List.iter (fun t ->
	    Display.display_term t; print_newline()) common_facts; *)
	    Some { coll with t_true_facts = common_facts }
	  end
	else
	  begin
	  (*
	  print_string "Depanal.matches ";
	  Display.display_term coll.t_charac;
	  print_string " with ";
	  Display.display_term coll.t_indep;
	  print_string " fails\n";
	  print_string "True facts:\n";
	  List.iter (fun t ->
	    Display.display_term t; print_newline()) coll.t_true_facts;
	  print_string "True facts':\n";
	  List.iter (fun t ->
	    Display.display_term t; print_newline()) coll'.t_true_facts;
	  print_string "Common facts:\n";
	  List.iter (fun t ->
	    Display.display_term t; print_newline()) common_facts;
	  print_string "used_indices\n";
	  Display.display_list Display.display_binder coll.t_used_indices;
	  print_newline();
	  print_string "initial_indices\n";
	  Display.display_list Display.display_binder coll.t_initial_indices;
	  print_newline();
	  print_string "really_used_indices\n";
	  Display.display_list Display.display_binder coll.t_proba.t_ri_list;
	  print_newline();
	  print_string "really_used_indices''\n";
	  Display.display_list Display.display_binder really_used_indices'';
	  print_newline();*)
	    None
	  end
  with Not_found -> None)

let readd_term_collision collision_info =
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
      | Some collision_info'' -> new_coll := collision_info''; false) (!term_collisions)
    in
    term_collisions := (!new_coll) :: term_collisions'

let readd_state (term_coll, prob_state) =
  List.iter readd_term_collision term_coll;
  Proba.readd_state prob_state
    
let add_term_collision (cur_array, true_facts, side_condition) t1 t2 b lopt probaf_mul_types =
  let used_indices = probaf_mul_types.p_ri_list in
  (* Add the indices of t1,t2 (in used_indices) to all_indices; some of them may be missing
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
      { t_side_cond = side_condition; t_true_facts = [];
	t_used_indices = used_indices; t_initial_indices = used_indices;
	t_charac = t1; t_indep = t2; t_var = b; t_lopt = lopt;
	t_proba = Proba.optim_probaf probaf_mul_types }
    else
      (* Try to reduce the list of used indices. *)
      let true_facts = Lazy.force true_facts in
      let initial_indices = order_indices all_indices used_indices in
      let really_used_indices = filter_indices_coll [] (t2::t1::side_condition::(get_terms_opt lopt)) true_facts used_indices initial_indices in
      (* OLD: I can forget the facts without losing precision when I removed no index
	 (initial_indices == really_used_indices);
	 Now, if I removed no index, the probability will be too large to eliminate collisions. *)
      let probaf_mul_types' =
	{ probaf_mul_types with
          p_ri_list = really_used_indices;
          p_ri_mul = Computeruntime.get_ri_mul really_used_indices (fst probaf_mul_types.p_ri_mul) }
      in
      if Proba.is_small_enough_coll_elim probaf_mul_types' then 
	{ t_side_cond = side_condition; t_true_facts = true_facts;
	  t_used_indices = used_indices; t_initial_indices = initial_indices;
	  t_charac = t1; t_indep = t2; t_var = b; t_lopt = lopt; t_proba = probaf_mul_types' }
      else
	(* Raises NoMatch when the probability is too large to be accepted *)
	raise NoMatch
  in
  readd_term_collision collision_info;
  true
  with NoMatch -> 
    false

      
let add_term_collisions current_state t1 t2 b lopt ((idx, all_coll), dep_types, full_type, indep_types) =
  match dep_types with
  | [ty] when ty == full_type -> false (* Quickly eliminate a case in which the probability will always be too large: the term [t2] can take any value depending of [b] *) 
  | _ ->
      let idx_t2 = ref [] in
      Proba.collect_array_indexes idx_t2 t2;
      let image_idx = (!idx_t2, [t2], dep_types, full_type, indep_types) in
      let (proba_term_collisions', proba_var_coll', proba_collision') =
	subst_idx_proba idx image_idx all_coll
      in
      let old_proba_state = get_current_state() in
      if List.for_all Proba.add_elim_collisions_inside proba_var_coll' &&
	List.for_all Proba.add_proba_red_inside proba_collision' &&
	List.for_all (function
	  | Fixed probaf_mul_types -> add_term_collision current_state t1 t2 b lopt probaf_mul_types
	  | ProbaIndepCollOfVar _ -> Parsing_helper.internal_error "ProbaIndepCollOfVar should have been instantiated"
		) proba_term_collisions' then
	true
      else
	begin
	  restore_state old_proba_state;
	  false
	end

let proba_for_term_collision tcoll =
  print_string "Eliminated collisions between ";
  Display.display_term tcoll.t_charac;
  print_string " and ";
  Display.display_term tcoll.t_indep;
  let p = Proba.proba_for tcoll.t_proba in
  print_string "(";
  if not (Terms.is_true tcoll.t_side_cond) then
    begin
      print_string "assuming ";
      Display.display_term tcoll.t_side_cond;
      print_string ", "
    end;
  Display.display_term tcoll.t_charac;
  print_string " collides with a value independent of ";
  begin
    match tcoll.t_lopt with
      None ->   Display.display_binder tcoll.t_var; print_string "[...]"
    | Some l -> Display.display_var tcoll.t_var l 
  end;
  print_string " with probability at most ";
  Display.display_proba 0 tcoll.t_proba.p_proba;
  print_string ";\n ";
  Display.display_term tcoll.t_indep;
  print_string " does not depend on ";
  begin
    match tcoll.t_lopt with
      None ->   Display.display_binder tcoll.t_var; print_string "[...]"
    | Some l -> Display.display_var tcoll.t_var l 
  end;
  if tcoll.t_proba.p_dep_types != [] then
    begin
      print_string " but takes at most ";
      Display.display_proba 0 (Polynom.p_prod (List.map (fun ty -> Card ty) tcoll.t_proba.p_dep_types));
      print_string " values"
    end;
  print_string ")\n";
  p
  

let display_proba_state (term_coll, prob_state) =
  List.iter (fun t -> ignore (proba_for_term_collision t)) term_coll;
  Proba.display_proba_state prob_state
    
(* Final addition of probabilities *)

let get_proba() =
  Proba.get_proba (List.map proba_for_term_collision (!term_collisions))
    
let final_add_proba() =
  let proba = get_proba() in
  final_empty_state();
  proba
    
(* For debugging *)
let display_depinfo depinfo =
  if depinfo.args_at_creation_only then print_string "args_at_creation_only ";
  print_string "indep = "; Display.display_list Display.display_term depinfo.nodep; print_string "; ";
  print_string "dep = "; Display.display_list (fun (b,_) -> Display.display_binder b) depinfo.dep;
  if depinfo.other_variables then print_string " + other variables"
  
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

let rec make_indep keep_var simp_facts ((b0,depinfo) as bdepinfo) t =
  match t.t_desc with
  | FunApp(f, [t1;t2]) when f.f_cat == LetEqual ->
	  (* Make sure that the left-hand side of LetEqual is not replaced:
	     it must remain a variable. *)
      Terms.build_term2 t (FunApp(f, [ make_indep true simp_facts bdepinfo t1;
				       make_indep false simp_facts bdepinfo t2 ]))
  | FunApp(f,l) ->
      Terms.build_term2 t (FunApp(f, List.map (make_indep false simp_facts bdepinfo) l))
  | ReplIndex(b) -> t
  | Var(b,l) ->
      if (List.exists (Terms.equal_terms t) depinfo.nodep) then
	t
      else if (b != b0 && Terms.is_restr b) ||
      ((not depinfo.other_variables) &&
       (not (List.exists (fun (b',_) -> b' == b) depinfo.dep)))
      then
	Terms.build_term2 t (Var(b, List.map (fun t' ->
	  try
	    make_indep false simp_facts bdepinfo t'
	  with Not_found ->
	    Terms.term_from_repl_index (Facts.new_repl_index_term t)
	      ) l))
      else if (b == b0) || keep_var then
	raise Not_found 
      else
        let t' = Terms.try_no_var simp_facts t in
	(* The next test aims to avoid a loop. 
           In particular, it avoids looping when t is a subterm of t' or t = t' *)
        if Terms.is_synt_subterm t t' then
	  raise Not_found
        else
          make_indep false simp_facts bdepinfo t'
  | _ -> Parsing_helper.internal_error "If/let/find/new unexpected in make_indep"

let rec make_indep_facts simp_facts bdepinfo = function
  | [] -> []
  | f::l ->
      let l' = make_indep_facts simp_facts bdepinfo l in
      try 
	(make_indep false simp_facts bdepinfo f) :: l'
      with Not_found ->
	l'

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
        if Terms.is_synt_subterm t t' then
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
      Terms.app f l_indep, l_dep_types,
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
        if Terms.is_synt_subterm t t' then
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
  (ri, ([Fixed { p_ri_list = ri::(!t_idx);
		 p_ri_mul = [t], None;
		 p_proba = Proba.pcoll1rand t.t_type;
		 p_dep_types = [];
		 p_full_type = t.t_type;
		 p_indep_types_option = None }],[],[]))
    
let extract_from_status t = function
  | Any -> None
  | Compos(probaf, t_1, l0opt') -> Some(probaf, t_1, l0opt')
  | Decompos(l0opt') -> Some(find_compos_probaf_from_term t, t, l0opt')

let indep_counter = ref 0
	
let indep_term t b idx =
  let b' = Terms.create_binder_internal (b.sname ^ "-indep") (!indep_counter) b.btype [idx] in
  incr indep_counter;
  ignore (Terms.set_def [b'] DNone DNone None);
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

let subst_args_ri_list b l ri_list_known_def =
  List.fold_left2 (fun (ri_list, known_def) idx t ->
    if List.memq idx ri_list then
      let ri_list' = ref [] in
      Proba.collect_array_indexes ri_list' t;
      (subst_idx idx (!ri_list') ri_list, t::known_def)
    else
      (ri_list, known_def)
	) ri_list_known_def b.args_at_creation l
    
let subst_args_probaf_mul_types b l p =
  let (ri_list', known_def') = subst_args_ri_list b l (p.p_ri_list, fst p.p_ri_mul) in
  { p with p_ri_list = ri_list'; p_ri_mul = known_def', None }

let subst_args_term_coll b l = function
  | Fixed probaf_mul_types ->
      Fixed(subst_args_probaf_mul_types b l probaf_mul_types)
  | ProbaIndepCollOfVar(b',args,ri_list,known_def) ->
      let known_def = List.map (Terms.subst b.args_at_creation l) known_def in
      let (ri_list', known_def') = subst_args_ri_list b l (ri_list, known_def) in
      ProbaIndepCollOfVar(b', List.map (Terms.subst b.args_at_creation l) args,
                          ri_list', known_def')
  
let subst_args_red_proba b l red_proba =
  { red_proba with r_proba = subst_args_probaf_mul_types b l red_proba.r_proba }
	
let subst_args_proba b l (ri_arg, (term_coll, var_coll, red_proba)) =
  let term_coll' = List.map (subst_args_term_coll b l) term_coll in
  let red_proba' = List.map (subst_args_red_proba b l) red_proba in
  (ri_arg, (term_coll', var_coll, red_proba'))
	
let rec find_compos_gen decompos_only allow_bin ((main_var, depinfo) as var_depinfo) simp_facts l0opt t =
  if !Settings.debug_simplif_add_facts then
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
      if !Settings.debug_simplif_add_facts then
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
      let get_dep_info (b,l) =
	if (b == main_var) &&
	  (match l0opt with
	  | None -> true
	  | Some l0 -> Terms.equal_term_lists l0 l)
	then
	  new_depinfo
	else
	  Facts.nodepinfo
      in
      let dependency_anal =
	(Facts.default_indep_test get_dep_info, Facts.no_collision_test)
      in
      let f1 = Facts.apply_reds dependency_anal simp_facts (Terms.make_equal t t') in
      let (find_proba, ac_coll, ac_red_proba) = Proba.get_current_state() in
      assert (find_proba = Zero);
      Proba.restore_state old_proba_state;
      Facts.reduced := old_reduced;
      let r =
	if Terms.is_false f1 then
	  Compos((idx, ([], ac_coll, ac_red_proba)), t, l0opt)
	else
	match find_compos_bin (main_var, new_depinfo) simp_facts l0opt f1 with
	  None -> Any
	| Some((idx', (proba', ac_coll', ac_red_proba')), _, l0opt') ->
	    let image_idx' = (!idx_t', [t'], [], t.t_type, None) in
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
	  let t' = Terms.app f l' in
	  Some(probaf, t', l0opt)

    
let rec dependency_collision_rec cur_array simp_facts get_dep_info t1 t2 t =
  match t.t_desc with
    Var(b,l) when (Terms.is_restr b) && (Proba.is_large_term t) ->
      begin
	let depinfo = get_dep_info (b,l) in
	let bdepinfo = (b,depinfo) in
	let t_simp_ind = remove_dep_array_index bdepinfo t in
	let l_simp_ind =
	  match t_simp_ind.t_desc with
	  | Var(b',l_simp_ind) when b == b' -> l_simp_ind
	  | _ -> assert false
	in
	let t1_simp_ind = remove_dep_array_index bdepinfo t1 in
	match extract_from_status t1_simp_ind (find_compos simp_facts bdepinfo (Some l_simp_ind) t1_simp_ind) with
	  Some(probaf, t1', _) -> 
	    begin
	      try 
		let collect_bargs = ref [] in
		let collect_bargs_sc = ref [] in
		let (t2', t2_eq, dep_types, indep_types) = is_indep_collect_args simp_facts (b,l,depinfo,collect_bargs,collect_bargs_sc) t2 in
	      (* We eliminate collisions because t1 characterizes b[l] and t2 does not depend on b[l],
                 In case b occurs in t2, we reason as follows:
                    1/ When the indices of b in t2 are all different from l, t2 does not depend on b[l].
                       We eliminate collisions under that additional condition, hence the equality 
                       t1 = t2 is false in this case.
                       We collect in collect_bargs the indices l_i of b in t2. Hence the additional
                       condition is &&_(l_i in collect_bargs) l <> l_i. This condition is added
                       as side_condition below.
                    2/ Therefore, we can replace t1 = t2 with 
	               (t1 = t2) && (||_(l_i in collect_bargs) l = l_i),
	               which we rewrite
                       ||_(l_i in collect_bargs) (l = l_i && t1 = t2 { l/l_i }) 
		 *)
		let side_condition = 
		  Terms.make_and_list (List.map (fun l' ->
		    Terms.make_or_list (List.map2 Terms.make_diff l l')
		      ) (!collect_bargs_sc))
		in
	        (* add probability; returns true if small enough to eliminate collisions, false otherwise. *)
		let true_facts = lazy (make_indep_facts simp_facts (b,depinfo) (Facts.true_facts_from_simp_facts simp_facts)) in
		if add_term_collisions (cur_array, true_facts, side_condition) t1' t2' b (Some l_simp_ind) (probaf, dep_types, t2.t_type, indep_types) then
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
  | FunApp(f,l) ->
      Terms.find_some (dependency_collision_rec cur_array simp_facts get_dep_info t1 t2) l
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

   [t] is the term as found in the game before transformation.
   [lhs_instance] is the instance of the LHS of the equivalence used in the transformation.
   When t is a product, it can happen that [lhs_instance] is not equal to [t]
   but to a subproduct of [t].
   *)

let rec get_counted = function
  | [] -> []
  | (a,Counted)::l ->
      a::(get_counted l)
  | _::l ->
      get_counted l
    
let filter_indices lhs_instance true_facts pps above_indices all_indices used_indices =
  let proba_state = Proba.get_current_state() in
  let used_indices' = get_counted used_indices in
  (* Try to remove useless indices using [true_facts] *)
  let initial_indices = order_indices all_indices used_indices' in
  let really_used_indices = filter_indices_coll above_indices [lhs_instance] true_facts used_indices' initial_indices in
  if really_used_indices == initial_indices then
    begin
      (* I removed no index, I can just leave things as they were *)
      Proba.restore_state proba_state;
      (used_indices,
       (lhs_instance, true_facts, pps, 
	above_indices, all_indices, initial_indices, used_indices', used_indices))
    end
  else
    let updated_indices =
      List.map (fun (i,flag) ->
	(i, if flag = Counted && not (List.memq i really_used_indices) then NotCounted else flag)
	  ) used_indices
    in
    (updated_indices, 
     (lhs_instance, true_facts, pps, 
      above_indices, all_indices, initial_indices, used_indices', updated_indices))

(***** Test if two expressions can be evaluated with the same value of *****
       certain indices. 
       (useful for reducing the probabilities in the crypto transformation) 
       For use from cryptotransf.ml.
*)

let rec find_same_type b = function
    [] -> raise Not_found 
  | b''::r ->
      if b''.ri_type == b.ri_type then
	(* relate b to b'' *)
	(b'', r)
      else
	let (bim, rest_r) = find_same_type b r in
	(bim, b''::rest_r)

(* Build a mapping of indices between 2 oracle calls. 
   We always use the same mapping when we want to determine whether 2 oracle
   calls may be executed with the same value of the counted indices
   (below in [is_compatible_indices] and in [Transf_crypto.is_incomp_diffbranch].

   The indices in [above_indices] at the same positions are always equal,
   because we count the number of calls to oracles for each random variable
   whose indices are in [above_indices]: if the random variable is the same,
   then its name is the same and its indices are the same. So we can map
   freely indices in [above_indices] *at the same positions* to each other.

   For counted indices (which do not occur in [above_indices]),
   the mapping must be coherent: 
   - we have the same mapping independently of which oracle call we present 
   first and which second
   - if i is mapped to i'  in the mapping from O1 to O2,
   and i' is mapped to i'' in the mapping from O2 to O3,
   then i must be mapped to i'' in the mapping from O1 to O3.
   This is guaranteed by mapping each counted index to first counted index 
   of the other oracle that is not used yet and has the same type.
   *)
	  
let build_idx_mapping (above_indices1, used_indices1) (above_indices2, used_indices2) =
  let rest_indices = ref (get_counted used_indices2) in
  (* The above indices correspond to the same name table, so they must
     match: the lists [above_indices1] and [above_indices2] have the same length. *)
  let above_indices = List.combine above_indices1 above_indices2 in
  List.map (fun (i, count_flag) ->
    match count_flag with
    | Counted ->
	(* An index that is counted never appears in the [above_indices] *)
	begin
	  try 
	    let (i', rest') = find_same_type i (!rest_indices) in
	    rest_indices := rest';
	    (i, Some i')
	  with Not_found ->
	    (i, None)
	end
    | NotCounted ->
	try
	  if List.exists (fun (t,t') ->
	    Terms.is_repl_index i t && Terms.is_repl_index i t') above_indices then
	    (i, Some i)
	  else
	    let (_,t') = List.find (fun (t,t') ->
	      (Terms.is_repl_index i t) &&
	      (match t'.t_desc with
	      | ReplIndex _ -> true
	      | _ -> false)
		) above_indices in
	    match t'.t_desc with
	    | ReplIndex i' -> (i,Some i')
	    | _ -> (i, None)
	with Not_found ->
	  (i, None)
	) used_indices1

let is_compatible_indices 
    (t1, true_facts1, pps1, above_indices1, all_indices1, _, _, really_used_indices1) 
    (t2, true_facts2, pps2, above_indices2, all_indices2, _, _, really_used_indices2) =
  (*
  print_string "Depanal.is_compatible_indices ";
  Display.display_term t1;
  print_string " with ";
  Display.display_term t2;
  *)
  let proba_state = Proba.get_current_state() in
    (* Find a relation between really_used_indices1 and really_used_indices2 that
       respect types. *)
  if (!Terms.current_bound_ri) != [] then
    Parsing_helper.internal_error "current_bound_ri should be cleaned up (simplify, filter_indices)";
  let mapping = build_idx_mapping (above_indices2, really_used_indices2) (above_indices1, really_used_indices1) in
  List.iter (fun (i, im) ->
    match im with
    | Some i' -> 
	Terms.ri_link i (TLink (Terms.term_from_repl_index i'))
    | None -> 
	let i' = Facts.new_repl_index i in
	Terms.ri_link i (TLink (Terms.term_from_repl_index i'))
	  ) mapping;
  let true_facts2' = List.map (Terms.copy_term Terms.Links_RI) true_facts2 in
  let pps2' = List.map (fun (ppl, args) -> (ppl, List.map (Terms.copy_term Terms.Links_RI) args)) pps2 in
  (* when we bound the replication parameter of an oracle, 
     2 oracles calls need to be counted simultaneously only when the 
     indices of the names above the currently considered replication are the same *)
  let eq_above_idx =
    List.map2 (fun t1 t2 ->
      Terms.make_equal t1 (Terms.copy_term Terms.Links_RI t2)
	) above_indices1 above_indices2
  in
  Terms.ri_cleanup();
  try
    let fact_accu = eq_above_idx @ true_facts1 @ true_facts2' in
    let fact_accu = Incompatible.both_ppl_ppl_add_facts fact_accu pps1 pps2' in
    ignore (Terms.auto_cleanup (fun () -> 
      Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) fact_accu));
    (* The terms t1 and t2 are compatible: they may occur for the same indices *)
    (* print_string " true\n"; *)
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

let add_pp l1 pp2 = 
  if List.exists (Incompatible.is_under pp2) l1 then
    (* If [pp2] is under some [pp1] in [l1] then [pp1 or pp2] is [pp1],
       so no need to add [pp2] *)
    l1
  else
    (* Remove the [pp1] in [l1] such that [pp1] is under [pp2],
       because in this case [pp1 or pp2] is [pp2] *)
    pp2::List.filter (fun pp1 -> not (Incompatible.is_under pp1 pp2)) l1
     
let rec union_pp l1 = function
  | [] -> l1
  | pp2::l2 ->
      union_pp (add_pp l1 pp2) l2

let update_to_length1 l orig_l pp =
  let n =
    match Incompatible.get_facts pp with
    | None -> raise Not_found
    | Some (_,_,_,_,_,_,n) -> n
  in
  let rec aux n =
    match Incompatible.get_facts n.definition_success with
    | None -> raise Not_found
    | Some (cur_array,_,_,_,_,_,n) -> 
	if List.length cur_array == l then
	  n.definition_success
	else if List.length cur_array < l then
	  raise Not_found
	else
	  match n.above_node with
	  | None -> raise Not_found
	  | Some n' -> aux n'
  in
  aux n

let update_to_length l orig_l ppl =
  if l == orig_l then ppl else
  List.fold_left (fun accu pp -> add_pp accu (update_to_length1 l orig_l pp)) [] ppl
    
let find_common_pp accu simp_facts2 (pp1, args1) pps2 =
  let rec find_common_length l1 l2 =
    match (l1,l2) with
    | [], _ | _, [] -> 0
    | t1::l1', t2::l2' ->
	try
	  Facts.match_term_list3 simp_facts2 (fun () -> ()) [t1] [t2] ();
	  1 + find_common_length l1' l2'
	with NoMatch -> 0
  in
  let max_common_length = ref 0 in
  let common_pps = ref [] in
  List.iter (fun ((pp2, args2) as pp_args2) ->
    let common_length = find_common_length (List.rev args1) (List.rev args2) in
    if common_length == (!max_common_length) then
      common_pps := pp_args2 :: (!common_pps)
    else if common_length > (!max_common_length) then
      begin
	max_common_length := common_length;
	common_pps := [pp_args2]
      end
	    ) pps2;
  let args1' = Terms.lsuffix (!max_common_length) args1 in
  try 
    let pp1' = update_to_length (!max_common_length) (List.length args1) pp1 in
    let add pp =
      if not (List.exists (fun pp' -> Incompatible.implies_ppl pp' pp) (!accu)) then
	accu := pp :: (List.filter (fun pp' -> not (Incompatible.implies_ppl pp' pp)) (!accu))
    in
    List.iter (fun (pp2, args2) ->
      try 
	let pp2' = update_to_length (!max_common_length) (List.length args2) pp2 in
	add (union_pp pp1' pp2', args1')
      with Not_found -> ()
	      ) (!common_pps)
  with Not_found -> ()

let find_common_pps simp_facts2 pps1 pps2 =
  let accu = ref [] in
  List.iter (fun pp1 -> find_common_pp accu simp_facts2 pp1 pps2) pps1;
  (* print_string "Links: ";
  List.iter (fun ri ->
    Display.display_repl_index ri;
    print_string " -> ";
    begin
      match ri.ri_link with
      | TLink t -> Display.display_term t
      | _ -> assert false
    end;
    print_newline()
	    ) (!Terms.current_bound_ri);
  print_string "Common pps between\n";
  Display.display_pps pps1;
  print_string "and\n";
  Display.display_pps pps2;
  print_string "Result = \n";
  Display.display_pps (!accu); *)
  !accu
      
let match_oracle_call simp_facts2 
    (t1, true_facts1, pps1, above_indices1, all_indices1, initial_indices1, used_indices1, really_used_indices1) 
    (t2, true_facts2, pps2, above_indices2, all_indices2, initial_indices2, used_indices2, really_used_indices2) =
  
  (*
  print_string "Depanal.match_oracle_call ";
  Display.display_term t1;
  print_string " with ";
  Display.display_term t2;
    *)
  let match_fun next_f t t' () = Facts.match_term_list3 simp_facts2 next_f [t] [t'] () in
  (* Note: we cannot use the facts at oracle1 to help the match succeed.
     First, we would need to use their instance of these facts found by the match
     itself, so that would be more complicated.
     Moreover, for example, if oracle1 is f(x[i]) with known fact x[i] = y[i,j]
     which is not true at oracle2  and oracle2 is f(y[i,j]), with i,j mapped to i,j
     by the matching, oracle2 cannot be considered as an instance of oracle1,
     because oracle1 is counted N times, while oracle2 can be executed
     N N' times (N = bound of i, N' = bound of j).
     (To be precise, to have i,j mapped to i,j, we need to have some other argument of f
     z[i,j] with z[i,j] = z'[i] on both sides, so that the filtering eliminates index j
     even after keeping the common facts.)
     *)
  Terms.auto_cleanup(fun () ->
    try
      Facts.match_term_list3 simp_facts2 (fun () -> 
	let common_facts = find_common match_fun true_facts1 true_facts2 in
	let common_pps = find_common_pps simp_facts2 pps1 pps2 in
	Terms.ri_cleanup();
        (* Check that we can remove the same indices using common_facts as with all facts *)
	let proba_state = Proba.get_current_state() in
	let r1 =
	  let counted_used_indices1 = get_counted really_used_indices1 in
	  ((* Nothing was removed by [filter_indices] so we have nothing to check *)
	  Terms.equal_lists (==) used_indices1 counted_used_indices1) ||
	  ((* Otherwise, redo the removal of indices using [common_facts] *)
	  let really_used_indices1' = filter_indices_coll above_indices1 [t1] common_facts used_indices1 initial_indices1 in
	  Terms.equal_lists (==) counted_used_indices1 really_used_indices1')
	in
	if r1 then
	  begin
	  (*
	  print_string "Depanal.match_oracle_call ";
	  Display.display_term t1;
	  print_string " with ";
	  Display.display_term t2;
	  print_string " succeeds\n";
	  print_string "Common facts:\n";
	  List.iter (fun t ->
	    Display.display_term t; print_newline()) common_facts;
	  *)
	    Some (t1, common_facts, common_pps, above_indices1, all_indices1, initial_indices1, used_indices1, really_used_indices1)
	  end
	else
	  begin
	  (*
          print_string "Depanal.match_oracle_call ";
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
	    ) (above_indices1 @ [t1]) (above_indices2 @ [t2]) ()
	(* Match the [above_indices] first to increase the chances of finding
	   the right indices at the first try *)
    with NoMatch ->
      (* 
      print_string "Depanal.match_oracle_call ";
      Display.display_term t1;
      print_string " with ";
      Display.display_term t2;
      print_string " fails\n";
      print_string "True facts 2:\n";
      List.iter (fun t ->
	 Display.display_term t; print_newline()) true_facts2;
      print_string "simp_facts:\n";
      Facts.display_facts simp_facts; *)
      None
    )
