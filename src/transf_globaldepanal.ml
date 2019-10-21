open Types

(* Find all variables that depend on a certain variable [b0], provided
   these variables are not output (raises BadDep when some
   of these variables may be output)

   When tests depend on these variables, they must be simplified (by
   eliminating collisions that have a negligible probability) into
   tests that do not depend on these variables (otherwise, it raises BadDep).

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

let whole_game = ref Terms.empty_game

(* The main variable on which we perform the dependency analysis (b0) *)
let main_var = ref (Terms.create_binder0 "dummy" Settings.t_bitstring [])

type probaf_total =
  | Unset
  | InProgress
  | Set of find_compos_probaf
    
(* List of variables that depend on the main variable b0.
   The list contains elements (b, (depend_status, args_opt, ([(t1,t2,probaf);...], ref probaf_total))) 
   meaning that b depends on b0, 
   - [depend_status] is its dependency status (see [depend_status] in types.ml)
   - When args_opt is (Some l), b[args_at_creation] depends on b0[l]
     and on no other cell of b0.
     When args_opt is None, b may depend on any cell of b0.
   - The list [(t1,t2,probaf);...] contains one entry for each definition of [b] (by an assignment,
     when the status of [b] is not [Any]):
     [t1] is the term stored in [b]
     [t2] is [b] itself.
     [probaf] is an upper bound on the probability of collision 
     between [t1] and a term independent of [b0].
   - [probaf_total] is an upper bound on the probability of collision 
     between [b[...]] and a term independent of [b0].
     (It is set by [compute_probas()] when the list [dvar_list] is stable,
     when the status of [b] is not [Any].)

   Corresponds to the field "dep" in `a depinfo *)
let dvar_list = ref ([]: (binder * (depend_status * term list option * ((term * term * find_compos_probaf) list * probaf_total ref))) list)

(* The flag [dvar_list_changed] is set when [dvar_list] has been changed
   since the last iteration. A new iteration of dependency analysis 
   is then needed. *)
let dvar_list_changed = ref false

(* List of variables known to be defined at some point *)
let defvar_list = ref ([]: binder list)

(* The flag [defvar_list_changed] is set when [defvar_list] has been
   changed since the last iterattion. A new iteration of dependency analysis
   is then needed. *)
let defvar_list_changed = ref false

(* The flag [local_changed] is set when the dependency analysis
   managed to simplify the game *)
let local_changed = ref false

(* The flag [defined_condition_update_needed] is set when the dependency analysis
   modified a term is such a way that a defined condition
   of a previous find may need to be updated. *)
let defined_condition_update_needed = ref false

(* Advised instructions *)
let advise = ref []

(* [add_advice_sarename b] adds [SArenaming b] to the list
   of advised instructions [advise] *)

let add_advice_sarename b =
  if Settings.occurs_in_queries b (!whole_game).current_queries then
    ()
  else if !Settings.no_advice_globaldepanal then 
    begin
      print_string "Manual advice: ";
      Display.display_instruct (SArenaming b);
      print_newline()
    end
  else
    advise := Terms.add_eq (SArenaming b) (!advise)

(* This exception is raised when the global dependency analysis fails *)
exception BadDep

type branch = Unreachable | OnlyThen | OnlyElse | BothDepB | BothIndepB of term

(* [expand_probaf f probaf] replaces [ProbaIndepCollOfVar b] with 
   the corresponding actual probability, computed by calling [f b]. *)

let expand_probaf f (ri_arg, (ac_term_coll0, ac_var_coll0, ac_red_proba0)) =
  let all_coll' =
    List.fold_left (fun (ac_term_coll, ac_var_coll, ac_red_proba) term_coll ->
      match term_coll with
      | Fixed _ -> (term_coll ::  ac_term_coll, ac_var_coll, ac_red_proba)
      | ProbaIndepCollOfVar(b, args, ri_list) ->
	  let probaf_b = f b in
	  let (ri_arg', all_coll1) = Depanal.subst_args_proba b args probaf_b in
	  let image = (ri_list,[], Settings.t_bitstring (*dummy type*), None) in
	  let (ac_term_coll1, ac_var_coll1, ac_red_proba1) =
	    Depanal.subst_idx_proba ri_arg' image all_coll1
	  in
	  (ac_term_coll1 @ ac_term_coll, ac_var_coll1 @ ac_var_coll, ac_red_proba1 @ ac_red_proba)
      ) ([], ac_var_coll0, ac_red_proba0) ac_term_coll0
  in
  (ri_arg, all_coll')

(* [find_compos_probaf_sum l] returns a structure [find_compos_probaf] 
   representing the sum of the elements of [l], which is a list
   of [find_compos_probaf]. *)
    
let find_compos_probaf_sum l =
  let ri_arg = Depanal.fresh_repl_index() in
  let image = ([ri_arg],[], Settings.t_bitstring (*dummy type*), None) in 
  let all_coll' = 
    List.fold_left (fun (ac_term_coll, ac_var_coll, ac_red_proba) (ri_arg1, all_coll1) ->
      let (ac_term_coll1, ac_var_coll1, ac_red_proba1) =
	Depanal.subst_idx_proba ri_arg1 image all_coll1
      in
      (ac_term_coll1 @ ac_term_coll, ac_var_coll1 @ ac_var_coll, ac_red_proba1 @ ac_red_proba)
	) ([],[],[]) l
  in
  (ri_arg, all_coll')
    
(* [compute_probas()] computes the probabilities associated with each
   [ProbaIndepCollOfVar b], for [b] in [dvar_list] *)

let compute_probas() =
  List.iter (fun (b, (_, _, (_, probaf_total_ref))) ->
    probaf_total_ref := Unset) (!dvar_list);
  let rec aux b =
    let (_,_,(_,probaf_total_ref)) as bval = List.assq b (!dvar_list) in
    aux_val bval;
    match !probaf_total_ref with
    | Set p -> p
    | _ -> Parsing_helper.internal_error "probability should be set"
	  
  and aux_val (st,_,(proba_info_list, probaf_total_ref)) =
    if st = Any then
      assert (!probaf_total_ref = Unset)
    else
      match !probaf_total_ref with
      | InProgress ->
	  print_string "Loop in variable dependencies.\n";
	  raise BadDep
      | Set _ -> ()
      | Unset ->
	  probaf_total_ref := InProgress;
	  let res =
	    find_compos_probaf_sum (List.map (fun (_,_,probaf) ->
	      expand_probaf aux probaf) proba_info_list)
	      (* Note that in case the sum contains several
		 identical collisions, they will be merged,
		 since they are registered as independent collisions.
		 I think a maximum instead of a sum would be also correct:
		 different definitions for the same variable
		 imply different values of indices,
		 so we never have two different collisions for the same 
		 terms and indices.*)
	  in
	  probaf_total_ref := Set res
  in
  List.iter (fun (b, bval) -> aux_val bval) (!dvar_list)

(* [get_val b] returns the probability corresponding to 
   [ProbaIndepCollOfVar b]. It works only after having called
   [compute_probas()]. *)
    
let get_val b =
  let (_,_,(_,probaf_total_ref)) as bval = List.assq b (!dvar_list) in
  match !probaf_total_ref with
  | Set p -> p
  | _ -> Parsing_helper.internal_error "probability should be set"
 

(* [add_collisions_for_current_check_dependency (cur_array, true_facts, facts_info) (t1,t2,probaf)] 
   takes into account the probability of collision between [t1] and [t2]. 
   [probaf] is an upper bound on the probability of collision 
   between [t1] and [t2], for one execution.
   [true_facts] and [facts_info] indicate facts that are known to be true.
   These facts are used to optimize the computation of the probability
   (to get a smaller probability).
   [add_collisions_for_current_check_dependency] raises [BadDep] when the 
   obtained probability is too large, so this collision cannot be eliminated. *)

let add_collisions_for_current_check_dependency (cur_array, true_facts, facts_info) (t1,t2,probaf,dep_types,full_type,indep_types) =
  match dep_types with
  | [ty] when ty == full_type -> false (* Quickly eliminate a case in which the probability will always be too large: the term [t2] can take any value depending of [b] *)
  | _ -> 
  (* If [dvar_list] has changed, we are going to iterate any way,
     no need to compute probabilities. Furthermore, the probabilities 
     in [dvar_list] may not be all set, possibly leading to an error
     in [expand_probaf get_val probaf]. *)
  if !dvar_list_changed then true else
  let (idx, all_coll) as probaf' = expand_probaf get_val probaf in
  (* Compute the used indices *)
  let idx_t2 = ref [] in
  Proba.collect_array_indexes idx_t2 t2;
  let image_idx = (!idx_t2, dep_types, full_type, indep_types) in
  let (proba_term_collisions', proba_var_coll', proba_collision') =
    Depanal.subst_idx_proba idx image_idx all_coll
  in
  try
    let true_facts' = 
      (* We optimize the speed of the system by not computing
	 [true_facts'] when the probability of collision
	 is small enough that it can be accepted without 
	 trying to eliminate some of the [used_indices].
	 (The facts in [true_facts'] are used only for that.) *)
      if
	(List.for_all (function
	  | Fixed probaf_mul_types -> Proba.is_small_enough_coll_elim probaf_mul_types
	  | ProbaIndepCollOfVar _ -> Parsing_helper.internal_error "ProbaIndepCollOfVar should have been instantiated by expand_probaf")
	   proba_term_collisions') &&
	(List.for_all (fun (_,_,_,probaf_mul_types) -> Proba.is_small_enough_coll_elim probaf_mul_types)
	   proba_collision')
      then
	[]
      else
	true_facts @ (Facts.get_facts_at facts_info) 
    in
    let proba_info = (probaf', dep_types,full_type,indep_types) in
    Depanal.add_term_collisions (cur_array, true_facts', [], Terms.make_true()) t1 t2 (!main_var) None proba_info
  with Contradiction ->
    true

(* [add_collisions_for_current_check_dependency2] is similar to
   [add_collisions_for_current_check_dependency].
   Three differences:
   - In [add_collisions_for_current_check_dependency], the known facts come both from
   [true_facts] and [facts_info], and a list of known facts must be computed from that.
   In [add_collisions_for_current_check_dependency2] the known facts are already computed
   in [true_facts].
   - In [add_collisions_for_current_check_dependency], any cell of [b0] may be 
   characterized by [t1] (i.e., for any term M that is independent of all cells
   of [b0], the probability of collision between M and [t1] is bounded by [probaf]).
   In [add_collisions_for_current_check_dependency2], the particular cell of [b0]
   characterized by [t1] may be indicated by [index_opt] (i.e., when [index_opt = Some l],
   for any term M that is independent of [b0[l]], the probability of collision 
   between M and [t1] is bounded by [probaf]). [side_condition] indicates
   a condition needed to make sure that [t2] does not depend on this particular cell [b0[l]] of [b0].
   - [add_collisions_for_current_check_dependency2] returns [true] when the probability of
   collision is small enough so that the collision can be eliminated, and [false]
   otherwise. *)

let add_collisions_for_current_check_dependency2 cur_array true_facts side_condition (t1,t2,probaf) index_opt =
  (* If [dvar_list] has changed, we are going to iterate any way,
     no need to compute probabilities. Furthermore, the probabilities 
     in [dvar_list] may not be all set, possibly leading to an error
     in [expand_probaf get_val probaf]. *)
  if !dvar_list_changed then true else
  let probaf' = expand_probaf get_val probaf in
  Depanal.add_term_collisions (cur_array, true_facts, [], side_condition) t1 t2 (!main_var) index_opt (probaf',[],t2.t_type,Some [t2.t_type])

(* [depends t] returns [true] when [t] may depend on [b0] *)

let depends t = 
  List.exists (fun (b, _) -> Terms.refers_to b t) (!dvar_list)

(* [defined t] returns [true] when [t] may be defined *)

let rec defined t =
  match t.t_desc with
    FunApp(f,l) -> List.for_all defined l
  | Var(b,l) ->
      (List.memq b (!defvar_list)) &&
      (List.for_all defined l)
  | ReplIndex _ -> true
  | _ -> Parsing_helper.internal_error "Only Var/FunApp/ReplIndex should appear in Transf_globaldepanal.defined"

(* [defined_br (b,l)] returns [true] when [b[l]] may be defined *)

let defined_br (b,l) =
  (List.memq b (!defvar_list)) &&
  (List.for_all defined l)

(* [add_defined b] adds the variable [b] to the list of defined variables

   Note: the variables defined inside terms in conditions of find
   must not have array accesses. Hence, I do not need to scan these
   terms to add their bound variables to the list of defined variables. *)

let add_defined b =
  if not (List.memq b (!defvar_list)) then
    begin
      defvar_list := b :: (!defvar_list);
      defvar_list_changed := true
    end

(* [add_defined_pat pat] adds all variables bound by the pattern [pat] 
   to the list of defined variables *)

let rec add_defined_pat = function
    PatVar b -> add_defined b
  | PatTuple(f,l) -> List.iter add_defined_pat l
  | PatEqual _ -> ()

(* [should_try_find_compos t] returns [true] when it may be possible
   to bound the probability of collision between [t] and terms
   independent from [b0], using [FindCompos.find_compos]. It makes a quick 
   test before calling [FindCompos.find_compos] which is more costly,
   to speed up the implementation. *)
	
let rec should_try_find_compos t =
  match t.t_desc with
  | Var(b,l) ->
      begin
        try
          let (st,_,_) = List.assq b (!dvar_list) in
	  st != Any
	with Not_found -> false
      end
  | FunApp(_,l) ->
      List.exists should_try_find_compos l
  | _ -> false

(* [current_bdepinfo()] returns the current dependency information,
   computed from [main_var] and [dvar_list] *)
	
let current_bdepinfo() =
  ((!main_var), { args_at_creation_only = false;
		  dep = (!dvar_list);
		  other_variables = false;
		  nodep = [] })
	
(* [find_compos t] returns the dependency status of the term
   [t] with respect to the variable [b0 = !main_var].
   It is returned in 2 forms, so that the result is a pair,
   [(st, extracted_st)]:
   [st] is the dependency status as defined in [depend_status] in types.ml
   [extracted_st] is the extracted dependency status as defined in 
   [extracted_depend_status] in types.ml *)
	
let find_compos simp_facts t =
  if should_try_find_compos t then
    let bdepinfo = current_bdepinfo() in
    let t' = Depanal.remove_dep_array_index bdepinfo t in (* Mostly for safety since no array variable should depend on (!main_var) *)
    let st = Depanal.find_compos simp_facts bdepinfo None t' in
    (st, Depanal.extract_from_status t' st)
  else
    (Any, None)


(* [is_indep t] returns a triple 
   [(t', dep_types, indep_types)] where 
   - [t'] is a term independent of [b0] in which some array 
   indices in [t] may have been replaced with
   fresh replication indices, and some other subterms of [t] 
   may have been replaced with variables [?].
   - [dep_types] is the list of types of subterms of [t]
   replaced with variables [?], so that the number of values
   that [t] can take depending on [b0] is at most 
   the product of |T| for T \in dep_types (ignoring replication
   indices).
   - [indep_types] is the list of types of subterms of [t]
   not replaced with variables [?]. This list is valid only
   when [trust_size_estimates] is not set. In this case, 
   subterms of [t] are replaced only under [data] functions,
   so that 
   product of |T| for T \in dep_types <= |type(t)|/product of |T| for T \in indep_types *)
let is_indep t =
  Depanal.is_indep Terms.simp_facts_id (current_bdepinfo()) t
      
(* [is_indep_pat] is similar to [is_indep] but for patterns.
   It converts the pattern into a term, replacing all 
   variables bound by the pattern with [?]. *)
let is_indep_pat pat =
  Depanal.is_indep_pat Terms.simp_facts_id (current_bdepinfo()) pat

(* This exception is raised by [get_dep_indices] when [t] actually depends on [b0]
   for unspecified indices *)
exception Depends

(* [get_dep_indices collect_bargs t] collects in [collect_bargs] the
   indices of [b0] such that [t] depends on the values of [b0] only at
   the indices in [collect_bargs]. If it is impossible to find such
   [collect_bargs], it raises Depends. *)

let rec get_dep_indices collect_bargs t =
  match t.t_desc with
    FunApp(f,l) -> List.iter (get_dep_indices collect_bargs) l
  | ReplIndex(b) -> ()
  | Var(b,l) ->
      begin
        (* Index variables cannot depend on [b0].
	   For safety, I verify that. *)
	List.iter (fun t' ->
	  assert (not(depends t'))
	    ) l;
        try
          let (_,depend_args_opt,_) = List.assq b (!dvar_list) in
	  match depend_args_opt with
	    Some b0_ind ->
	      (* b[args_at_creation] depends only on b0[b0_ind] *)
	      let l' = List.map (Terms.subst b.args_at_creation l) b0_ind (* b0_ind{l/b.args_at_creation} *) in
              (* The access to b[l] depends only on b0[l'],
                 while the other term of the equality characterizes b0[l0] *)
	      if not (List.exists (List.for_all2 Terms.equal_terms l') (!collect_bargs)) then
		collect_bargs := l' :: (!collect_bargs)
	  | _ -> raise Depends
        with Not_found ->
	  ()
      end
  | _ -> Parsing_helper.internal_error "If/let/find/new unexpected in get_dep_indices"

(* [dependency_collision cur_array true_facts t1 t2] simplifies [t1 = t2]
using dependency analysis. Basically, when [t1] characterizes a part of [b0]
(i.e. for all terms M independent of [b0], the probability of collision between
[t1] and M is bounded negligibly)
and [t2] does not depend on [b0], the equality has a negligible probability
to hold, so it can be simplified into [false]. 
[dependency_collision] extends this simplification to the case in which
[t1] characterizes a part of a certain cell of [b0] and [t2] does not depend
on that cell, possibly by adding assumptions that certain array indices are different.
It returns
- [Some t'] when it simplified [t1 = t2] into [t'];
- [None] when it could not simplify [t1 = t2]. 
[cur_array] is the list of current replication indices at [t1 = t2].
[true_facts] is a list of facts that are known to hold.
 *)

let dependency_collision cur_array simp_facts t1 t2 =
  match find_compos simp_facts t1 with
  | _, Some(probaf, t1', charac_args_opt) ->
      begin
	try 
	  match charac_args_opt with
	  | Some b0_ind ->
	      (* t1 characterizes b0[b0_ind] *)
	      let collect_bargs = ref [] in
	      get_dep_indices collect_bargs t2;
	      if List.exists (List.for_all2 Terms.equal_terms b0_ind) (!collect_bargs) then
	        (* If t2 depends on b0[b0_ind], we cannot eliminate collisions *)
		None
	      else
		let side_condition = 
		  Terms.make_and_list (List.map (fun l'' ->
		    Terms.make_or_list (List.map2 Terms.make_diff b0_ind l'')
		      ) (!collect_bargs))
		in
	        (* add probability; returns true if small enough to eliminate collisions, false otherwise. *)
		let true_facts = Facts.true_facts_from_simp_facts simp_facts in
	        if add_collisions_for_current_check_dependency2 cur_array true_facts side_condition (t1',t2,probaf) charac_args_opt then
		  let res = 
		    Terms.make_or_list (List.map (fun l'' ->   
		      let t2'' = Terms.replace l'' b0_ind t2 in
		      Terms.make_and (Terms.make_and_list (List.map2 Terms.make_equal b0_ind l'')) (Terms.make_equal t1 t2'')
			) (!collect_bargs))
		  in
		      (*print_string "Simplified ";
		      Display.display_term t1;
		      print_string " = ";
		      Display.display_term t2;
		      print_string " into ";
		      Display.display_term res;
		      print_newline();*)
		  Some res
		else
		  None
	  | None -> 
	      (* b[args_at_creation] characterizes b0 for some unknown indices *)
	      let collect_bargs = ref [] in
	      get_dep_indices collect_bargs t2;
              if !collect_bargs != [] then
                (* if [t2] depends on [b0], the dependency analysis fails to
		   eliminate the required collisions *)
		None
	        (* add probability; returns true if small enough to eliminate collisions, false otherwise. *)
	      else
		let true_facts = Facts.true_facts_from_simp_facts simp_facts in
		if add_collisions_for_current_check_dependency2 cur_array true_facts (Terms.make_true()) (t1',t2,probaf) None then
		begin
		      (*print_string "Simplified ";
		      Display.display_term t1;
		      print_string " = ";
		      Display.display_term t2;
		      print_string " into false\n";*)
		  Some (Terms.make_false())
		end
	      else
		None
	with Depends -> None
      end
  | _, None -> None


(* [dependency_anal cur_array = (indep_test, collision_test)]

[collision_test simp_facts t1 t2] simplifies [t1 = t2] using dependency 
analysis.
It returns
- [Some t'] when it simplified [t1 = t2] into [t'];
- [None] when it could not simplify [t1 = t2]. 
[cur_array] is the list of current replication indices at [t1 = t2].
[simp_facts] contains facts that are known to hold. 

[indepTest t (b,l)] 
returns [Some (t', side_condition)] when [t'] is a term obtained from [t] 
by replacing array indices that depend on [b[l]] with fresh indices.
[t'] does not depend on [b[l]] when [side_condition] is true.
Returns [None] if that is not possible.
*)

let dependency_anal cur_array = 
  let indep_test simp_facts t (b,l) =
    let result = 
      (* [b] must be a restriction. The only case in which we have information 
	 is when [b] is [b0] ([main_var]). *)
      if b != (!main_var) then None else
      if List.exists depends l then None else
      begin
	try 
	  let collect_bargs = ref [] in
	  get_dep_indices collect_bargs t;
	  if List.exists (List.for_all2 Terms.equal_terms l) (!collect_bargs) then
	  (* t depends on b0[l] *)
	    raise Depends;
	  Some (t, if (!collect_bargs) == [] then NoSideCond else SideCondFixed(l, (!collect_bargs)))
	with Depends -> None
      end
    in
    if result = None then
      Facts.default_indep_test Facts.nodepinfo simp_facts t (b,l)
    else
      result
  in
  let collision_test simp_facts t1 t2 =
    let t1' = Terms.try_no_var_rec simp_facts t1 in
    let t2' = Terms.try_no_var_rec simp_facts t2 in
    match dependency_collision cur_array simp_facts t1' t2' with
      (Some _) as x -> x
    | None -> dependency_collision cur_array simp_facts t2' t1'
  in
  (indep_test, collision_test)
    
(* [almost_indep_test cur_array true_facts fact_info t] 
   checks that the result of test [t] does not depend on 
   variables in [dvar_list], up to negligible probability.
Returns
- Unreachable when the term t is in fact unreachable
- BothDepB when the result may depend on variables in [dvar_list];
- OnlyThen when the test is true with overwhelming probability;
- OnlyElse when the test is false with overwhelming probability;
- BothIndepB t' when the result does not depend on variables in [dvar_list] and is equal to [t']. 
[cur_array] is the list of current replication indices at [t].
[true_facts] is a list of facts that are known to be true,
because [t] occur in a conjunction or disjunction, so it is
evaluated only when the facts in [true_facts] are true.
[fact_info] indicates the true facts and defined variables at [t].
*)

let to_term = function
    Unreachable -> raise Contradiction
  | OnlyThen -> Terms.make_true()
  | OnlyElse -> Terms.make_false()
  | BothIndepB t -> t
  | BothDepB -> raise BadDep
	
let rec almost_indep_test cur_array true_facts fact_info t =
  match t.t_desc with
    FunApp(f,[t1;t2]) when f == Settings.f_and ->
      begin
	let t2res = almost_indep_test cur_array (t1::true_facts) fact_info t2 in
	let t1res = match t2res with
	  OnlyElse -> 
            (* t2 is always false, the value of t1 does not matter *) 
	    BothDepB
	| Unreachable | OnlyThen -> 
	    (* I have eliminated a collision in t2 using the fact that t1 is true,
	       I won't assume t2 when analyzing t1 *)
	    almost_indep_test cur_array true_facts fact_info t1
	| BothDepB ->
	    (* I did not eliminate any collision when analyzing t2,
	       I can swap the "and" and assume t2 when analyzing t1 *)
	    almost_indep_test cur_array (t2::true_facts) fact_info t1
	| BothIndepB t2' ->
	    (* I can swap the "and" after simplification of t2
	       and assume t2' when analyzing t1 *)
	    almost_indep_test cur_array (t2'::true_facts) fact_info t1
	in
	match (t1res, t2res) with
	  (Unreachable, _) | (_, Unreachable) -> OnlyElse
             (* t1 is unreachable when t2 is true, so t2 is false *) 
	| (OnlyElse, _) | (_, OnlyElse) -> OnlyElse
	| (OnlyThen, x) -> x
	| (x, OnlyThen) -> x
	| (BothDepB, _) | (_, BothDepB) -> BothDepB
	| (BothIndepB t1, BothIndepB t2) -> BothIndepB(Terms.make_and t1 t2)
      end
  | FunApp(f,[t1;t2]) when f == Settings.f_or ->
      begin
	let t2res = almost_indep_test cur_array ((Terms.make_not t1)::true_facts) fact_info t2 in
	let t1res = match t2res with
	  Unreachable | OnlyElse -> 
	    (* I have eliminated a collision in t2 using the fact that t1 is false,
	       I won't assume (not t2) when analyzing t1 *)
	    almost_indep_test cur_array true_facts fact_info t1
	| OnlyThen ->
	    (* t2 is always true, the value of t1 does not matter *)
	    BothDepB
	| BothDepB ->
	    (* I did not eliminate any collision when analyzing t2,
	       I can swap the "or" and assume (not t2) when analyzing t1 *)
	    almost_indep_test cur_array ((Terms.make_not t2)::true_facts) fact_info t1
	| BothIndepB t2' ->
	    (* I can swap the "or" after simplification of t2
	       and assume (not t2') when analyzing t1 *)
	    almost_indep_test cur_array ((Terms.make_not t2')::true_facts) fact_info t1
	in
	match (t1res, t2res) with
	  (Unreachable, _) | (_, Unreachable) -> OnlyThen
	| (OnlyThen, _) | (_, OnlyThen) -> OnlyThen
	| (OnlyElse, x) -> x
	| (x, OnlyElse) -> x
	| (BothDepB, _) | (_, BothDepB) -> BothDepB
	| (BothIndepB t1, BothIndepB t2) -> BothIndepB(Terms.make_or t1 t2)
      end
  | FunApp(f,[t1]) when f == Settings.f_not ->
      begin
	match almost_indep_test cur_array true_facts fact_info t1 with
	  Unreachable -> Unreachable
	| OnlyThen -> OnlyElse
	| OnlyElse -> OnlyThen
	| BothDepB -> BothDepB
	| BothIndepB t' -> BothIndepB (Terms.make_not t')
      end
(* Be careful: do not use or-patterns with when: 
   If both patterns of the or succeed but the when clause fails for the 
   first one and succeeds for the second one, Caml considers that the
   match fails.
*)
  | FunApp(f,[t1;t2]) 
    when ((f.f_cat == Equal) || (f.f_cat == Diff)) && (Proba.is_large_term t1 || Proba.is_large_term t2) ->
      begin
	match find_compos Terms.simp_facts_id t1 with
	| _, Some(probaf,t1',_) ->
	    let (t2', dep_types, indep_types) = is_indep t2 in 
	    if add_collisions_for_current_check_dependency (cur_array, true_facts, fact_info) (t1', t2', probaf, dep_types, t2.t_type, indep_types) then
	      begin
		local_changed := true;
		if (f.f_cat == Diff) then OnlyThen else OnlyElse
	      end
	    else
	      BothDepB
	| _, None ->
	    match find_compos Terms.simp_facts_id t2 with
	    | _, Some(probaf,t2',_) ->
		let (t1', dep_types, indep_types) = is_indep t1 in
		if add_collisions_for_current_check_dependency (cur_array, true_facts, fact_info) (t2', t1, probaf, dep_types, t2.t_type, indep_types) then
		  begin
		    local_changed := true;
		    if (f.f_cat == Diff) then OnlyThen else OnlyElse
		  end
		else
		  BothDepB
	    | _, None ->
		if depends t then 
		  BothDepB
		else
		  BothIndepB t
      end
  | _ ->
      if Terms.is_false t then
	OnlyElse
      else if Terms.is_true t then
	OnlyThen
      else if depends t then 
	BothDepB 
      else
	BothIndepB t

(* [almost_indep_test cur_array t] 
   checks that the result of test [t] does not depend on 
   variables in [dvar_list], up to negligible probability.
Returns
- BothDepB when the result may depend on variables in [dvar_list];
- OnlyThen when the test is true with overwhelming probability;
- OnlyElse when the test is false with overwhelming probability;
- BothIndepB t' when the result does not depend on variables in [dvar_list] and is equal to [t']. 
[cur_array] is the list of current replication indices at [t].
*)

let almost_indep_test cur_array t =
  (* Call a fast version of almost_indep_test first. *)
  let res = almost_indep_test cur_array [] (DTerm t) t in
  if res != BothDepB then res else
  (* In case this version is not sufficient to eliminate the dependency,
     use a more costly and more precise version *)
  try
    let true_facts = Facts.get_facts_at (DTerm t) in
    let simp_facts = Facts.simplif_add_list (dependency_anal cur_array) ([],[],[]) true_facts in
    let t' = Facts.simplify_term (dependency_anal cur_array) simp_facts t in
    (*print_string ("At " ^ (string_of_int t.t_occ) ^ ", the term ");
    Display.display_term t;
    print_string " is simplified into ";
    Display.display_term t';
    print_newline();*)
    if Terms.is_true t' then 
      OnlyThen
    else if Terms.is_false t' then
      OnlyElse
    else if depends t' then
      BothDepB
      (*begin
	print_string ("At " ^ (string_of_int t.t_occ) ^ ", the term ");
	Display.display_term t;
	if Terms.synt_equal_terms t t' then
	  print_string (" depends on " ^ (Display.binder_to_string (!main_var)) ^ "\n")
	else
	  begin
	    print_string " is simplified into ";
	    Display.display_term t';
	    print_string (", but still depends on " ^ (Display.binder_to_string (!main_var)) ^ "\n")
	  end;
	BothDepB
      end*)
    else
      BothIndepB (Terms.move_occ_term t')
  with Contradiction ->
    (* The term [t] is in fact unreachable *)
    Unreachable


(* [aux_dep_args t] must be called with a term [t] that depends on [b0].
   It returns [Some l] when [t] depends only on [b0[l]].
   It returns [None] when it is unable to compute such as [l]. *)
      
let aux_dep_args t =
  let collect_bargs = ref [] in
  try
    get_dep_indices collect_bargs t;
    match !collect_bargs with
      [l] -> Some l (* [t] depends only on [b0[l]] *)
    | [] -> Parsing_helper.internal_error "aux_dep_args t called with t independent of b0!"
    | _ -> None
  with Depends -> None
      
(* [set_depend b t] adds the information in [dvar_list] to record that 
   [b] is defined as [t], by [let b = t in ...] in a LetE term in a find condition.
   Since variables defined in conditions of find have no array accesses,
   we know that accesses to b in the body of the let will use only the definition
   [b = t], so we need not combine that definition of [b] with definitions of [b]
   that may occur elsewhere. *)

let set_depend b t =
  let dvar_list_nob = List.filter (fun (b',_) -> b' != b) (!dvar_list) in
  match find_compos Terms.simp_facts_id t with
  | _,None -> 
      if depends t then
	(* The variable [b] depends on [b0], but we do not have more precise information *)
	dvar_list := (b, (Any, aux_dep_args t, ([], ref Unset))) :: dvar_list_nob
      (* When [t] does not depend on [b0], we have nothing to do *)
  | st, Some(probaf, t1, _) -> 
      (* [t] characterizes a part of [b0] *)
      let t2 = Terms.term_from_binder b in
          (*print_string "Adding ";
            Display.display_binder b;
            print_newline();*)
      let b_st =  (b,(st, aux_dep_args t, ([t1, t2, probaf], ref Unset))) in
      dvar_list := b_st :: dvar_list_nob

(* [add_indep b] adds the information that there is a definition of
   [b] that does not depend on [b0]. When there is another definition
   of [b] that depends on [b0], we lose the information on the precise
   dependency of [b] from [b0]. *) 

let add_indep b =
  try 
    let ((st',depend_args_opt,_), dvar_list_nob) = Terms.assq_rest b (!dvar_list) in
    if st' != Any then
      begin
	add_advice_sarename b;
	dvar_list_changed := true;
	dvar_list := (b, (Any, depend_args_opt, ([], ref Unset))) :: dvar_list_nob
      end
  with Not_found ->
    ()

(* [combine_options b opt_old opt_new] combines optional values 
   [opt_old], [opt_new] obtained from several definitions of [b],
   where the optional values have the following meaning:
   - [None] means any value
   - [Some l] (where [l] is a list of terms) means that the value
   is known to be [l].
   Hence, two different values yield [None],
   and [Some l] combined with itself is unchanged.
   [dvar_list_changed] is set when the result is not equal
   to the old value [opt_old]. *)
      
let combine_options b opt_old opt_new =
  match opt_old, opt_new with
    Some l1, Some l2 ->
      if List.for_all2 Terms.equal_terms l1 l2 then opt_old else
      begin
	(* SArenaming b may allow to keep explicit indices characterized by [b] or on which [b] depends *)
	add_advice_sarename b;
	dvar_list_changed := true;
	None
      end
  | None, _ -> opt_old
  | _ -> 
      dvar_list_changed := true;
      None

(* [add_proba_info one_info proba_info_list] adds [one_info] to [proba_info_list].
   It tests whether [one_info] is already contained in [proba_info_list],
   if not, it adds it and sets [dvar_list_changed]. *)

let display_find_compos_probaf (ri_arg, (ac_term_coll, ac_var_coll, ac_red_proba)) =
  print_string "Index of independent term: "; Display.display_repl_index ri_arg; print_newline();
  print_string "Term collisions:\n";
  List.iter (function
    | Fixed probaf_mul_types -> ignore (Proba.proba_for probaf_mul_types)
    | ProbaIndepCollOfVar(b, args, ri) ->
	print_string "Indep. coll of ";
	Display.display_var b args;
	print_string " ";
	Display.display_list Display.display_repl_index ri;
	print_newline()) ac_term_coll;
  print_string "Variable collisions:\n";
  List.iter (fun (b1,b2) ->
    print_string " ";
    ignore (Proba.proba_for_collision b1 b2)
      ) ac_var_coll;
  print_string "Application of collision statements:\n";
  List.iter (fun red_proba ->
    print_string " ";
    ignore (Proba.proba_for_red_proba red_proba)
      ) ac_red_proba
    
let display_proba_info (t1, t2, probaf) =
  Display.display_term t1;
  print_string ", ";
  Display.display_term t2;
  print_string ", ";
  print_newline();
  display_find_compos_probaf probaf

let add_proba_info proba_info proba_info_list =
  if not (List.exists (fun proba_info' ->
    Depanal.matches_proba_info proba_info' proba_info) proba_info_list)
  then
    begin
      (* Above, I use "matches_pair" to check that t1 = t2 is
         a particular case of the assignment t1' = t2' seen before.
         If this is true, I have nothing to add.
         (Testing equality (t1,t2) = (t1',t2') is not exactly 
	 what we want because these terms may contain wildcards "?") 
      print_string " Already present: ";
      List.iter display_proba_info proba_info_list;
      print_string "Adding: ";
      display_proba_info proba_info;
	      *)
      dvar_list_changed := true;
      proba_info :: proba_info_list
    end
  else
    proba_info_list
      
(* [add_depend b t] adds the information in [dvar_list] to record that 
   [b] is defined as [t], by [let b = t in ...].
   Sets [dvar_list_changed] if needed. *)

let find_compos_proba_of_coll_var b = 
  let ri = Depanal.fresh_repl_index() in
  (ri, ([ProbaIndepCollOfVar(b, List.map Terms.term_from_repl_index b.args_at_creation, [ri])],[],[]))
      
let add_depend b t =
  match find_compos Terms.simp_facts_id t with
  | new_st, Some (probaf,t1,new_charac_args_opt) ->
      (* [t] characterizes a part of [b0] *)
      let t2 = Terms.term_from_binder b in
      let new_depend_args_opt = aux_dep_args t in
      begin
	try 
	  let ((st,depend_args_opt,(proba_info_list, probaf_total_ref)), dvar_list_nob) = Terms.assq_rest b (!dvar_list) in
	  let depend_args_opt' = combine_options b depend_args_opt new_depend_args_opt in
	  let (st', proba_info_list') =
	    match st, new_st with
	    | Any, Any -> Any, []
	    | Any, _ ->
		add_advice_sarename b;
		Any, []
	    | _, Any ->
		add_advice_sarename b;
		dvar_list_changed := true;
		Any, []
	    | Compos(_,_,charac_args_opt), _ ->
		let charac_args_opt' = combine_options b charac_args_opt new_charac_args_opt in
		Compos(find_compos_proba_of_coll_var b, t2, charac_args_opt'),
		add_proba_info (t1, t2, probaf) proba_info_list
	    | Decompos(charac_args_opt), Compos _ ->
		dvar_list_changed := true;
		let charac_args_opt' = combine_options b charac_args_opt new_charac_args_opt in
		Compos(find_compos_proba_of_coll_var b, t2, charac_args_opt'),
		add_proba_info (t1, t2, probaf) proba_info_list
	    | Decompos(charac_args_opt), Decompos _ ->
		let charac_args_opt' = combine_options b charac_args_opt new_charac_args_opt in
		Decompos(charac_args_opt'), 
		add_proba_info (t1, t2, probaf) proba_info_list
	  in
	  dvar_list := (b, (st', depend_args_opt', (proba_info_list', probaf_total_ref))) :: dvar_list_nob
	with Not_found ->
          (*print_string "Adding ";
            Display.display_binder b;
            print_newline();*)
	  if Terms.is_assign b then
	    begin
	      let st' =
		match new_st with
		| Compos(_,_,charac_args_opt) ->
		    Compos(find_compos_proba_of_coll_var b, t2, charac_args_opt)
		| _ -> new_st
	      in
	      let b_st =  (b,(st', new_depend_args_opt, ([t1, t2, probaf], ref Unset))) in
      	      dvar_list := b_st :: (!dvar_list)
	    end
	  else
	    begin
	      add_advice_sarename b;
	      dvar_list := (b, (Any, None, ([], ref Unset))) :: (!dvar_list)
	    end;
	  dvar_list_changed := true
      end
  | _, None -> 
      if depends t then
	(* The variable [b] depends on [b0], but we do not have more precise information *)
	begin
	  let new_depend_args_opt = aux_dep_args t in
	  try 
	    let ((st',depend_args_opt, _), dvar_list_nob) = Terms.assq_rest b (!dvar_list) in
	    let depend_args_opt' = combine_options b depend_args_opt new_depend_args_opt in
	    if st' != Any then dvar_list_changed := true;
	    dvar_list := (b, (Any, depend_args_opt', ([], ref Unset))) :: dvar_list_nob
	  with Not_found ->
	    dvar_list := (b, (Any, new_depend_args_opt, ([], ref Unset))) :: (!dvar_list);
	    dvar_list_changed := true
	end
      else
        (* When [t] does not depend on [b0], 
	   if we already recorded that [b] may depend on [b0],
	   it becomes an [Any] dependency: [b] may depend on [b0], 
	   but we do not have more precise information*)
	add_indep b

(* Independence test for find conditions, which may contain if/let/find *)


(* This exception is raised when both branches of a LetE may be taken,
   and the choice may depend on [b0]. *)
exception BothDep
      
let rec almost_indep_fc cur_array t0 =
  match t0.t_desc with
  | FindE(l0,p2,find_info) ->
      begin
      try
	let always_then = ref false in
	let check_br (b,l) = 
	  List.iter (fun t -> if depends t then raise BadDep) l
	in
	let l0' = ref [] in
	List.iter (fun ((bl,def_list,t,p1) as findbranch) ->
	  (* Variables defined in conditions of find never have array accesses,
	     so we need record that the variables in bl are defined,
	     and we can remove the "find" if it always give the same result,
	     without checking that the variables in bl are not used. *)
	  if not (List.for_all defined_br def_list) then
	    local_changed := true
	  else
	    begin
	      List.iter check_br def_list;
	      let bl' = List.map snd bl in
	    (* Compute the probability that the test fails.*)
              match almost_indep_fc (bl' @ cur_array) t with
		BothDepB -> raise BadDep
	      | OnlyThen ->
		  if def_list == [] then always_then := true;
		  begin
		    try
		      let p1' = to_term (almost_indep_fc cur_array p1) in
		      let t' = Terms.make_true() in
		      let find_branch' = 
			if not (Terms.equal_terms t t' && Terms.equal_terms p1 p1') then
			  let already_defined = Facts.get_def_vars_at (DTerm t0) in
			  let newly_defined = Facts.def_vars_from_defined (Facts.get_initial_history (DTerm t0)) def_list in
			  Facts.update_def_list_term already_defined newly_defined bl def_list t' p1'
			else
			  findbranch
		      in
		      l0' := find_branch' :: (!l0')
		    with Contradiction ->
		      (* The variables in the defined condition can never be defined,
			 or the process p1 is unreachable;
			 we can remove the branch *)
		      local_changed := true
		  end				 
	      | BothIndepB t' ->
		  begin
		    try 
		      let p1' = to_term (almost_indep_fc cur_array p1) in
		      let find_branch' = 
			if not (Terms.equal_terms t t' && Terms.equal_terms p1 p1') then
			  let already_defined = Facts.get_def_vars_at (DTerm t0) in
			  let newly_defined = Facts.def_vars_from_defined (Facts.get_initial_history (DTerm t0)) def_list in
			  Facts.update_def_list_term already_defined newly_defined bl def_list t' p1'
			else
			  findbranch
		      in
		      l0' := find_branch' :: (!l0')
		    with Contradiction -> 
		      (* The variables in the defined condition can never be defined,
			 or the process p1 is unreachable;
			 we can remove the branch *)
		      local_changed := true
		  end
	      | OnlyElse | Unreachable -> 
		  local_changed := true
	  end) l0;
	if !always_then then
	  begin
	    if List.for_all (fun (_,_,_,p1') -> Terms.is_true p1') (!l0') then
	      begin
		local_changed := true;
		OnlyThen
	      end
	    else if List.for_all (fun (_,_,_,p1') -> Terms.is_false p1') (!l0') then
	      begin
		local_changed := true;
		OnlyElse
	      end
	    else
	      begin
		if not (Terms.is_false p2) then local_changed := true;
		BothIndepB (Terms.build_term2 t0 (FindE(List.rev (!l0'), Terms.make_false(), find_info)))
	      end
	  end
	else
	  match almost_indep_fc cur_array p2 with
	    BothIndepB p2' -> BothIndepB (Terms.build_term2 t0 (FindE(List.rev (!l0'), p2', find_info)))
	  | OnlyThen ->
	      if List.for_all (fun (_,_,_,p1') -> Terms.is_true p1') (!l0') then
		begin
		  local_changed := true;
		  OnlyThen
		end
	      else
		BothIndepB (Terms.build_term2 t0 (FindE(List.rev (!l0'), Terms.make_true(), find_info)))
	  | OnlyElse | Unreachable ->
	      if List.for_all (fun (_,_,_,p1') -> Terms.is_false p1') (!l0') then
		begin
		  local_changed := true;
		  OnlyElse
		end
	      else
		BothIndepB (Terms.build_term2 t0 (FindE(List.rev (!l0'), Terms.make_false(), find_info)))
	  | BothDepB -> BothDepB
      with BadDep -> BothDepB
      end
  | TestE(t',p1,p2) ->
      begin
	match almost_indep_test cur_array t' with
	  BothDepB -> 
	    let p1' = almost_indep_fc cur_array p1 in
	    let p2' = almost_indep_fc cur_array p2 in
	    begin
	      match p1', p2' with
		Unreachable, _ ->
		  local_changed := true;
		  p2'
	      | _, Unreachable ->
		  local_changed := true;
		  p1'
	      | OnlyThen, OnlyThen ->
		  local_changed := true;
		  OnlyThen
	      | OnlyElse, OnlyElse ->
		  local_changed := true;
		  OnlyElse
              | BothIndepB t1', BothIndepB t2'  ->
		  begin
		    try
                      let true_facts = Facts.get_facts_at (DTerm t0) in
		      let simp_facts = Facts.simplif_add_list (dependency_anal cur_array) ([],[],[]) true_facts in
                      if Terms.simp_equal_terms simp_facts true t1' t2' then
			BothIndepB t1' 
                      else
			BothDepB
		    with Contradiction ->
		      (* The term [t0] is in fact unreachable *)
		      Unreachable
		  end
	      | _ -> BothDepB
	    end
	| BothIndepB t'' ->
	    let p1' = almost_indep_fc cur_array p1 in
	    let p2' = almost_indep_fc cur_array p2 in
	    begin
	      match p1', p2' with
		Unreachable, _ ->
		  local_changed := true;
		  p2'
	      | _, Unreachable ->
		  local_changed := true;
		  p1'		  
	      |	OnlyThen, OnlyThen ->
		  local_changed := true;
		  OnlyThen
	      | OnlyElse, OnlyElse ->
		  local_changed := true;
		  OnlyElse
	      | BothDepB, _ | _, BothDepB -> BothDepB
	      | _, _ -> BothIndepB (Terms.build_term2 t0 (TestE(t'', to_term p1', to_term p2')))
	    end
	| OnlyThen ->
	    local_changed := true;
	    almost_indep_fc cur_array p1
	| OnlyElse ->
	    local_changed := true;
	    almost_indep_fc cur_array p2
	| Unreachable -> Unreachable
      end
  | LetE(pat,t1,p1,p2opt) ->
      begin
	(* Variables defined in conditions of find never have array accesses,
	   so we need record that the variables in pat are defined,
	   and we can remove the "let" if it always give the same result,
	   without checking that the variables in pat are not used. *)
	match pat with
	  PatVar b ->
	    (* Since [b] has no array accesses, the only definition of
	       [b] in [p1] is [b = t1]. We record that dependency by [set_depend]. *)
	    let old_dvar_list = !dvar_list in
	    set_depend b t1;
	    let res = 
	      match almost_indep_fc cur_array p1 with
		OnlyThen ->
		  local_changed := true;
		  OnlyThen
	      | OnlyElse ->
		  local_changed := true;
		  OnlyElse
	      | BothDepB -> BothDepB
	      | BothIndepB p1' -> 
		  if Terms.refers_to b p1' then
		    BothIndepB (Terms.build_term2 t0 (LetE(pat,t1, p1', None)))
		  else
		    BothIndepB p1'
	      | Unreachable -> Unreachable
	    in
	    dvar_list := old_dvar_list;
	    res
	| _ ->
	    let p2 = Terms.get_else p2opt in
	    try
	      match find_compos Terms.simp_facts_id t1 with
	      | _, Some (probaf,t1',_) ->
		  let (t2', dep_types, indep_types) = is_indep_pat pat in
		  if add_collisions_for_current_check_dependency (cur_array, [], DTerm t0) (t1', t2', probaf, dep_types, t1.t_type, indep_types) then
		    begin
		      (* [t'] characterizes [b0], the pattern is independent of [b0]
			 => only the else branch can be taken up to negligible probability *)
		      local_changed := true;
		      almost_indep_fc cur_array p2
		    end
		  else		    
		    raise BothDep
	      | _, None ->
		  match Depanal.find_compos_pat (find_compos Terms.simp_facts_id) pat with
		  | Some(probaf, t2', _) ->
		      let (t1', dep_types, indep_types) = is_indep t1 in
		      if add_collisions_for_current_check_dependency (cur_array, [], DTerm t0) (t2', t1', probaf, dep_types, t1.t_type, indep_types) then
			begin
                          (* [t'] independent of [b0], the pattern characterizes [b0]
			     => only the else branch can be taken up to negligible probability *)
			  local_changed := true;
			  almost_indep_fc cur_array p2
			end
		      else
			raise BothDep
		  | None ->
		      begin
			if (Depanal.depends_pat depends pat) || (depends t1) then raise BothDep;
		        (* Both branches may be taken, and the test is independent of b0 *)
			let p1' = almost_indep_fc cur_array p1 in
			let p2' = almost_indep_fc cur_array p2 in
			match p1', p2' with
			| Unreachable, _ ->
			    local_changed := true;
			    p2'
			| _, Unreachable ->
			    local_changed := true;
			    p1'
			| OnlyThen, OnlyThen ->
			    local_changed := true;
			    OnlyThen
			| OnlyElse, OnlyElse ->
			    local_changed := true;
			    OnlyElse
			| BothDepB, _ | _, BothDepB -> BothDepB
			| _, _ -> BothIndepB (Terms.build_term2 t0 (LetE(pat,t1, to_term p1', Some (to_term p2'))))
		      end
	    with BothDep ->
	      (* Both branches may be taken, and the choice may depend on [b0]
		 Dependency analysis can succeed only if both branches of the let
		 yield the same result. *)
	      let old_dvar_list = !dvar_list in
	      (* Take into account that the variables in [pat] may depend on [b0],
		 in an unspecified way *)
	      let vars = Terms.vars_from_pat [] pat in
	      dvar_list := 
		 (List.map (fun b -> (b, (Any, None, ([], ref Unset)))) vars) @
		 (List.filter (fun (b',_) -> not (List.memq b' vars)) (!dvar_list));
	      let p1' = almost_indep_fc cur_array p1 in
	      dvar_list := old_dvar_list;
	      let p2' = almost_indep_fc cur_array p2 in
	      begin
		match p1', p2' with
		  Unreachable, _ ->
		    local_changed := true;
		    p2'
		| _, Unreachable ->
		    local_changed := true;
		    p1'
		| OnlyThen, OnlyThen ->
		    local_changed := true;
		    OnlyThen
		| OnlyElse, OnlyElse ->
		    local_changed := true;
		    OnlyElse
		| BothIndepB t1', BothIndepB t2'  ->
		    begin
		      try 
			let true_facts = Facts.get_facts_at (DTerm t0) in
			let simp_facts = Facts.simplif_add_list (dependency_anal cur_array) ([],[],[]) true_facts in
			if Terms.simp_equal_terms simp_facts true t1' t2' then
			  BothIndepB t2' 
			else
			  BothDepB
		      with Contradiction ->
			(* The term [t0] is in fact unreachable *)
			Unreachable
		    end
		| _ -> BothDepB
	      end
      end
  | _ -> almost_indep_test cur_array t0

(* Add a display of the explanation of why the dependency analysis fails,
   for [almost_indep_fc] and [almost_indep_test]. *)
	
let almost_indep_fc cur_array t =
  let res = almost_indep_fc cur_array t in
  if res = BothDepB then
    begin
      print_string ("At " ^ (string_of_int t.t_occ) ^ ", the term ");
      Display.display_term t;
      print_string (" depends on " ^ (Display.binder_to_string (!main_var)) ^ "\n")
    end;
  res

let almost_indep_test cur_array t =
  let res = almost_indep_test cur_array t in
  if res = BothDepB then
    begin
      print_string ("At " ^ (string_of_int t.t_occ) ^ ", the term ");
      Display.display_term t;
      print_string (" depends on " ^ (Display.binder_to_string (!main_var)) ^ "\n")
    end;
  res

(* [check_depend_process cur_array p] performs the dependency analysis 
   by scanning the process [p]. 
   It returns a simplified process when it succeeds,
   and raises [BadDep] when it fails.
   [cur_array] is the list of current replication indices. *)

let rec check_depend_process cur_array p' =
  match p'.i_desc with
    Nil -> Terms.iproc_from_desc Nil
  | Par(p1,p2) -> 
      let p1' = check_depend_process cur_array p1 in
      let p2' = check_depend_process cur_array p2 in
      Terms.iproc_from_desc (Par(p1',p2'))
  | Repl(b,p) -> 
      Terms.iproc_from_desc (Repl(b,check_depend_process (b::cur_array) p))
  | Input((c,tl),pat,p) -> 
      List.iter (fun t ->  
	if depends t then
	  begin
	    print_string ("At " ^ (string_of_int t.t_occ) ^ ", index of input channel ");
	    Display.display_term t;
	    print_string (" depends on " ^ (Display.binder_to_string (!main_var)) ^ ".\n");
	    raise BadDep
	  end
	    ) tl;
      match Depanal.find_compos_pat (find_compos Terms.simp_facts_id) pat with
      | Some(probaf, t1, _) -> 
	  (* The pattern matching of this input always fails *)
          (* Create a dummy variable for the input message *)
	  let b = Terms.create_binder "dummy_input"
	      (Terms.get_type_for_pattern pat)
	      cur_array
	  in
	  let t2 = Terms.term_from_binder b in
	  if add_collisions_for_current_check_dependency (cur_array, [], DInputProcess p') (t1, t2, probaf, [], t2.t_type, Some [t2.t_type]) then
	    begin
	      local_changed := true;
	      Terms.iproc_from_desc (Input((c, tl), PatVar b, Terms.oproc_from_desc Yield))
	    end
	  else
	    begin
	      print_string ("At " ^ (string_of_int p'.i_occ) ^ ", pattern of input ");
	      Display.display_pattern pat;
	      print_string (" depends on " ^ (Display.binder_to_string (!main_var)) ^ " but does not characterize a part of it.\n");
	      raise BadDep
	    end
      |	None ->
	begin
	  if Depanal.depends_pat depends pat then
	    begin
	      print_string ("At " ^ (string_of_int p'.i_occ) ^ ", pattern of input ");
	      Display.display_pattern pat;
	      print_string (" depends on " ^ (Display.binder_to_string (!main_var)) ^ " but does not characterize a part of it.\n");
	      raise BadDep
	    end;
	  let vars = Terms.vars_from_pat [] pat in
	  List.iter add_indep vars;
	  add_defined_pat pat;
	  Terms.iproc_from_desc (Input((c,tl), pat, check_depend_oprocess cur_array p))
	end

and check_depend_oprocess cur_array p = 
  match p.p_desc with
    Yield -> Terms.oproc_from_desc Yield
  | EventAbort f -> Terms.oproc_from_desc (EventAbort f)
  | Restr(b,p) -> 
      add_defined b;
      Terms.oproc_from_desc (Restr(b, check_depend_oprocess cur_array p))
  | Test(t,p1,p2) -> 
      begin
	match almost_indep_test cur_array t with
	  BothDepB -> raise BadDep
	| BothIndepB t' -> 
	    if not (Terms.equal_terms t t') then
	      defined_condition_update_needed := true;
	    let p1' = check_depend_oprocess cur_array p1 in
	    let p2' = check_depend_oprocess cur_array p2 in
	    Terms.oproc_from_desc (Test(t', p1',p2'))
	| OnlyThen -> 
	    local_changed := true;
	    check_depend_oprocess cur_array p1
	| OnlyElse -> 
	    local_changed := true;
	    check_depend_oprocess cur_array p2
	| Unreachable -> 
	    local_changed := true;
	    Terms.oproc_from_desc Yield
      end
  | Find(l0,p2,find_info) ->
      let always_then = ref false in
      let check_br (b,l) = 
	List.iter (fun t -> 
	  if depends t then
	    begin
	      print_string ("At " ^ (string_of_int t.t_occ) ^ ", index of defined condition ");
	      Display.display_term t;
	      print_string (" depends on " ^ (Display.binder_to_string (!main_var)) ^ ".\n");
	      raise BadDep
	    end) l
      in
      let l0' = ref [] in
      List.iter (fun ((bl,def_list,t,p1)) ->
	if not (List.for_all defined_br def_list) then
	  local_changed := true
	else
	  begin
	    List.iter check_br def_list;
	    let bl' = List.map snd bl in
	    (* Compute the probability that the test fails.*)
            match almost_indep_fc (bl' @ cur_array) t with
	      BothDepB -> raise BadDep
	    | OnlyThen ->
		List.iter (fun (b,_) -> add_defined b) bl;
		if def_list == [] then always_then := true;
		let defined_condition_update_needed_tmp = !defined_condition_update_needed in
		defined_condition_update_needed := false;
		let p1' = check_depend_oprocess cur_array p1 in
		let t' = Terms.make_true() in
		begin
		  try 
		    let findbranch' = 
		      if !defined_condition_update_needed then
			let already_defined = Facts.get_def_vars_at (DProcess p) in
			let newly_defined = Facts.def_vars_from_defined (Facts.get_initial_history (DProcess p)) def_list in
			Facts.update_def_list_process already_defined newly_defined bl def_list t' p1'
		      else
			(bl, def_list, t', p1')
		    in
		    defined_condition_update_needed := 
		       defined_condition_update_needed_tmp || (!defined_condition_update_needed);
		    l0' := findbranch' :: (!l0')
		  with Contradiction ->
		    (* The variables in the defined condition can never be defined,
                       we can remove the branch *)
		    local_changed := true;
		    defined_condition_update_needed := defined_condition_update_needed_tmp
		end
	    | BothIndepB t' ->
		List.iter (fun (b,_) -> add_defined b) bl;
		let defined_condition_update_needed_tmp = !defined_condition_update_needed in
		defined_condition_update_needed := not (Terms.equal_terms t t');
		let p1' = check_depend_oprocess cur_array p1 in
		begin
		  try 
		    let findbranch'  = 
		      if !defined_condition_update_needed then
			let already_defined = Facts.get_def_vars_at (DProcess p) in
			let newly_defined = Facts.def_vars_from_defined (Facts.get_initial_history (DProcess p)) def_list in
			Facts.update_def_list_process already_defined newly_defined bl def_list t' p1'
		      else
			(bl, def_list, t', p1')
		    in
		    defined_condition_update_needed := 
		       defined_condition_update_needed_tmp || (!defined_condition_update_needed);
		    l0' := findbranch' :: (!l0')
		  with Contradiction ->
		    (* The variables in the defined condition can never be defined,
                       we can remove the branch *)
		    local_changed := true;
		    defined_condition_update_needed := defined_condition_update_needed_tmp
		end
	    | OnlyElse | Unreachable -> 
		local_changed := true
	  end) l0;
      if !always_then then
	begin
	  local_changed := true;
	  Terms.oproc_from_desc (Find(List.rev (!l0'), Terms.oproc_from_desc Yield, find_info))
	end
      else
	Terms.oproc_from_desc (Find(List.rev (!l0'), check_depend_oprocess cur_array p2, find_info))
  | Output((c,tl),t2,p) ->
      List.iter (fun t ->
	if depends t then
	begin
	  print_string ("At " ^ (string_of_int t.t_occ) ^ ", index of output channel ");
	  Display.display_term t;
	  print_string (" depends on " ^ (Display.binder_to_string (!main_var)) ^ ".\n");
	  raise BadDep
	end) tl;
      if depends t2 then
	begin
	  print_string ("At " ^ (string_of_int t2.t_occ) ^ ", output message ");
	  Display.display_term t2;
	  print_string (" depends on " ^ (Display.binder_to_string (!main_var)) ^ ".\n");
	  raise BadDep
	end;
      Terms.oproc_from_desc (Output((c,tl),t2, check_depend_process cur_array p))
  | Let(PatVar b, t, p1, _) ->
      add_depend b t;
      add_defined b;
      let p1' = check_depend_oprocess cur_array p1 in
      Terms.oproc_from_desc (Let(PatVar b, t, p1', Terms.oproc_from_desc Yield))
  | Let(pat,t,p1,p2) ->
      let bad_dep() =
	print_string ("At " ^ (string_of_int p.p_occ) ^ ", the assignment ");
	Display.display_pattern pat;
	print_string " = ";
	Display.display_term t;
	print_string " introduces a bad dependency:\nit may succeed or fail depending on the value of ";
	print_string (Display.binder_to_string (!main_var));
	print_string ".\n"; 
	raise BadDep
      in
      begin
	match find_compos Terms.simp_facts_id t with
	| _, Some (probaf,t1',_) ->
	    let (t2', dep_types, indep_types) = is_indep_pat pat in
	    if add_collisions_for_current_check_dependency (cur_array, [], DTerm t) (t1', t2', probaf, dep_types, t.t_type, indep_types) then
	      begin
                (* [t] characterizes [b0], the pattern is independent of [b0]
		   => only the else branch can be taken up to negligible probability *)
		local_changed := true;
		check_depend_oprocess cur_array p2
	      end
	    else
		(* Both branches may be taken, and the choice may depend on [b0]
		   => dependency analysis fails *)
	      bad_dep()
	| _, None ->
	    match Depanal.find_compos_pat (find_compos Terms.simp_facts_id) pat with
	    | Some(probaf, t2', _) ->
		let (t1', dep_types, indep_types) = is_indep t in
                (* [t] independent of [b0], the pattern characterizes [b0]
		   => only the else branch can be taken up to negligible probability *)
		if add_collisions_for_current_check_dependency (cur_array, [], DProcess p) (t2', t1', probaf, dep_types, t.t_type, indep_types) then
		  begin
		    local_changed := true;
		    check_depend_oprocess cur_array p2
		  end
		else
		  bad_dep()
	    | None ->
		if (Depanal.depends_pat depends pat) || (depends t) then
		  (* Both branches may be taken, and the choice may depend on [b0]
		     => dependency analysis fails *)
		  bad_dep();
		(* Both branches may be taken, but the test is independent of b0 *)
		let vars = Terms.vars_from_pat [] pat in
		List.iter add_indep vars;
		add_defined_pat pat;
		let p1' = check_depend_oprocess cur_array p1 in
		let p2' = check_depend_oprocess cur_array p2 in
		Terms.oproc_from_desc (Let(pat, t, p1', p2'))
      end
  | EventP(t,p) ->
      Terms.oproc_from_desc (EventP(t, check_depend_oprocess cur_array p))
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"
      
(* [check_depend_iter init_proba_state] iterates the dependency analysis:
   when the dependency analysis discovers new variables that depend on [b0],
   or new variables that may defined (so new branches of [find] may be executed),
   the dependency analysis needs to be redone. 
   [init_proba_state] contains collisions eliminated before the dependency analysis.
   The probability state is reset to this value before each iteration,
   so that the actual collisions eliminated are the ones already eliminated
   before dependency analysis, plus the ones of the final iteration of the
   dependency analysis. *)

let rec check_depend_iter ((old_proba, old_term_collisions) as init_proba_state) =
  List.iter (fun (b0, _) ->
    if Settings.occurs_in_queries b0 (!whole_game).current_queries then
      begin
	print_string ("The variable " ^ (Display.binder_to_string b0) ^ 
		      " depends on " ^ (Display.binder_to_string (!main_var)) ^ 
		      " and occurs in a query.\n");
        raise BadDep
      end;
    ) (!dvar_list);
  Proba.restore_state old_proba;
  Depanal.term_collisions := old_term_collisions;
  compute_probas();
  local_changed := false;
  dvar_list_changed := false;
  defvar_list_changed := false;
  defined_condition_update_needed := false;
  let proc' = check_depend_process [] (Terms.get_process (!whole_game)) in
  if (!dvar_list_changed) || (!defvar_list_changed) then check_depend_iter init_proba_state else proc'

(* [check_all_deps b0 init_proba_state g] is the entry point for calling 
   the dependency analysis from simplification.
   [b0] is the variable on which we perform the dependency analysis.
   [init_proba_state] contains collisions eliminated by before the dependency analysis,
   in previous passes of simplification.
   [g] is the full game to analyze. *)

let init_find_compos_probaf b0 = 
  let ri = Depanal.fresh_repl_index() in
  (ri, ([Fixed(ri::b0.args_at_creation,Proba.pcoll1rand b0.btype,[],b0.btype,None)],[],[]))
    
let check_all_deps b0 init_proba_state g =
  whole_game := g;
  main_var := b0;
  let vcounter = Terms.get_var_num_state() in
  try
    let dummy_term = Terms.term_from_binder b0 in
    let args_opt = Some (List.map Terms.term_from_repl_index b0.args_at_creation) in
    let b0st = (b0, (Decompos(args_opt), args_opt, ([dummy_term, dummy_term, init_find_compos_probaf b0], ref Unset))) in
    dvar_list := [b0st];
    defvar_list := [];
    let proc' = check_depend_iter init_proba_state in
    let res_game = Terms.build_transformed_game proc' g in
    if not (!local_changed) then
      begin
	print_string "The global dependency analysis succeeded but did not make any change.\n";
	raise BadDep
      end;
    (* Some cleanup to free memory *)
    dvar_list := [];
    defvar_list := [];
    whole_game := Terms.empty_game;
    Some(res_game)
  with BadDep -> 
    (* Some cleanup to free memory *)
    dvar_list := [];
    defvar_list := [];
    whole_game := Terms.empty_game;
    Terms.set_var_num_state vcounter; (* Forget variables when fails *)
    None

(* [main b0 coll_elim g] is the entry point for calling
   the dependency analysis alone.
   [b0] is the variable on which we perform the dependency analysis.
   [coll_elim] is a list of occurrences, types or variable names 
   for which we allow eliminating collisions even if they are not [large].
   [g] is the full game to analyze. *)

let main b0 coll_elim g =
  Depanal.reset coll_elim g;
  let g_proc = Terms.get_process g in
  Array_ref.array_ref_process g_proc;
  Improved_def.improved_def_game None false g;
  let dummy_term = Terms.term_from_binder b0 in
  let result = 
  if not ((Terms.is_restr b0) && (Proba.is_large_term dummy_term)) then
    (g, [], []) 
  else
    begin
    advise := [];
    let res = check_all_deps b0 (([],[]),[]) g in
    (* Transfer the local advice to the global advice in Settings.advise *)
    List.iter (fun x -> Settings.advise := Terms.add_eq x (!Settings.advise)) (!advise);
    advise := [];
    match res with
      None -> (g, [], []) 
    | Some(res_game) ->
	Settings.changed := true;
	let proba = Depanal.final_add_proba() in
	(res_game, proba, [DGlobalDepAnal(b0,coll_elim)])
    end
  in
  Improved_def.empty_improved_def_game false g;
  result
