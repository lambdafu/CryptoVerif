open Types

(* 1. Compute and use simp_facts: facts that are separated into
   equalities that can be used as substitutions, other terms,
   else-find facts *)

(* true_facts_from_simp_facts gets the true facts from a triple (facts, substitutions, else_find facts) *)
val true_facts_from_simp_facts : simp_facts -> term list

(* Filter out terms if/let/find/res/event, so that the remaining terms
   can be used as facts *)
val filter_ifletfindres : term list -> term list

(* match_term is an intermediate function used for apply_reds. It is exported
   because we need to compute a variant of apply_reds in dependency analyses. *)
val match_term : simp_facts -> binder list -> (unit -> 'a) -> term -> term -> unit -> 'a

(* [match_term_list3] is used to match oracle calls in [Depanal].
   It considers all replication indices as variables.
   It cleans up the links only in case of failure of matching. *)
val match_term_list3 : simp_facts -> (unit -> 'a) -> term list -> term list -> unit -> 'a
    
(* set to true by the functions below when they reduce the term *)
val reduced : bool ref

(* [apply_eq_statements_and_collisions_subterms_once reduce_rec dep_info simp_facts t] 
   simplifies the term [t] using the equalities coming from the
   equational theories, the equality statements, and the collisions  
   given in the input file.
   [reduce_rec f t] must simplify the term [t] knowing the fact [f] 
   in addition to the already known facts. It returns
   the reduced term as well as a boolean that is true 
   when [t] has really been modified.
   [simp_facts] contains facts that are known to hold. *)
val apply_eq_statements_and_collisions_subterms_once : (term -> term -> term * bool) -> dep_anal -> simp_facts -> term -> term

(* [apply_eq_statements_subterms_once simp_facts t] simplifies
   the term [t] using the equalities coming from the
   equational theories and the equality statements given in the input file.
   [simp_facts] is as above. *)
val apply_eq_statements_subterms_once : simp_facts -> term -> term

(* [apply_reds dep_info simp_facts t] applies all equalities coming from the
   equational theories, equality statements, and collisions given in
   the input file to all subterms of the term [t], taking into account
   the equalities in [simp_facts] to enable their application.
   Application is repeated until a fixpoint is reached. *)
val apply_reds : dep_anal -> simp_facts -> term -> term

(* [simplify_equal t1 t2] simplifies [t1 = t2].
   Raises [Contradiction] when false.
   Raises [Unchanged] when no simplification found.
   Returns a pair of lists such that matching elements are equal terms 
   otherwise. *)
exception Unchanged
val simplify_equal : term -> term -> term list * term list

(* [new_repl_index_term] and [new_repl_index] create new replication 
   indices, to replace find indices in probability computations.
   These indices are stored in [repl_index_list], which can be reset by
   [reset_repl_index_list]. *)
val reset_repl_index_list : unit -> unit

val new_repl_index_term : term -> repl_index
val new_repl_index : repl_index -> repl_index
    
(* See type [dep_anal] in [types.ml] for an explanation of dependency analysis.

   [no_dependency_anal] is a particular dependency analysis that works
   without any dependency information, so it can be used as a default.
   Other dependency analyses are defined in [simplify1.ml], 
   [transf_simplify.ml], etc.
   *)
val indep_test_noinfo : dep_anal_indep_test
val no_collision_test : dep_anal_collision_test
val no_dependency_anal : dep_anal

(* [default_indep_test get_depinfo] builds an independence test 
   based on the dependency information provided by [get_depinfo].
   [get_depinfo: binderref -> 'a depinfo] is a function that returns
   the dependency information (see type ['a depinfo] in types.ml)
   for each binder reference.

[default_indep_test get_depinfo simp_facts t (b,l)] 
returns [Some (t', side_condition_proba, side_condition_term)] 
when [t'] is a term obtained from [t] by replacing array indices that 
depend on [b[l]] with fresh indices.
[t'] does not depend on [b[l]] when a side condition is true.
The side condition is present in 2 forms:
 - [side_condition_proba] is the side condition to include in the 
   probability computation. It uses fresh indices like [t']. It is a term.
 - [side_condition_term] is used in the simplified term that we include 
   in the process. It is a list of terms, such that the or of these terms 
   corresponds to the negation of the side condition.
Returns [None] if that is not possible.

[simp_facts] contains facts that are known to hold.  *)
val default_indep_test : (binderref -> 'a depinfo) -> dep_anal_indep_test

(* Empty dependency information *)
val nodepinfo : 'a depinfo
    
(* [simplif_add dep_anal facts t] updates the facts by taking into
   account that the term [t] is true. It can use [dep_anal] to eliminate
   collisions. 
   Raises Contradiction when the added fact [t] cannot be true when
   [facts] hold.
*)
val simplif_add : dep_anal -> simp_facts -> term -> simp_facts
(* [simplif_add_list dep_anal facts tl] updates the facts by taking into
   account that the terms in [tl] are true. It can use [dep_anal] to eliminate
   collisions.
   Raises Contradiction when the added facts [tl] cannot be true when
   [facts] hold.
 *)
val simplif_add_list : dep_anal -> simp_facts -> term list -> simp_facts

(* 2. Compute the facts that hold and the variables that are defined
   at certain program points. *)

(* [is_reachable_same_block n n'] is true when the variable defined 
   at [n] is defined above the one defined at [n'] and within the 
   same input...output block. *)
val is_reachable_same_block : def_node -> def_node -> bool
    
(* [is_before_same_block pp pp'] is true when the program point [pp]
   may be before [pp'] and in the same input...output block. *)
val is_before_same_block : program_point -> program_point -> bool
    
(* [get_initial_history pp] gets the known_history corresponding to the program
   point [pp] *)
val get_initial_history : program_point -> known_history option
val get_initial_history_args : program_point_args -> known_history option

(* [get_compatible_def_nodes history pps b l] *)
val get_compatible_def_nodes : known_history option -> program_points_args list
    -> binder -> term list -> def_node list
    
(* [def_vars_from_defined known_pps known_def_vars history def_list]
   returns the program points known to be executed and the variables
   known to be defined when the condition of a find with defined
   condition [def_list] holds.
   [known_pss] are the program points already known to be executed.
   [known_def_vars] are the variables already known to be defined.
   [history] is the history of the find, at which [def_list] is tested
   (may be returned by [get_initial_history], [get_def_vars_at], or
   [get_facts_at]).
   The returned program points include [known_pss]. The returned defined
   variables do not include [known_def_vars].
   Raises Contradiction when a variable that must be defined when [def_list]
   is defined has no definition in the game. *)
val def_vars_from_defined : program_points_args list -> binderref list ->
  known_history option -> binderref list ->
    program_points_args list * binderref list

(* [def_vars_before known_pps br] with [br = (b,tl)]
   returns the variables known to be defined before [b[al]] when
   [tl] evaluates to [al].
   [known_pss] are the program points already known to be executed. *)
val def_vars_before :  program_points_args list -> binderref -> binderref list 
      
(* [facts_from_defined known_pps known_def_vars history def_list]
   returns the facts known to hold, the program points known to be
   executed, and the variables known to be defined when the condition
   of a find with defined condition [def_list] holds.
   [known_pss] are the program points already known to be executed.
   [known_def_vars] are the variables already known to be defined.
   [history] is the history of the find, at which [def_list] is tested
   (may be returned by [get_initial_history], [get_def_vars_at], or
   [get_facts_at]).
   The returned program points include [known_pss]. The returned defined
   variables do not include [known_def_vars]. 
   Raises Contradiction when a variable that must be defined when [def_list]
   is defined has no definition in the game. *)
val facts_from_defined :  program_points_args list -> binderref list ->
  known_history option -> binderref list ->
    term list * program_points_args list * binderref list 

(* [get_def_vars_at pp] returns the program points
   known to be executed and the defined variables at program point [pp],
   as well as the history at program point [pp].
   May raise Contradiction when the program point [pp] is
   unreachable. *)
val get_def_vars_at : program_point -> program_points_args list * binderref list * known_history option

(* [get_facts_at pp] returns the facts known to hold, the program points
   known to be executed, and the defined variables at program point [pp],
   as well as the history at program point [pp].
   May raise Contradiction when the program point [pp] is
   unreachable. *)
val get_facts_at : program_point -> term list * program_points_args list * binderref list * known_history option

(* [get_facts_at_args known_pps known_def_vars (pp,args)]
   returns the facts known to hold, the program points known to be executed,
   and the defined variables at program point
   [pp] with indices [args], knowing that the program points [known_pps]
   have been executed and the variables [known_def_vars] are defined.
   May raise Contradiction when the program point [pp] is
   unreachable. *)
val get_facts_at_args : program_points_args list -> binderref list ->
  program_point_args -> term list * program_points_args list * binderref list

(* [get_facts_full_block_args known_pps known_def_vars (pp,args)]
   returns the facts that are known to hold at the end of the
   input...output block containing program point [pp], knowing that
   the program points [known_pps] have been executed and the variables
   [known_def_vars] are defined.
   Also returns the program points known to be executed and the defined
   variables at program point [pp] with indices [args].
   (Future defined variables are handled separately.
   When [Settings.corresp_cases] is true, distinguishes cases depending on the
   definition point of variables (instead of taking intersections), to
   facilitate the proof of correspondences.
   May raise Contradiction when the program point [pp] is
   unreachable. *)
val get_facts_full_block_args : program_points_args list -> binderref list ->
  program_point_args ->
    term list * term list list list * program_points_args list * binderref list

(* [get_elsefind_facts_at pp] returns the elsefind facts that are known to hold
   at program point [pp]. *)
   
val get_elsefind_facts_at : program_point -> elsefind_fact list

(* [reduced_def_list fact_info def_list] removes variables that are 
   certainly defined from a [def_list] in a find. [fact_info] corresponds
   to the facts at the considered find. *)
val reduced_def_list : fact_info -> binderref list -> binderref list

(* Functions useful to simplify def_list *)

(* [remove_subterms accu l] returns a def_list that contains
   all elements of [accu] and [l] except elements that
   also occur as subterms in [l].
   The typical call is  [remove_subterms [] l], which returns
   [l] with elements that occur as subterms removed. *)
val remove_subterms : binderref list -> binderref list -> binderref list

(* [eq_deflists dl dl'] returns true when the two def_list [dl]
   and [dl'] are equal (by checking mutual inclusion) *)
val eq_deflists : binderref list -> binderref list -> bool

(* [update_def_list_term (already_pps, already_defined, history_pp) newly_defined_opt bl def_list tc' p'] 
   returns an updated find branch [(bl, def_list', tc'', p'')].
   This function should be called after modifying a branch of find 
   (when the find is a term), to make sure that all needed variables are defined.
   It updates in particular [def_list], but may also add defined conditions
   inside [tc'] or [p'].
   [already_pps] is a list of program points known to be executed
   above the find.
   [already_defined] is a list of variables already known to be defined
   above the find.
   [history_pp] is the initial history at the program point of the find.
   [newly_defined_opt] is either [Some(newly_defined)] where [newly_defined]
   is the set of variables whose definition is guaranteed by the old defined
   condition [def_list], or [None] is which is case it is recomputed by the
   function.
   [bl, def_list, tc', p'] describe the modified branch of find:
   [bl] contains the indices of find
   [def_list] is the old def_list
   [tc'] is the modified condition of the find
   [p'] is the modified then branch of the find. *) 
val update_def_list_term :
    program_points_args list * binderref list * known_history option ->
      binderref list option -> 
	(binder * repl_index) list -> binderref list -> term -> term ->
	  term findbranch

(* [update_def_list_process (already_pps, already_defined, history_pp) newly_defined_opt bl def_list t' p1'] 
   returns an updated find branch [(bl, def_list', t'', p1'')].
   This function should be called after modifying a branch of find 
   (when the find is a process), to make sure that all needed variables are defined.
   It updates in particular [def_list], but may also add defined conditions
   inside [t'] or [p1'].
   [(already_pps, already_defined, history_pp) newly_defined_opt] are as in
   [update_def_list_term].
   [bl, def_list, t', p1'] describe the modified branch of find:
   [bl] contains the indices of find
   [def_list] is the old def_list
   [t'] is the modified condition of the find
   [p1'] is the modified then branch of the find. *) 
val update_def_list_process :
    program_points_args list * binderref list * known_history option ->
      binderref list option -> 
	(binder * repl_index) list -> binderref list -> term -> process ->
	  process findbranch

(* Priorities for orienting equalities into rewrite rules
   Used by both transf_simplify and transf_expand. 
   It is important that a single list is used, so that variables
   with priority set are always in the priority list. *)
val current_max_priority : int ref
val priority_list : binder list ref
    
(*** Treatment of "elsefind" facts ***)

val match_among_list :
  (unit -> 'a) -> simp_facts -> repl_index list ->
  ('b * term list) list -> ('b * term list) list -> 'a

val always_true_def_list_t :
  term list ref -> term -> simp_facts -> repl_index list ->
  ('a * term list) list -> ('a * term list) list -> unit
    
exception SuccessBranch of (binder * repl_index * term) list * (binder * repl_index) list
val branch_succeeds : 'b findbranch -> dep_anal -> simp_facts -> 
  binderref list -> unit
val add_elsefind : dep_anal -> binderref list -> simp_facts ->
  ('a findbranch * elsefind_fact list) list ->
    simp_facts
val update_elsefind_with_def : binder list -> simp_facts -> simp_facts
val convert_elsefind : dep_anal -> binderref list -> simp_facts -> simp_facts

(*** Helper functions for simplification ***)
    
(* [needed_vars vars] returns true when some variables in [vars]
   have array accesses or are used in queries. That is, we must keep
   them even if they are not used in their scope. *)
val needed_vars : binder list -> cur_queries_t -> bool
val needed_vars_in_pat : pattern -> cur_queries_t -> bool

(* Add lets to a process or a term *)
val add_let : process -> (binder * term) list -> process
val add_let_term : term -> (binder * term) list -> term

(* [filter_deflist_indices bl def_list] removes from [def_list] all
   elements that refer to replication indices in [bl].
   Used when we know that the indices in [bl] are in fact not used. *)
val filter_deflist_indices :
  (binder * repl_index) list -> binderref list -> binderref list


(* 3. Some rich functions that rely on collecting facts and reasoning 
   about them *)

(* [simplify_term dep_anal facts t] returns a simplified form of
   the term [t] using the dependency analysis [dep_anal] and the
   true facts [facts]. *)
val simplify_term : dep_anal -> simp_facts -> term -> term

(* [check_equal t t' simp_facts] returns true when [t] and [t'] are
   proved equal when the facts in [simp_facts] are true.
   It is called from transf_insert_replace.ml. The probability of collisions
   eliminated to reach that result is taken into account by module [Proba]. *)
val check_equal : term -> term -> simp_facts -> bool

(* [display_facts_at p occ] displays the facts that are known
   to hold at the program point [occ] of the process [p]. *)
val display_facts_at : inputprocess -> int -> unit
