open Types

(* Helper functions for simplify, mergebranches, global_dep_anal, ... *)

(* Priorities for orienting equalities into rewrite rules
   Used by both transf_simplify and transf_expand. 
   It is important that a single list is used, so that variables
   with priority set are always in the priority list. *)
val current_max_priority : int ref
val priority_list : binder list ref
    
(*** Treatment of "elsefind" facts ***)

exception SuccessBranch of (binder * repl_index * term) list * (binder * repl_index) list
val branch_succeeds : 'b findbranch -> dep_anal -> simp_facts -> 
  binderref list -> unit
val add_elsefind : dep_anal -> binderref list -> simp_facts ->
  'a findbranch list -> simp_facts
val update_elsefind_with_def : binder list -> simp_facts -> simp_facts
val convert_elsefind : dep_anal -> binderref list -> simp_facts -> simp_facts

(* [get_facts_of_elsefind_facts] uses elsefind facts to derive more facts, 
   by performing a case distinction depending on the order of 
   definition of variables. 
   [get_facts_of_elsefind_facts g cur_array simp_facts def_vars]
   returns a list of terms [tl] that are proved.
   [g] is the current game
   [cur_array] the current replication indices
   [simp_facts] the facts known to hold at the current program point
   [def_vars] the variables known to be defined
   The probability that the facts do not hold must be collected from outside 
   [get_facts_of_elsefind_facts], by calling [Simplify1.reset] before
   and [Simplify1.final_add_proba()] after calling [get_facts_of_elsefind_facts].
*)

val get_facts_of_elsefind_facts : game -> repl_index list -> simp_facts -> binderref list -> term list

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

(* [is_unique l0' find_info] returns Unique when a [find] is unique,
   that is, at runtime, there is always a single possible branch 
   and a single possible value of the indices:
   either it is marked [Unique] in the [find_info],
   or it has a single branch with no index.
   [l0'] contains the branches of the considered [find]. *)
val is_unique : 'a findbranch list -> find_info -> find_info

(* [infer_unique g cur_array simp_facts def_vars dep_info current_history l0' find_info]
   tries to prove that there is single possible choice in the find with
   branches [l0'], and if so it returns the modified [find_info] equal to
   [Unique]. It also returns a boolean set to true when a real change has been made.

   [g] is the current game
   [cur_array] the current replication indices
   [simp_facts] the facts known to hold at the current program point
   [def_vars] the variables known to be defined
   [dep_info] is a dependency analysis
   [current_history] is the known history at the find, at which [def_list]
   is tested (may be returned by [Facts.get_initial_history]) *)
val prove_unique : game -> repl_index list -> simp_facts -> binderref list ->
                   dep_anal -> known_history option ->
                   'a findbranch list -> bool
val infer_unique : game -> repl_index list -> simp_facts -> binderref list ->
                   dep_anal -> known_history option ->
                   'a findbranch list -> find_info -> find_info * bool
                                                     
(*** [improved_def_process event_accu compatible_needed p]
     Improved version of [Terms.build_def_process] that infers facts from 
     variables being defined at a program point, variables being simultaneously
     defined, and elsefind facts.
     Reverts to [Terms.build_def_process] when [Settings.improved_fact_collection = false].
     When [compatible_needed] is true, always initializes the [incompatible] field.
 ***)
val improved_def_process : (term * program_point) list ref option -> bool -> inputprocess -> unit

val empty_improved_def_process : bool -> inputprocess -> unit
