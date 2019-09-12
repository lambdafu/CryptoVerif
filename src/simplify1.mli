open Types

(* Helper functions for simplify, mergebranches, global_dep_anal, ... *)

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
  'a findbranch list -> simp_facts
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

