open Types

(* [def_vars_and_facts_from_term expanded in_find t] extracts a list of defined 
   variables and a list of facts implied by [t]

   [expanded] is true when [t] is for sure already expanded.
   (Otherwise, it will be expanded internally.)

   When [in_find = true], it assumes that [t] is a condition
   of [find].
   When [in_find = false], it does not make such assumptions. *)
val def_vars_and_facts_from_term : bool -> bool -> term -> term list * binderref list * elsefind_fact list

(* [else_info_from_find_branch expanded br] returns 
   information certainly true when the condition in the branch [br] fails
   (elsefind facts) *) 
val else_info_from_find_branch : bool -> 'a findbranch -> elsefind_fact list
    
(* [add_else_info_find expanded l0] adds information collected 
   by [else_info_from_find_branch] to each branch of find in [l0] *)
val add_else_info_find : bool -> 'a findbranch list -> ('a findbranch * elsefind_fact list) list

(* [info_from_find_branch expanded br] returns a pair of
   information certainly true when the condition of find in the branch [br]
   succeeds (facts, defined variables, elsefind facts)
   and information certainly true when this condition fails
   (elsefind facts) *) 
val info_from_find_branch : bool -> 'a findbranch -> (term list * binderref list * elsefind_fact list) * elsefind_fact list

(* [add_info_find expanded l0] adds information collected 
   by [info_from_find_branch] to each branch of find in [l0] *)
val add_info_find : bool -> 'a findbranch list -> ('a findbranch * ((term list * binderref list * elsefind_fact list) * elsefind_fact list)) list
