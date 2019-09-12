open Types

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

