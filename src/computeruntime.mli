open Types

(* [make_length_term accu_ref g t] modifies [accu_ref] so that it
   represents the maximum of [!accu_ref] and [Maxlength(g,t)] *)
val make_length_term : Polynom.minmax_accu ref -> game -> term -> unit

val compute_runtime_for_context : game -> equiv_nm ->
  (term -> term list * int * int * repl_index list * (binder list * term list) list) ->
  binder list -> probaf

val compute_runtime_for : game -> probaf

(* Two version of the function that computes the time to add when 
   we add a replication on top of an equiv statement
   [compute_add_time lhs rhs param opt2] computes
   an upper bound of 
     max(time(lhs),time(rhs)) * (param-1) when opt2 = Decisional
     time(lhs) when opt2 = Computational
   [compute_add_time_totcount] is similar, but uses #O counts
   to count the number of executions of oracles, which avoids
   having to multiply afterwards and gives better results when param >> 1.
   *)
val compute_add_time : fungroup -> fungroup -> param -> eqopt2 -> probaf
val compute_add_time_totcount : fungroup -> fungroup -> param -> eqopt2 -> probaf
    
val compute_runtime_for_term : game -> term -> probaf

(* [get_oracle b] returns the oracle in which [b] is defined.
   Raises [Not_found] in case of failure.
   [Def.build_def_process] must have been called on the current game
   for it to succeed. *)
val get_oracle : binder -> channel

(* [get_ri_mul ri_list tl] returns an optimized version of the
   product of the bounds of [ri_list], assuming that the terms in
   [tl] are defined. *)
val get_ri_mul : repl_index list -> term list -> ri_mul_t 
