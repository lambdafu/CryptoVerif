open Types

(* [make_length_term accu_ref g t] modifies [accu_ref] so that it
   represents the maximum of [!accu_ref] and [Maxlength(g,t)] *)
val make_length_term : Polynom.max_accu ref -> game -> term -> unit

val compute_runtime_for_context : game -> equiv_nm ->
  (term -> term list * int * int * repl_index list * (binder list * term list) list) ->
  binder list -> probaf

val compute_runtime_for : game -> probaf

val compute_runtime_for_fungroup : game -> fungroup -> probaf
val compute_runtime_for_term : game -> term -> probaf
