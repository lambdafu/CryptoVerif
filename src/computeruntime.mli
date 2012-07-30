open Types

val make_length_term : game -> term -> probaf
val make_length : game -> term list -> probaf list

val compute_runtime_for_context : game -> equiv_nm ->
  (term -> term list * int * int * repl_index list * (binder list * term list) list) ->
  binder list -> probaf

val compute_runtime_for : game -> probaf
