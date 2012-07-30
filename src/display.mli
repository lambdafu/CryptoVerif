open Types

val display_occurrences : bool ref
val display_arrays : bool ref
val display_list : ('a -> unit) -> 'a list -> unit

val len_num : int -> int
val useful_occs : int list ref
val mark_occs : detailed_instruct list -> unit

val ends_with_underscore_number : string -> bool
val binder_to_string : binder -> string
val repl_index_to_string : repl_index -> string
val display_binder : binder -> unit
val display_repl_index : repl_index -> unit
val display_var : binder -> term list -> unit
val display_term : term -> unit
val display_statement : statement -> unit
val display_pattern : pattern -> unit
val display_proba : int -> probaf -> unit
val display_set : setf list -> unit
val display_equiv : equiv_nm -> unit
val display_equiv_with_name : equiv_nm -> unit
val display_oprocess : string -> process -> unit
val display_process : inputprocess -> unit

val display_bl_assoc : binder list -> unit
val display_query : query * game -> unit
val display_instruct : instruct -> unit

(* The next functions are made public so that displaytex can call them *)

val proba_table : ((query * game) * (setf list * state)) list ref

exception NotBoundEvent of funsymb * game

(* [compute_proba q p s] returns a computation of probabilities 
of query [q] in state [s]. [p] is the probability of [q] in the game
that proves it (corresponding to the last elimination of collisions).
When the obtained probability refers to the probability of executing
event [e] in game [g], and that probability has not been bounded, raises
[NotBoundEvent(e,g)]. The returned probability is guaranteed not to
contain [SetEvent]. *)

val compute_proba : query * game -> setf list -> state -> setf list

(* [proba_since g s] returns the probability of distinguishing game [g]
from the game corresponding to state [s] *)

val proba_since : game -> state -> setf list

(* [proba_from_set q p] converts the probability [p] represented as
a [setf list] into a probability represented as a [probaf].
[p] must not contain [SetEvent]. *)

val proba_from_set : setf list -> probaf
val proba_from_set_may_double : query * game -> setf list -> probaf


val display_state : state -> unit

