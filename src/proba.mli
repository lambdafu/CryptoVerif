open Types

(* 1. Is a type large? (i.e. the inverse of its cardinal is negligible) *)

(* Returns true when the type has size >= Settings.tysize_MIN_Auto_Coll_Elim
   i.e. collisions should be automatically elimminated on this type. *)
val is_large : typet -> bool

(* List of variables/types/occurrences that are considered to be large, even if
   only declared "password" *)
val elim_collisions_on_password_occ : string list ref

(* Returns true when collisions should be eliminated on the considered term
   This includes two cases:
   a. the type has size >= Settings.tysize_MIN_Auto_Coll_Elim
   b. the type has size >= 1
   and the elimination of collisions on this value has been explicitly 
   requested by the user (arguments of command "simplify") *)
val is_large_term : term -> bool

(* 2. Cardinality operations *) 

val card : typet -> probaf
val card_index : binder -> probaf

(* 3. Computation of probabilities of collisions *)

(* [is_small_enough_coll_elim (proba_l, proba)] tests if 
   [proba_l/proba] is considered small enough to eliminate collisions *)
val is_small_enough_coll_elim : repl_index list * typet -> bool

(* [pcoll1rand num t] is the probability of collision between a
   random value of type [t], and an independent value. The collision
   occurs [num] times. *) 
val pcoll1rand : probaf -> typet -> probaf

(* [pcoll2rand num t] is the probability of collision between two
   random values of type [t]. The collision occurs [num] times. *) 
val pcoll2rand : probaf -> typet -> probaf

(* [collect_array_indexes accu t] adds in [accu] the array indices that
   occur in the term [t]. *)
val collect_array_indexes : repl_index list ref -> term -> unit

(* [add_elim_collisions b1 b2] add the probability of collision between
   [b1] and [b2]
   Returns true when the probability is considered small enough to
   eliminate collisions, and false otherwise. (In the latter case,
   the probability is obviously not counted, and the collisions must
   not be eliminated by the caller.) *)
val add_elim_collisions : binder -> binder -> bool

(* [add_proba_red t1 t2 proba tl] adds the probability change that
   happens when reducing [t1] into [t2] using a "collision" statement.
   [proba] is the probability formula in that collision statement.
   [tl] is the correspondence between the "new" in the collision statement
   and the "new" in the process. 
   Returns true when the probability is considered small enough to
   eliminate collisions, and false otherwise. (In the latter case,
   the probability is obviously not counted, and the collisions must
   not be eliminated by the caller.) *)
val add_proba_red : term -> term -> probaf -> (binder * term) list -> bool

(* [reset coll_elim g] initializes probability counting.
   [g] is the whole game. [coll_elim] is the list of arguments of the
   "simplify" commands, which determines on which data of type marked 
   [passwd] we will eliminate collisions. *)
val reset : string list -> game -> unit

(* [final_add_proba coll_list] computes the final probability of
   collisions. [coll_list] is a list of probabilities of complex collisions
   coming from dependency analsysis, to be added to other probabilities
   of collisions. *)
val final_add_proba : probaf list -> setf list

(* [get_current_state()] returns the current state of eliminated collisions,
   to be restored by [restore_state internal_info] in case we want to undo
   the collision eliminations done between [get_current_state] and 
   [restore_state]. *)
val get_current_state : unit -> simplify_internal_info_t
val restore_state : simplify_internal_info_t -> unit
