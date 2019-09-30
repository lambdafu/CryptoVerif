open Types

(* 1. Is a type large? (i.e. the inverse of its cardinal is negligible) *)

(* Returns true when the type has size >= Settings.tysize_MIN_Auto_Coll_Elim
   i.e. collisions should be automatically elimminated on this type. *)
val is_large : typet -> bool

(* List of variables/types/occurrences that are considered to be large, even if
   only declared "password" *)
val elim_collisions_on_password_occ : coll_elim_t list ref

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

(* [is_small_enough_coll_elim proba] tests if 
   [proba] is considered small enough to eliminate collisions *)
val is_small_enough_coll_elim : probaf_mul_types -> bool

(* [pcoll1rand t] is the probability of collision between a
   random value of type [t], and an independent value. *) 
val pcoll1rand : typet -> probaf

(* [pcoll2rand t] is the probability of collision between two
   random values of type [t]. *) 
val pcoll2rand : typet -> probaf

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

(* [add_proba_red t1 t2 side_cond proba tl] adds the probability change that
   happens when reducing [t1] into [t2] using a "collision" statement.
   [side_cond] is a side condition that must hold to be able to 
   apply the "collision" statement.
   [proba] is the probability formula in that collision statement.
   [tl] is the correspondence between the "new" and variables with
   independence conditions in the collision statement
   and their value in the process. 
   Returns true when the probability is considered small enough to
   eliminate collisions, and false otherwise. (In the latter case,
   the probability is obviously not counted, and the collisions must
   not be eliminated by the caller.) *)
val add_proba_red : term -> term -> term -> probaf -> (binder * term) list -> bool

(* [add_proba_red_inside t1 t2 side_cond ri_list probaf_mul_types] 
   also adds the probability change that happens when reducing 
   [t1] into [t2] using a "collision" statement.
   [side_cond] is a side condition that must hold to be able to 
   apply the "collision" statement.
   The probability in question is the product of cardinals of
   the types of indices in [ri_list] times the probability
   multiplied by cardinals of types in [probaf_mul_types].
   Returns true when the probability is considered small enough to
   eliminate collisions, and false otherwise. (In the latter case,
   the probability is obviously not counted, and the collisions must
   not be eliminated by the caller.) *)
val add_proba_red_inside : red_proba_t -> bool

(* [equal_probaf_mul_types probaf_mul_types probaf_mul_types'] tests
   equality between values of type [probaf_mul_types] *)
val equal_probaf_mul_types : probaf_mul_types -> probaf_mul_types -> bool

val equal_coll : binder_coll_t -> binder_coll_t -> bool

val equal_red : red_proba_t -> red_proba_t -> bool
    
(* [proba_for probaf_mul_types] returns the probability equal
   to the probability multiplied by cardinals of types in
   [probaf_mul_types]. It also displays this probability. *)
val proba_for : probaf_mul_types -> probaf
    
(* [reset coll_elim g] initializes probability counting.
   [g] is the whole game. [coll_elim] is the list of arguments of the
   "simplify" commands, which determines on which data of type marked 
   [passwd] we will eliminate collisions. *)
val reset : coll_elim_t list -> game -> unit

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
val get_and_empty_state : unit -> simplify_internal_info_t
val restore_state : simplify_internal_info_t -> unit
