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

(* 3. Evaluation of conditions OptimIf in probabilities.
   [is_sure_cond to_polynom cond] returns true when the condition
   [cond] is certainly true. That allows using the [then]
   branch of the [optim-if] condition; otherwise, the [else]
   branch is used.
   [to_polynom] converts a probability formula into a polynom,
   possibly performing transformation on the way, such as 
   instantiating variables of the probability formula with their values. *)

val is_sure_cond : (probaf -> polynom) -> optimcond -> bool
    
(* 4. Computation of probabilities of collisions *)

(* Optimize a probability formula using #O when possible *)
val optim_probaf : probaf_mul_types -> probaf_mul_types
    
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

(* [add_proba_find cur_array l0 find_info] adds the probability coming from
   reorganization of branches of a find with branches [l0] and options [find_info].
   [cur_array] are the current replication indices at that find. 
   This extremely small probability comes from the fact that the distribution
   used to select the find branch and indices when there are several choices
   is not exactly uniform. It is ignored by default. *)
val add_proba_find : repl_index list -> 'a findbranch list -> find_info -> unit
    
(* [add_elim_collisions b1 b2] add the probability of collision between
   [b1] and [b2]
   Returns true when the probability is considered small enough to
   eliminate collisions, and false otherwise. (In the latter case,
   the probability is obviously not counted, and the collisions must
   not be eliminated by the caller.) *)
val add_elim_collisions : binder -> binder -> bool
val add_elim_collisions_inside : binder_coll_t -> bool
    
(* [proba_for_collision (b1, b2, _)] returns the probability of
   collision between [b1] and [b2], and displays it. *)
val proba_for_collision : binder_coll_t -> probaf
    
(* [add_proba_red coll_statement restr_indep_map any_var_map] 
   adds the probability change that happens when applying the
   collision statement [coll_statement] with variables
   bound as defined by [restr_indep_map] and [any_var_map].
   [restr_indep_map] is the correspondence between the "new" and variables with
   independence conditions in the collision statement
   and their value in the process. 
   [any_var_map]  is the correspondence between other variables 
   in the collision statement and their value in the process. 
   Returns true when the probability is considered small enough to
   eliminate collisions, and false otherwise. (In the latter case,
   the probability is obviously not counted, and the collisions must
   not be eliminated by the caller.) *)
val add_proba_red : collision -> (binder * term) list ->
  (binder * term) list -> bool

(* [add_proba_red_inside (t1, t2, side_cond, probaf_mul_types)] 
   also adds the probability change that happens when reducing 
   [t1] into [t2] using a "collision" statement.
   [side_cond] is a side condition that must hold to be able to 
   apply the "collision" statement.
   The probability in question is the probability
   multiplied by cardinals of types in [probaf_mul_types].
   Returns true when the probability is considered small enough to
   eliminate collisions, and false otherwise. (In the latter case,
   the probability is obviously not counted, and the collisions must
   not be eliminated by the caller.) *)
val add_proba_red_inside : red_proba_t -> bool

(* [proba_for_red_proba (t1, t2, side_cond, probaf_mul_types)]
   returns the probability of reducing [t1] into [t2] 
   using a "collision" statement, assuming [side_cond] holds,
   as stored in [probaf_mul_types], and displays it. *)
val proba_for_red_proba : red_proba_t -> probaf

(* Name for joker variables, which may contain anything *)
val any_term_name : string
    
(* [match_term_any_var any_vars_opt next_f t t' ()] calls [next_f()] when [t']
   is an instance of [t], with
   any value for the [?] variables when [any_vars_opt == None],
   values stored in links for variables in the list [any_vars] 
   when [any_vars_opt = Some any_vars],
   and values stored in links for replication indices.
   It raises [NoMatch] when [t'] is not an instance of [t]. *)
val match_term_any_var : binder list option ->
  (unit -> 'a) -> term -> term -> unit -> 'a

(* The function [instantiate_ri_list] replace indices with their
   value stored in links, inside the [p_ri_list] field
   of [probaf_mul_types].
   The functions [copy_probaf_mul_types] and [copy_red_proba] copy 
   respectively probaf_mul_types and red_proba_t, following links
   according to [transf] (see [Terms.copy_transf]). 
   [transf] must be [Terms.Links_RI] or [Terms.Links_RI_Vars],
   to be coherent with following links in replication indices
   in [instantiate_ri_list].
   *)
val instantiate_ri_list : repl_index list -> repl_index list -> repl_index list
val copy_probaf_mul_types : Terms.copy_transf -> probaf_mul_types -> probaf_mul_types
val copy_red_proba : Terms.copy_transf -> red_proba_t -> red_proba_t
    
(* [equal_probaf_mul_types probaf_mul_types probaf_mul_types'] tests
   equality between values of type [probaf_mul_types] *)
val equal_probaf_mul_types : probaf_mul_types -> probaf_mul_types -> bool

val equal_coll : binder_coll_t -> binder_coll_t -> bool

(* [equal_red red1 red2] is true when the [red_proba_t] elements
   [red1] and [red2] are equal *)
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

(* The state used in this module contains probabilities coming from
   non-uniformity of choices in [find], collisions between random variables,
   and probabilities coming from [collision] statements.
   The module [Depanal] adds one more component. *)
    
(* [get_proba coll_list] computes the final probability of
   collisions. [coll_list] is a list of probabilities of complex collisions
   coming from dependency analsysis, to be added to other probabilities
   of collisions.
   [final_add_proba coll_list] additionally cleans up the state.
   One must call [reset] to initialize it again, before counting
   probabilities. *)
val get_proba : probaf list -> setf list
val final_add_proba : probaf list -> setf list

(* [get_current_state()] returns the current state of eliminated collisions,
   to be restored by [restore_state state] in case we want to undo
   the collision eliminations done between [get_current_state] and 
   [restore_state]. *)
val get_current_state : unit -> simplify_internal_info_t

(* [get_and_empty_state()] returns the current state of eliminated collisions,
   like [get_current_state()] but additionally removes the eliminated collisions
   from the current state. The probability module is still initialized to be able
   to count probabilities. *)
val get_and_empty_state : unit -> simplify_internal_info_t

(* [final_empty_state()] clears the probability state. 
   One must call [reset] to initialize it again, before counting
   probabilities. *)
val final_empty_state : unit -> unit

(* [restore_state state] restores a previous probability state,
   typically obtained via [get_current_state()] or [get_and_empty_state()].
   The collisions eliminated before [restore_state] are forgotten. *)
val restore_state : simplify_internal_info_t -> unit

(* [readd_state state] adds the collisions eliminated in state [state]
   to the collisions currently eliminated. Collisions eliminated
   both in [state] and in the current state are counted once. *)
val readd_state : simplify_internal_info_t -> unit

(* [empty_proba_state] is the empty probability state, with no
   collision eliminated. *)
val empty_proba_state : simplify_internal_info_t

(* [display_proba_state state] displays the probability state [state].
   Used for debugging. *)
val display_proba_state : simplify_internal_info_t -> unit
    
val is_complex_time : probaf -> bool
    
