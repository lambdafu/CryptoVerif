open Types

(* 0. Operations on monomials *)

(* [same_monomial m1 m2] returns true when [m1] and [m2]
   are equal monomials. *)
val same_monomial : monomial -> monomial -> bool
    
(* [build_monomial l] returns a monomial representing the
   product of the probabilities in [l]. [l] must contain
   only basic probabilities, considered as variables of
   polynomials. *)
val build_monomial : probaf list -> monomial
  
(* 1. Operations on polynoms *)

val zero : polynom

(* [sum p1 p2] is the polynom [p1 + p2], where [p1] and [p2] are polynoms *)
val sum : polynom -> polynom -> polynom

(* [max p1 p2] is a polynom upper bound of the maximum of two polynoms 
   [p1] and [p2], assuming all variables are positive or zero *)
val max : polynom -> polynom -> polynom

(* [sub p1 p2] is the polynom [p1 - p2], where [p1] and [p2] are polynoms *)
val sub : polynom -> polynom -> polynom

(* [product p1 p2] is the polynom [p1 * p2], where [p1] and [p2] are polynoms *)
val product : polynom -> polynom -> polynom

(* [power_to_polynom_map f x n] is the polynom [f (x^n)] where [x] is
   a probability formula, and [f] maps probability formulas to
   polynoms and maps product, division, and power to product,
   division, and power respectively. *)
val power_to_polynom_map : (probaf -> polynom) -> probaf -> int -> polynom

(* Tests. They answer true only when the result is true.
   In case the result is not know for sure, they answer false. *)
val is_constant : polynom -> bool
val is_zero : polynom -> bool
val is_positive : polynom -> bool
val is_nonnegative : polynom -> bool
    
(* 2. Basic operations on probabilities, with simple simplifications *) 

val p_div : probaf * probaf -> probaf
val p_mul : probaf * probaf -> probaf
val p_prod : probaf list -> probaf
val p_add : probaf * probaf -> probaf
val p_sum : probaf list -> probaf

(* [minmax_accu] represents the maximum or minimum of some probabilities 
   [empty_minmax_accu] is the maximum or minimum of no probability at all

   [add_max accu_ref p] modifies [accu_ref] into [max (!accu_ref) p]
   [p_max accu] converts [accu] into a probability, for computing the maximum

   [add_min] and [p_min] are similar for the minimum. *)
type minmax_accu
val empty_minmax_accu : minmax_accu
val add_max : minmax_accu ref -> probaf -> unit
val p_max : minmax_accu -> probaf
val add_min : minmax_accu ref -> probaf -> unit
val p_min : minmax_accu -> probaf
    
(* 3. Conversion probaf/polynom *)

val probaf_to_polynom : probaf -> polynom
val polynom_to_probaf : polynom -> probaf 
