open Types

(* 1. Operations on polynoms *)

val zero : polynom

val sum : polynom -> polynom -> polynom
val max : polynom -> polynom -> polynom
val sub : polynom -> polynom -> polynom
val product : polynom -> polynom -> polynom

(* 2. Basic operations on probabilities, with simple simplifications *) 

val p_div : probaf * probaf -> probaf
val p_mul : probaf * probaf -> probaf
val p_prod : probaf list -> probaf
val p_add : probaf * probaf -> probaf
val p_sum : probaf list -> probaf

(* [max_accu] represents the maximum of some probabilities 
   [empty_max_accu] is the maximum of no probability at all
   [add_max accu_ref p] modifies [accu_ref] into [max (!accu_ref) p]
   [p_max accu] converts [accu] into a probability *)
type max_accu
val empty_max_accu : max_accu
val add_max : max_accu ref -> probaf -> unit
val p_max : max_accu -> probaf
    
(* 3. Conversion probaf/polynom *)

val probaf_to_polynom : probaf -> polynom
val polynom_to_probaf : polynom -> probaf 
