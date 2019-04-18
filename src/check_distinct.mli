open Types

(* [check_distinct b g] show that elements of the array [b] 
   at different indices are always different (up to negligible probability).
   This is useful for showing secrecy of a key, and is called from success.ml.
   [g] is the full game. In addition to the boolean result, when it is true, 
   it also returns the probability of collisions eliminated to reach that 
   result.
*)
val check_distinct :  (* TO DO 'a *) 'a list ref option ->
  binder -> game -> bool * setf list
