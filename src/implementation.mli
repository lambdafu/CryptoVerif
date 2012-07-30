
open Types

(* takes the program list given by osyntax, checks if it is valid
   and then adds the read options in the list *)
val impl_check : impl_process list -> impl_process list
(* takes an inputprocess and its options, and returns the contents 
   of the implementation and interface files*)
val impl_translate : inputprocess -> impl_opt list -> (string*string)


