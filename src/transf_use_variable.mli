open Types

(* [use_variable l] transforms the game by replacing
   all terms equal to a variable [x] in the list [l]
   with [x]. The replacement is obviously done only
   when [x] is known to be defined. It is also done for
   array accesses. It is the inverse of [remove_assign]. *)
  
val use_variable : binder list -> game_transformer
