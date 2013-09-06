open Types

(* [sa_rename b p] renames all occurrences of b with distinct names,
   expanding code with array references to b if necessary.

   The terms and processes in the input game must be physically
   distinct, since [Terms.build_def_process] is called.  *)

val sa_rename : binder -> game_transformer

