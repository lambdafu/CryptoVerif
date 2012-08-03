open Types

(* [sa_rename b p] renames all occurrences of b with distinct names,
   expanding code with array references to b if necessary *)

val sa_rename : binder -> game_transformer

