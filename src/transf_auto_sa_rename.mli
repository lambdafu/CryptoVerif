open Types

(* [auto_sa_rename p] renames variables that are defined in find
   conditions, defined several times, and have no array references *)

val auto_sa_rename : game_transformer
