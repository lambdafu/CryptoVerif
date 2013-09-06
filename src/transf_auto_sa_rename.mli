open Types

(* [auto_sa_rename] renames variables that are defined in find
   conditions, defined several times, and have no array references.
   Additionally, it also guarantees that all terms and processes in
   the returned game are physically distinct, which is needed as a 
   precondition to [Terms.build_def_process]. *)

val auto_sa_rename : game_transformer
