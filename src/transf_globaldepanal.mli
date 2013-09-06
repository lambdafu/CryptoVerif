open Types

(* The "global_dep_anal" game transformation.
   This transformation can be called in two ways:
   - the normal game transformation, function main
   - as a subtransformation of "simplify", called from simplify.ml, function check_all_deps
   *)

(* Local advice *)
val advise : instruct list ref

val check_all_deps : binder -> game ->
  (game * ((repl_index list * term list) * (term * term * typet list)) list) option

(* When calling [main], the terms and processes in the input game must be physically
   distinct, since [Terms.build_def_process] is called.  *)
val main : binder -> string list -> game_transformer
