open Types

(* The "global_dep_anal" game transformation.
   This transformation can be called in two ways:
   - the normal game transformation, function main
   - as a subtransformation of "simplify", called from simplify.ml, function check_all_deps
   *)

(* Local advice *)
val advise : instruct list ref

(* [check_all_deps b0 init_proba_state g] is the entry point for calling 
   the dependency analysis from simplification.
   [b0] is the variable on which we perform the dependency analysis.
   [init_proba_state] contains collisions eliminated by before the dependency analysis,
   in previous passes of simplification.
   [g] is the full game to analyze. *)
val check_all_deps : binder -> simplify_internal_info_t * term_coll_t list -> 
  game -> game option

(* [main b0 coll_elim g] is the entry point for calling
   the dependency analysis alone.
   [b0] is the variable on which we perform the dependency analysis.
   [coll_elim] is a list of occurrences, types or variable names 
   for which we allow eliminating collisions even if they are not [large].
   [g] is the full game to analyze.

   When calling [main], the terms and processes in the input game must be physically
   distinct, since [Terms.build_def_process] is called.  *)
val main : binder -> coll_elim_t list -> game_transformer
