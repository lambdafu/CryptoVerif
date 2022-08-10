open Types

(* [remove_assignments sarename_new rem_set] replaces variables with their values
   in the input game, as designated by [rem_set], and renames variables defined
   by "new" that do not have array accesses to distinct names if [sarename_new] is true.
   The terms and processes in the input game must be physically
   distinct, since [Terms.build_def_process] is called. The terms and
   processes in the returned game (and in the intermediate games
   inside the transformation) are guaranteed to be physically
   distinct, by adequate copies of the replaced terms. *)

val remove_assignments : bool -> rem_set -> game_transformer

val remove_assignments_eqside : eqmember -> eqmember
