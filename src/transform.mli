open Types

val queries : (query * game) list ref
val statements : statement list ref
val collisions : collision list ref
val equivs : equiv_nm list ref
val move_new_eq : (typet * equiv_nm) list ref

val collect_public_vars : unit -> unit
val occurs_in_queries : binder -> bool
val has_array_ref : binder -> bool
val event_occurs_in_queries : funsymb -> bool

(* [auto_sa_rename p] renames variables that are defined in find
   conditions, defined several times, and have no array references *)

val auto_sa_rename : game_transformer

(* [expand_process p] expands the expressions If, Let, and Find 
   into processes If, Let, and Find; expressions If, Let, Find
   may be left in conditions of Find, when they cannot be expanded. *)

val expand_process : game_transformer

(* [sa_rename b p] renames all occurrences of b with distinct names,
   expanding code with array references to b if necessary *)

val sa_rename : binder -> game_transformer

(* [remove_assignments rem_set p] replaces variables with their values
   in p, as designated by rem_set *)

val remove_assignments : rem_set -> game_transformer

(* [move_new_let move_set p] moves new/lets downwards as much as possible *)

val move_new_let : move_set -> game_transformer

(* [insert_event occ s g] replaces the subprocess at occurrence [occ]
   with the event [s] in game [g] *)

val insert_event : int -> string -> game_transformer


(* Set when a game is modified *)
val changed : bool ref

(* Instructions are added in advise when an instruction I cannot be fully
   performed. The added instructions correspond to suggestions of instructions
   to apply before I so that instruction I can be better performed. *)

val advise : instruct list ref

