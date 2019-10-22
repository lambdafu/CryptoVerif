open Types

(* [insert_event occ s g] replaces the subprocess or term at occurrence [occ]
   with the event [s] in game [g] *)

val insert_event : int -> Parsing_helper.extent -> string -> game_transformer

