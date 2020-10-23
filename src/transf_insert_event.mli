open Types

(* [insert_event occ ext_o s ext_s g] replaces the subprocess or term at occurrence [occ]
   with the event [s] in game [g] *)

val insert_event : int -> Parsing_helper.extent -> string -> Parsing_helper.extent -> game_transformer

