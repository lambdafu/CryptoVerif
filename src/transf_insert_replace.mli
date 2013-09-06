open Types

(* [insert_instruct occ ext s ext' p] inserts instruction [s] at program
   point [occ] in [p] *)
val insert_instruct : int -> Parsing_helper.extent -> string -> Parsing_helper.extent ->
game_transformer

(* [replace_term simplify_internal_info occ ext s ext g] replaces the term
   at occurrence [occ] with [s] in game [g].

   The terms and processes in the input game must be physically
   distinct, since [Terms.build_def_process] is called. *)
val replace_term : int -> Parsing_helper.extent -> string -> Parsing_helper.extent -> game_transformer
