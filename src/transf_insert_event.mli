open Types

(* [get_event queries (s,ext_s)] returns a pair [(f,add_query)]
   where [f] is the symbol of the event named [s]
   and [add_query] is true when a query [event(f) ==> false] should be added *)
val get_event : cur_queries_t -> ident -> funsymb * bool

(* [insert_event occ ext_o s ext_s g] replaces the subprocess or term
   at occurrence [occ] with the event [s] in game [g] *)

val insert_event : int -> Parsing_helper.extent -> string ->
  Parsing_helper.extent -> game_transformer

