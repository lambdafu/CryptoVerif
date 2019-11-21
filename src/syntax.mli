open Types

(* [parse_from_string parse_fun (s, ext)] parses the string [s] with
   extent [ext] using the parsing function [parse_fun]. *)
val parse_from_string : ((Lexing.lexbuf -> Parser.token) -> Lexing.lexbuf -> 'a) -> ident -> 'a

val read_file : string -> (statement list) * (collision list) * (equiv_nm list) * (query list) * Ptree.command list option * impl_process list * final_process

(* Transform a parsed query into a query as used by CryptoVerif
   Raises Error in case of error. *)
val check_query : Ptree.query -> query

val check_move_array_coll : Stringmap.env_type -> binder -> Ptree.move_array_coll_t -> move_array_collision

val check_eqstatement : bool -> Ptree.eqstatement -> equiv_nm
