open Types

(* [parse_from_string parse_fun (s, ext)] parses the string [s] with
   extent [ext] using the parsing function [parse_fun]. *)
val parse_from_string : ((Lexing.lexbuf -> Parser.token) -> Lexing.lexbuf -> 'a) -> ?lex : (Lexing.lexbuf -> Parser.token) -> ident -> 'a

val read_file : string -> (statement list) * (collision list) * (equiv_gen list) * (query list) * Ptree.command list option * impl_info * final_process

(* Transform a parsed query into a query as used by CryptoVerif
   Raises Error in case of error. *)
val check_query : Ptree.query -> query

val check_special_equiv_coll : Stringmap.env_type -> expect_t -> Ptree.special_equiv_coll_t -> special_equiv_collision

val check_eqstatement : bool -> Ptree.eqstatement -> equiv_gen
