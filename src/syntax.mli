open Types

val read_file : string -> (statement list) * (collision list) * (equiv_nm list) * ((typet * equiv_nm) list) * (query list) * Ptree.command list option * impl_process list * final_process

(* Transform a parsed query into a query as used by CryptoVerif
   Raises Error in case of error. *)
val check_query : Ptree.query -> query
