open Types

val read_file : string -> (statement list) * (collision list) * (equiv list) * ((typet * equiv) list) * (query list) * Ptree.command list option * impl_process list * final_process

val check_query : Ptree.query -> query
