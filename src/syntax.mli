open Types

val read_file : string -> (statement list) * (collision list) * (equiv list) * ((typet * equiv) list) * (query list) * Ptree.ident list list option * impl_process list * inputprocess
