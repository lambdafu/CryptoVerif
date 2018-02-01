open Types

module StringMap : Map.S with type key = string

val env : Ptree.env_entry StringMap.t ref

val get_param : Ptree.env_entry StringMap.t -> string -> Parsing_helper.extent -> param
val get_type : Ptree.env_entry StringMap.t -> string -> Parsing_helper.extent -> typet
val get_type_or_param : Ptree.env_entry StringMap.t -> string -> Parsing_helper.extent -> typet
val get_process : Ptree.env_entry StringMap.t -> string -> Parsing_helper.extent -> Ptree.process_e
val get_table : Ptree.env_entry StringMap.t -> string -> Parsing_helper.extent -> table
val get_function : Ptree.env_entry StringMap.t -> string -> Parsing_helper.extent -> funsymb
