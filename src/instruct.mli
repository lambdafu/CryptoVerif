open Types

val do_proof : Ptree.ident list list option -> state -> unit

val execute_with_advise_last : state -> instruct -> state
