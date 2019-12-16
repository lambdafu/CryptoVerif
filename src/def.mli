open Types

val def_term : (term * program_point) list ref option -> repl_index list -> def_node -> term list -> binderref list -> elsefind_fact list -> term -> def_node
val build_def_process : (term * program_point) list ref option -> inputprocess -> unit
val empty_def_process : inputprocess -> unit
