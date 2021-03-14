open Types

val display_occurrences : bool ref
val display_arrays : bool ref
val display_list : ('a -> unit) -> 'a list -> unit

val display_binder : binder -> unit
val display_term : term -> unit
val display_statement : statement -> unit
val display_pattern : pattern -> unit
val display_equiv : equiv_nm -> unit
val display_process : inputprocess -> unit

val display_bl_assoc : binder list -> unit
val display_query : query * game -> unit
val display_instruct : instruct -> unit

val display_state : state -> unit

val print_string : string -> unit
val start : unit -> unit
val stop : unit -> unit
val file_out : string -> Parsing_helper.extent -> (unit -> unit) -> unit
