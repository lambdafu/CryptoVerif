open Types

val display_occurrences : bool ref
val display_arrays : bool ref

val display_statement : statement -> unit
val display_equiv : equiv_nm -> unit
val display_process : inputprocess -> unit

val display_state : state -> unit

val print_string : string -> unit
val start : unit -> unit
val stop : unit -> unit
val file_out : string -> Parsing_helper.extent -> (unit -> unit) -> unit
