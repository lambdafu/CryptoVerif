type extent = Lexing.position * Lexing.position

exception Error of string * extent

val accept_arobase : bool ref
val dummy_ext : extent
val next_line : Lexing.lexbuf -> unit
val extent : Lexing.lexbuf -> extent
val parse_extent : unit -> extent
val combine_extent : extent -> extent -> extent
val display_error : string -> extent -> unit
val input_error : string -> extent -> 'a
val input_warning : string -> extent -> unit
val user_error : string -> 'a
val internal_error : string -> 'a
(* Get a string representation of an extent. *)
val file_position : extent -> string
(* Get a string representation of the second extent, without displaying the
   file name when it is equal to the file given in the first extent. *)
val in_file_position : extent -> extent -> string

(*String parsing*)
val clear_buffer : unit -> unit
val get_string : unit -> string
val add_char : char -> unit
val char_backslash : char -> char

