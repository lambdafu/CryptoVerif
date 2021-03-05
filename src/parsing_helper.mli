type extent

exception Error of string * extent

val raise_error : string -> extent -> 'a
val raise_user_error : string -> 'a    

(* Integer operations that check overflow 
   [ovf_dim] is the error message in case the overflow happens
   when computing a dimension.
   [<op>_check_overflow msg ext n1 n2] computes [n1 <op> n2]
   and raises [Error(msg,ext)] in case of overflow. *)
    
val ovf_dim : string
val add_check_overflow : string -> extent -> int -> int -> int
val sub_check_overflow : string -> extent -> int -> int -> int
val mul_check_overflow : string -> extent -> int -> int -> int
    
val dummy_ext : extent
val merge_ext : extent -> extent -> extent
val extent : Lexing.lexbuf -> extent
val parse_extent : unit -> extent
val set_start : Lexing.lexbuf -> extent -> unit
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
val get_string : unit -> string * extent
val set_start_pos : Lexing.lexbuf -> unit
val set_end_pos : Lexing.lexbuf -> unit
val add_char : char -> unit
val char_backslash : char -> char

