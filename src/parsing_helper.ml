open Lexing

let internal_error mess =
  print_string ("Internal error: " ^ mess ^ "\nPlease report bug to Bruno.Blanchet@inria.fr, including input file and output\n");
  exit 3

(* extent, for error messages *)

type extent = Lexing.position * Lexing.position

exception Error of string * extent

let dummy_ext = (Lexing.dummy_pos, Lexing.dummy_pos)

let merge_ext (p1,_) (_,p2) = (p1,p2)

let extent lexbuf = 
  (Lexing.lexeme_start_p lexbuf,
   Lexing.lexeme_end_p lexbuf)

let set_start lexbuf (loc_start, _) =
  if loc_start != Lexing.dummy_pos then
    begin
      lexbuf.lex_abs_pos <- loc_start.pos_cnum;
      lexbuf.lex_start_p <- loc_start;
      lexbuf.lex_curr_p <- loc_start
    end
      
let parse_extent () =
  (Parsing.symbol_start_pos(),
   Parsing.symbol_end_pos())

let display_error mess (loc_start, loc_end) =
  if loc_start.pos_cnum = -1 then
    Printf.printf "Error: %s\n" mess
  else
    Printf.printf "Character %d - character %d:\nError: %s\n"
      loc_start.pos_cnum
      loc_end.pos_cnum
      mess

let line_position (loc_start, loc_end) =
  let ch_start = loc_start.pos_cnum - loc_start.pos_bol +1 in
  let ch_end = loc_end.pos_cnum - loc_end.pos_bol+1 in
  if loc_start.pos_lnum = loc_end.pos_lnum then
    if ch_start = ch_end then
      Printf.sprintf "line %d, character %d"
	loc_start.pos_lnum ch_start
    else
      Printf.sprintf "line %d, characters %d-%d"
	loc_start.pos_lnum ch_start ch_end
  else
    Printf.sprintf "line %d, character %d - line %d, character %d"
      loc_start.pos_lnum ch_start
      loc_end.pos_lnum ch_end
      
let in_file_position (def_start,_) ((loc_start, _) as extent) =
  if loc_start.pos_cnum = -1 then
    "<unknown>"
  else
    if loc_start.pos_fname = def_start.pos_fname then
      line_position extent
    else
      "file \"" ^ loc_start.pos_fname ^ "\", " ^ (line_position extent)


let file_position ((loc_start, _) as extent) =
  if loc_start.pos_cnum = -1 then
    "<unknown>"
  else
    "File \"" ^ loc_start.pos_fname ^ "\", " ^ (line_position extent)

let input_error mess (loc_start, loc_end) =
  if loc_start.pos_cnum = -1 then
    Printf.printf "Error: %s\n" mess
  else
    Printf.printf "%s:\nError: %s\n"
      (file_position (loc_start, loc_end))
      mess;
  exit 2

let input_warning mess (loc_start, loc_end) =
  if loc_start.pos_cnum = -1 then
    Printf.printf "Warning: \n%s\n" mess
  else
    Printf.printf "%s:\nWarning: %s\n"
      (file_position (loc_start, loc_end))
      mess

let user_error mess =
  print_string mess;
  exit 2

(* Helper functions to lex strings *)
    
let buf = Buffer.create 64
let start_pos = ref Lexing.dummy_pos
let end_pos = ref Lexing.dummy_pos

(* The position of the beginning of a string is just after the opening quotation mark *)
let set_start_pos lexbuf = start_pos := Lexing.lexeme_end_p lexbuf
(* The position of the end of a string is just before the closing quotation mark *)
let set_end_pos lexbuf = end_pos := Lexing.lexeme_start_p lexbuf
    
let clear_buffer () =
  Buffer.reset buf

let get_string () =
  let s = Buffer.contents buf in
  clear_buffer ();
  (s, (!start_pos, !end_pos))

let add_char c =
  Buffer.add_char buf c

let char_backslash = function
    'n' -> '\n'
  | 't' -> '\t'
  | 'b' -> '\b'
  | 'r' -> '\r'
  | c -> c

