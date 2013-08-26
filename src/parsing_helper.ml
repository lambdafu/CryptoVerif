open Lexing

exception IllegalCharacter
exception IllegalEscape
exception UnterminatedString

let accept_arobase = ref false

let internal_error mess =
  print_string ("Internal error: " ^ mess ^ "\nPlease report bug to Bruno.Blanchet@ens.fr, including input file and output\n");
  exit 3

(* extent, for error messages *)

type extent = Lexing.position * Lexing.position

exception Error of string * extent

let dummy_ext = (Lexing.dummy_pos, Lexing.dummy_pos)

let next_line lexbuf =
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with 
			 pos_bol = lexbuf.lex_curr_p.pos_cnum;
			 pos_lnum = lexbuf.lex_curr_p.pos_lnum + 1 }

let extent lexbuf = 
  (Lexing.lexeme_start_p lexbuf,
   Lexing.lexeme_end_p lexbuf)

let parse_extent () =
  (Parsing.symbol_start_pos(),
   Parsing.symbol_end_pos())

let combine_extent ((outer_start, _) as outer_ext) ((inner_start, inner_end) as inner_ext) =
  if inner_ext == dummy_ext then outer_ext else
  if outer_ext == dummy_ext then inner_ext else
  ({ outer_start with 
     pos_cnum = outer_start.pos_cnum + inner_start.pos_cnum + 1 },
   { outer_start with 
     pos_cnum = outer_start.pos_cnum + inner_end.pos_cnum + 1 })

let display_error mess (loc_start, loc_end) =
  if loc_start.pos_cnum = -1 then
    Printf.printf "Error: %s\n" mess
  else
    Printf.printf "Character %d - character %d:\nError: %s\n"
      loc_start.pos_cnum
      loc_end.pos_cnum
      mess

let file_position (loc_start, loc_end) =
  if loc_start.pos_cnum = -1 then
    "<unknown>"
  else
    Printf.sprintf "File \"%s\", line %d, character %d - line %d, character %d"
      loc_start.pos_fname
      loc_start.pos_lnum (loc_start.pos_cnum - loc_start.pos_bol +1)
      loc_end.pos_lnum (loc_end.pos_cnum - loc_end.pos_bol+1)

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

let buf = ref (String.create 64)
let index = ref 0

let clear_buffer () =
  buf := String.create 64;
  index := 0

let get_string () =
  let s=String.sub (!buf) 0 (!index) in
    clear_buffer ();
    s

let add_char c =
    begin
      let buf_len = String.length (!buf) in
        if !index >= buf_len then
          let new_buf = String.create (buf_len * 2) in
            String.blit !buf 0 new_buf 0 buf_len;
            buf := new_buf
    end;
  (!buf).[!index] <- c;
  index := (!index) + 1

let char_backslash = function
    'n' -> '\n'
  | 't' -> '\t'
  | 'b' -> '\b'
  | 'r' -> '\r'
  | c -> c

