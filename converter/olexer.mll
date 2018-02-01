{
open Parsing_helper
open Oparser
open Changes

let create_hashtable size init =
  let tbl = Hashtbl.create size in
  List.iter (fun (key,data) -> Hashtbl.add tbl key data) init;
  tbl

let keyword_table =
  create_hashtable 11
[ "if", IF;
  "then", THEN;
  "else", ELSE;
  "find", FIND;
  "orfind", ORFIND;
  "suchthat", SUCHTHAT;
  "fun", FUN;
  "param", PARAM;
  "forall", FORALL;
  "equation", EQUATION;
  "proba", PROBA;
  "type", TYPE;
  "equiv", EQUIV;
  "process", PROCESS;
  "let", LET;
  "in", IN;
  "query", QUERY;
  "secret", SECRET;
  "secret1", SECRET1;
  "public_vars", PUBLICVARS;
  "const", CONST;
  "set", SET;
  "defined", DEFINED;
  "collision", COLLISION;
  "event", EVENT;
  "time", TIME;
  "end", END;
  "event_abort", EVENT_ABORT;
  "otheruses", OTHERUSES;
  "maxlength", MAXLENGTH;
  "length", LENGTH;
  "max", MAX;
  "eps_find", EPSFIND;
  "eps_rand", EPSRAND;
  "Pcoll1rand", PCOLL1RAND;
  "Pcoll2rand", PCOLL2RAND;
  "newOracle", NEWORACLE;
  "inj", INJ;
  "foreach", FOREACH;
  "do", DO;
  "return", RETURN;
  "define", DEFINE;
  "expand", EXPAND;
  "proof", PROOF;
  "implementation", IMPLEMENTATION;
  "get", GET;
  "insert", INSERT;
  "table", TABLE;
  "letfun", LETFUN
]

}

rule token = parse
  "\010" | "\013" | "\013\010"
     { next_line lexbuf; token lexbuf }
| [ ' ' '\009' '\012' ] +
     { token lexbuf }
| [ '@' 'a'-'z' 'A'-'Z' ] (( [ '@' 'a'-'z' 'A'-'Z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '\'' '0'-'9' ] )*)
     { let s = Lexing.lexeme lexbuf in
       (* The keyword "define" becomes "def" *)
       if s = "define" then
         Changes.add_change (extent lexbuf) (Replace "def");
       try
	 Hashtbl.find keyword_table s
       with Not_found ->
	 if (not (!accept_arobase)) && (String.contains s '@') then
	   raise (Error("Illegal character", extent lexbuf));
         IDENT (s, extent lexbuf)
     }
| '\"'
    { 
      clear_buffer ();
      string lexbuf;
      STRING (get_string (),extent lexbuf) } 
| ([ '0'-'9' ]) +
    { 
      try 
        INT (int_of_string(Lexing.lexeme lexbuf))
      with Failure _ ->
	raise (Error("Incorrect integer", extent lexbuf))
    }
| ([ '0'-'9' ]) + '.' ([ '0'-'9' ])+
     { FLOAT (float_of_string(Lexing.lexeme lexbuf)) }
| "(*" {
         comment lexbuf;
         token lexbuf
       }
| ',' { COMMA }
| '(' { LPAREN }
| ')' { RPAREN }
| '[' { LBRACKET }
| ']' { RBRACKET }
| '{' { LBRACE }
| '}' { RBRACE }
| '|' { BAR }
| ';' { SEMI }
| ':' { COLON }
| "<=" { LEQ }
| '=' { EQUAL }
| "<>" { DIFF }
| "&&" { AND }
| "||" { OR }
| '.' { DOT }
| "<=(" { EQUIVLEFT }
| ")=>" { EQUIVRIGHT } 
| "==>" { IMPLIES }
| "->" { MAPSTO }
| ":=" { DEF }
| "<-" { LEFTARROW }
| "<-R" { RANDOM }
| '+' { ADD }
| '-' { SUB }
| '*' { MUL }
| '/' { DIV }
| '^' { POWER }
| '<' { READ }
| '>' { WRITE }
| '#' { COUNT }
| eof { EOF }	
| _ { raise (Error("Illegal character", extent lexbuf)) }

and comment = parse
| "*)" { }
| "\010" | "\013" | "\013\010"
     { next_line lexbuf; comment lexbuf }
| eof { }
| _ { comment lexbuf }

and string = parse 
| '\"' { () }
| '\\' ['\\' '\'' '"' 'n' 't' 'b' 'r']
      { 
        add_char (char_backslash (Lexing.lexeme_char lexbuf 1));
        string lexbuf
      }
| '\\' _
      { raise (Error("Illegal escape", extent lexbuf)) }
| eof 
      { raise (Error("Unterminated string", extent lexbuf)) }
| _ 
      { 
        add_char (Lexing.lexeme_char lexbuf 0);
        string lexbuf 
      }
      
