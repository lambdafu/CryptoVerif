{
open Parsing_helper
open Parser
open Types
  
let create_hashtable size init =
  let tbl = Hashtbl.create size in
  List.iter (fun (key,data) -> Hashtbl.add tbl key data) init;
  tbl

let comment_depth = ref 0
let comment_extent_list = ref []

let in_proof = ref false
    
let common_keywords =
[ "new", NEW;
  "in", IN;
  "if", IF;
  "then", THEN;
  "else", ELSE;
  "find", FIND;
  "orfind", ORFIND;
  "suchthat", SUCHTHAT;
  "fun", FUN;
  "param", PARAM;
  "forall", FORALL;
  "exists", EXISTS;
  "equation", EQUATION;
  "builtin", BUILTIN;
  "proba", PROBA;
  "type", TYPE;
  "equiv", EQUIV;
  "process", PROCESS;
  "let", LET;
  "query", QUERY;
  "secret", SECRET;
  "public_vars", PUBLICVARS;
  "const", CONST;
  "set", SET;
  "defined", DEFINED;
  "collision", COLLISION;
  "event", EVENT;
  "time", TIME;
  "yield", YIELD;
  "event_abort", EVENT_ABORT;
  "maxlength", MAXLENGTH;
  "length", LENGTH;
  "max", MAX;
  "min", MIN;
  "eps_find", EPSFIND;
  "eps_rand", EPSRAND;
  "Pcoll1rand", PCOLL1RAND;
  "Pcoll2rand", PCOLL2RAND;
  "number", NUMBER;
  "foreach", FOREACH;
  "do", DO;
  "return", RETURN;
  "def", DEFINE;
  "expand", EXPAND;
  "proof", PROOF;
  "implementation", IMPLEMENTATION;
  "get", GET;
  "insert", INSERT;
  "table", TABLE;
  "letfun", LETFUN;
  "letproba", LETPROBA;
  "equivalence", EQUIVALENCE;
  "query_equiv", QUERY_EQUIV;
  "special", SPECIAL;
  "inf", FLOAT infinity
]  
    
let keyword_table_channel =
  create_hashtable 11
    ([ "out", OUT;
       "newChannel", NEWCHANNEL;
       "channel", CHANNEL ]
     @ common_keywords)

let keyword_table_oracle = 
  create_hashtable 11
    (("newOracle", NEWORACLE)::("run", RUN)::common_keywords)

let keyword_table_proof =
  create_hashtable 11
    [ "set", SET;
      "insert", INSERT;
      "at", AT;
      "at_nth", AT_NTH;
      "before", BEFORE;
      "before_nth", BEFORE_NTH;
      "after", AFTER;
      "after_nth", AFTER_NTH;
      "terms", TERMS;
      "variables", VARIABLES;
      "remove_assign", REMOVE_ASSIGN;
      "use_variable", USE_VARIABLE;
      "useless", USELESS;
      "findcond", FINDCOND;
      "all", ALL;
      "binder", BINDER;
      "move", MOVE;
      "noarrayref", NOARRAYREF;
      "random", RANDOM;
      "random_noarrayref", RANDOM_NOARRAYREF;
      "assign", ASSIGN;
      "array", ARRAY;
      "simplify", SIMPLIFY;
      "coll_elim", COLL_ELIM;
      "insert_event", INSERT_EVENT;
      "replace", REPLACE;
      "merge_arrays", MERGE_ARRAYS;
      "merge_branches", MERGE_BRANCHES;
      "SArename", SARENAME;
      "global_dep_anal", GLOBAL_DEP_ANAL;
      "expand", EXPAND;
      "all_simplify", ALL_SIMPLIFY;
      "crypto", CRYPTO;
      "start_from_other_end", START_FROM_OTHER_END;
      "quit", QUIT;
      "success", SUCCESS;
      "show_game", SHOW_GAME;
      "occ", OCC;
      "show_state", SHOW_STATE;
      "show_facts", SHOW_FACTS;
      "show_equiv", SHOW_EQUIV;
      "show_commands", SHOW_COMMANDS;
      "out_game", OUT_GAME;
      "out_state", OUT_STATE;
      "out_facts", OUT_FACTS;
      "out_equiv", OUT_EQUIV;
      "out_commands", OUT_COMMANDS;
      "auto", AUTO;
      "allowed_collisions", ALLOWED_COLLISIONS;
      "undo", UNDO;
      "restart", RESTART;
      "forget_old_games", FORGET_OLD_GAMES;
      "help", HELP;
      "interactive", INTERACTIVE;
      "types", TYPES;
      "focus", FOCUS;
      "tag", TAG;
      "special", SPECIAL;
      "assume", ASSUME;
      "guess", GUESS;
      "guess_branch", GUESS_BRANCH;
      "no_test", NO_TEST;
      "above", ABOVE
    ]
    
}

rule token = parse
  "\010" | "\013" | "\013\010"
     { Lexing.new_line lexbuf; token lexbuf }
| [ ' ' '\009' '\012' ] +
     { token lexbuf }
| [ 'a'-'z' 'A'-'Z' ] (( [ 'a'-'z' 'A'-'Z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '\'' '0'-'9' ] )*)
    { let s = Lexing.lexeme lexbuf in
         try
	   let keyword = Hashtbl.find
	       (if !in_proof then
		 keyword_table_proof
	       else
		 match !Settings.front_end with
	       Settings.Channels -> keyword_table_channel
	     | Settings.Oracles -> keyword_table_oracle) s
	   in
	   if keyword == PROOF then
	     in_proof := true;
	   keyword
         with Not_found ->
           IDENT (s, extent lexbuf)
     }
| '\"'    
    { 
      clear_buffer ();
      set_start_pos lexbuf;
      string lexbuf;
      STRING (get_string ()) } 

| ([ '0'-'9' ]) +
    { 
      try 
        INT (int_of_string(Lexing.lexeme lexbuf))
      with Failure _ ->
	raise (Error("Incorrect integer", extent lexbuf))
    }
| [ '0'-'9' ]+ ((('.' [ '0'-'9' ]*)? ['e' 'E'] ['+' '-']? [ '0'-'9' ]+) |  '.' [ '0'-'9' ]+)
     { FLOAT (float_of_string(Lexing.lexeme lexbuf)) }
| "(*" {
      comment_depth := 1;
      comment_extent_list := (extent lexbuf) :: !comment_extent_list;
         comment lexbuf;
         token lexbuf
}
| '_' { UNDERSCORE }
| ',' { COMMA }
| '(' { LPAREN }
| ')' { RPAREN }
| '[' { LBRACKET }
| ']' { RBRACKET }
| '{' { LBRACE }
| '}' { in_proof := false; RBRACE }
| '|' { BAR }
| ';' { SEMI }
| ':' { COLON }
| '!' { REPL }
| "<=" { LEQ }
| ">=" { GEQ }
| '=' { EQUAL }
| "<>" { DIFF }
| "&&" { AND }
| "||" { OR }
| '.' { DOT }
| "<=(" { EQUIVLEFT }
| ")=>" { EQUIVRIGHT } 
| "==>" { IMPLIES }
| '+' { ADD }
| '-' { SUB }
| '*' { MUL }
| '/' { DIV }
| '^' { POWER }
| '<' { LESS }
| '>' { GREATER }
| "->" { MAPSTO }
| ":=" { DEF }
| "<-" { LEFTARROW }
| "<-R" { RANDOM }
| '#' { COUNT }
| '?' { HELP }
| "inj-event" { INJEVENT }
| "independent-of" { INDEPOF }
| "optim-if" { OPTIMIF }
| "is-cst" { ISCST }
| eof { EOF }	
| _ { raise (Error("Illegal character", extent lexbuf)) }

and comment = parse
| "(*" {
    incr comment_depth;
    comment_extent_list := (extent lexbuf) :: !comment_extent_list;
    comment lexbuf }
| "*)"
    {
      decr comment_depth;
      comment_extent_list := List.tl !comment_extent_list;
      if !comment_depth = 0 then () else comment lexbuf
    }
| "\010" | "\013" | "\013\010"
     { Lexing.new_line lexbuf; comment lexbuf }
| eof { raise (Error("Unterminated comment", List.hd !comment_extent_list)) }
| _ { comment lexbuf }

and string = parse 
| '\"' { set_end_pos lexbuf }
| '\\' ['\\' '\'' '"' 'n' 't' 'b' 'r']
      { 
        add_char (char_backslash (Lexing.lexeme_char lexbuf 1));
        string lexbuf
      }
| '\\' _
      { raise (Error("Illegal escape", extent lexbuf)) }
| "\010" | "\013" 
     { Lexing.new_line lexbuf; 
       add_char (Lexing.lexeme_char lexbuf 0);
       string lexbuf }
| "\013\010"
     { Lexing.new_line lexbuf;
       add_char (Lexing.lexeme_char lexbuf 0);
       add_char (Lexing.lexeme_char lexbuf 1);
       string lexbuf  }
| eof 
      { raise (Error("Unterminated string", extent lexbuf)) }
| _ 
      { 
        add_char (Lexing.lexeme_char lexbuf 0);
        string lexbuf 
      }

and collision_matrix = parse
  "\010" | "\013" | "\013\010"
     { Lexing.new_line lexbuf; collision_matrix lexbuf }
| [ ' ' '\009' '\012' ] +
     { collision_matrix lexbuf }
| (( [ 'a'-'z' 'A'-'Z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '\'' '0'-'9' ] )*)
     { IDENT(Lexing.lexeme lexbuf, extent lexbuf) }
| ',' { COMMA }
| ';' { SEMI }
| "(*" {
         comment lexbuf;
         collision_matrix lexbuf
       }
| eof { EOF }	
| _ { raise (Error("Illegal character", extent lexbuf)) }
