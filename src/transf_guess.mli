open Types

(* Guess replication index or variable *)
  
val guess : guess_arg_t -> state -> game_transformer

(* Guess a branch *)
  
val guess_branch : int(*occurrence*) -> bool(* true when "no_test"*) -> Parsing_helper.extent -> state -> game_transformer

(* [next_case state] returns 
   - [Some next_g] where [next_g] is the game to prove the queries in the next 
   case (next branch). 
   - [None] in case all branches have already been proved *)
val next_case : state -> game option
 
