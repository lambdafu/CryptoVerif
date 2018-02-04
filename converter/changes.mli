open Types

type change =
    Replace of string
  | Remove
  | ChEquation of Ptree.statement
  | ChEquiv of Ptree.eqstatement
  | ChCollision of Ptree.collision
  | ChQuery of Ptree.query list
  | ChProcess of inputprocess

val add_change : Parsing_helper.extent -> change -> unit
    
val get_changes : string -> (Parsing_helper.extent * change) list
    
    
      
