open Types
open Lexing

type change =
    Replace of string
  | Remove
  | ChEquation of Ptree.statement
  | ChEquiv of Ptree.eqstatement
  | ChCollision of Ptree.collision
  | ChQuery of Ptree.query list
  | ChProcess of inputprocess

let changes = ref ([] : (Parsing_helper.extent * change) list)

let add_change ext ch =
  changes := (ext, ch) :: (!changes)

let ch_compare ((loc_start1, loc_end1),_) ((loc_start2, loc_end2),_) =
  loc_start1.pos_cnum - loc_start2.pos_cnum

let rec check_ok = function
    [] | [_] -> ()
  | ((loc_start1, loc_end1),_)::(((loc_start2, loc_end2),_)::_ as r) ->
      if loc_start1.pos_fname <> loc_start2.pos_fname then
	Parsing_helper.internal_error "Changes are not all in the same file";
      if loc_end1.pos_cnum > loc_start2.pos_cnum then
	Parsing_helper.internal_error "Changes overlap";
      check_ok r
      
let get_changes fname =
  let changes_fname =
    List.filter (fun ((loc_start, loc_end), _) -> loc_start.pos_fname = fname) (!changes)
  in
  let changes_ordered = List.sort ch_compare changes_fname in
  check_ok changes_ordered;
  changes_ordered
