type 'a occ_map = (int * int * 'a) list

let empty = []

let add map min_occ max_occ image =
  if max_occ < min_occ then
    Parsing_helper.internal_error "max_occ not set properly";
  (min_occ, max_occ, image) :: map

let rec find occ = function 
    [] -> raise Not_found
  | (min_occ, max_occ, image)::rest ->
      if (min_occ <= occ) && (occ <= max_occ) then image else find occ rest

  
