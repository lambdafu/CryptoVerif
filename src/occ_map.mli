(* Maps from occurrences to 'a *)

type 'a occ_map

val empty : 'a occ_map

(* [map_add map min_occ max_occ image] returns a map that
   maps all occurrences from [min_occ] to [max_occ] to [image],
   and all other occurrences like [map] *)

val add : 'a occ_map -> int -> int -> 'a -> 'a occ_map

(* [map_find occ map] returns the image of [occ] by [map] *)

val find : int -> 'a occ_map -> 'a
