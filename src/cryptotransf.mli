open Types

(* [crypto_transform stop no_advice e bl g] applies an equivalence e coming 
   from the definition of a cryptographic primitive to game g 
   bl is the list of names in p that correspond to names defined at the
   top of the left member of e
   when stop is true, do not add more names to the list bl
   when no_advice is true, only try the transformation without advice *)

val crypto_transform : bool -> bool -> equiv_nm -> binder list -> game -> trans_res

