open Types

(* [crypto_transform stop no_advice e bl g] applies an equivalence e coming 
   from the definition of a cryptographic primitive to game g 
   bl is the list of names in p that correspond to names defined at the
   top of the left member of e
   when stop is true, do not add more names to the list bl
   when no_advice is true, only try the transformation without advice 

   The terms and processes in the input game must be physically
   distinct, since [Terms.build_def_process] is called. The terms and
   processes in the returned game are guaranteed to be physically
   distinct, since that game is returned by [Transf_expand.expand_process]
   which guarantees that by calling [Transf_auto_sa_rename.auto_sa_rename].
*)

val crypto_transform : bool -> bool -> equiv_nm -> binder list -> game -> trans_res

