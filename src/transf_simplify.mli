open Types

(* The "simplify" game transformation
   The terms and processes in the input game must be physically
   distinct, since [Terms.build_def_process] is called. The terms and
   processes in the returned game (and in the intermediate games
   inside the transformation) are guaranteed to be physically
   distinct, by calling [Transf_auto_sa_rename.auto_sa_rename].
 *)

val simplify_main : known_when_adv_wins option -> coll_elim_t list -> game_transformer


