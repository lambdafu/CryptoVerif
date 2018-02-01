open Types

(* [expand_process] expands the expressions If, Let, and Find 
   into processes If, Let, and Find; expressions If, Let, Find
   may be left in conditions of Find, when they cannot be expanded. 

   This transformation begins with a basic simplification pass of the game,
   to avoid generating too large games.

   The terms and processes in the input game must be physically
   distinct, since [Terms.build_def_process] is called. The terms and
   processes in the returned game are guaranteed to be physically
   distinct, by calling [Transf_auto_sa_rename.auto_sa_rename].
*)

val expand_process : game_transformer

val final_pseudo_expand : repl_index list -> simp_facts -> term -> term

