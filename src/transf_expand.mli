open Types

(* [expand_process p] expands the expressions If, Let, and Find 
   into processes If, Let, and Find; expressions If, Let, Find
   may be left in conditions of Find, when they cannot be expanded. *)

val expand_process : game_transformer

