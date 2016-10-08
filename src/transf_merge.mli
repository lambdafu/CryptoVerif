open Types

(* [merge_arrays bll mode g] merges arrays 
   contained in [bll] in game [g]. [bll] is a list of list of variables, say
   bll = [[b11, ..., b1n],[b21, ..., b2n], ..., [bk1, ..., bkn]]
   Each list [bi1,...,bin] corresponds to variables to merge together; they
   are merged to bi1. See comments in mergebranches.ml for more details.

   The terms and processes in the input game must be physically
   distinct, since [Terms.build_def_process] is called. The terms and
   processes in the returned game are *not* guaranteed to be physically
   distinct. They are made distinct later in instruct.ml by calling
   [Terms.move_occ_process].
 *)

val merge_arrays : (binder * Parsing_helper.extent) list list -> merge_mode -> game_transformer

(* [merge_branches g] merges branches of find
   as much as possible in game [g].

   The terms and processes in the input game must be physically
   distinct, since [Terms.build_def_process] is called. *)

val merge_branches : game_transformer
