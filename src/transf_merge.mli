open Types

(* Test equality of processes modulo renaming of variables.
   Used to simplify tests and find: when all branches are equal,
   the test/find can be removed.
   There is room for more general equivalences between processes,
   but this is already a first step.
 *)

type 'a eqtester

val equal_oprocess : process eqtester
val equal_find_cond : term eqtester

val equal : 'a eqtester -> simp_facts -> 'a -> 'a -> bool
val can_merge_all_branches : 'a eqtester ->
    fact_info -> simp_facts -> 'a findbranch list -> 'a -> bool 
val can_merge_one_branch : 'a eqtester ->
    fact_info -> simp_facts -> 'a findbranch -> 'a -> bool 

(* [merge_arrays bll mode g] merges arrays 
   contained in [bll] in game [g]. [bll] is a list of list of variables, say
   bll = [[b11, ..., b1n],[b21, ..., b2n], ..., [bk1, ..., bkn]]
   Each list [bi1,...,bin] corresponds to variables to merge together; they
   are merged to bi1. See comments in mergebranches.ml for more details. *)

val merge_arrays : (binder * Parsing_helper.extent) list list -> merge_mode -> game_transformer

(* [merge_branches g] merges branches of find
   as much as possible in game [g] *)

val merge_branches : game_transformer
