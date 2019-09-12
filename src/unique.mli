open Types

(* [is_unique l0' find_info] returns Unique when a [find] is unique,
   that is, at runtime, there is always a single possible branch 
   and a single possible value of the indices:
   either it is marked [Unique] in the [find_info],
   or it has a single branch with no index.
   [l0'] contains the branches of the considered [find]. *)
val is_unique : 'a findbranch list -> find_info -> find_info

(* [infer_unique g cur_array simp_facts def_vars dep_info current_history l0' find_info]
   tries to prove that there is single possible choice in the find with
   branches [l0'], and if so it returns the modified [find_info] equal to
   [Unique]. It also returns a boolean set to true when a real change has been made.

   [g] is the current game
   [cur_array] the current replication indices
   [simp_facts] the facts known to hold at the current program point
   [def_vars] the variables known to be defined
   [dep_info] is a dependency analysis
   [current_history] is the known history at the find, at which [def_list]
   is tested (may be returned by [Facts.get_initial_history]) *)
val prove_unique : game -> repl_index list -> simp_facts -> binderref list ->
                   dep_anal -> known_history option ->
                   'a findbranch list -> bool
val infer_unique : game -> repl_index list -> simp_facts -> binderref list ->
                   dep_anal -> known_history option ->
                   'a findbranch list -> find_info -> find_info * bool
