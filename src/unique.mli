open Types

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

val infer_unique : game -> repl_index list -> simp_facts -> program_points_args list -> binderref list ->
                   dep_anal -> known_history option ->
                   'a findbranch list -> find_info -> find_info * bool

(* [prove_unique_game initial g] proves that find[unique?], that is, 
   with find_info = UniqueToProve, in [g] are really unique. 
   - When [initial = true], a failure is an error (raises [Error]), except when 
   [Settings.allow_unproved_unique = true], in which case it is a warning.
   The performed transformation is recorded in the result as [DProveUnique]
   or [DProveUniqueFailed] in case of failure. This case is for use on the 
   initial game, after expanding tables.
   - When [initial = false], a failure is always an error, which raises 
   exception [Error]. The performed transformation is not recorded in the result,
   as it is considered to be part of the [insert] command. This case is for use 
   in command [insert]. *)
val prove_unique_game : bool -> game_transformer
