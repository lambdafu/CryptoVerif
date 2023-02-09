open Types

val empty_comp_process : inputprocess -> unit
(* [build_def_process] must be called before [build_compatible_defs] *)
val build_compatible_defs : inputprocess -> unit

(* [get_facts pp] returns the fact_info at program point [pp] *)
val get_facts : program_point -> fact_info

(* [incompatible_suffix_length_var_var b b'] returns a length [l] such that if
   [b[args]] and [b'[args']] are both defined, then the suffixes of
   length [l] of [args] and [args'] must be different.
   Raises [Not_found] when [b[args]] and [b'[args']] can be defined 
   for any [args,args']. *)
val incompatible_suffix_length_var_var : binder -> binder -> int
(* [is_compatible (b,args) (b',args')] returns true when
   [b[args]] and [b'[args']] may both be defined *)
val is_compatible : binderref -> binderref -> bool
(* [is_compatible_history (n,args) history] returns true when 
   the information in [history] is compatible with the execution
   of node [n] with indices [args] before that history. *)
val is_compatible_history : program_point_args -> known_history -> bool
(* [facts_compatible_history fact_accu (nl,args) history] returns
   [fact_accu] with additional facts inferred from the execution of a
   node in [nl] with indices [args] before the history [history]. *)
val facts_compatible_history : term list -> program_points_args -> known_history -> term list 
(* [both_def_add_fact fact_accu (b,args) (b',args')] returns [fact_accu] 
   after adding a fact that always holds when
   [b[args]] and [b'[args']] are both defined. *)
val both_def_add_fact : term list -> binderref -> binderref -> term list
(* [both_ppl_facts old_ppl ppl] returns facts
   inferred from the knowledge that the program points in [ppl] and
   [old_ppl] are both executed. It considers pairs 
   of variables in [ppl] and of one variable in [ppl]
   and one in [old_ppl], but does not consider pairs of variables
   in [old_ppl] as those should have been taken into account before.
   Uses the field "incompatible" set by Terms.build_compatible_defs
 *)
val both_ppl_facts : term list -> program_points_args list -> program_points_args list -> term list
(* [ppl_before_pp_facts fact_accu pp args def_list] returns [fact_accu] 
   after adding facts inferred from the knowledge that the variables in [def_list]
   are defined before the execution of program point [pp] with indices [args].
   (Typically, that some indices in [args] are different
   from some indices of variables in [def_list].) *)
val ppl_before_pp_facts : term list -> program_point_args -> program_points_args list -> term list
(* [both_pp (pp, args) (pp', args')] returns true when
   program point [pp] with indices [args] and 
   program point [pp'] with indices [args'] can both be executed. *)
val both_pp :  program_point_args -> program_point_args -> bool
(* [both_pp_add_fact fact_accu (ppa, lidxa) (ppb, lidxb)] returns [fact_accu] 
   after adding a fact inferred from the execution of both
   program point [ppa] with indices [lidxa] and 
   program point [ppb] with indices [lidxb], if any. *)
val both_pp_add_fact : term list ->
  program_point_args -> program_point_args -> term list
(* [both_pp_ppl (pp, args) (ppl', args')] returns true when
   program point [pp] with indices [args] and 
   a program point in [ppl'] with indices [args'] can both be executed. *)
val both_pp_ppl : program_point_args -> program_points_args -> bool
(* [both_pp_ppl_add_fact fact_accu (ppa, lidxa) (pplb, lidxb)] returns [fact_accu] 
   after adding a fact inferred from the execution of both
   program point [ppa] with indices [lidxa] and 
   a program point in [pplb] with indices [lidxb], if any. *)
val both_pp_ppl_add_fact : term list ->
  program_point_args -> program_points_args -> term list
(* [both_ppl_ppl_add_fact fact_accu (ppla, lidxa) (pplb, lidxb)] returns [fact_accu] 
   after adding a fact inferred from the execution of both
   a program point in [ppla] with indices [lidxa] and 
   a program point in [pplb] with indices [lidxb], if any. *)
val both_ppl_ppl_add_fact : term list ->
  program_points_args -> program_points_args -> term list
val both_ppl_ppl_add_facts : term list ->
  program_points_args list -> program_points_args list -> term list
(* [may_def_before (b,args) (b',args')] returns true when
   [b[args]] may be defined before or at the same time as [b'[args']] *)
val may_def_before : binderref -> binderref -> bool

(* [is_under pp pp'] returns true when the program point [pp]
   is syntactically under [pp']. *)   
val is_under : program_point -> program_point -> bool
(* [implies (ppl, args) (ppl', args')] returns true when the
   execution of a program point in [ppl] with indices [args]
   implies the execution of a program point in [ppl'] with
   indices [args'] (without taking into account defined conditions). *)
val implies_ppl : program_points_args -> program_points_args -> bool
