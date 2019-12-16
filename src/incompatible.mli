open Types

val empty_comp_process : inputprocess -> unit
(* [build_def_process] must be called before [build_compatible_defs] *)
val build_compatible_defs : inputprocess -> unit

(* [get_facts pp] returns the fact_info at program point [pp] *)
val get_facts : program_point -> fact_info

(* [occ_from_pp pp] returns the occurrence of program point [pp] *)
val occ_from_pp : program_point -> int
    
(* [incompatible_suffix_length b b'] returns a length [l] such that if
   [b[args]] and [b'[args']] are both defined, then the suffixes of
   length [l] of [args] and [args'] must be different.
   Raises [Not_found] when [b[args]] and [b'[args']] can be defined 
   for any [args,args']. *)
val incompatible_suffix_length : binder -> binder -> int
(* [is_compatible (b,args) (b',args')] returns true when
   [b[args]] and [b'[args']] may both be defined *)
val is_compatible : binderref -> binderref -> bool
(* [is_compatible_node (b,args) n (b',args')] returns true when
   [b[args]] and [b'[args']] may both be defined, with [b[args]]
   defined at node [n]. *)
val is_compatible_node : binderref -> def_node -> binderref -> bool
(* [is_compatible_history (n,args) history] returns true when 
   the information in [history] is compatible with the execution
   of node [n] with indices [args] before that history. *)
val is_compatible_history : (def_node * term list) -> known_history -> bool
(* [facts_compatible_history fact_accu (nl,args) history] returns
   [fact_accu] with additional facts inferred from the execution of a
   node in [nl] with indices [args] before the history [history]. *)
val facts_compatible_history : term list -> (def_node list * term list) -> known_history -> term list 
(* [both_def_add_fact fact_accu (b,args) (b',args')] returns [fact_accu] 
   after adding a fact that always holds when
   [b[args]] and [b'[args']] are both defined. *)
val both_def_add_fact : term list -> binderref -> binderref -> term list
(* [both_def_list_facts fact_accu old_def_list def_list] returns [fact_accu] 
   after adding facts
   inferred from the knowledge that the variables in [def_list] and
   [old_def_list] are simultaneously defined. It considers pairs
   of variables in [def_list] and of one variable in [def_list]
   and one in [old_def_list], but does not consider pairs of variables
   in [old_def_list] as those should have been taken into account before.
   Uses the field "incompatible" set by Terms.build_compatible_defs
 *)
val both_def_list_facts : term list -> binderref list -> binderref list -> term list
(* [def_list_pp fact_accu pp_args def_list] returns facts
   inferred from the knowledge that the variables in [def_list] are
   defined and the program point [pp_args] is executed.
   (The variables in [def_list] may be defined before or after
   executing the program point [pp_args].
   Uses the field "incompatible" set by Terms.build_compatible_defs *)
val def_list_pp : term list -> program_point * term list -> binderref list -> term list
(* [def_at_pp_add_fact fact_accu pp args (b',args')] returns [fact_accu] 
   after adding a fact that always holds when [b'[args']] is defined
   before the execution of program point [pp] with indices [args], if
   any. *)
val def_at_pp_add_fact : term list -> program_point -> term list -> binderref -> term list
(* [def_list_at_pp_facts fact_accu pp args def_list] returns [fact_accu] 
   after adding facts inferred from the knowledge that the variables in [def_list]
   are defined before the execution of program point [pp] with indices [args].
   (Typically, that some indices in [args] are different
   from some indices of variables in [def_list].) *)
val def_list_at_pp_facts : term list -> program_point -> term list -> binderref list -> term list
(* [both_pp_add_fact fact_accu (lidxa, ppa) (lidxb, ppb)]returns [fact_accu] 
   after adding a fact inferred from the execution of both
   program point [ppa] with indices [lidxa] and 
   program point [ppb] with indices [lidxb], if any. *)
val both_pp_add_fact : term list ->
  term list * program_point -> term list * program_point -> term list
(* [may_def_before (b,args) (b',args')] returns true when
   [b[args]] may be defined before or at the same time as [b'[args']] *)
val may_def_before : binderref -> binderref -> bool

