open Types

val cleanup_array_ref : unit -> unit
val array_ref_eqside : eqmember -> unit
val array_ref_process : inputprocess -> unit
val has_array_ref : binder -> bool
val has_array_ref_q : binder -> cur_queries_t -> bool

val exclude_array_ref_term : binder list -> term -> unit
val exclude_array_ref_def_list : binder list -> binderref list -> unit
val exclude_array_ref_pattern : binder list -> pattern -> unit
val cleanup_exclude_array_ref : unit -> unit
val all_vars_exclude : binder list ref
val has_array_ref_non_exclude : binder -> bool
