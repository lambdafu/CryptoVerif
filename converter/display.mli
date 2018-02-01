open Types

val set_files : out_channel -> in_channel -> unit

val print_string : string -> unit
val print_newline : unit -> unit  

val display_arrays : bool ref
val display_list : ('a -> unit) -> 'a list -> unit

val may_have_elset : term -> bool
val may_have_elseo : process -> bool
    
val ends_with_underscore_number : string -> bool
val binder_to_string : binder -> string
val repl_index_to_string : repl_index -> string
val display_binder : binder -> unit
val display_repl_index : repl_index -> unit
val display_var : binder -> term list -> unit
val display_term : term -> unit
val display_statement : statement -> unit
val display_pattern : pattern -> unit
val display_equiv : Ptree.eqstatement -> unit
val display_collision : Ptree.collision -> unit
val display_oprocess : string -> process -> unit
val display_process : inputprocess -> unit

val display_queries : Ptree.query list -> unit
