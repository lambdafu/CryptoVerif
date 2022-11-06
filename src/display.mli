open Types

val file_out : string -> Parsing_helper.extent -> (unit -> unit) -> unit
val fun_out : (string -> unit) -> (unit -> unit) -> unit
val string_out : (unit -> unit) -> string
    
val print_string : string -> unit
val print_newline : unit -> unit  

val get_game_id : game -> string

type display_occ_t = NoOcc | AllOccs | ProcessOccs      
val display_occurrences : display_occ_t ref
val display_arrays : bool ref
val display_list : ('a -> unit) -> 'a list -> unit

val len_num : int -> int
val useful_occs : int list ref
val mark_occs : detailed_instruct list -> unit

val max_game_number : int ref
    
val may_have_elset : term -> bool
val may_have_elseo : process -> bool
    
val ends_with_underscore_number : string -> bool
val binder_to_string : binder -> string
val repl_index_to_string : repl_index -> string
val display_binder : binder -> unit
val display_binder_with_type : binder -> unit
val display_repl_index : repl_index -> unit
val display_var : binder -> term list -> unit
val display_def_list : binderref list -> unit
val display_term : term -> unit
val display_statement : statement -> unit
val display_collision : collision -> unit
val display_pattern : pattern -> unit
val display_proba : ?separate_time:bool -> int -> probaf -> unit
val display_up_to_proba : ?separate_time:bool -> probaf -> unit
val display_polynom : polynom -> unit
val display_equiv : equiv_nm -> unit
val display_equiv_with_name : equiv_nm -> unit
val display_call : Ptree.equiv_call_t -> unit
val display_special_equiv : equiv_gen -> unit
val display_equiv_gen : equiv_gen -> unit
val display_oprocess : string -> process -> unit
val display_process : inputprocess -> unit
val display_game_process : game -> unit
                                        
val display_bl_assoc : binder list -> unit
val display_user_info : crypto_transf_user_info -> unit
val display_with_user_info : crypto_transf_user_info -> unit
val display_query2 : qterm -> unit
val display_query3 : query -> unit
val display_query : query * game -> unit
val display_instruct : instruct -> unit

(* Display the facts. Mainly used for debugging *)
val display_elsefind : elsefind_fact -> unit
val display_facts : simp_facts -> unit
val display_def_list_lines : binderref list -> unit
val display_ppl : program_points_args -> unit
val display_pps : program_points_args list -> unit
    
val get_initial_game : state -> game

(*** Display the result ***)
val display_state : state_display_info -> unit
val display_conclusion : state_display_info -> unit
