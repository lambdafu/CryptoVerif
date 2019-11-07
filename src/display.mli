open Types

val file_out : string -> Parsing_helper.extent -> (unit -> unit) -> unit
val fun_out : (string -> unit) -> (unit -> unit) -> unit
    
val print_string : string -> unit
val print_newline : unit -> unit  

val get_game_id : game -> string
    
val display_occurrences : bool ref
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
val display_term : term -> unit
val display_statement : statement -> unit
val display_pattern : pattern -> unit
val display_proba : int -> probaf -> unit
val display_polynom : polynom -> unit
val display_set : setf list -> unit
val display_equiv : equiv_nm -> unit
val display_equiv_with_name : equiv_nm -> unit
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

(* The next functions are made public so that displaytex can call them *)

type query_specif =
    InitQuery of query
  | QEvent of funsymb

val equal_qs : query_specif * game -> query_specif * game -> bool

type proof_tree =
    { pt_game : game;
      mutable pt_sons : (instruct * setf list * proof_tree * (query_specif * game) list ref) list }

exception NotBoundEvent of funsymb * game

val build_proof_tree : query * game -> setf list -> state -> proof_tree

val double_if_needed : (query_specif * game) list -> setf list -> setf list

(* [proba_from_set q p] converts the probability [p] represented as
a [setf list] into a probability represented as a [probaf].
[p] must not contain [SetEvent]. *)

val proba_from_set : setf list -> probaf
val proba_from_set_may_double : query * game -> setf list -> probaf

val get_initial_game : state -> game
val get_initial_queries : state -> cur_queries_t

val get_all_states_from_queries : cur_queries_t -> state list

val remove_duplicate_states : state list -> state list -> state list


val display_state : state -> unit
val display_conclusion : state -> unit
