open Types

type frontend =
    Channels
  | Oracles

val get_implementation : bool ref
val out_dir : string ref
val proof_output : string ref
val equiv_output : string ref
val command_output : string ref
    
val front_end : frontend ref

val lib_name : string list ref

val events_to_ignore_lhs : funsymb list ref
    
(* memory saving *)
val forget_old_games : bool ref
                      
(* debug settings *)
val debug_instruct : bool ref
val debug_cryptotransf : int ref
val debug_find_unique : bool ref
val debug_elsefind_facts : bool ref
val debug_simplify : bool ref
val debug_simplif_add_facts : bool ref
val debug_corresp : bool ref
val debug_event_adv_loses : bool ref
    
(* To parse games output by CryptoVerif, 
set this variable to true: such games may contain
"defined" conditions on variables that are never defined. *)
val allow_undefined_var : bool ref

val proba_zero : bool ref

val use_oracle_count_in_result : bool ref

val max_efl : int ref
val max_depth_add_fact : int ref
val max_depth_try_no_var_rec : int ref
val max_replace_depth : int ref
val elsefind_facts_in_replace : bool ref
val elsefind_facts_in_success : bool ref
val elsefind_facts_in_simplify : bool ref
val elsefind_facts_in_success_simplify : bool ref
val else_find_additional_disjunct : bool ref
val improved_fact_collection : bool ref
val corresp_cases : bool ref
val simplify_use_equalities_in_simplifying_facts : bool ref
val re_reduce_root_sides : bool ref
    
val diff_constants : bool ref
val constants_not_tuple : bool ref 

val use_known_equalities_crypto : bool ref
val priority_event_unchanged_rand : int ref

val normalize_in_match_funapp : bool ref
                                        
val expand_letxy : bool ref

val trust_size_estimates : bool ref
    
val max_advice_possibilities_beginning : int ref
val max_advice_possibilities_end : int ref

val minimal_simplifications : bool ref
val merge_branches : bool ref
val merge_arrays : bool ref
val unique_branch : bool ref
val unique_branch_reorg : bool ref
val infer_unique : bool ref
                               
val auto_sa_rename : bool ref
val auto_remove_assign_find_cond : bool ref
val auto_remove_if_find_cond : bool ref
val auto_move : bool ref
val auto_expand : bool ref
    
val ignore_small_times : int ref
val interactive_mode : bool ref
val auto_advice : bool ref
val no_advice_crypto : bool ref
val no_advice_globaldepanal : bool ref

val backtrack_on_crypto : bool ref
val simplify_after_sarename : bool ref


val max_iter_simplif : int ref
val max_iter_removeuselessassign : int ref

val detect_incompatible_defined_cond : bool ref

val allow_unproved_unique : bool ref
    
val do_set : string -> Ptree.pval -> unit

(* Parameter sizes *)
val psize_NONINTERACTIVE : int
val psize_PASSIVE : int
val psize_DEFAULT : int
val psize_SMALL : int

(* Type sizes *)
val tysize_LARGE : int

val min_exp : int
val max_exp : int
    
val tysize_MIN_Auto_Coll_Elim : int ref
val tysize_MIN_Coll_Elim : int ref
(* Determines the probabilities that are considered small enough to 
   eliminate collisions. It consists of a list of probability descriptions
   of the form ([(psize1, n1); ...; (psizek,nk)], tsize) 
   which represent probabilities of the form
   constant * (parameter of size <= psize1)^n1 * ... * 
   (parameter of size <= psizek)^nk / (type of size >= tsize) *) 
val allowed_collisions : ((int * int) list * int) list ref

val tysize_MAX_Guess : int ref
    
val parse_type_size_pcoll : string * Parsing_helper.extent -> (int * int) option * (int * int) option
val parse_pest : string * Parsing_helper.extent -> int
val parse_psize : string * Parsing_helper.extent -> int

(* Type options *)

(* Types consisting of all bitstrings of the same length *)
val tyopt_FIXED : int

(* Finite types *)
val tyopt_BOUNDED : int

(* Types for which the standard distribution for generating
   random numbers is non-uniform *)
val tyopt_NONUNIFORM : int

(* Types for which we can generate random numbers.
   Corresponds to one of the three options above *)
val tyopt_CHOOSABLE : int

(* Function options *)

val fopt_COMPOS : int
val fopt_DECOMPOS : int
val fopt_UNIFORM : int

val tex_output : string ref

val t_bitstring : typet
val t_bitstringbot : typet
val t_bool : typet
(*For precise computation of the runtime only*)
val t_unit : typet
(* For events in terms; they have a type compatible with any type*)
val t_any : typet
val t_empty_idx : typet

val create_fun :  string -> typet list * typet -> 
  ?options:int -> ?eqth:eq_th -> ?impl:impl_name -> ?impl_inv: string option -> funcats -> funsymb
    
val c_true : funsymb
val c_false : funsymb

val f_comp : funcats -> typet -> typet -> funsymb
val f_or : funsymb
val f_and : funsymb
val f_not : funsymb

val get_tuple_fun : typet list -> funsymb
val empty_tuple : funsymb
    
(*For precise computation of the runtime only*)
val t_interv : typet
val f_plus : funsymb
val f_mul : funsymb
val get_inverse : funsymb -> int -> funsymb

(* Assumptions given in the input file *)
val equivs : equiv_gen list ref

val get_query_status : ((query * game) * proof_t ref) -> proof_t
val get_public_vars : cur_queries_t -> binder list
val occurs_in_queries : binder -> cur_queries_t -> bool

(* [event_occurs_in_queries f queries] returns true when the events [f]
   must be preserved in game transformations, that is, when [f] occurs
   in active queries. All events are preserved when we prove 
   indistinguishability. *)
val event_occurs_in_queries : funsymb -> cur_queries_t -> bool

(* Set when a game is modified *)
val changed : bool ref

(* Instructions are added in advise when an instruction I cannot be fully
   performed. The added instructions correspond to suggestions of instructions
   to apply before I so that instruction I can be better performed. *)
val advise : instruct list ref

