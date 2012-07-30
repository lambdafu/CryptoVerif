open Types

(* Basic list functions *)

(* [repeat n x] returns a list containing [n] copies of [x] *)
val repeat : int -> 'a -> 'a list

(* [skip n l] returns the list [l] without its [n] first elements.
   Raises an exception if [l] contains fewer than [n] elements *)
val skip : int -> 'a list -> 'a list

(* [split n l] splits [l] into two lists: the first [n] elements,
   and the rest.
   Raises an internal error if [l] contains fewer than [n] elements *)
val split : int -> 'a list -> ('a list * 'a list)

(* [find x l] looks for [x] in list [l], and returns its position. 
   (The first element has position 0.) 
   Raises Not_found if [x] does not occur in [l]. *)
val find_in_list : 'a -> 'a list -> int

(* [lsuffix n l] returns a suffix of [l] of length [n].
   Raises an exception if [l] contains fewer than [n] elements *)
val lsuffix : int -> 'a list -> 'a list

(* [remove_suffix n l] returns the list [l] without its last [n] elements.
   Raises an internal error if [l] contains fewer than [n] elements *)
val remove_suffix : int -> 'a list -> 'a list


(* Intersection / Union *)

(* [intersect eqtest l1 l2] returns the intersection of [l1] and [l2]
   considered as sets, where [eqtest] is used to test equality between
   elements. *)
val intersect : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list

(* [intersect_list eqtest l] returns the intersection of all lists
   in [l] (which is a list of lists), where [eqtest] is used to test
   equality between elements. 
   Raises Contradiction when [l] is the empty list. (The intersection
   should be the full set.) *)
val intersect_list : ('a -> 'a -> bool) -> 'a list list -> 'a list

(* [union eqtest l1 l2] returns the union of [l1] and [l2]
   considered as sets, where [eqtest] is used to test equality between
   elements. *)
val union : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list

(* [map_union eqtest f l] applies [f] to each element of [l]. 
   [f] returns a list, [map_union] then returns the union of all these
   lists, where [eqtest] is used to test equality between
   elements. *)
val map_union : ('b -> 'b -> bool) -> ('a -> 'b list) -> 'a list -> 'b list




val equal_lists : ('a -> 'a -> bool) -> 'a list -> 'a list -> bool
val equal_instruct : instruct -> instruct -> bool
val add_eq : instruct -> instruct list -> instruct list

val type_for_param : param -> typet
val param_from_type : typet -> param

val binder_from_term : term -> binder
val binderref_from_term : term -> binderref
val repl_index_from_term : term -> repl_index
val term_from_binder : binder -> term
val term_from_binderref : binderref -> term
val term_from_repl_index : repl_index -> term
val build_term : term -> term_desc -> term
val build_term2 : term -> term_desc -> term
val build_term_type : typet -> term_desc -> term

val iproc_from_desc : inputprocess_desc -> inputprocess
val oproc_from_desc : process_desc -> process
val iproc_from_desc2 : inputprocess -> inputprocess_desc -> inputprocess
val oproc_from_desc2 : process -> process_desc -> process
val nil_proc : inputprocess
val yield_proc : process
val abort_proc : process

val cst_for_type : typet -> term

val is_restr : binder -> bool
val is_assign : binder -> bool

val current_bound_vars : binder list ref
val cleanup : unit -> unit
val link : binder -> linktype -> unit
val auto_cleanup : (unit -> 'a) -> 'a

(* [max_occ] is the maximum occurrence number seen so far.
   It is used to determine the left margin in the display of games,
   so that there is enough space to display occurrence numbers in 
   the margin *)
val max_occ : int ref
(* [new_occ()] returns a new occurrence number *)
val new_occ : unit -> int
(* [vcounter] is a variable counter, incremented to create a fresh variable. *)
val vcounter : int ref
val new_vname : unit -> int
val new_binder : binder -> binder
val new_repl_index : repl_index -> repl_index
val create_binder : string -> int -> typet -> term list -> binder
val create_repl_index : string -> int -> typet -> repl_index

(* Copy a term, process, ..., substituting variables with their links.
   The substitution is performed in different ways, depending on
   the value of the argument [copy_transf]. *)
type copy_transf =
    Links_RI (* Substitutes replication indices that are linked *)
  | Links_Vars 
     (* Substitutes variables that are linked, when their arguments are args_at_creation
	The linked variables are supposed to be defined above the copied terms/processes *)
  | Links_RI_Vars (* Combines Links_RI and Links_Vars *)
  | OneSubst of binder * term * bool ref 
     (* [OneSubst(b,t,changed)] substitutes b[b.args_at_creation] with t.
	It sets [changed] to true when such a substitution has been done.
	[b] is assumed to be defined above the copied terms/processes *) 
  | OneSubstArgs of binderref * term 
     (* [OneSubstArgs(br,t)] substitutes [t] for the accesses [br].
	It is assumed that [br] and [t] are already guaranteed to be defined,
	so [br] is removed from defined conditions if it occurs. *)
  | Rename of term list * binder * binder
     (* Rename(args, b, b') replaces array accesses b[args] with b'[args] *)
  | Links_Vars_Args of (binder * binder) list
     (* Links_Vars_Args(replacement_def_list) substitutes variables that are 
	linked, for any arguments: if b is linked to M, b[l] is
	replaced with M{l/b.args_at_creation}. replacement_def_list defines
	variable replacements to do in defined conditions.
	This transformation is used in the removal of assignments. *)

val copy_binder : copy_transf -> binderref -> binderref (* For the transformation Rename only *)
val copy_term : copy_transf -> term -> term
val copy_pat : copy_transf -> pattern -> pattern
val copy_def_list : copy_transf -> binderref list -> binderref list
val copy_oprocess : copy_transf -> process -> process
val copy_process : copy_transf -> inputprocess -> inputprocess

(* [subst cur_array l t] returns the term [t] in which the replication
   indices in [cur_array] have been replaced with their corresponding
   term in [l]. 
   The lists [cur_array] and [l] must have the same length.

   [subst_def_list] and [subst_simp_facts] are similar functions for
   defined conditions and facts instead of terms. *)
val subst : repl_index list -> term list -> term -> term
val subst_def_list : repl_index list -> term list -> binderref list -> binderref list
val subst_simp_facts : repl_index list -> term list -> simp_facts -> simp_facts

(* [subst3 l t] returns the term [t] after applying the substitution
   defined by [l]: [l] is a list of pairs (variable, term), and [subst3]
   replaces each variable with the corresponding term. 

   [subst_def_list3] and [subst_oprocess3] are similar functions
   for defined conditions and processes instead of terms. *)
val subst3 : (binder * term) list -> term -> term
val subst_def_list3 : (binder * term) list -> binderref list -> binderref list
val subst_oprocess3 : (binder * term) list -> process -> process

(* Equality tests between terms, lists of terms, ... *)
val equal_terms : term -> term -> bool
val equal_term_lists : term list -> term list -> bool 
val equal_probaf : probaf -> probaf -> bool
val equal_def_lists : binderref list -> binderref list -> bool
val equal_elsefind_facts : elsefind_fact -> elsefind_fact -> bool

(* [len_common_suffix l1 l2] returns the length of the longest 
   common suffix between lists of terms [l1] and [l2] *)
val len_common_suffix : term list -> term list -> int

val equal_binderref : binderref -> binderref -> bool
val mem_binderref : binderref -> binderref list -> bool
val add_binderref : binderref -> binderref list ref -> unit
val setminus_binderref : binderref list -> binderref list -> binderref list
val inter_binderref : binderref list -> binderref list -> binderref list

val get_deflist_subterms : binderref list ref -> term -> unit
val get_deflist_process : binderref list ref -> inputprocess -> unit
val get_deflist_oprocess : binderref list ref -> process -> unit

val refers_to : binder -> term -> bool
val refers_to_br : binder -> binderref -> bool
val refers_to_pat : binder -> pattern -> bool
val refers_to_process : binder -> inputprocess -> bool
val refers_to_oprocess : binder -> process -> bool
val refers_to_fungroup :  binder -> fungroup -> bool

val refers_to_nodef : binder -> term -> bool
val refers_to_process_nodef : binder -> process -> bool

val vars_from_pat : binder list -> pattern -> binder list
val occurs_in_pat : binder -> pattern -> bool

val is_true : term -> bool
val is_false : term -> bool

val make_and_ext : Parsing_helper.extent -> term -> term -> term
val make_or_ext : Parsing_helper.extent -> term -> term -> term
val make_equal_ext : Parsing_helper.extent -> term -> term -> term
val make_diff_ext : Parsing_helper.extent -> term -> term -> term

val make_and : term -> term -> term
val make_or : term -> term -> term
val make_and_list : term list -> term
val make_or_list : term list -> term
val make_not : term -> term
val make_equal : term -> term -> term
val make_let_equal : term -> term -> term
val make_diff : term -> term -> term
val make_for_all_diff : term -> term -> term
val make_true : unit -> term
val make_false : unit -> term

val or_and_form : term -> term

val is_tuple : term -> bool
val is_pat_tuple : pattern -> bool

val put_lets : pattern list -> term list -> process -> process -> process
val put_lets_term : pattern list -> term list -> term -> term option -> term
exception Impossible
val split_term : funsymb -> term -> term list

val move_occ_process : inputprocess -> inputprocess

val term_from_pat : pattern -> term
val get_type_for_pattern : pattern -> typet

exception NonLinearPattern
val gvar_name : string
val gen_term_from_pat : pattern -> term
val single_occ_gvar : binder list ref -> term -> bool

val not_deflist : binder -> elsefind_fact -> bool
val not_deflist_l : binder list -> elsefind_fact -> bool

(* [close_def_subterm accu br] adds in [accu] all variable references in [br] *)
val close_def_subterm : binderref list ref -> binderref -> unit
(* [close_def_term accu t] adds in [accu] all variable references in [t] *)
val close_def_term : binderref list ref -> term -> unit
(* [defined_refs_find bl def_list defined_refs] computes a pair
   [(defined_refs_cond, defined_refs_branch)] of variable references
   guaranteed to be defined in the condition, resp. then branch of
   [find bl suchthat defined(def_list) && condition then branch], 
   assuming the variable references in [defined_refs] are already 
   known to be defined before the find. *)
val defined_refs_find : (binder * repl_index) list -> binderref list -> 
  binderref list -> binderref list * binderref list

val def_term : def_node -> term list -> binderref list -> term -> def_node
val build_def_process : (term * fact_info) list ref option -> inputprocess -> unit
val add_def_vars_node : binder list -> def_node -> binder list

val cleanup_array_ref : unit -> unit
val array_ref_eqside : eqmember -> unit
val array_ref_process : inputprocess -> unit
val has_array_ref : binder -> bool

val exclude_array_ref_term : binder list -> term -> unit
val exclude_array_ref_def_list : binder list -> binderref list -> unit
val exclude_array_ref_pattern : binder list -> pattern -> unit
val cleanup_exclude_array_ref : unit -> unit
val all_vars_exclude : binder list ref
val has_array_ref_non_exclude : binder -> bool

val unionq : 'a list -> 'a list -> 'a list (* union using physical equality *)

val compatible_empty : binderset
val empty_comp_process : inputprocess -> unit
val build_compatible_defs : inputprocess -> unit
val is_compatible : binderref -> binderref -> bool
