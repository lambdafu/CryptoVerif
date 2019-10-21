open Types

val add_else_find : elsefind_fact list -> simp_facts -> simp_facts

val add_to_collector : 'a list ref option -> 'a -> unit

val for_all_collector : 'a option -> ('b -> bool) -> 'b list -> bool
    
(* Basic string functions *)

(* [ends_with s sub] is true when the string [s] ends with [sub] *)
val ends_with : string -> string -> bool
    
(* [starts_with s sub] is true when the string [s] starts with [sub] *)
val starts_with : string -> string -> bool

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

(** [assq_rest a l] returns the value associated with key [a] in the list of
   pairs [l], as well as the list of other elements of [l]. That is,
   [assq_rest a [ ...; (a,b); ...] = (b, lrest)]
   if [(a,b)] is the leftmost binding of [a] in list [l] and
   [lrest] is [l] with [(a,b)] removed, reversed.
   Raise [Not_found] if there is no value associated with [a] in the
   list [l]. Uses physical equality to compare keys. *)
val assq_rest : 'a -> ('a * 'b) list -> 'b * ('a * 'b) list

(* Addition of integers bounded by max_exp.
   The second argument must be >= 0, so that there is no overflow.  *)
val plus : int -> int -> int

(* [sum_list f l] is the sum of [f x] ([f x] >= 0) for all [x] in [l],
   bounded by max_exp *)
val sum_list : ('a -> int) -> 'a list -> int
    
(* [max_list f l] is the maximum of [f x] for all [x] in [l].
   Assumes [f x >= 0]. When [l] is empty, the result is 0. *)
val max_list : ('a -> int) -> 'a list -> int

(* [min_list f l] is the minimum of [f x] for all [x] in [l] *)
val min_list : ('a -> int) -> 'a list -> int
    
(* [get_size_low ty] and [get_size_high ty] return n such that 
   the size of ty is at least (resp. at most) 2^n *)
val get_size_low : typet -> int
val get_size_high : typet -> int

(* [get_pcoll1_low ty] and [get_pcoll1_high ty] return n such 
   that the probability Pcoll1rand(ty) of collision with a 
   random element of the type [ty] is at least (resp. at most) 2^n (n <= 0) *)
val get_pcoll1_low : typet -> int
val get_pcoll1_high : typet -> int

(* [get_pcoll2_low ty] and [get_pcoll2_high ty] return n such 
   that the probability Pcoll2rand(ty) of collision between 
   2 random elements of the type [ty] is at least (resp. at most) 2^n (n <= 0) *)
val get_pcoll2_low : typet -> int    
val get_pcoll2_high : typet -> int    
    
(* [addq accu x] returns [accu] with [x] added if it is not already in 
   (for physical equality) *)
val addq : 'a list -> 'a -> 'a list
    
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

(* Iterators *)

    (* Exists *)
    
val exists_subterm :
  (term -> bool) -> (binderref -> bool) -> (pattern -> bool) -> term -> bool
val exists_subpat :
  (term -> bool) -> (pattern -> bool) -> pattern -> bool
val exists_subiproc :
  (inputprocess -> bool) ->
  (channel * term list -> pattern -> process -> bool) ->
  inputprocess -> bool
val exists_suboproc :
  (process -> bool) -> (term -> bool) -> (binderref -> bool) ->
  (pattern -> bool) -> (inputprocess -> bool) -> process -> bool



val equal_lists : ('a -> 'a -> bool) -> 'a list -> 'a list -> bool
val equal_lists_sets : ('a -> 'a -> bool) -> 'a list -> 'a list -> bool
val equal_lists_sets_q : 'a list -> 'a list -> bool
val equal_query_any_pubvars : query -> query -> bool
val equal_query : query -> query -> bool
val equal_instruct : instruct -> instruct -> bool
val add_eq : instruct -> instruct list -> instruct list

val type_for_param : param -> typet
val param_from_type : typet -> param

val get_else : term option -> term
val binder_from_term : term -> binder
val binderref_from_term : term -> binderref
val repl_index_from_term : term -> repl_index
val term_from_binder : binder -> term
val term_from_binderref : binderref -> term
val binderref_from_binder : binder -> binderref
val term_from_repl_index : repl_index -> term
val build_term : term -> term_desc -> term
val build_term2 : term -> term_desc -> term
val build_term3 : term -> term_desc -> term
val build_term_type : typet -> term_desc -> term
val build_term_type_occ : typet -> int -> term_desc -> term
val new_term : typet -> Parsing_helper.extent -> term_desc -> term
    
val new_iproc : inputprocess_desc -> Parsing_helper.extent -> inputprocess
val new_oproc : process_desc -> Parsing_helper.extent -> process
val iproc_from_desc : inputprocess_desc -> inputprocess
val oproc_from_desc : process_desc -> process
val iproc_from_desc2 : inputprocess -> inputprocess_desc -> inputprocess
val oproc_from_desc2 : process -> process_desc -> process
val iproc_from_desc3 : inputprocess -> inputprocess_desc -> inputprocess
val oproc_from_desc3 : process -> process_desc -> process

val empty_game : game
(* Used the designate the LHS and RHS of an equivalence *)
val lhs_game : game
val rhs_game : game
val get_process : game -> inputprocess
val build_transformed_game : ?expanded: bool -> inputprocess -> game -> game
                   
val app : funsymb -> term list -> term

val is_args_at_creation : binder -> term list -> bool

module HashedType : Hashtbl.HashedType with type t = typet 

module TypeHashtbl : Hashtbl.S with type key = HashedType.t
                                                   
val cst_for_type_table : funsymb TypeHashtbl.t
val cst_for_type : typet -> term

val is_restr : binder -> bool
val is_assign : binder -> bool

val current_bound_vars : binder list ref
val cleanup : unit -> unit
val link : binder -> linktype -> unit
val auto_cleanup : (unit -> 'a) -> 'a

val current_bound_ri : repl_index list ref
val ri_cleanup : unit -> unit
val ri_link : repl_index -> linktype -> unit
val cleanup_until : repl_index list -> repl_index list -> unit
val ri_auto_cleanup : (unit -> 'a) -> 'a
val ri_auto_cleanup_failure : (unit -> 'a) -> 'a
    
(* [max_occ] is the maximum occurrence number seen so far.
   It is used to determine the left margin in the display of games,
   so that there is enough space to display occurrence numbers in 
   the margin *)
val max_occ : int ref
(* [new_occ()] returns a new occurrence number *)
val new_occ : unit -> int

(* State used to choose variable numbers *)
type var_num_state
val get_var_num_state : unit -> var_num_state
val set_var_num_state : var_num_state -> unit

val new_var_name : string -> string * int
val record_id : string -> Parsing_helper.extent -> unit
val fresh_id : string -> string
val new_binder : binder -> binder
val new_repl_index : repl_index -> repl_index
val create_binder_internal : string -> int -> typet -> repl_index list -> binder
val create_binder : string -> typet -> repl_index list -> binder
val create_binder0 : string -> typet -> repl_index list -> binder
val create_repl_index : string -> typet -> repl_index

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
    
    (* The links define a substitution. 
     We want to apply this substitution to the elsefind fact (bl, def_vars, t) as argument.
     To avoid capture, the image of the substitution must not contain replication indices in bl.
     For instance, the image of the substitution may be fresh replication indices. *)
val copy_elsefind : elsefind_fact -> elsefind_fact
    
(* [subst cur_array l t] returns the term [t] in which the replication
   indices in [cur_array] have been replaced with their corresponding
   term in [l]. 
   The lists [cur_array] and [l] must have the same length.

   [subst_def_list] and [subst_simp_facts] are similar functions for
   defined conditions and facts instead of terms. *)
val subst : repl_index list -> term list -> term -> term
val subst_def_list : repl_index list -> term list -> binderref list -> binderref list
val subst_else_find : repl_index list -> term list -> elsefind_fact -> elsefind_fact
val subst_simp_facts : repl_index list -> term list -> simp_facts -> simp_facts

(* [subst3 l t] returns the term [t] after applying the substitution
   defined by [l]: [l] is a list of pairs (variable, term), and [subst3]
   replaces each variable with the corresponding term. 

   [subst_def_list3] and [subst_oprocess3] are similar functions
   for defined conditions and processes instead of terms. *)
val subst3 : (binder * term) list -> term -> term
val subst_def_list3 : (binder * term) list -> binderref list -> binderref list
val subst_oprocess3 : (binder * term) list -> process -> process

(* [find_some f l] returns [f a] for the first element
   [a] of the list [l] such that [f a <> None].
   It returns [None] if [f a = None] for all [a] in [l]. *)
val find_some : ('a -> 'b option) -> 'a list -> 'b option

(* [replace l1 l0 t] replaces all terms in [l1] with the 
   corresponding term in [l0] inside [t] *)
val replace : term list -> term list -> term -> term

(* Functions for manipulating terms with equations *)

(* [try_no_var simp_facts t] returns [t] unchanged when it
   is a function application and tries to replace it with its value
   using the rewrite rules in [simp_facts] when it is a variable.
   See facts.ml for additional information on [simp_facts]. *)
val try_no_var : simp_facts -> term -> term

val normalize : simp_facts -> term -> term

(* [try_no_var_rec] replaces variables with their values as much as possible *)
val try_no_var_rec : simp_facts -> term -> term
    
(* Identity function, to be used as placeholder for
   a term simplification function when we don't want to do
   any simplification *)
val try_no_var_id : term -> term

(* [compute_inv try_no_var reduced (prod, inv, neut) t] computes the inverse of
   term [t].
   [prod] is the product function, [inv] is the inverse function,
   [neut] is the neutral element.
   [reduced] is set to true when [t] has been simplified.
   [try_no_var] is a function from terms to terms that tries to replace
   variables with their values. It leaves non-variable terms unchanged.
   It can be the identity when we do not have information on the values
   of variables. *)
val compute_inv : (term -> term) -> bool ref ->
  funsymb * funsymb * funsymb -> term -> term

(* [make_prod prod l] computes the product by function [prod]
   of the elements in list [l]. [l] must not be empty. *)
val make_prod : funsymb -> term list -> term

(* [make_inv_prod eq_th l1 t l2] computes the product 
   inv (product (List.rev l1)) * t * inv(product l2) *)
val make_inv_prod : eq_th -> term list -> term -> term list -> term

(* [get_prod try_no_var t] returns the equational theory of the root
   function symbol of term [t], when it is a product
   in a group or xor. [try_no_var] is as in [compute_inv] above. *)
val get_prod : (term -> term) -> term -> eq_th
val get_prod_list : (term -> term) -> term list -> eq_th

(* [is_fun f t] is true if and only if the root function symbol
   of [t] is [f]. *)
val is_fun : funsymb -> term -> bool

(* Simplification function:
   [simp_prod simp_facts reduced f t] simplifies term [t].
   [f] is a binary function with an equational theory. 
   [simp_prod] returns a list of terms [l], such that [t] is equal to
   the product of the elements of [l] by function [f].
   [simp_facts] collects the rewrite rules corresponding to known equalities
   and other known facts, which we use in order to replace variables with their values and
   to test equality between terms.
   [reduced] is set to true when [t] has really been simplified. *)
val simp_prod : simp_facts -> bool ref -> funsymb -> term -> term list

(* [remove_inverse_ends simp_facts reduced group_th l] removes the
   inverse elements at the two ends of the list [l]. In a non-commutative group,
   the product of the elements [l] is the neutral element if and only if the
   product of the resulting list is: x * t * x^-1 = e iff t = e by multiplying
   on the left by x^-1 and on the right by x. 
   [group_th = (f, inv,n)] is supposed to be a group, with product [f],
   inverse function [inv], and neutral element [n].    
   [simp_facts], [reduced], and [sub_eq] are as above. *)

val remove_inverse_ends :
  simp_facts -> bool ref -> funsymb * funsymb * funsymb ->
  term list -> term list

(* [apply_eq_reds simp_facts reduced t] simplifies the term [t] using
   the equational theory. [reduced] is set when the term [t] is really
   simplified. [simp_facts] is as in [simp_prod] above. *) 
val apply_eq_reds : simp_facts -> bool ref -> term -> term

(* [simp_facts_id] is a placeholder for [simp_facts] when there are 
   no known facts. *)
val simp_facts_id : simp_facts

(* Equality tests between terms, lists of terms, ... *)

(* [simp_equal_terms simp_facts normalize_root t1 t2] returns true when
   the terms [t1] and [t2] are equal. It uses the rewrite rules in
   [simp_facts] to reduce the terms in order to infer more equalities.
   When [normalize_root] is false, the rewrite rules in [simp_facts]
   are not applied at the root of the terms [t1] and [t2]. *)
val simp_equal_terms : simp_facts -> bool -> term -> term -> bool

val equal_terms : term -> term -> bool
val synt_equal_terms : term -> term -> bool
val equal_term_lists : term list -> term list -> bool 
val equal_probaf : probaf -> probaf -> bool
val equal_def_lists : binderref list -> binderref list -> bool
val equal_elsefind_facts : elsefind_fact -> elsefind_fact -> bool

(* [is_subterm t1 t2] returns [true] when [t1] is a subterm of [t2]
   This function is allowed only for Var/FunApp/ReplIndex terms. *)
val is_subterm : term -> term -> bool

(* [len_common_suffix l1 l2] returns the length of the longest 
   common suffix between lists of terms [l1] and [l2] *)
val len_common_suffix : term list -> term list -> int

val equal_binderref : binderref -> binderref -> bool
val mem_binderref : binderref -> binderref list -> bool
val add_binderref : binderref -> binderref list ref -> unit
val setminus_binderref : binderref list -> binderref list -> binderref list
val inter_binderref : binderref list -> binderref list -> binderref list
val union_binderref : binderref list -> binderref list -> binderref list

val get_deflist_subterms : binderref list ref -> term -> unit

val get_needed_deflist_term : binderref list -> binderref list ref -> term -> unit
val get_needed_deflist_oprocess : binderref list -> binderref list ref -> process -> unit

val refers_to : binder -> term -> bool
val refers_to_br : binder -> binderref -> bool
val refers_to_pat : binder -> pattern -> bool
val refers_to_process : binder -> inputprocess -> bool
val refers_to_oprocess : binder -> process -> bool
val refers_to_fungroup :  binder -> fungroup -> bool

val refers_to_nodef : binder -> term -> bool
val refers_to_process_nodef : binder -> process -> bool

val vars_from_pat : binder list -> pattern -> binder list
val vars_from_pat_list : binder list -> pattern list -> binder list
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

val make_true_at : term -> term
val make_false_at : term -> term
val make_and_at : term -> term -> term -> term
val make_or_at : term -> term -> term -> term
val make_not_at : term -> term -> term
    
val or_and_form : term -> term

val is_tuple : term -> bool
val is_pat_tuple : pattern -> bool

val put_lets : (pattern * term) list -> process -> process -> process
val put_lets_term : (pattern * term) list -> term -> term option -> term
(* [simplify_let_tuple get_tuple pat t] serves to simplify "let pat = t in ..."
   when pat is a tuple.
   [get_tuple] is a function that tries to transform a term into a tuple.
   It returns 
   - the list of performed transformations
   - a term [t] meant to be transformed into a test "if t then ... else ..." 
   before the following [let]s (no test should be generated when [t] is true)
   - a list [(pat1, t1);...;(patn, tn)] meant to
   be transformed into "let pat1 = t1 in ... let patn = tn in ...".
   It makes sure that, when the initial pattern matching fails,
   none of the variables of pat is defined in the transformed let.
   It raises the exception [Impossible] when the initial pattern 
   matching always fails. *)
exception Impossible
val simplify_let_tuple : (term -> term) -> pattern -> term -> let_transfo * term * (pattern * term) list

val move_occ_term : term -> term
val move_occ_br : binderref -> binderref
(* [move_occ_process] renumbers the occurrences in the process given
   as argument. Additionally, it makes sure that all terms and processes
   inside the returned process are physically distinct, which is a 
   requirement for calling [Terms.build_def_process]. *)
val move_occ_process : inputprocess -> inputprocess
val move_occ_game : game -> unit
                                         
val term_from_pat : pattern -> term
val get_type_for_pattern : pattern -> typet

val count_var : term -> int
val size : term -> int

exception NonLinearPattern
val gvar_name : string
val gen_term_from_pat : pattern -> term
val single_occ_gvar : binder list ref -> term -> bool

val update_elsefind_with_def : binder list -> elsefind_fact -> elsefind_fact

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

(* [check_simple_term t] returns true if [t] is a basic term:
   it contains no if/let/find/new/event. *)
val check_simple_term : term -> bool

val add_def_vars_node : binder list -> def_node -> binder list


val unionq : 'a list -> 'a list -> 'a list (* union using physical equality *)

(* Update args_at_creation: since variables in conditions of find have
as args_at_creation the indices of the find, transformations of the
find may lead to changes in these indices.  This function updates
these indices. It relies on the invariant that variables in conditions
of find have no array accesses, and that new/event do not occur in
conditions of find. It creates fresh variables for all variables
defined in the condition of the find. *)
val update_args_at_creation : repl_index list -> term -> term

