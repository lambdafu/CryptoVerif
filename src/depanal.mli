open Types

val any_term_name : string
val any_term_from_type : typet -> term
val any_term : term -> term
val any_term_pat : pattern -> term
val fresh_indep_term : term -> term * typet list * typet list option

val fresh_repl_index : unit -> repl_index
    
(*** Computation of probabilities of collision between terms ***)

(* Recorded term collisions *)
val term_collisions : term_coll_t list ref

(* Resets repl_index_list and term_collisions, and also calls Proba.reset *)
val reset : coll_elim_t list -> game -> unit

(* [matches_proba_info (t1, t2, probaf) (t1', t2', probaf')]
   returns true when [(t1', t2', probaf')] is instance of 
   [(t1, t2, probaf)]. Then [(t1', t2', probaf')] does not 
   need to be added if [(t1, t2, probaf)] is already present.
   Used for various definitions of a variable with their
   find_compos probability in Transf.global_dep_anal. *)
val matches_proba_info : term * term * find_compos_probaf -> term * term * find_compos_probaf -> bool

(* [subst_idx_proba idx image collision_proba] replaces
   [idx] with its image [image = (ri_list,dep_types, full_type, indep_types_opt)]
   corresponding to all indices [ri_list] and types of [?] variables [dep_types] in a term,
   inside a probability [collision_proba].
   When [indep_types_opt = Some indep_types], 
   \prod_{T \in dep_types} |T| <= |full_type|/\prod{T \in indep_types} |T|. *)
val subst_idx_proba : repl_index ->
  repl_index list * typet list * typet * typet list option ->
    all_coll_t -> all_coll_t

(* [subst_args_proba b l probaf] replaces [b.args_at_creation]
   with [l] (or indices in [l]) in a probability [probaf] (of type [find_compos_probaf]) *)
val subst_args_proba : binder -> term list -> find_compos_probaf -> find_compos_probaf
	
(* Adds a term collision *)
val add_term_collisions :
  repl_index list * term list * term -> term -> term ->
  binder -> term list option -> (find_compos_probaf * typet list * typet * typet list option) -> bool

(* Computes the probability of term collisions *)
val final_add_proba : unit -> setf list

(* [depends (b, depinfo) t] returns [true] when the term [t]
   may depend on the variable [b]. 
   [depinfo] is the dependency information for variable [b]. *)
val depends : (binder * 'a depinfo) -> term -> bool

(* [depends_pat f_depends pat] takes as argument a depencency function [f_depends] for terms
   ([f_depends t] returns true when the term [t] may depend on some variable [b] fixed from the context).
   It extends it to patterns: [depends_pat f_depends pat] returns true when the pattern [pat]
   may depend on [b]. *)
val depends_pat : (term -> bool) -> pattern -> bool
    
(* [is_indep simp_facts (b, depinfo) t] returns a triple 
   [(t', dep_types, indep_types_option)] where 
   - [t'] is a term independent of [b] in which some array 
   indices in [t] may have been replaced with
   fresh replication indices, and some other subterms of [t] 
   may have been replaced with variables [?].
   - [dep_types] is the list of types of subterms of [t]
   replaced with variables [?], so that the number of values
   that [t] can take depending on [b] is at most 
   the product of |T| for T \in dep_types (ignoring replication
   indices).
   - [indep_types_option] is [Some indep_types] where
   [indep_types] is the list of types of subterms of [t]
   not replaced with variables [?]. This list is valid only
   when subterms of [t] are replaced only under [data] functions,
   so that 
   product of |T| for T \in dep_types <= |type(t)|/product of |T| for T \in indep_types
   [indep_types_option = None] when this list of not valid. *)
val is_indep : simp_facts -> (binder * 'a depinfo) -> term -> term * typet list * typet list option 

(* [is_indep_pat] is similar to [is_indep] but for patterns.
   It converts the pattern into a term, replacing all 
   variables bound by the pattern with [?]. *)
val is_indep_pat : simp_facts -> (binder * 'a depinfo) -> pattern -> term * typet list * typet list option 
    
(* [remove_dep_array_index (b, depinfo) t] returns a modified 
   version of [t] in which the array indices that depend on [b]
   are replaced with fresh indices.
   [depinfo] is the dependency information for variable [b].*)
val remove_dep_array_index : (binder * 'a depinfo) -> term -> term

(* [is_indep_collect_args simp_facts ((b0,l0,depinfo,collect_bargs,collect_bargs_sc) as bdepinfo) t] 
   returns a quadruple [(t_indep, t_eq, dep_types, indep_types_option)]:
   - [t_eq] is a term equal to [t] using the equalities in [simp_facts]
   - [t_indep] is a term independent of [b0[l0]] in which some array indices in [t_eq] 
   may have been replaced with fresh replication indices, and some other subterms of [t_eq] 
   may have been replaced with variables [?]. 
   - [dep_types] is the list of types of subterms of [t_eq]
   replaced with variables [?], so that the number of values
   that [t_eq] can take depending on [b] is at most 
   the product of |T| for T \in dep_types (ignoring replication
   indices).
   - [indep_types_option] is [Some indep_types] where
   [indep_types] is the list of types of subterms of [t]
   not replaced with variables [?]. This list is valid only
   when subterms of [t] are replaced only under [data] functions,
   so that 
   product of |T| for T \in dep_types <= |type(t)|/product of |T| for T \in indep_types
   [indep_types_option = None] when this list of not valid.

   [depinfo] is the dependency information (see ['a depinfo] in types.ml):
   [collect_bargs] collects the indices of [b0] (different from [l0]) on which [t] depends
   [collect_bargs_sc] is a modified version of [collect_bargs] in which  
   array indices that depend on [b0] are replaced with fresh replication indices
   (as in the transformation from [t2] to [t1]). *)
val is_indep_collect_args : simp_facts -> 
  binder * term list * 'a depinfo *
  term list list ref * term list list ref ->
  term -> term * term * typet list * typet list option

(* [find_compos (b0, depinfo) l0opt t] returns
   the dependency status of the term [t] with respect to the variable [b0].
   (See the definition of [depend_status] in types.ml for its meaning.)
   [depinfo] is the dependency information we have for variable [b0].
   (See the definition of ['a depinfo] in types.ml for its meaning.)
   [l0opt = Some l0] means that we focus on the dependency of [t] with respect to the cell [b0[l0]]
   [l0opt = None] means that we consider the dependency of [t] with respect to any cell of [b0]. *)
  val find_compos : simp_facts -> (binder * 'a depinfo) -> term list option -> term -> depend_status

(* [find_compos_pat f_find_compos pat] takes a find_compos function [f_find_compos] for terms
   ([f_find_compos t] returns the dependency status of the term [t], in two forms
   - [depend_status] as defined in types.ml
   - [extracted_depend_status] also defined in types.ml.)
   It extends it to patterns: it returns the dependency status of the pattern [pat],
   in the form of an [extracted_depend_status]. *)
  val find_compos_pat : (term -> depend_status * extracted_depend_status) -> pattern -> extracted_depend_status
      
  (* [extract_from_status t status] extracts information from the 
     dependency status [status] of term [t], and returns the
     corresponding [extracted_depend_status], defined in types.ml. *)
  val extract_from_status : term -> depend_status -> extracted_depend_status


(* [dependency_collision_rec cur_array true_facts
   get_dep_info t1 t2 t] aims 
   to simplify [t1 = t2] by eliminating collisions
   using that randomly chosen values do not depend on other variables.
   Basically, the collision is eliminated when [t1] characterizes
   a large part of a random variable [b] and [t2] does not depend 
   on [b]. 
   [t] is a subterm of [t1] that contains the variable [b].
   (Initially, it is [t1], and recursive calls are made until [t] is 
   just a variable.)

   It returns [None] when it fails, and [Some t'] when it
   succeeds in simplifying [t1=t2] into [t'].

   [cur_array] is the list of current replication indices.
   [true_facts] is a list of facts that are known to hold.
   [get_dep_info (b,l)] returns the dependency information for [(b,l)] *)
val dependency_collision_rec :
  repl_index list -> simp_facts -> (binderref -> 'a depinfo) -> term -> term -> term -> term option

(* [try_two_directions f t1 t2] tries a dependency analysis [f]
   on both sides of [t1 = t2] *)
val try_two_directions :
  ('a -> 'a -> 'a -> 'b option) -> 'a -> 'a -> 'b option

(*** Helper functions for cryptotransf: show that calls to oracles are incompatible or
   correspond to the same oracle call, to optimize the computation of probabilities. ***)

type compat_info_elem = term * term list * 
      repl_index list(* all indices *) * 
      repl_index list(* initial indices *) * 
      repl_index list(* used indices *) * 
      repl_index list(* really used indices *)

val filter_indices : term -> term list -> repl_index list -> term list -> 
  term list * compat_info_elem 
val is_compatible_indices : compat_info_elem -> compat_info_elem -> bool
val same_oracle_call : compat_info_elem -> compat_info_elem -> compat_info_elem option

