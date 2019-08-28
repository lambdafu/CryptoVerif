open Types

(* Helper functions for simplify, mergebranches, global_dep_anal, ... *)

(* Priorities for orienting equalities into rewrite rules
   Used by both transf_simplify and transf_expand. 
   It is important that a single list is used, so that variables
   with priority set are always in the priority list. *)
val current_max_priority : int ref
val priority_list : binder list ref
    
(*** Computation of probabilities of collision between terms ***)

(* Recorded term collisions *)
val term_collisions :
  ((binderref * binderref) list * (* For each br1, br2 in this list, the collisions are eliminated only when br2 is defined before br1 *)
   term * (* The collisions are eliminated only when this term is true *)
   term list * (* Facts that are known to hold when the collision is eliminated *)
   repl_index list * (* Indices that occur in colliding terms *) 
   repl_index list * (* Indices at the program point of the collision *)
   repl_index list * (* Reduced list of indices taking into account known facts *)
   term * term * (* The two colliding terms, t1 and t2 *)
   binder * term list option (* The random variable that is (partly) characterized by t1 and from which t2 is independent *) * 
   probaf (* The probability of one collision *)) list ref

(* Resets repl_index_list and term_collisions, and also calls Proba.reset *)
val reset : coll_elim_t list -> game -> unit

val any_term_pat : pattern -> term
val matches_pair : term -> term -> term -> term -> bool

(* Adds a term collision *)
val add_term_collisions :
  repl_index list * term list * (binderref * binderref) list * term -> term -> term ->
  binder -> term list option -> probaf -> bool

(* Computes the probability of term collisions *)
val final_add_proba : unit -> setf list

(*** Module used in dependency analyses ***)

module FindCompos :
  sig
    (* [init_elem] is the empty dependency information *)
    val init_elem : 'a depinfo

    (* [depends (b, depinfo) t] returns [true] when the term [t]
       may depend on the variable [b]. 
       [depinfo] is the dependency information for variable [b]. *)
    val depends : binder * 'a depinfo -> term -> bool

    (* [is_indep simp_facts (b, depinfo) t] returns a term independent of [b]
       in which some array indices in [t] may have been replaced with
       fresh replication indices. When [t] depends on [b] by variables
       that are not array indices, it raises [Not_found] *)
    val is_indep : simp_facts -> binder * 'a depinfo -> term -> term

    (* [remove_dep_array_index (b, depinfo) t] returns a modified 
       version of [t] in which the array indices that depend on [b]
       are replaced with fresh indices.
       [depinfo] is the dependency information for variable [b].*)
    val remove_dep_array_index : binder * 'a depinfo -> term -> term

    (* [remove_array_index t] returns a modified version of [t] in which
       the array indices that are not replication indices are replaced
       with fresh indices. *) 
    val remove_array_index : term -> term

    (* [find_compos (b0, depinfo) l0opt t] returns
       the dependency status of the term [t] with respect to the variable [b0].
       (See the definition of [depend_status] in types.ml for its meaning.)
       [depinfo] is the dependency information we have for variable [b0].
       (See the definition of ['a depinfo] in types.ml for its meaning.)
       [l0opt = Some l0] means that we focus on the dependency of [t] with respect to the cell [b0[l0]]
       [l0opt = None] means that we consider the dependency of [t] with respect to any cell of [b0]. *)
    val find_compos : (binder * 'a depinfo) -> term list option -> term -> depend_status

    (* [extract_from_status t status] extracts information from the 
       dependency status [status] of term [t].
       It returns [Some(p, t_1, l0opt)] if
       - when l0opt = Some l0, for all [t'] independent of [b0[l0]], Pr[t = t'] <= p,
       - when l0opt = None, for all [t'] independent of [b0[l]] for all [l], Pr[t = t'] <= p,
       [t_1] is a modified version of [t] in which the parts that are not useful
       to show this property are replaced with variables [?].
       It returns [None] otherwise. *)
    val extract_from_status : term -> depend_status -> (probaf * term * term list option) option

  end

(*** Treatment of "elsefind" facts ***)

exception SuccessBranch of (binder * repl_index * term) list * (binder * repl_index) list
val branch_succeeds : 'b findbranch -> dep_anal -> simp_facts -> 
  binderref list -> unit
val add_elsefind : dep_anal -> binderref list -> simp_facts ->
  'a findbranch list -> simp_facts
val update_elsefind_with_def : binder list -> simp_facts -> simp_facts
val convert_elsefind : dep_anal -> binderref list -> simp_facts -> simp_facts

(*** Evaluation of terms: 
     true_facts_from_simp_facts gets the true facts from a triple (facts, substitutions, else_find facts)
     try_no_var_rec replaces variables with their values as much as possible ***)

val true_facts_from_simp_facts : simp_facts -> term list

val try_no_var_rec : simp_facts -> term -> term

(* [get_facts_of_elsefind_facts] uses elsefind facts to derive more facts, 
   by performing a case distinction depending on the order of 
   definition of variables. 
   [get_facts_of_elsefind_facts g cur_array simp_facts def_vars]
   returns a list of terms [tl] that are proved.
   [g] is the current game
   [cur_array] the current replication indices
   [simp_facts] the facts known to hold at the current program point
   [def_vars] the variables known to be defined
   The probability that the facts do not hold must be collected from outside 
   [get_facts_of_elsefind_facts], by calling [Simplify1.reset] before
   and [Simplify1.final_add_proba()] after calling [get_facts_of_elsefind_facts].
*)

val get_facts_of_elsefind_facts : game -> repl_index list -> simp_facts -> binderref list -> term list

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

(*** Helper functions for simplification ***)
    
(* [dependency_collision_rec3 cur_array true_facts t1 t2 t] aims 
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
   [true_facts] is a list of facts that are known to hold. *)
val dependency_collision_rec3 :
  repl_index list -> simp_facts -> term -> term -> term -> term option

(* [try_two_directions f t1 t2] tries a dependency analysis [f]
   on both sides of [t1 = t2] *)
val try_two_directions :
  ('a -> 'a -> 'a -> 'b option) -> 'a -> 'a -> 'b option

(* [needed_vars vars] returns true when some variables in [vars]
   have array accesses or are used in queries. That is, we must keep
   them even if they are not used in their scope. *)
val needed_vars : binder list -> cur_queries_t -> bool
val needed_vars_in_pat : pattern -> cur_queries_t -> bool

(* Add lets to a process or a term *)
val add_let : process -> (binder * term) list -> process
val add_let_term : term -> (binder * term) list -> term

(* [filter_deflist_indices bl def_list] removes from [def_list] all
   elements that refer to replication indices in [bl].
   Used when we know that the indices in [bl] are in fact not used. *)
val filter_deflist_indices :
  (binder * repl_index) list -> binderref list -> binderref list

(* [is_unique l0' find_info] returns Unique when a [find] is unique,
   that is, at runtime, there is always a single possible branch 
   and a single possible value of the indices:
   either it is marked [Unique] in the [find_info],
   or it has a single branch with no index.
   [l0'] contains the branches of the considered [find]. *)
val is_unique : 'a findbranch list -> find_info -> find_info

(* [infer_unique g cur_array simp_facts def_vars dep_info current_history l0' find_info]
   tries to prove that there is single possible choice in the find with
   branches [l0'], and if so it returns the modified [find_info] equal to
   [Unique]. It also returns a boolean set to true when a real change has been made.

   [g] is the current game
   [cur_array] the current replication indices
   [simp_facts] the facts known to hold at the current program point
   [def_vars] the variables known to be defined
   [dep_info] is a dependency analysis
   [current_history] is the known history at the find, at which [def_list]
   is tested (may be returned by [Facts.get_initial_history]) *)
val prove_unique : game -> repl_index list -> simp_facts -> binderref list ->
                   dep_anal -> known_history option ->
                   'a findbranch list -> bool
val infer_unique : game -> repl_index list -> simp_facts -> binderref list ->
                   dep_anal -> known_history option ->
                   'a findbranch list -> find_info -> find_info * bool
                                                     
(*** [improved_def_process event_accu compatible_needed p]
     Improved version of [Terms.build_def_process] that infers facts from 
     variables being defined at a program point, variables being simultaneously
     defined, and elsefind facts.
     Reverts to [Terms.build_def_process] when [Settings.improved_fact_collection = false].
     When [compatible_needed] is true, always initializes the [incompatible] field.
 ***)
val improved_def_process : (term * program_point) list ref option -> bool -> inputprocess -> unit

val empty_improved_def_process : bool -> inputprocess -> unit
