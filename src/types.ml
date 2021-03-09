(* Types module declares types of the abstract syntax
   tree and of sets of messages.
   There are recursive dependencies between these types,
   that is why they are included in the same module
*)

type ident = string * Parsing_helper.extent

type special_args_t =
  | SpecialArgId of ident
  | SpecialArgString of ident
  | SpecialArgTuple of special_args_e list

and special_args_e = special_args_t * Parsing_helper.extent
	
(* For the "replace" command: check or assume the equality *)

type replace_check_opt_t =
  | Check
  | Assume

(* Collision elimination options *)
      
type coll_elim_t =
    CollVars of string list
  | CollTypes of string list
  | CollTerms of int list	
      
(* integer parameter *)

type param = { pname : string;
	       psize : int }

(* A dimension is represented as a pair (t,l) corresponding to time^t * length^l *)

type dim = (int * int) option

type computed_dim = (int option * int * int) option

(* probability *)

type proba = { prname : string;
	       mutable pargs : dim list option;
	       pestimate : int }

(* channel *)

type channel = { cname : string }

(* types *)

type typet = { tname : string;
	       tcat : ttcat;
	       toptions : int;
	       tsize : (int * int) option; (* Some(min,max) means 2^min <= |T| <= 2^max *)
	       tpcoll : (int * int) option; (* Some(min,max) means 2^-max <= Pcoll1rand(T) <= 2^-min *)
	       (* The next fields are used for generating OCaml implementations *)
               mutable timplsize : int option; 
                 (* Number of bits of bitstrings of this type, when they have a fixed length *) 
               mutable tpredicate : string option;
	         (* Name of the OCaml function that tests whether an OCaml element belongs to
		    this type. *)
               mutable timplname : string option;
	         (* Name of the OCaml type that corresponds to this type *)
               mutable tserial : (string * string) option;
	         (* Name of the OCaml serialization and deserialization functions for this type *)
               mutable trandom : string option 
		 (* Name of the OCaml random element generation for this type *)
	     }

and ttcat = 
    BitString
  | Interv of param


type table = { tblname : string;
               tbltype : typet list;
	         (* Type of the elements of the table *)
	       (* The next field is used for generating OCaml implementations *)
               mutable tblfile : string option
		 (* Name of the file that contains this table *)
	     }


type find_info =
    Nothing
  | Unique
  | UniqueToProve (* Used when a find[unique] is inserted by the command "insert". CryptoVerif must prove that the find is really unique, the find_info becomes Unique when the proof is done. *)

(* terms *)

type binder = { sname : string;
                vname : int;
		   (* The name of a variable consists of two elements:
		      sname is a string, vname is an integer, the full name
		      of the variable is sname_vname. 
		      When I want to rename a variable, I keep its sname
		      and choose a fresh integer vname. *)
		btype : typet; 
		   (* The type of the variable *)
		args_at_creation : repl_index list;
		   (* The replication indices coming from replications and find
		      above the definition of this variable. 
		      These are the indices at the definition of the variable,
		      and also the indices used implicitly when the variable
		      is used without explicit indices. *)
		mutable def : def_node list;
		   (* Pointer to the nodes at which this variable is defined. 
		      Set by Terms.build_def_process. *)
		mutable link : linktype;
		   (* Link of the variable to a term. 
		      This is used for implementing substitutions:
		      1. One sets the links to the desired images of the variables.
		      2. Then one copies terms, replacing links with their value.
		      3. Finally one cleans up the links. *)

		   (* The next fields count_def...count_exclude_array_ref
		      mainly deal with array references. 
                      They are set by Terms.array_ref_process *)
		mutable count_def : int;
		   (* Number of definitions of the variable *)
	        mutable root_def_array_ref : bool;
		   (* True when the variable has an array
		      reference at the root of a defined condition:
		         defined(b[l]) with l <> b.args_at_creation
		      or b not in scope. *)
	        mutable root_def_std_ref : bool;
		   (* True when the variable has a standard reference
		      at the root of a defined condition:
			 defined(b[b.args_at_creation])
		      with b in scope. Such defined conditions can be removed. *)
	        mutable array_ref : bool;
		   (* True when the variable has an array reference
		      b[l] with l <> b.args_at_creation
		      or b not in scope, not at the root of a defined condition *)
                mutable std_ref : bool;
		   (* True when the variable has a standard reference
		      b[b.args_at_creation] with b in scope, not at
                      the root of a defined condition. *)
		mutable count_array_ref : int;
		   (* Number of array references to this variable
                      (including those at the root of defined conditions) *)
		mutable count_exclude_array_ref : int;
		   (* When we want to know if a variable has array references
		      outside certain terms, we first count the total
		      number of array references (using Terms.array_ref_process),
		      then exclude the array references in the considered 
		      terms, by counting them in the field 
		      count_exclude_array_ref using Terms.exclude_array_ref_term. *)
	        mutable priority : int 
		   (* This integer is used to improve the orientation
		      of equations, see Facts.orient *)
	      }

and binderref = binder * term list

(* Definition graph *)
and def_node = { above_node : def_node option;
		 binders : binder list; (* The variables defined at this node *)
		 mutable true_facts_at_def : term list; 
                    (* The facts that are guaranteed to be true at this node *)
		 def_vars_at_def : binderref list; 
                    (* The variables that are guaranteed to be defined at 
		       this node, due to defined conditions above this node *)
		 elsefind_facts_at_def : elsefind_fact list;
		    (* The elsefind_facts that are guaranteed to be true just 
		       before this node. (If this node defines b, and the
                       elsefind_fact is forall bl, not (defined(b[...]) && t),
                       the elsefind_fact may no longer hold after the definition
                       of b, but it is still present in elsefind_facts_at_def.) 
		       *)
		 mutable future_binders : binder list;
		    (* The variables that are guaranteed to be defined
		       before we reach the end of the current input...output block.
		       They come from let definitions and restrictions after this
		       node. *)
		 mutable future_true_facts : term list;
		    (* The facts that are guaranteed to hold
		       before we reach the end of the current input...output block.
		       They come from let definitions and events after this node. *)
	         definition : program_point;
		    (* Pointer to the process or term that contains the variable definition *)
		 definition_success : program_point
		   (* Pointer to the process or term that is executed just after the variable is defined *)
	       }

and program_point = 
    DProcess of process
  | DInputProcess of inputprocess
  | DTerm of term
  | DFunRestr
  | DFunArgs
  | DGenVar
  | DNone

and linktype = 
    NoLink
  | TLink of term

and funcats = 
    Std
  | Tuple 
  | Equal
  | LetEqual (* Special equality symbol for let assignments *)
  | Diff
  | ForAllDiff (* Special symbol meaning "for all variables named ?x_..., t1 <> t2" *)
  | Or
  | And
  | Event (* Function symbols for events *)
  | SepLetFun (* Function symbols defined by letfun, and that can 
		 be implemented as a separate functon (no find, array access,
		 out of scope access) *)

and impl_name =
    Func of string
  | Const of string
  | SepFun (* Function symbol defined by letfun and implemented 
              as a separate function (corresponds to f_cat = SepLetFun
              and the function is used in the part translated to 
	      implementation) *)
  | No_impl

and funsymb = { f_name : string;
		f_type : typet list * typet; (* argument and result types *)
                f_cat : funcats;
	    	f_options : int; (* options *)
		mutable f_statements : collision list;
		mutable f_collisions : collision list;
		mutable f_eq_theories : eq_th; (* equational theories for this function symbol *)
                mutable f_impl : impl_name; (* implementation name *)
                mutable f_impl_inv : string option; (* implementation of inverse if applicable *)
              }

and eq_th =
    NoEq
  | Commut 
  | Assoc 
  | AssocCommut 
  | AssocN of funsymb(*associative function*) * funsymb(*neutral*)
  | AssocCommutN of funsymb(*AC function*) * funsymb(*neutral*)
  | Group of funsymb(*mult*) * funsymb(*inverse*) * funsymb(*neutral*)
  | CommutGroup of funsymb(*mult*) * funsymb(*inverse*) * funsymb(*neutral*)
  | ACUN of funsymb(*xor*) * funsymb(*neutral*)

(* Replication index *)
and repl_index = { ri_sname : string;
                   ri_vname : int;
		     (* The name of the replication index consists of two elements:
			ri_sname is a string, ri_vname is an integer, the full name
			of the replication index is (ri_sname)_(ri_vname). 
			This is similar to the name of variables. *) 
		   ri_type : typet; 
		     (* Type of the replication index.
			Must be an interval *)
		   mutable ri_link : linktype
		     (* Link of the replication index to a term.
			This is used for implementating substitutions. *)
		 }

and term_desc = 
    Var of binder * term list (* array access *)
  | ReplIndex of repl_index (* replication index *)
  | FunApp of funsymb * term list
  | TestE of term * term * term
  | FindE of term findbranch list * term * find_info
  | LetE of pattern * term * term * term option
  | ResE of binder * term
  | EventAbortE of funsymb
  | EventE of term * term
  | InsertE of table * term list * term
  | GetE of table * pattern list * term option * term * term * find_info
	
and 'a findbranch = (binder(*the variable defined when the find succeeds*) * repl_index(*the corresponding replication index used for searching in the arrays*)) list * binderref list(*guaranteed defined array references*) * term(*condition*) * 'a(*then branch*)

and term = { t_desc : term_desc;
	     t_type : typet;
	     t_occ : int;
	        (* Occurrence of the term *)
	     t_max_occ : int;
	        (* Maximum occurrence of any subterm of the considered term.
		   [Terms.move_occ_term] guarantees that the occurrences of the subterms
		   of the considered term form exactly the interval [t_occ,t_max_occ].
		   When [t_max_occ] cannot be set to satisfy this constraint,
		   it is set to 0. *)
	     t_loc : Parsing_helper.extent;
	     mutable t_incompatible : int Occ_map.occ_map;
	        (* Incompatible program points:
		   if [(pp -> n) \in t.t_incompatible] and 
                   the common suffix of [l] and [l'] has length at least [n], then
		   [t] with indices [l] and [pp] with indices [l'] cannot be both executed.
		   Program points are represented by their occurrence. *)
	     mutable t_facts : fact_info }

and fact_info = (repl_index list * term list * elsefind_fact list * binderref list * term list * binder list * def_node) option
      (* Some(cur_array, true_facts, elsefind, def_vars, future_true_facts, future_def_vars, def_node):
	 cur_array = replication indices at the current program point
	 true_facts = the facts that are true at the current program point
	 elsefind = elsefind facts that are true at the current program point
	 def_vars = the variables whose definition is guaranteed because
	    of defined conditions above the current program point
	 future_true_facts = the facts that are certainly true when the block
	    containing the current program point is executed until the end
         future_binders = variables whose definition is guaranteed when the block
            containing the current program point is executed until the end
	 def_node = the node immediately above the current program point *)

and elsefind_fact = repl_index list * binderref list * term
      (* The elsefind_fact (bl, def_list, t) means 
	 forall bl, not(defined(def_list) && t) 
	 It is generated in the "else" branch of a 
	 find bl suchthat defined(def_list) && t. *)

(* Processes *)

and pattern = 
    PatVar of binder
  | PatTuple of funsymb * pattern list
  | PatEqual of term

and inputprocess_desc = 
    Nil
  | Par of inputprocess * inputprocess
  | Repl of repl_index * inputprocess
  | Input of (channel * term list) * pattern * process

and inputprocess =
    { i_desc : inputprocess_desc;
      i_occ : int;
      i_max_occ : int;
      i_loc : Parsing_helper.extent;
      mutable i_incompatible : int Occ_map.occ_map; (* similar to t_incompatible *)
      mutable i_facts : fact_info }

and process_desc =  
    Yield
  | EventAbort of funsymb
  | Restr of binder * process 
  | Test of term * process * process
  | Find of process findbranch list * process * find_info
  | Output of (channel * term list) * term * inputprocess
  | Let of pattern * term * process * process
  | EventP of term * process
  | Insert of table * term list * process
  | Get of table * pattern list * term option * process * process * find_info

and process =
    { p_desc : process_desc;
      p_occ : int;
      p_max_occ : int;
      p_loc : Parsing_helper.extent;
      mutable p_incompatible : int Occ_map.occ_map; (* similar to t_incompatible *)
      mutable p_facts : fact_info }

(* Equivalences *)

and action =
    AFunApp of funsymb         (* Application of f *)
  | APatFunApp of funsymb      (* Pattern matching with f *)
  | AReplIndex                 (* Reading a replication index *)
  | AArrayAccess of int        (* Array access with n indexes *)
  | ANew of typet              (* Random number generation of type t *)
  | ANewChannel                (* Create a private channel *)
  | AIf                        (* Test *)
  | AFind of int               (* Find: one choice with n indexes to choose *)
  | AOut of typet list * typet (* Output with channel indexes of types tl and output bitstring of type t *)
  | AIn of int                 (* Record input with n channel indexes in input list *)

and mode =
    ExistEquiv | AllEquiv

and options =
    StdOpt | UsefulChange

and restropt =
    NoOpt | Unchanged | DontKnow

and name_to_discharge_t = (binder * restropt ref) list
    
and fungroup =
    ReplRestr of repl_index(*replication*) option * (binder * restropt) list(*restrictions*) * fungroup list
  | Fun of channel * binder list(*inputs*) * term * (int(*priority*) * options)

and eqmember = 
    (fungroup * mode) list

and eqopt =
    StdEqopt | ManualEqopt | PrioEqopt of int

and eqopt2 =
    Decisional | Computational

and eqname = 
    CstName of ident
  | ParName of ident * ident
  | NoName


and stored_game =
  { text_display: string; (*file storing displayed game*)
    tex_display: string option; (*file storing displayed game in Latex*)
  }
    
and game_process =
  | RealProcess of inputprocess
  | Forgotten of stored_game

and game = 
    { mutable proc : game_process;
      mutable expanded : bool;
      mutable game_number : int;
      mutable current_queries : cur_queries_t
	(* [current_queries] contains, for each query:
	   [(query, game), ref proof] where
	   the query [query] should be proved in game [game],
	   [proof = ToProve] when it is not proved yet;
	   [proof = Inactive] when a [focus] command indicated not 
	   to focus on this query (it is left to proof in another branch).
	   [proof = Proved(proba_info, state)] when it is proved using the sequence of games [state],
	   and [proba_info] defines the probability that query is broken in the last game of [state].
	   Hence, the probability of breaking the initial query [query] is the sum of all 
	   probability differences on the sequence from [game] to the final game of [state]
	   plus [proba_info].
	   However, this probability may depend on the probability of events
	   introduced during the proof (which may not be bounded yet).
	   [proba_info] can be either a constant probability [CstProba proba]
	   or [MulQueryProba(N, (q,g), proof_ref)], which means [N] times the probability
	   of breaking [q] in game [g]; [proof_ref] is the proof information for
	   query [q]. This case is used by the transformation "guess", which guesses 
	   the tested session. *)
    }

and cur_queries_t = ((query * game) * proof_t ref) list

and proba_info =
  | CstProba of setf list
  | MulQueryProba of param * (query * game) * proof_t ref
      
and proof_t =
  | Proved of proba_info * state
  | ToProve
  | Inactive

and probaf = 
    Proba of proba * probaf list
  | Count of param
  | OCount of channel
  | Add of probaf * probaf
  | Mul of probaf * probaf
  | Power of probaf * int
  | Cst of float
  | Zero
  | Sub of probaf * probaf
  | Div of probaf * probaf
  | Max of probaf list
  | Min of probaf list
  | Card of typet
  | EpsFind (* 2 times the distance between the uniform distribution and the one 
	       generated by Find when several choices are possible. *)
  | EpsRand of typet (* For bounded types t, the distance between the uniform distribution and the
                        distribution generated by "new x:t" *)
  | PColl2Rand of typet (* Probability of collision between two independent random elements chosen 
			   according to the standard distribution for type t. 
			   This is \sum_{x \in t} P(x)^2, which is at most PColl1Rand(t). *)
  | PColl1Rand of typet (* Probability of collision between one random element chosen according to the standard
			   distribution for type t, and an element of type t that does not depend on it.
			   This is also the maximum probability of choosing any given element of t in the
			   standard distribution for that type.  *)
  | AttTime (* Time of the attacker *)
  | Time of game * probaf (* Time i = runtime of game number i *)
  | ActTime of action * probaf list 
  | Maxlength of game * term
  | TypeMaxlength of typet
  | Length of funsymb * probaf list
  | OptimIf of optimcond * probaf * probaf

and optimcond =
  | OCProbaFun of string * probaf list
  | OCBoolFun of string * optimcond list
	
and var_proba =
    { vp_name : string;
      vp_dim : computed_dim;
      vp_val : probaf }

(* An element of type [setf list] represents a probability
   computed as the sum of the probabilities [proba] 
   of all elements [SetProba proba] of the list, plus
   the probability of the disjunction of all events
   recorded by elements [SetEvent ...] of the list. *)

and setf =
    SetProba of probaf
  | SetEvent of funsymb * game * binder list(*public variables*) * proof_t ref
  | SetAssume (* A command that may not be correct has been used *)

and equiv_gen =
    { eq_name : eqname;
      mutable eq_fixed_equiv : (eqmember * eqmember * setf list * eqopt2) option;
      mutable eq_name_mapping : (binder * binder * def_check) list option;
      eq_special : (ident * special_args_e list) option;
      eq_exec : eqopt }
	
and equiv = eqname * eqmember * eqmember * setf list * eqopt * eqopt2

and def_check = term list

and equiv_nm = equiv * (binder * binder * def_check) list 
        (* equivalence with name mapping *)

(* Logical statements *)

and statement = binder list * term * term(*side condition*)

(* Collision statements *)
and indep_cond =
    IC_And of indep_cond * indep_cond
  | IC_Or of indep_cond * indep_cond
  | IC_True
  | IC_Indep of binder * binder
      
and collision =
    { c_restr : binder list; (*restrictions*)
      c_forall : binder list; (*forall*)
      c_redl : term;
      c_proba : probaf;
      c_redr : term;
      c_indep_cond : indep_cond; (*independence conditions*)
      c_side_cond : term; (*side condition*)
      c_restr_may_be_equal : bool }(*restrictions may be equal?*)

(* Queries *)

and qterm =
    QEvent of bool(*true when injective*) * term
  | QTerm of term
  | QAnd of qterm * qterm
  | QOr of qterm * qterm

and query = 
  | QSecret of binder * binder list(*public variables*) * bool(*true when onesession*) 
  | QEventQ of (bool(*true when injective*) * term) list * qterm * binder list(*public variables*)
  | QEquivalence of state(*sequence of games transformations from final game*) * binder list(*public variables*) * bool(*current game comes from LHS*)
  | QEquivalenceFinal of game * binder list(*public variables*)
  | AbsentQuery
  
(* Instructions for modifying games *)

(* For removal of assignments *)
and rem_set =
    All
  | Binders of binder list
  | FindCond
  | Minimal
  | EqSide (* Specific for the RHS of equiv statements. 
	      Removes useless assignments let x = y; does not remove let x = y[...] *)

and move_set =
    MAll
  | MNoArrayRef
  | MLet
  | MNew
  | MNewNoArrayRef
  | MBinders of binder list

and merge_mode =
    MNoBranchVar
  | MCreateBranchVar
  | MCreateBranchVarAtProc of process list * repl_index list
  | MCreateBranchVarAtTerm of term list * repl_index list

(* User info for cryptographic transformation *)

and var_mapping = (binder(*variable in game*) * binder(*variable in equivalence*)) list * 
      binder(*variable in game, when the corresponding variable in equivalence is not known*) list * bool
    (* bool is true when the list ends with "."
       no other variable should be added by the transformation in this case *)
and term_mapping = (int(*occurrence in game*) * term(*oracle in equivalence*)) list * bool

and crypto_transf_user_info =
    VarList of binder list * bool (* bool is true when the list ends with "."
				    no other variable should be added by the transformation in this case *)
  | Detailed of var_mapping option * term_mapping option

and guess_arg_t =
  | GuessRepl of repl_index * Parsing_helper.extent
  | GuessOcc of int * Parsing_helper.extent
	
and instruct =
  | ExpandGetInsert_ProveUnique
  | Expand
  | Simplify of known_when_adv_wins option * coll_elim_t list(*occurrences, variables, or types for collision elimination of password types*)
  | SimplifyNonexpanded
  | GlobalDepAnal of binder * coll_elim_t list (* same as for Simplify *)
  | RemoveAssign of rem_set
  | UseVariable of binder list
  | SArenaming of binder
  | MoveNewLet of move_set
  | CryptoTransf of equiv_nm * crypto_transf_user_info
  | InsertEvent of string(*event name*)  * Parsing_helper.extent * int(*occurrence of insertion*) * Parsing_helper.extent
  | InsertInstruct of string(*instruction*) * Parsing_helper.extent * int (*occurrence of insertion*) * Parsing_helper.extent
  | ReplaceTerm of string(*term*) * Parsing_helper.extent * int (*occurrence of replacement*) * Parsing_helper.extent * replace_check_opt_t
  | MergeArrays of (binder * Parsing_helper.extent) list list * merge_mode
  | MergeBranches
  | Proof of ((query * game) * setf list) list
  | IFocus of query list
  | Guess of guess_arg_t
	
and ins_updater = (instruct -> instruct list) option

and to_do_t = (instruct list * int * name_to_discharge_t) list

(* Detailed game transformations. Used to record what transformations 
   have been done. *)

and pat_simp_type = 
    DEqTest
  | DExpandTuple
  | DImpossibleTuple

and let_transfo = (pattern * pat_simp_type) list
      
and simplify_ins =
    SReplaceTerm of term * term
  | STestTrue of program_point
  | STestFalse of program_point
  | STestMerge of program_point
  | STestOr of program_point
  | STestEElim of term
  | SFindBranchRemoved of program_point * program_point findbranch
  | SFindSingleBranch of program_point * program_point findbranch
  | SFindRemoved of program_point 
  | SFindElseRemoved of program_point
  | SFindBranchMerge of program_point * program_point findbranch list
  | SFindDeflist of program_point * binderref list * binderref list
  | SFindinFindCondition of program_point * term
  | SFindinFindBranch of program_point * program_point
  | SFindtoTest of program_point
  | SFindIndexKnown of program_point * program_point findbranch * (binder * term) list
  | SFindInferUnique of program_point
  | SLetElseRemoved of program_point
  | SLetRemoved of program_point
  | SLetSimplifyPattern of program_point * let_transfo
  | SResRemoved of program_point
  | SResToAssign of program_point
  | SEventRemoved of program_point
  | SAdvLoses of program_point
	
and def_change =
    DRemoveDef
  | DKeepDefPoint
  | DKeepDef

and usage_change =
    DRemoveAll
  | DRemoveNonArray

and detailed_instruct =
    DExpandGetInsert of table
  | DProveUnique
  | DProveUniqueFailed
  | DExpandIfFind of simplify_ins list
  | DSimplify of simplify_ins list
  | DGlobalDepAnal of binder * coll_elim_t list
  | DLetSimplifyPattern of program_point * let_transfo
  | DRemoveAssign of binder * def_change * usage_change
  | DUseVariable of binder * (term * term) list
  | DSArenaming of binder * binder list
  | DMoveNew of binder
  | DMoveLet of binder
  | DCryptoTransf of equiv_nm * crypto_transf_user_info
  | DInsertEvent of funsymb(*event name*) * int(*occurrence of insertion*) 
  | DInsertInstruct of string * int (*occurrence of insertion*)
  | DReplaceTerm of term * term * int (*occurrence of replacement*)
  | DMergeArrays of (binder * Parsing_helper.extent) list list * merge_mode
  | DMergeBranches of process * process list
  | DMergeBranchesE of term * term list
  | DGuess of guess_arg_t

(* The type of game transformations: they take as input a game
and return a triple (transformed game, probability difference,
detailed description of the transformation).
Game transformations also set Transform.changed when they actually
modify the game, and add advised instructions in Transform.advise. *)

and game_transformer = game -> game * setf list * detailed_instruct list

(* State. Used to remember a sequence of game modifications *)

and state =
    { game : game;
      prev_state : (instruct * setf list * detailed_instruct list * state) option;
      mutable tag : string option }

and simp_facts = term list * term list * elsefind_fact list

(* Collector for known information when the adversary wins,
   i.e. manages to falsify a query.
   The top list is a disjunction.
   Each element of the list is a tuple 
     (all_indices, pp_list, simp_facts, def_list)
   where 
   [all_indices] is the list of all replication indices that parameterize
   the collected facts
   [pp_list] is a list of program points that have been
   executed with the associated replication indices,
   [simp_facts] are facts are known to hold,
   [def_list] is a list of variables known to be defined. *)
      
and known_when_adv_wins =
    (repl_index list * (term list * program_point) list * simp_facts * binderref list) list

(* Polynoms of probabilities *)

type monomial = (probaf * int) list

type polynom = (float * monomial) list
      
(* Result of a cryptographic transformation *)
type failure_reason =
    Term of term
  | UntransformableTerm of term
  | RefWithIndicesWithoutMatchingStandardRef of binderref * binderref
  | RefWithIndicesWithIncompatibleStandardRef of binderref * binderref * int
  | IncompatibleRefsWithIndices of binderref * binderref * binderref * binderref * int
  | NoChange
  | NoChangeName of binder
  | NoUsefulChange
  | NameNeededInStopMode


type trans_res =
    TSuccess of setf list * detailed_instruct list * game
  | TFailure of (equiv_nm * crypto_transf_user_info * instruct list) list * ((binder * binder) list * failure_reason) list

type dep_anal_side_cond =
    NoSideCond
  | SideCondToCompute
  | SideCondFixed of term list * term list list
      
type dep_anal_indep_test = simp_facts -> term -> binderref -> (term * dep_anal_side_cond) option
type dep_anal_collision_test = simp_facts -> term -> term -> term option

type dep_anal = dep_anal_indep_test * dep_anal_collision_test

(* A dependency analysis (type [dep_anal]) consists of a pair
[(indep_test, collision_test)].

[indepTest simp_facts t (b,l)] 
returns [Some (t', side_condition)] 
when [t'] is a term obtained from [t] by replacing array indices that 
depend on [b[l]] with fresh indices. These fresh indices are linked to 
the term they replace.
When [side_condition = NoSideCond], [t'] does not depend on [b[l]].
When [side_condition = SideCondToCompute] is true, [t'] contains [b] itself.
[t'] does not depend on [b[l]] when the indices of [b] in [t'] are different from [l].
When [side_condition = SideCondFixed(l, [l1; ...; ln])], [t'] does not depend on [b[l]]
when [l <> li] for all [i] in [[1;...;n]].
Returns [None] if that is not possible.
      
[collision_test simp_facts t1 t2] simplifies [t1 = t2] using dependency 
analysis.
It returns
- [Some t'] when it simplified [t1 = t2] into [t'];
- [None] when it could not simplify [t1 = t2]. 

[simp_facts] contains facts that are known to hold. 
*)

exception NoMatch
exception Contradiction

(* Where are we in add_facts/add_def_vars:
   current_point = the current program point
   cur_array = the value of the replication indices at the current program point 
   current_node = the definition node at the current program point

   Due to "defined" conditions above the current program point, I know
   that some variables are defined before this point.
   def_vars_in_different_blocks and def_vars_maybe_in_same_block
   collect ordered sequences of variables defined before the current
   program point.
   The elements in these two lists occur in chronological order of
   definition (the first element has been defined first).
   The elements of def_vars_maybe_in_same_block are all defined before
   the elements of def_vars_in_different_blocks.
   Each element of these lists contains
   - the nodes at which the variable may have been defined
   - the indices of the variable.

   The elements of def_vars_in_different_blocks are known to be defined
   after the end of the input...output block of code that defines 
   the first element of def_vars_maybe_in_same_block.
   current_in_different_block is true when the current program point
   is known to be after the end of the input...output block of code
   that defined the first element of def_vars_maybe_in_same_block.
   Invariant: current_in_different_block is always true when 
   def_vars_in_different_blocks is non-empty. *)

type known_history =
    { current_point : program_point;
      cur_array : term list;
      current_node : def_node;
      current_in_different_block : bool;
      def_vars_in_different_blocks : (def_node list * term list) list;
      def_vars_maybe_in_same_block : (def_node list * term list) list }


      
(* For the generation of implementations
   type for a program : name, options, process *)

type impl_opt = Read of binder * string | Write of binder * string 

type impl_process = string * impl_opt list * inputprocess

type impl_letfun = funsymb * binder list * term

type impl_info = impl_letfun list * impl_process list
      
type final_process =
    SingleProcess of inputprocess
  | Equivalence of inputprocess * inputprocess * binder list(*public variables*)
  
type ri_mul_t =
  term list * (repl_index list * probaf) option
      
type probaf_mul_types =
  { p_ri_list : repl_index list; (* List of replication indices *)
    p_ri_mul  : ri_mul_t; (* Probability formula that represents the number of repetitions of the collision
			   p_ri_mul = known_def, Some(ri_list, p) corresponds to  \prod_{ri \in ri_list} |ri.ri_type| * p
			   It may be a better formula than \prod_{ri \in p.p_ri_list} |ri.ri_type| using #O for some oracles O.
			   p_ri_mul = known_def, None means that the terms in [known_def] are known to be defined.
			   This information is later exploited to replace some factors
			   in prod_{ri \in p.p_ri_list} |ri.ri_type| with #O,
			   in order to replace None with Some(ri_list,p). *)
    p_proba : probaf; (* p: The probability of one collision. For all M independent of the random variable, Pr[t1 = M] <= p *)
    p_dep_types : typet list; (* dep_types: The list of types of subterms (non-replication indices) of t2 replaced with variables [?] *)
    p_full_type : typet; (* The type of t2 *)
    p_indep_types_option : typet list option } (* indep_types_option: 
	 indep_types_option = Some indep_types, where indep_types is 
	 The list of types of subterms of t2 
	 not replaced with variables [?].  This list is valid only
	 when subterms of [t2] are replaced only under [data]
	 functions, so that product of |T| for T \in dep_types <=
	 |type(t2)|/product of |T| for T \in indep_types.  When it is
	 not valid, indep_types_option = None. *) 

 (* a record [p: probaf_mul_types] represents
    When p.p_ri_mul = (ri_list, p_nb)
       \prod_{ri \in ri_list} |ri.ri_type| * p_nb * p.p_proba * \prod_{T \in p.p_dep_types} |T|.
    When p.p_indep_types_option = Some indep_types, 
    \prod_{T \in p.p_dep_types} |T| <= |p.p_full_type|/\prod{T \in indep_types} |T|. *)
      
type term_coll_t = 
  { t_side_cond : term; (* The collisions are eliminated only when this term is true *)
    t_true_facts : term list; (* Facts that are known to hold when the collision is eliminated *)
    t_used_indices : repl_index list; (* Indices that occur in colliding terms *) 
    t_initial_indices : repl_index list; (* Indices at the program point of the collision *)
    t_charac : term; (* The two colliding terms, t1 and t2 *)
    t_indep : term; 
    t_var : binder; (* The random variable that is (partly) characterized by t1 and from which t2 is independent, with its indices *)
    t_lopt : term list option;
    t_proba : probaf_mul_types } (* see above *)

type binder_coll_t = binder * binder * probaf_mul_types
      (* [(b1,b2,_)] means that we eliminated collisions
	 between the random variables [b1] and [b2] *)

type instantiated_collision =
    { ic_restr : term list; (*restrictions*)
      ic_redl : term; (*lhs*)
      ic_proba : probaf;
      ic_redr : term; (*rhs*)
      ic_indep_cond : term; (*indep cond*)
      ic_side_cond : term; (*side cond*)
      ic_restr_may_be_equal : bool } (*restr_may_be_equal*)

type any_var_map_list_t =
    { source : binder list;
      images : term list list }
      
type red_proba_t =
    { r_coll_statement : collision;
      r_restr_indep_map : (binder * term) list;
      r_any_var_map_list : any_var_map_list_t;
      r_i_coll_statement : instantiated_collision;
      r_proba : probaf_mul_types }
      (* a record [r: red_proba_t]
	 means that we applied the collision statement [r.r_coll_statement]
	 with variables bound as defined by [r.r_restr_indep_map]
	 and [r.r_any_var_map list]. [r.r_restr_indep_map] binds variables
	 defined by "new" and those with independence conditions.
	 [any_var_map] binds other variables (universally quantified).
	 There can be several applications with different values of 
	 [any_var_map]; all those applications are collected in 
	 [r.r_any_var_map_list]; the images are omitted when those
	 variables do not occur in the probability.
	 [r.r_i_coll_statement] is the collision statement instantiated
	 following [r.r_restr_indep_map].
	 [r.r_proba] represents the probability of collision 
	 (see type [probaf_mul_types] for details) *)

type simplify_internal_info_t = probaf * binder_coll_t list * red_proba_t list
      
(* For the dependency analyses *)

type term_coll_proba_t =
  | Fixed of probaf_mul_types
  | ProbaIndepCollOfVar of binder * term list * repl_index list * term list
     (* [ProbaIndepOfVar (b, args, ri_list, known_def)] represents a probability p such that
	for all M independent of b0[l0], Pr[b[args] = M] <= p,
	where the indices of M are [ri_list].
	[known_def] is a list of terms that are known to be defined
	when this property is proved. It is useful to optimize the
	probability by replacing some indices by #O.
	It is used only in global dependency analysis, where b0 is the main
	variable on which we perform the analysis.
	This element is used in a status Compos(proba, term, l0opt).
	When l0opt = None, l0 and args above are any index.
	Otherwise, l0opt = Some l0, 
	the status of b must be Compos(proba_b, term_b, Some l0'),
	which tells us b[args_at_creation] depends on b0[l0'].
	Then l is such that l0 = l0'{l/b.args_at_creation}. *)
      
type all_coll_t = term_coll_proba_t list * binder_coll_t list * red_proba_t list
      
type find_compos_probaf = repl_index * all_coll_t
      (* (ri_arg, all_coll) 
         [ri_arg] is a placeholder for the replication indices and variables 
	 of the term [t'] below (independent of [b0[...]]),
         [all_coll] represents the probabilities of collisions found in
	 [find_compos]. *)
      
type depend_status =
  | Compos of find_compos_probaf * term * term list option
  | Decompos of term list option
  | Any
(* The dependency status of a term [t] with respect to a variable [b0] is
   - [Compos(p, t_1, l0opt)]:
     - when l0opt = Some l0, for all [t'] independent of [b0[l0]], Pr[t = t'] <= p,
     - when l0opt = None, for all [t'] independent of [b0[l]] for all [l], Pr[t = t'] <= p,
     [t_1] is a modified version of [t] in which the parts that are not useful
     to show this property are replaced with variables [?].
     [p] is the probability for one test t = t'. The placeholder [ri_arg] inside [p]
     should be replaced by the indices of the term [t'].
   - [Decompos(l0opt)]:
     - when l0opt = Some l0, [t] is obtained from [b0[l0]] by applying functions
     that extract a part of their argument (functions marked [uniform]);
     - when l0opt = None, [t] is obtained from [b0[l0']] by applying decomposition 
     functions, for some l0'.
   - [Any] in the other cases 

   Decompos(l0opt) => Compos(PColl1Rand t.t_type, t, l0opt) *)

type extracted_depend_status = (find_compos_probaf * term * term list option) option
  (* The dependency status of a term [t] with respect to a variable [b0] 
     presented as follows:
   - [Some(p, t_1, l0opt)] if
     - when l0opt = Some l0, for all [t'] independent of [b0[l0]], Pr[t = t'] <= p,
     - when l0opt = None, for all [t'] independent of [b0[l]] for all [l], Pr[t = t'] <= p,
     [t_1] is a modified version of [t] in which the parts that are not useful
     to show this property are replaced with variables [?].
   - [None] otherwise. *)
      
type 'a depinfo =      
    { args_at_creation_only: bool; (* True when the field [dep] deals only with variables with indices args_at_creation *)
      dep: (binder * (depend_status * term list option * 'a)) list; 
          (* List of variables that depend on b0 
             Each element of the list is (b, (depend_status, args_opt, x)), where
             b is a variable that depends on b0.
             depend_status is its dependency status as defined above.
             When args_opt is (Some l), b[args_at_creation] depends on b0[l]
             and on no other cell of b0.
             When args_opt is None, b may depend on any cell of b0.
             x is some additional information, which may differ between dependency analyses.
             *)
      other_variables: bool; (* True when variables not in dep may also depend on b0 *)
      nodep: term list } (* List of terms that do not depend on b0 *)


(* Kinds of definitions of a variable *)

type def_kind_t =
  | AssignDef of binder * term list
  | RestrDef
  | OtherDef

(* Collision used special equivalences and in the "move array" command *)

type special_equiv_collision = binder list * binder list * term

(* Expected type or variable in the collisions in special equivalences
   and in the "move array" command *)

type expect_t =
  | ExpectType of typet
  | ExpectVar of binder

(* Structure of oracles *)

type oracle_struct =
    { oname: channel;
      otype: typet list(*types of indices*) * typet list(*types of arguments*) * typet list option(*type of result*);
      onext: oracle_struct list }
      
