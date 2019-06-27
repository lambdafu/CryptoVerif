open Ptree
open Types

type frontend =
    Channels
  | Oracles

let get_implementation = ref false

let out_dir = ref "."
let proof_output = ref ""
    
let front_end = ref Channels

let lib_name = ref "default"

(* memory saving *)
let forget_old_games = ref false
                   
(* debug settings *)
let debug_instruct = ref false
let debug_cryptotransf = ref 0
let debug_find_unique = ref false
let debug_simplify = ref false
let debug_elsefind_facts = ref false
let debug_simplif_add_facts = ref false
let debug_corresp = ref false
let debug_event_adv_loses = ref false
    
(* To parse games output by CryptoVerif, 
set this variable to true: such games may contain
"defined" conditions on variables that are never defined. *)
let allow_undefined_var = ref false
    
let max_depth_add_fact = ref 1000
let max_depth_try_no_var_rec = ref 20
let max_replace_depth = ref 20
let elsefind_facts_in_replace = ref true
let elsefind_facts_in_success = ref true
let elsefind_facts_in_simplify = ref true
let elsefind_facts_in_success_simplify = ref true
let else_find_additional_disjunct = ref true
let improved_fact_collection = ref false
let corresp_cases = ref true
let simplify_use_equalities_in_simplifying_facts = ref false
let re_reduce_root_sides = ref true
    
let diff_constants = ref true
let constants_not_tuple = ref true

let use_known_equalities_crypto = ref true
let priority_event_unchanged_rand = ref 5

let normalize_in_match_funapp = ref false
                                        
let expand_letxy = ref true

(* Bound the number of advice possibilities in cryptotransf.ml
   Having too many of them does not help because we will need to try
   all of them and it will take a lot of time. *)
let max_advice_possibilities_beginning = ref 50
let max_advice_possibilities_end = ref 10

let minimal_simplifications = ref true
let merge_branches = ref true
let merge_arrays = ref true
let unique_branch = ref true
let unique_branch_reorg = ref true
let infer_unique = ref false
                              
let auto_sa_rename = ref true
let auto_remove_assign_find_cond = ref true
let auto_remove_if_find_cond = ref true
let auto_move = ref true

let optimize_let_vars = ref false

let ignore_small_times = ref 3

let interactive_mode = ref false

let auto_advice = ref true
let no_advice_crypto = ref false
let no_advice_globaldepanal = ref false

let backtrack_on_crypto = ref false

let simplify_after_sarename = ref true

let max_iter_simplif = ref 2
let max_iter_removeuselessassign = ref 10

let detect_incompatible_defined_cond = ref true

let psize_NONINTERACTIVE = 20
let psize_PASSIVE = 10
let psize_DEFAULT = 0

let tysize_LARGE = 20
let tysize_PASSWORD = 10
let tysize_SMALL = 0

let tysize_MIN_Manual_Coll_Elim = ref 5
let tysize_MIN_Auto_Coll_Elim = ref 15
(* Determines the probabilities that are considered small enough to 
   eliminate collisions. It consists of a list of probability descriptions
   of the form ([(psize1, n1); ...; (psizek,nk)], tsize) 
   which represent probabilities of the form
   constant * (parameter of size <= psize1)^n1 * ... * 
   (parameter of size <= psizek)^nk / (type of size >= tsize) 

   The default value allows: anything/large type and 
   default parameter/password *) 
let allowed_collisions = ref [ ([max_int, max_int], tysize_LARGE); 
                               ([psize_DEFAULT, 1], tysize_PASSWORD) ]

(* Similar to allowed_collisions but for "collision" statements:
   It consists of a list of probability descriptions
   of the form [(psize1, n1); ...; (psizek,nk)] 
   which represent probabilities of the form
   constant * (parameter of size <= psize1)^n1 * ... * 
   (parameter of size <= psizek)^nk.

   The default value allows any probability formula *)
let allowed_collisions_collision = ref [ [max_int, max_int] ]

let parse_type_size = function
    "large" -> tysize_LARGE
  | "password" -> tysize_PASSWORD
  | s -> (* option size<n> *)
      try
	if (String.sub s 0 4) <> "size" then raise Not_found;
	int_of_string (String.sub s 4 (String.length s - 4))
      with _ -> raise Not_found

let parse_bool v var =
  match v with
    S ("true",_) -> var := true
  | S ("false",_) -> var := false
  | _ -> raise Not_found
	  
let do_set p v =
  match (p,v) with
  | "allowUndefinedVar", _ -> parse_bool v allow_undefined_var
  | "diffConstants", _ -> parse_bool v diff_constants 
  | "constantsNotTuple", _ -> parse_bool v constants_not_tuple 
  | "expandAssignXY", _ -> parse_bool v expand_letxy
  | "minimalSimplifications", _ -> parse_bool v minimal_simplifications 
  | "mergeBranches", _ -> parse_bool v merge_branches
  | "mergeArrays", _ -> parse_bool v merge_arrays
  | "uniqueBranch", _ -> parse_bool v unique_branch
  | "uniqueBranchReorganize", _ -> parse_bool v unique_branch_reorg
  | "inferUnique", _ -> parse_bool v infer_unique
  | "autoSARename", _ -> parse_bool v auto_sa_rename
  | "autoRemoveAssignFindCond", _ -> parse_bool v auto_remove_assign_find_cond
  | "autoRemoveIfFindCond", _ -> parse_bool v auto_remove_if_find_cond
  | "autoMove", _ -> parse_bool v auto_move
  | "optimizeVars", _ -> parse_bool v optimize_let_vars
  | "interactiveMode", _ -> parse_bool v interactive_mode
  | "autoAdvice", _ -> parse_bool v auto_advice
  | "noAdviceCrypto", _ -> parse_bool v no_advice_crypto
  | "noAdviceGlobalDepAnal", _ -> parse_bool v no_advice_globaldepanal
  | "backtrackOnCrypto", _ -> parse_bool v backtrack_on_crypto
  | "simplifyAfterSARename", _ -> parse_bool v simplify_after_sarename
  | "detectIncompatibleDefined", _ -> parse_bool v detect_incompatible_defined_cond
  | "ignoreSmallTimes", I n -> ignore_small_times := n
  | "maxIterSimplif", I n -> max_iter_simplif := n
  | "maxIterRemoveUselessAssign", I n -> max_iter_removeuselessassign := n
  | "maxAdvicePossibilitiesBeginning", I n -> max_advice_possibilities_beginning := n
  | "maxAdvicePossibilitiesEnd", I n -> max_advice_possibilities_end := n
  | "useKnownEqualitiesInCryptoTransform", _ -> parse_bool v use_known_equalities_crypto
  | "priorityEventUnchangedRand", I n -> priority_event_unchanged_rand := n
  | "useKnownEqualitiesWithFunctionsInMatching", _ -> parse_bool v normalize_in_match_funapp
  | "minAutoCollElim", S (s,_) -> 
      let r = parse_type_size s in
      if r <= 0 then raise Not_found;
      tysize_MIN_Auto_Coll_Elim := r
  | "elsefindFactsInReplace", _ -> parse_bool v elsefind_facts_in_replace
  | "elsefindFactsInSuccess", _ -> parse_bool v elsefind_facts_in_success
  | "elsefindFactsInSimplify", _ -> parse_bool v elsefind_facts_in_simplify
  | "elsefindFactsInSuccessSimplify", _ -> parse_bool v elsefind_facts_in_success_simplify
  | "elsefindAdditionalDisjunct", _ -> parse_bool v else_find_additional_disjunct
  | "improvedFactCollection", _ -> parse_bool v improved_fact_collection
  | "useEqualitiesInSimplifyingFacts", _ -> parse_bool v simplify_use_equalities_in_simplifying_facts
  | "reReduceRootSides", _ -> parse_bool v re_reduce_root_sides
  | "maxReplaceDepth", I n -> max_replace_depth := n
  | "maxAddFactDepth", I n -> max_depth_add_fact := n
  | "maxTryNoVarDepth", I n ->
      (* For uniformity with maxAddFactDepth, 0 means no limit *)
      max_depth_try_no_var_rec := (if n = 0 then -1 else n)
  | "casesInCorresp", _ -> parse_bool v corresp_cases

  | "debugInstruct", _ -> parse_bool v debug_instruct
  | "debugFindUnique", _ -> parse_bool v debug_find_unique
  | "debugCryptotransf", I n -> debug_cryptotransf := n
  | "debugElsefindFacts", _ -> parse_bool v debug_elsefind_facts
  | "debugSimplify", _ -> parse_bool v debug_simplify
  | "debugSimplifAddFacts", _ -> parse_bool v debug_simplif_add_facts
  | "debugCorresp", _ -> parse_bool v debug_corresp
  | "debugAdvLoses", _ -> parse_bool v debug_event_adv_loses
  | "forgetOldGames", _ -> parse_bool v forget_old_games
  | _ -> raise Not_found


(* Type options *)

(* Types consisting of all bitstrings of the same length *)
let tyopt_FIXED = 2

(* Finite types *)
let tyopt_BOUNDED = 4

(* Types for which the standard distribution for generating
   random numbers is non-uniform *)
let tyopt_NONUNIFORM = 8

(* Types for which we can generate random numbers.
   Corresponds to one of the three options above *)
let tyopt_CHOOSABLE = tyopt_FIXED + tyopt_BOUNDED + tyopt_NONUNIFORM

(* Function options *)

let fopt_COMPOS = 1
let fopt_DECOMPOS = 2
let fopt_UNIFORM = 8

let tex_output = ref ""

(* Types and constants should be added to the initial environment,
as well as f_not *)
(* Types *)

let t_bitstring = { tname = "bitstring";
		    tcat = BitString;
		    toptions = 0;
		    tsize = tysize_LARGE;
                    timplsize = None;
                    tpredicate = Some "always_true";
                    timplname = Some "string";
                    tserial = Some ("id","id");
                    trandom = None }

let t_bitstringbot = { tname = "bitstringbot";
		       tcat = BitString;
		       toptions = 0;
		       tsize = tysize_LARGE;
                       timplsize = None;
                       tpredicate = Some "always_true";
                       timplname = Some "string option"; 
                       tserial = Some ("stringbot_from","stringbot_to");
                       trandom = None }

let t_bool = { tname = "bool";
	       tcat = BitString;
	       toptions = tyopt_FIXED + tyopt_BOUNDED;
	       tsize = 0;
               timplsize = Some(1);
               tpredicate = Some "always_true";
               timplname = Some "bool";
               tserial = Some ("bool_from","bool_to");
               trandom = Some ("rand_bool") }


(* For precise computation of the runtime only*)
let t_unit = { tname = "unit";
	       tcat = BitString;
	       toptions = tyopt_BOUNDED;
	       tsize = 0;
               timplsize = None;
               tpredicate = None;
               timplname = None;
               tserial = None;
               trandom = None }


(* For events in terms; they have a type compatible with any type*)
let t_any = { tname = "any";
	      tcat = BitString;
	      toptions = 0;
	      tsize = 0;
              timplsize = None;
              tpredicate = None;
              timplname = None;
              tserial = None;
              trandom = None }


(* Constants *)

let c_true = { f_name = "true";
	       f_type = [],t_bool;
	       f_cat = Std;
	       f_options = 0;
	       f_statements = [];
	       f_collisions = [];
	       f_eq_theories = NoEq;
               f_impl = Const "true";
               f_impl_inv = None }

let c_false = { f_name = "false";
		f_type = [],t_bool;
		f_cat = Std;
		f_options = 0;
		f_statements = [];
		f_collisions = [];
		f_eq_theories = NoEq;
		f_impl = Const "false";
		f_impl_inv = None }

(* Functions *)

let rec f_and = { f_name = "&&";
		  f_type = [t_bool; t_bool], t_bool;
		  f_cat = And;
		  f_options = 0;
		  f_statements = [];
		  f_collisions = [];
		  f_eq_theories = AssocCommutN(f_and, c_true);
		  f_impl = Func "(&&)";
		  f_impl_inv = None }

let rec f_or = { f_name = "||";
		 f_type = [t_bool; t_bool], t_bool;
		 f_cat = Or;
		 f_options = 0;
		 f_statements = [];
		 f_collisions = [];
		 f_eq_theories = AssocCommutN(f_or, c_false);
		 f_impl = Func "(||)";
		 f_impl_inv = None }

module HashedCatType =
  struct
    type t = Types.funcats * Types.typet
    let equal (cat1, t1) (cat2, t2) = (cat1 == cat2) && (t1 == t2)
    (* The hash function must use only parts that are not modified,
       otherwise, we may have the same element with several different hashes *)
    let hash (cat, t) = Hashtbl.hash (cat, t.tname)
  end

module CatTypeHashtbl = Hashtbl.Make(HashedCatType)

let comp_funs = CatTypeHashtbl.create 7

let f_comp cat t t2 =
  let t = 
    if t2 == t_any then t else
    if t == t_any then t2 else
    if t != t2 then
      Parsing_helper.internal_error "Comparisons for compatible types only"
    else
      t
  in
  try 
    CatTypeHashtbl.find comp_funs (cat,t)
  with Not_found ->
    let r = { f_name = 
	      begin
		match cat with
		  Equal -> "="
		| Diff -> "<>"
		| LetEqual -> ">>="
		| ForAllDiff -> "<A>"
		| _ -> Parsing_helper.internal_error "no comparison for this category"
	      end;
	      f_type = [t; t], t_bool;
	      f_cat = cat;
	      f_options = 0;
	      f_statements = [];
	      f_collisions = [];
	      f_eq_theories = if cat == Equal || cat == Diff then Commut else NoEq;
              f_impl = 
              begin
                match cat with
                    Equal -> Func "(=)"
                  | Diff -> Func "(<>)"
                  | _ -> No_impl
              end;
              f_impl_inv = None
            }
    in
    CatTypeHashtbl.add comp_funs (cat,t) r;
    r

let f_not = { f_name = "not";
	      f_type = [t_bool], t_bool;
	      f_cat = Std;
	      f_options = 0;
	      f_statements = [];
	      f_collisions = [];
	      f_eq_theories = NoEq;
              f_impl = Func "not";
              f_impl_inv = None;
            }

(* Event *)

let e_adv_loses =
  { f_name = "adv_loses";
    f_type = [t_bitstring], t_bool;
    f_cat = Event;
    f_options = 0;
    f_statements = [];
    f_collisions = [];
    f_eq_theories = NoEq;
    f_impl = No_impl;
    f_impl_inv = None }

    
(* Create tuple function of given type *)

module HashedTypeList =
  struct
    type t = Types.typet list
    let equal x1 x2 = (List.length x1 == List.length x2) && (List.for_all2 (==) x1 x2)
    (* The hash function must use only parts that are not modified,
       otherwise, we may have the same element with several different hashes *)
    let hash x = Hashtbl.hash (List.map (fun t -> t.tname) x)
  end

module TypeListHashtbl = Hashtbl.Make(HashedTypeList)

let tuple_fun_table = TypeListHashtbl.create 7

let get_tuple_fun tl =
  try 
    TypeListHashtbl.find tuple_fun_table tl
  with Not_found ->
    let f = { f_name = "";
	      f_cat = Tuple;
	      f_type = tl, t_bitstring;
	      f_options = fopt_COMPOS;
	      f_statements = [];
	      f_collisions = [];
	      f_eq_theories = NoEq;
              f_impl = Func "tuple";
              f_impl_inv = Some "detuple" }
    in
    TypeListHashtbl.add tuple_fun_table tl f;
    f

(*For precise computation of the runtime only*)

let t_interv = { tname ="[1,*]";
		 tcat = Interv { pname = "N*"; psize = 0 };
		 toptions = tyopt_BOUNDED;
	         tsize = 0;
                 timplsize = None;
                 tpredicate = None;
                 timplname = None;
                 tserial = None;
                 trandom = None }

let f_plus = { f_name = "+";
	       f_type = [t_interv; t_interv],t_interv;
	       f_cat = Std;
	       f_options = 0;
	       f_statements = [];
	       f_collisions = [];
	       f_eq_theories = Commut;
               f_impl = No_impl;
               f_impl_inv = None }


let f_mul = { f_name = "*";
	      f_type = [t_interv; t_interv],t_interv;
	      f_cat = Std;
	      f_options = 0;
	      f_statements = [];
	      f_collisions = [];
	      f_eq_theories = Commut;
              f_impl = No_impl;
              f_impl_inv = None }

module HashedFunInt =
  struct
    type t = funsymb * int
    let equal (x1,y1) (x2,y2) = (x1 == x2) && (y1 == y2)
    (* The hash function must use only parts that are not modified,
       otherwise, we may have the same element with several different hashes *)
    let hash (x,y) = Hashtbl.hash (x.f_name, List.map (fun t -> t.tname) (fst x.f_type), (snd x.f_type).tname, x.f_cat, x.f_options, y)
  end

module FunIntHashtbl = Hashtbl.Make(HashedFunInt)

let inverse_table = FunIntHashtbl.create 7

let get_inverse f n = 
  if f.f_options land fopt_COMPOS == 0 then
    Parsing_helper.internal_error "Can get inverse only for COMPOS functions";
  if (n < 1) || (n > (List.length (fst f.f_type))) then
    Parsing_helper.internal_error "Arity error in get_inverse";
  try
    FunIntHashtbl.find inverse_table (f,n)
  with Not_found ->
    let finv = { f_name = f.f_name ^ "^-1_" ^ (string_of_int n);
		 f_type = [snd f.f_type], (List.nth (fst f.f_type) (n-1));
		 f_cat = Std;
		 f_options = fopt_DECOMPOS;
		 f_statements = [];
		 f_collisions = [];
		 f_eq_theories = NoEq;
                 f_impl = No_impl;
                 f_impl_inv = None }
    in
    FunIntHashtbl.add inverse_table (f,n) finv;
    finv

(***************************************************************************)

let get_query_status (_, poptref) =
  !poptref
      
let get_public_vars queries =
  let public_vars = ref [] in
  let add_pub_vars pub_vars =
    List.iter (fun b ->
      if not (List.memq b (!public_vars)) then
	public_vars := b :: (!public_vars)
			      ) pub_vars
  in
  List.iter (function 
    | q when get_query_status q != ToProve -> () (* I ignore already proved and inactive queries *)
    | (QSecret (b',pub_vars,onesession),_),_ ->
	add_pub_vars (b'::pub_vars)
    | (QEventQ (_,_,pub_vars),_),_
    | (QEquivalence(_,pub_vars),_),_ 
    | (QEquivalenceFinal(_,pub_vars),_),_ ->
	add_pub_vars pub_vars
    | (AbsentQuery,_),_ -> ()) queries;
  
  !public_vars
    
let occurs_in_queries b q = List.memq b (get_public_vars q)

let event_occurs_in_term f t = 
  match t.t_desc with
    FunApp(f',_) -> f == f'
  | _ -> false

let rec event_occurs_in_qterm f = function
    QEvent(_,t) -> event_occurs_in_term f t
  | QTerm _ -> false
  | QAnd(t1,t2) | QOr(t1,t2) -> 
      (event_occurs_in_qterm f t1) || (event_occurs_in_qterm f t2)

let event_occurs_in_queries f q =
  List.exists (function
      q when get_query_status q != ToProve -> false (* I ignore already proved and inactive queries *)
    | (QSecret _, _),_ -> false
    | ((AbsentQuery | QEquivalence _ | QEquivalenceFinal _), _),_ ->
       (* When I want to prove indistinguishability, keep all events *)
       true
    | (QEventQ (l,r,_),_),_ ->
	(List.exists (fun (_,t) -> event_occurs_in_term f t) l) ||
	(event_occurs_in_qterm f r)
	  ) q

(***************************************************************************)

let equivs = ref []

let move_new_eq = ref []

(****************************************************************************)

(* Set when a game is modified *)

let changed = ref false

(* Instructions are added in advise when an instruction I cannot be fully
   performed. The added instructions correspond to suggestions of instructions
   to apply before I so that instruction I can be better performed. *)

let advise = ref ([] : instruct list)

