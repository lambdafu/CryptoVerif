open Ptree
open Types

let underscore_var_name = "ignored"
  
type frontend =
    Channels
  | Oracles

type impl_language = OCaml | FStar | Prove
(* Prove the protocol, do not generate an implementation *)

let get_implementation = ref Prove
let out_dir = ref Filename.current_dir_name
let proof_output = ref ""

let equiv_output = ref ""
let command_output = ref ""
    
let front_end = ref Channels

let lib_name = ref []

(* When handling "query_equiv", [events_to_ignore_lhs] contains events 
   that occur in the RHS of the equivalence to prove. Their probability 
   is implicitly added to the probability of distinguishing the LHS
   from the RHS, without trying to prove that it is negligible. *)
let events_to_ignore_lhs = ref []

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
    
let proba_zero = ref false
    (* When true, prevents all eleiminations of collisions, so that
       computed equalities *always* hold (not up to negligible probability). *)

let use_oracle_count_in_result = ref true

let max_efl = ref 50
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

let guess_remove_unique = ref false
    
let auto_sa_rename = ref true
let auto_remove_assign_find_cond = ref true
let auto_remove_if_find_cond = ref true
let auto_move = ref true
let auto_expand = ref true

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

let psize_NONINTERACTIVE = 80 (* Eg. an attacker can make at most 2^80 hash computations *)
let psize_PASSIVE = 30

let psize_DEFAULT = psize_PASSIVE

let psize_SMALL = 2
(* For active sessions, when the number of failed
    attempts is limited, e.g. max 4 attemtps then the
    card is blocked. *)

let tysize_LARGE = 160
let tysize_PASSWORD_min = 20
let tysize_PASSWORD_max = 40
let tysize_SMALL = 2

let trust_size_estimates = ref false

let tysize_MIN_Coll_Elim = ref tysize_PASSWORD_min
let tysize_MIN_Auto_Coll_Elim = ref 80
let tysize_MAX_Guess = ref 40
    
let max_exp = 1000000000
(* min_exp = -max_exp is needed for the code in proba.ml
   to evaluate orders of magnitude to be correct *)
let min_exp = -max_exp

(* Determines the probabilities that are considered small enough to 
   eliminate collisions. It consists of a list of probability descriptions
   of the form ([(psize1, n1); ...; (psizek,nk)], tsize) 
   which represent probabilities of the form
   constant * (parameter of size <= psize1)^n1 * ... * 
   (parameter of size <= psizek)^nk / (type of size >= tsize) 

   Also applies to collision statements; the probability
   of one collision must have size <= -tsize, and the number of 
   repetitions be less than constant * (parameter of size <= psize1)^n1 * ... * 
   (parameter of size <= psizek)^nk.

   The default value allows: anything/(a bit less than "large") and 
   small/password *) 
let allowed_collisions = ref [ ([max_int, max_int], tysize_LARGE-5); 
                               ([psize_SMALL, 1], tysize_PASSWORD_min) ]


let check_exp v ext =
  if v < 0 then
    raise (Parsing_helper.Error ("Bounds should be greater or equal to 0", ext));
  if v > max_exp then
    raise
      (Parsing_helper.Error
         ("Bounds should be at most " ^ string_of_int max_exp, ext))

let parse_type_size_pcoll (s, ext) =
  match s with
  | "large" -> Some (tysize_LARGE, max_exp), Some (tysize_LARGE, max_exp)
  | "password" -> Some (tysize_PASSWORD_min, tysize_PASSWORD_max), Some (tysize_PASSWORD_min, tysize_PASSWORD_max)
  | "small" -> Some (0, tysize_SMALL), None
  | s -> (* option size<n>, size<min>_<max>, or pcoll<n> *)
      try
	if (String.sub s 0 4) = "size" then
	  let s1 = String.sub s 4 (String.length s - 4) in
	  try
	    let pos_underscore = String.index s1 '_' in
	    let smin = String.sub s1 0 pos_underscore in
	    let smax = String.sub s1 (pos_underscore+1) (String.length s1-pos_underscore-1) in
	    let min = int_of_string smin in
	    let max = int_of_string smax in
	    if min > max then
	      raise (Parsing_helper.Error ("In option size<min>_<max>, <min> should be at most <max>", ext));
	    check_exp min ext;
	    check_exp max ext;
	    Some (min, max), None
	  with Not_found ->
	    let v = int_of_string s1 in
	    check_exp v ext;
	    Some (v, v), None
	else if (String.sub s 0 5) = "pcoll" then
	  let min = int_of_string (String.sub s 5 (String.length s - 5)) in
	  check_exp min ext;
	  None, Some (min, max_exp)
	else
	  raise Not_found
      with
      | (Parsing_helper.Error _) as x -> raise x
      | _ -> raise (Parsing_helper.Error ("Unknown type option " ^ s, ext))

let parse_pest (s, ext) =
  match s with
  | "large" -> tysize_LARGE
  | "password" -> tysize_PASSWORD_min
  | _ -> (* option pest<n> *)
      try
	if (String.sub s 0 4) <> "pest" then raise Not_found;
	let v = int_of_string (String.sub s 4 (String.length s - 4)) in
	check_exp v ext;
	v
      with
      | (Parsing_helper.Error _) as x -> raise x
      | _ -> raise (Parsing_helper.Error("Unknown probability estimate option "^s^" (allowed options are large, password, and pest<n>)", ext))
	  
let parse_psize (s, ext) =
  match s with
  | "noninteractive" -> psize_NONINTERACTIVE
  | "passive" -> psize_PASSIVE
  | "default" -> psize_DEFAULT
  | "small" -> psize_SMALL
  | _ -> (* option "size<n>" where <n> is an integer *)
      try
	if (String.sub s 0 4) <> "size" then raise Not_found;
	let v = int_of_string (String.sub s 4 (String.length s - 4)) in
	check_exp v ext;
	v	  
      with
      | (Parsing_helper.Error _) as x -> raise x
      | _ -> raise (Parsing_helper.Error("Unknown size option " ^ s^" (allowed options are noninteractive, passive, default, small, and size<n>)", ext))
	  
	  
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
  | "uniqueBranch", _ -> parse_bool v unique_branch
  | "uniqueBranchReorganize", _ -> parse_bool v unique_branch_reorg
  | "inferUnique", _ -> parse_bool v infer_unique
  | "guessRemoveUnique", _ -> parse_bool v guess_remove_unique
  | "autoMergeBranches", _ -> parse_bool v merge_branches
  | "autoMergeArrays", _ -> parse_bool v merge_arrays
  | "autoSARename", _ -> parse_bool v auto_sa_rename
  | "autoRemoveAssignFindCond", _ -> parse_bool v auto_remove_assign_find_cond
  | "autoRemoveIfFindCond", _ -> parse_bool v auto_remove_if_find_cond
  | "autoMove", _ -> parse_bool v auto_move
  | "autoExpand", _ -> parse_bool v auto_expand
  | "autoAdvice", _ -> parse_bool v auto_advice
  | "interactiveMode", _ -> parse_bool v interactive_mode
  | "noAdviceCrypto", _ -> parse_bool v no_advice_crypto
  | "noAdviceGlobalDepAnal", _ -> parse_bool v no_advice_globaldepanal
  | "backtrackOnCrypto", _ -> parse_bool v backtrack_on_crypto
  | "simplifyAfterSARename", _ -> parse_bool v simplify_after_sarename
  | "detectIncompatibleDefined", _ -> parse_bool v detect_incompatible_defined_cond
  | "ignoreSmallTimes", I n -> ignore_small_times := n
  | "maxElsefind", I n -> max_efl := n
  | "maxIterSimplif", I n -> max_iter_simplif := n
  | "maxIterRemoveUselessAssign", I n -> max_iter_removeuselessassign := n
  | "maxAdvicePossibilitiesBeginning", I n -> max_advice_possibilities_beginning := n
  | "maxAdvicePossibilitiesEnd", I n -> max_advice_possibilities_end := n
  | "useKnownEqualitiesInCryptoTransform", _ -> parse_bool v use_known_equalities_crypto
  | "priorityEventUnchangedRand", I n -> priority_event_unchanged_rand := n
  | "useKnownEqualitiesWithFunctionsInMatching", _ -> parse_bool v normalize_in_match_funapp
  | "minAutoCollElim", S s_ext -> 
      let r = parse_pest s_ext in
      if r <= 0 then raise Not_found;
      tysize_MIN_Auto_Coll_Elim := r
  | "maxGuess", S s_ext ->
      let r = parse_psize s_ext in
      tysize_MAX_Guess := r
  | "trustSizeEstimates", _ -> parse_bool v trust_size_estimates
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
let fopt_AUTO_SWAP_IF = 16
    
let tex_output = ref ""

(* Types and constants should be added to the initial environment,
as well as f_not *)
(* Types *)

let t_bitstring =
  {
    tname = "bitstring";
    tcat = BitString;
    toptions = 0;
    tsize = Some (max_exp, max_exp);
    tpcoll = None;
    timplsize = None;
    tpredicate = Some "always_true";
    timplname = Some "string";
    tserial = Some ("id", "id");
    trandom = None;
    tequal = None;
  }

let t_bitstringbot =
  {
    tname = "bitstringbot";
    tcat = BitString;
    toptions = 0;
    tsize = Some (max_exp, max_exp);
    tpcoll = None;
    timplsize = None;
    tpredicate = Some "always_true";
    timplname = Some "string option";
    tserial = Some ("stringbot_to", "stringbot_from");
    trandom = None;
    tequal = None;
  }

let t_bool =
  {
    tname = "bool";
    tcat = BitString;
    toptions = tyopt_FIXED + tyopt_BOUNDED;
    tsize = Some (1, 1);
    tpcoll = Some (1, 1);
    timplsize = Some 1;
    tpredicate = Some "always_true";
    timplname = Some "bool";
    tserial = Some ("bool_to", "bool_from");
    trandom = Some "rand_bool";
    tequal = Some "(=)";
  }

(* For precise computation of the runtime only*)
let t_unit =
  {
    tname = "unit";
    tcat = BitString;
    toptions = tyopt_BOUNDED;
    tsize = Some (0, 0);
    tpcoll = Some (0, 0);
    timplsize = None;
    tpredicate = None;
    timplname = None;
    tserial = None;
    trandom = None;
    tequal = None;
  }

(* For events in terms; they have a type compatible with any type*)
let t_any =
  {
    tname = "any";
    tcat = BitString;
    toptions = 0;
    tsize = None;
    tpcoll = None;
    timplsize = None;
    tpredicate = None;
    timplname = None;
    tserial = None;
    trandom = None;
    tequal = None;
  }

let p_empty_idx = { pname = "0"; psize = 0 }

let t_empty_idx =
  {
    tname = "empty-idx";
    tcat = Interv p_empty_idx;
    toptions = tyopt_BOUNDED;
    tsize = Some (0, 0);
    tpcoll = Some (0, 0);
    timplsize = None;
    tpredicate = None;
    timplname = None;
    tserial = None;
    trandom = None;
    tequal = None;
  }

let create_fun s ty ?(options=0) ?(eqth=NoEq) ?(impl=No_impl) ?(impl_inv=None) cat =
  { f_name = s;
    f_type = ty;
    f_cat = cat;
    f_options = options;
    f_statements = [];
    f_collisions = [];
    f_eq_theories = eqth;
    f_impl = impl;
    f_impl_inv = impl_inv;
    f_impl_ent = false;
    f_impl_needs_state = false }
    
(* Constants *)

let c_true = create_fun "true" ([],t_bool) ~impl:(Const "true") Std

let c_false = create_fun "false" ([],t_bool) ~impl:(Const "false") Std

(* Functions *)

let f_and = create_fun "&&" ([t_bool; t_bool], t_bool) ~impl:(Func "(&&)") And

let f_or = create_fun "||" ([t_bool; t_bool], t_bool) ~impl:(Func "(||)") Or

let _ =
  f_and.f_eq_theories <- AssocCommutN(f_and, c_true);
  f_or.f_eq_theories <- AssocCommutN(f_or, c_false)

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
    if t2 == t_any then t
    else if t == t_any then t2
    else if t != t2 then
      Parsing_helper.internal_error "Comparisons for compatible types only"
    else t
  in
  try CatTypeHashtbl.find comp_funs (cat, t)
  with Not_found ->
    let r = create_fun
	(match cat with
	  Equal -> "="
	| Diff -> "<>"
	| LetEqual -> ">>="
	| ForAllDiff -> "<A>"
	| _ -> Parsing_helper.internal_error "no comparison for this category")
	([t; t], t_bool) 
	~eqth:(if cat == Equal || cat == Diff then Commut else NoEq)
        ~impl:(match cat with
          Equal -> FuncEqual
        | Diff -> FuncDiff
        | _ -> No_impl)
	cat
    in
    CatTypeHashtbl.add comp_funs (cat, t) r;
    r

let f_not = create_fun "not" ([t_bool], t_bool) ~impl:(Func "not") Std

(* Create tuple function of given type *)

module HashedTypeList = struct
  type t = Types.typet list

  let equal x1 x2 =
    List.length x1 == List.length x2 && List.for_all2 ( == ) x1 x2

  (* The hash function must use only parts that are not modified,
     otherwise, we may have the same element with several different hashes *)
  let hash x = Hashtbl.hash (List.map (fun t -> t.tname) x)
end

module TypeListHashtbl = Hashtbl.Make (HashedTypeList)

let tuple_fun_table = TypeListHashtbl.create 7

let get_tuple_fun tl =
  try TypeListHashtbl.find tuple_fun_table tl
  with Not_found ->
    let f = create_fun "" (tl, t_bitstring) ~impl:(Func "tuple")
	~impl_inv:(Some "detuple") ~options:fopt_COMPOS	Tuple 
    in
    TypeListHashtbl.add tuple_fun_table tl f;
    f

let empty_tuple = get_tuple_fun []

(* if functions *)

module HashedType =
  struct
    type t = Types.typet
    let equal = (==)
    (* The hash function must use only parts that are not modified,
       otherwise, we may have the same element with several different hashes *)
    let hash x = Hashtbl.hash x.tname
  end

module TypeHashtbl = Hashtbl.Make(HashedType)

let if_fun_table = TypeHashtbl.create 7

let get_if_fun t =
  try 
    TypeHashtbl.find if_fun_table t
  with Not_found ->
    let f = create_fun "if_fun" ([t_bool; t; t], t) ~impl:(Func "if_fun") If in
    TypeHashtbl.add if_fun_table t f;
    f
      
(*For precise computation of the runtime only*)

let t_interv =
  {
    tname = "[1,*]";
    tcat = Interv { pname = "N*"; psize = 0 };
    toptions = tyopt_BOUNDED;
    tsize = None;
    tpcoll = None;
    timplsize = None;
    tpredicate = None;
    timplname = None;
    tserial = None;
    trandom = None;
    tequal = None;
  }

let f_plus = create_fun "+" ([t_interv; t_interv],t_interv) ~eqth:Commut Std

let f_mul = create_fun "*" ([t_interv; t_interv],t_interv;) ~eqth:Commut Std

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
  if n < 1 || n > List.length (fst f.f_type) then
    Parsing_helper.internal_error "Arity error in get_inverse";
  try FunIntHashtbl.find inverse_table (f, n)
  with Not_found ->
    let finv = create_fun (f.f_name ^ "^-1_" ^ (string_of_int n))
		 ([snd f.f_type], (List.nth (fst f.f_type) (n-1)))
		 ~options:fopt_DECOMPOS Std
    in
    FunIntHashtbl.add inverse_table (f, n) finv;
    finv

(***************************************************************************)

let get_query_status (_, poptref) =
  !poptref

let add_pub_vars_q public_vars q =
  let add_pub_vars pub_vars =
    List.iter
      (fun b ->
        if not (List.memq b !public_vars) then public_vars := b :: !public_vars)
      pub_vars
  in
  match q with
  | QSecret (b',pub_vars,onesession) ->
      add_pub_vars (b'::pub_vars)
  | QEventQ (_,_,pub_vars)
  | QEquivalence(_,pub_vars,_)
  | QEquivalenceFinal(_,pub_vars) ->
      add_pub_vars pub_vars
  | AbsentQuery -> ()
	
let get_public_vars0 queries =
  let public_vars = ref [] in
  List.iter (add_pub_vars_q public_vars) queries;  
  !public_vars

let get_public_vars queries =
  let public_vars = ref [] in
  List.iter (function 
    | q when get_query_status q != ToProve -> () (* I ignore already proved and inactive queries *)
    | (q,_),_ -> add_pub_vars_q public_vars q) queries;
  !public_vars

let occurs_in_queries b q = List.memq b (get_public_vars q)

let event_occurs_in_term f t =
  match t.t_desc with FunApp (f', _) -> f == f' | _ -> false

let rec event_occurs_in_qterm f = function
  | QEvent (_, t) -> event_occurs_in_term f t
  | QTerm _ -> false
  | QAnd (t1, t2) | QOr (t1, t2) ->
      event_occurs_in_qterm f t1 || event_occurs_in_qterm f t2

let event_occurs_in_queries f q =
  List.exists
    (function
      | q when get_query_status q != ToProve ->
          false (* I ignore already proved and inactive queries *)
      | (QSecret _, _), _ -> false
      | ((AbsentQuery | QEquivalence _ | QEquivalenceFinal _), _), _ ->
          (* When I want to prove indistinguishability, keep all events *)
          true
      | (QEventQ (l, r, _), _), _ ->
          List.exists (fun (_, t) -> event_occurs_in_term f t) l
          || event_occurs_in_qterm f r)
    q

(***************************************************************************)

let equivs = ref ([] : equiv_gen list)

(****************************************************************************)

(* Set when a game is modified *)

let changed = ref false

(* Instructions are added in advise when an instruction I cannot be fully
   performed. The added instructions correspond to suggestions of instructions
   to apply before I so that instruction I can be better performed. *)

let advise = ref ([] : instruct list)
