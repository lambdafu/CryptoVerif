open Types
open Parsing_helper

(* Environment.
   May contain function symbols, variables, ...
   Is a map from strings to the description of the ident *)

module String = struct
   type t = string
   let compare = compare
end

module StringMap = Map.Make(String)

(* Environment.
   May contain function symbols, variables, ...
   Is a map from strings to the description of the ident *)

type env_entry =
    EFunc of funsymb
  | EEvent of funsymb
  | EParam of param
  | EProba of proba
  | EType of typet
  | EVar of binder
  | EReplIndex of repl_index
  | EChannel of channel
  | ELetFun of funsymb * env_type * (Ptree.ident * Ptree.ty(*type*)) list * Ptree.term_e
  | EProcess of env_type * (Ptree.ident * Ptree.ty(*type*)) list * Ptree.process_e
  | ETable of table
  | EVarProba of var_proba
  | ELetProba of proba * env_type * (Ptree.ident * Ptree.dim_e(*dimension*)) list * (env_type -> probaf)

and env_type = env_entry StringMap.t

let env = ref (StringMap.empty : env_type)

(* Read environment *)

let decl_name = function
  | EFunc _ -> "function"
  | EEvent _ -> "event"
  | EParam _ -> "parameter"
  | EProba _ -> "probability"
  | EType _ -> "type"
  | EVar _ -> "variable"
  | EReplIndex _ -> "replication index"
  | EChannel _ -> "channel"
  | ELetFun _ -> "function declared by letfun"
  | EProcess _ -> "process"
  | ETable _ -> "table"
  | EVarProba _ -> "probability variable"
  | ELetProba _ -> "probability function declared by letproba"
    
let get_param env s ext =
  try
  match StringMap.find s env with
    EParam p -> p
  | d -> raise_error (s ^ " was previously declared as a " ^ (decl_name d) ^". Expected a parameter.") ext
  with Not_found -> raise_error (s ^ " not defined. Expected a parameter.") ext

let get_event env s ext =
  try 
    match StringMap.find s env with
    | EEvent(f) -> f
    | d -> raise_error (s ^ " was previously declared as a " ^ (decl_name d) ^". Expected an event.") ext
  with Not_found -> raise_error (s ^ " not defined. Expected an event.") ext
      
let get_type env s ext =
  try
  match StringMap.find s env with
    EType t -> t
  | d -> raise_error (s ^ " was previously declared as a " ^ (decl_name d) ^". Expected a type.") ext
  with Not_found -> raise_error (s ^ " not defined. Expected a type.") ext

let get_table env s ext =
  try
  match StringMap.find s env with
    ETable t -> t
  | d -> raise_error (s ^ " was previously declared as a " ^ (decl_name d) ^". Expected a table.") ext
  with Not_found -> raise_error (s ^ " not defined. Expected a table.") ext

let get_type_or_param env s ext =
  try
  match StringMap.find s env with
    EType t -> t
  | EParam p -> Terms.type_for_param p
  | d -> raise_error (s ^ " was previously declared as a " ^ (decl_name d) ^". Expected a type or a parameter.") ext
  with Not_found -> raise_error (s ^ " not defined. Expected a type or a parameter.") ext

let get_ty env = function
    Ptree.Tid (s2, ext2) -> (get_type env s2 ext2, ext2)
  | Ptree.TBound (s2, ext2) -> 
      let p = get_param env s2 ext2 in
      (Terms.type_for_param p, ext2)
      
let get_process env s ext =
  try
  match StringMap.find s env with
    EProcess(env', args, p) -> (env', args, p)
  | d -> raise_error (s ^ " was previously declared as a " ^ (decl_name d) ^". Expected a process.") ext
  with Not_found -> raise_error (s ^ " not defined. Expected a process.") ext

let get_function_no_letfun env s ext =
  try
  match StringMap.find s env with
    EFunc f -> f
  | d -> raise_error (s ^ " was previously declared as a " ^ (decl_name d) ^". Expected a function (letfun forbidden).") ext
  with Not_found -> raise_error (s ^ " not defined. Expected a function (letfun forbidden).") ext

let get_function_or_letfun env s ext =
  try
  match StringMap.find s env with
    EFunc f -> f
  | ELetFun(f, _, _, _) -> f
  | d -> raise_error (s ^ " was previously declared as a " ^ (decl_name d) ^". Expected a function (letfun allowed).") ext
  with Not_found -> raise_error (s ^ " not defined. Expected a function (letfun allowed).") ext

(* Functions for dimensions *)	

let power_opt n =
  if n = 1 then "" else "^"^(string_of_int n)
    
let dim_to_string = function
  | (0,0) -> "number"
  | (n,0) -> "time"^(power_opt n)
  | (0,l) -> "length"^(power_opt l)
  | (n,l) -> "time"^(power_opt n)^" * length"^(power_opt l)

let dim_list_to_string l =
  let dim_to_string d =
    match d with
    | None -> "any"
    | Some d0 -> dim_to_string d0
  in
  let rec aux = function
    | [] -> ""
    | [a] -> dim_to_string a
    | a::l ->
	(dim_to_string a)^", "^(aux l)
  in
  (string_of_int (List.length l)) ^" argument(s)"^
    (if l = [] then "" else " of dimension(s) "^(aux l))
						 
let proba_dim_list_to_string l =
  let dim_to_string (_,d) =
    match d with
    | None -> "any"
    | Some (p,t,l) ->
	dim_to_string (t,l)
  in
  let rec aux = function
    | [] -> ""
    | [a] -> dim_to_string a
    | a::l ->
	(dim_to_string a)^", "^(aux l)
  in
  (string_of_int (List.length l)) ^" argument(s)"^
    (if l = [] then "" else " of dimension(s) "^(aux l))

let time_dim = Some (Some 0, 1, 0)
let length_dim = Some (Some 0, 0, 1)
let proba_dim = Some(Some 1, 0, 0)
let num_dim = Some(Some 0, 0, 0)

let computed_dim_to_dim = function
  | None -> None
  | Some(_,t,l) -> Some (t,l)
    
let rec merge_dim dl tdl =
  match dl, tdl with
  | [], [] -> []
  | _, [] | [], _ -> raise Not_found
  | d::dr, (_, d')::tdr ->
      (match d, d' with
      | None, _ -> computed_dim_to_dim d'
      | _, None -> d
      | Some(t,l), Some (_,t',l') ->
	  if t == t' && l == l' then d else raise Not_found) ::
       (merge_dim dr tdr)

let apply_proba (s, ext) env args_with_dim =
  (* Remove "TypeMaxlength" arguments for simplicity; they are constants.
     TO DO This removing is perhaps questionable *)
  let args_notypemaxl = List.filter (function 
    | (TypeMaxlength _,_) -> false
    | _ -> true) args_with_dim
  in
  let adapt_args p =
    match p.pargs with
    | None ->
	p.pargs <- Some (List.map (fun (_,d) -> computed_dim_to_dim d) args_notypemaxl);
	args_notypemaxl
    | Some dimlist ->
	try 
	  p.pargs <- Some (merge_dim dimlist args_with_dim);
	  args_with_dim
	with Not_found ->
	  try 
	    p.pargs <- Some (merge_dim dimlist args_notypemaxl);
	    args_notypemaxl
	  with Not_found -> 
	    raise_error ("Probability function "^s^
			 " expects "^(dim_list_to_string dimlist)^
			 " but is here given "^(proba_dim_list_to_string args_with_dim)^
			 (if List.length args_with_dim > List.length args_notypemaxl then
			   " (or "^(proba_dim_list_to_string args_notypemaxl)^" after removing constant lengths)"
			 else "")) ext
  in
  let rec check_args env' vardecl args =
    match (vardecl, args) with
    | [], [] -> env'
    | [], _ | _, [] ->
	Parsing_helper.internal_error "Stringmap.check_args vardecl and args should have the same length"
    | ((s1,ext1),_)::rvardecl, (p,dim)::rargs ->
	let vproba = { vp_name = s1;
		       vp_dim = dim;
		       vp_val = p }
	in
	let env'' = StringMap.add s1 (EVarProba vproba) env' in
	check_args env'' rvardecl rargs
  in
  try 
    match StringMap.find s env with
    | EProba p ->
	let args' = adapt_args p in
	Proba(p, List.map fst args')
    | ELetProba(p, env', vardecl, p') ->
	let args' = adapt_args p in
	let env'' = check_args env' vardecl args' in
	p' env''
    | d -> raise_error (s ^ " was previously declared as a "^(decl_name d)^". Expected a probability.") ext
  with Not_found ->
    raise_error (s ^ " is not defined. Expected a probability.") ext
	  
(* Global binder environment *)

type err_mess = string
      
let error_ambiguous = "several times in incompatible ways"
let error_no_type = "without type"
let error_find_cond = "in a condition of find or get"
let error_in_input_process = "as an argument of a parametric input process"
    
type binder_env_content = 
    Uniq of binder
  | Error of err_mess

type binder_env_type = binder_env_content StringMap.t
	
let binder_env = ref (StringMap.empty : binder_env_type)
(* binder_env_content = [Uniq b] means that the binder can be used globally.
Its the only declaration is [b] and its type is known; 
binder_env_content = [Error s] means that we cannot use this binder globally.
The string [s] details the reason:
- [error_ambiguous] means that there are several incompatible declarations 
of this binder.
- [error_no_type] means that there is a unique declaration of this
binder, and it has no explicit type; 
- [error_find_cond] means that this binder is defined in
a find condition, so array references to this binder are forbidden. 
- [error_in_input_process] means that this binder is defined
as an argument of a parametric input process, so it disappears 
in the expansion of the parametric processes. *)

let empty_binder_env = StringMap.empty
    
(* Add a binder in the environment *)

let add_in_env1 env s t cur_array =
  if StringMap.mem s env then
    StringMap.add s (Error error_ambiguous) env
  else
    let b = Terms.create_binder s t cur_array in
    StringMap.add s (Uniq b) env

let add_in_env1reusename env s b0 t cur_array =
  if StringMap.mem s env then
    StringMap.add s (Error error_ambiguous) env
  else
    let b = Terms.create_binder_internal b0.sname b0.vname t cur_array in
    StringMap.add s (Uniq b) env

let add_in_env1error env mess s =
  if StringMap.mem s env then
    StringMap.add s (Error error_ambiguous) env
  else
    StringMap.add s (Error mess) env

let add_in_env1existing env s b =
  if StringMap.mem s env then
    failwith "duplicate variable"
  else
    StringMap.add s (Uniq b) env

(* Union *)

(* [union_both] computes the union of environments that are obtained
   in pieces of code that can both run *)

let union_both env1 env2 = 
  StringMap.merge (fun s opt1 opt2 ->
    match (opt1, opt2) with
    | None, x -> x
    | x, None -> x
    | Some _, Some _ -> Some (Error error_ambiguous)
      ) env1 env2

(* [union_exclude] computes the union of environments that are obtained
   in different branches of if/find/let/get. *)

let union_exclude env1 env2 =
    StringMap.merge (fun s opt1 opt2 ->
    match (opt1, opt2) with
    | None, x -> x
    | x, None -> x
    | ((Some (Uniq b1)) as x1), Some (Uniq b2) -> 
        if b1.btype == b2.btype &&
           Terms.equal_lists (==) b1.args_at_creation b2.args_at_creation
        then x1
        else Some (Error error_ambiguous)
    | ((Some (Error _)) as x1), _ -> x1
    | _, ((Some (Error _)) as x2) -> x2
      ) env1 env2

(* Set binder env *)

let set_binder_env env =
   binder_env := env

let set_and_get_old_binder_env env =
  let old_env = !binder_env in
  set_binder_env env;
  old_env
	
(* Get a global binder *)

exception Undefined of ident
	
let get_global_binder ref (i,ext) = 
  try
    match StringMap.find i (!binder_env) with
      Uniq b -> b
    | Error mess ->
	raise_error (i ^ " is referenced " ^ ref ^ " and is defined "^ mess) ext
  with Not_found ->
    raise (Undefined(i,ext))

let get_global_binder_if_possible i =
  try
    match StringMap.find i (!binder_env) with
      Uniq b -> Some b
    | _ -> None
  with Not_found ->
    internal_error ("Binder " ^ i ^ " should be in binder_env")

(* Constant for each type
   Add it to the environment env *)

module HashedType =
  struct
    type t = Types.typet
    let equal = (==)
    (* The hash function must use only parts that are not modified,
       otherwise, we may have the same element with several different hashes *)
    let hash t = Hashtbl.hash t.tname
  end

module TypeHashtbl = Hashtbl.Make(HashedType)

let cst_for_type_table = TypeHashtbl.create 7

let cst_for_type ty =
  let f = 
    try
      TypeHashtbl.find cst_for_type_table ty
    with Not_found ->
      let r = { f_name = Terms.fresh_id ("cst_" ^ ty.tname);
		f_type = [],ty;
		f_cat = Std;
		f_options = 0;
		f_statements = [];
		f_collisions = [];
		f_eq_theories = NoEq;
                f_impl = No_impl;
                f_impl_inv = None }
      in
      TypeHashtbl.add cst_for_type_table ty r;
      env := StringMap.add r.f_name (EFunc r) (!env);
      r
  in
  Terms.build_term_type ty (FunApp(f,[]))

