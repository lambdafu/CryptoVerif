open Types
open Ptree
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
    EFunc of Types.funsymb
  | EEvent of Types.funsymb
  | EParam of Types.param
  | EProba of Types.proba
  | EType of Types.typet
  | EVar of Types.binder
  | EReplIndex of Types.repl_index
  | EChannel of Types.channel
  | EProcess of env_type * (Ptree.ident * Ptree.ty(*type*)) list * Ptree.process_e
  | ETable of Types.table

and env_type = env_entry StringMap.t

let env = ref (StringMap.empty : env_type)

(* Read environment *)

let get_param env s ext =
  try
  match StringMap.find s env with
    EParam p -> p
  | _ -> input_error (s ^ " should be a parameter.") ext
  with Not_found -> input_error (s ^ " not defined.") ext

let get_type env s ext =
  try
  match StringMap.find s env with
    EType t -> t
  | _ -> input_error (s ^ " should be a type.") ext
  with Not_found -> input_error (s ^ " not defined.") ext

let get_table env s ext =
  try
  match StringMap.find s env with
    ETable t -> t
  | _ -> input_error (s ^ " should be a table.") ext
  with Not_found -> input_error (s ^ " not defined.") ext

let get_type_or_param env s ext =
  try
  match StringMap.find s env with
    EType t -> t
  | EParam p -> Terms.type_for_param p
  | _ -> input_error (s ^ " should be a type or a parameter.") ext
  with Not_found -> input_error (s ^ " not defined.") ext

let get_ty env = function
    Tid (s2, ext2) -> (get_type env s2 ext2, ext2)
  | TBound (s2, ext2) -> 
      let p = get_param env s2 ext2 in
      (Terms.type_for_param p, ext2)
      
let get_process env s ext =
  try
  match StringMap.find s env with
    EProcess(env', args, p) -> (env', args, p)
  | _ -> input_error (s ^ " should be a process.") ext
  with Not_found -> input_error (s ^ " not defined.") ext

let get_function env s ext =
  try
  match StringMap.find s env with
    EFunc f -> f
  | _ -> input_error (s ^ " should be a function.") ext
  with Not_found -> input_error (s ^ " not defined.") ext


(* Global binder environment *)

type err_mess = string
      
let error_ambiguous = "several times in incompatible ways"
let error_no_type = "without type"
let error_find_cond = "in a condition of find or get"
let error_in_input_process = "as an argument of a parametric input process"
let error_find_index_in_equiv = "as an index of find in an equivalence"
    
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
    failwith "duplicate variable"
  else
    let b = Terms.create_binder_internal b0.sname b0.vname t cur_array in
    StringMap.add s (Uniq b) env

let add_in_env1error env mess s =
  if StringMap.mem s env then
    StringMap.add s (Error error_ambiguous) env
  else
    StringMap.add s (Error mess) env

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

(* [union_both] computes the union of environments that are obtained
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

(* Get a global binder *)

exception Undefined of ident
	
let get_global_binder ref (i,ext) = 
  try
    match StringMap.find i (!binder_env) with
      Uniq b -> b
    | Error mess ->
	input_error (i ^ " is referenced " ^ ref ^ " and is defined "^ mess) ext
  with Not_found ->
    raise (Undefined(i,ext))

let get_global_binder_if_possible i =
  try
    match StringMap.find i (!binder_env) with
      Uniq b -> Some b
    | _ -> None
  with Not_found ->
    internal_error ("Binder " ^ i ^ " should be in binder_env")
