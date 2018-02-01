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

let env = ref (StringMap.empty : env_entry StringMap.t)

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

let get_process env s ext =
  try
  match StringMap.find s env with
    EProcess p -> p
  | _ -> input_error (s ^ " should be a process.") ext
  with Not_found -> input_error (s ^ " not defined.") ext

let get_function env s ext =
  try
  match StringMap.find s env with
    EFunc f -> f
  | _ -> input_error (s ^ " should be a function.") ext
  with Not_found -> input_error (s ^ " not defined.") ext
