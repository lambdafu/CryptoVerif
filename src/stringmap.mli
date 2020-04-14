open Types

module StringMap : Map.S with type key = string

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

and env_type = env_entry StringMap.t

val env : env_type ref

val get_param : env_type -> string -> Parsing_helper.extent -> param
val get_type : env_type -> string -> Parsing_helper.extent -> typet
val get_type_or_param : env_type -> string -> Parsing_helper.extent -> typet
val get_ty : env_type -> Ptree.ty(*type*) -> typet * Parsing_helper.extent
val get_process : env_type -> string -> Parsing_helper.extent ->
  env_type * (Ptree.ident * Ptree.ty(*type*)) list * Ptree.process_e
val get_table : env_type -> string -> Parsing_helper.extent -> table
val get_function_no_letfun : env_type -> string -> Parsing_helper.extent -> funsymb
val get_function_or_letfun : env_type -> string -> Parsing_helper.extent -> funsymb

(* Global binder environment *)

type err_mess

val error_ambiguous : err_mess
val error_no_type : err_mess
val error_find_cond : err_mess
val error_in_input_process : err_mess
val error_find_index_in_equiv : err_mess

type binder_env_type

val empty_binder_env : binder_env_type
      
val add_in_env1 : binder_env_type -> string -> typet -> repl_index list -> binder_env_type
val add_in_env1reusename : binder_env_type -> string -> binder -> typet -> repl_index list -> binder_env_type
val add_in_env1error : binder_env_type -> err_mess -> string -> binder_env_type
val add_in_env1existing : binder_env_type -> string -> binder -> binder_env_type
val union_both : binder_env_type -> binder_env_type -> binder_env_type
val union_exclude : binder_env_type -> binder_env_type -> binder_env_type

val set_binder_env : binder_env_type -> unit
exception Undefined of ident
val get_global_binder : string -> ident -> binder
val get_global_binder_if_possible : string -> binder option

val cst_for_type : typet -> term

