(* Terms *)

type ident = Types.ident

type term = PIdent of ident
          | PArray of ident * term_e list
          | PFunApp of ident * term_e list
	  | PInjEvent of ident * term_e list (* For queries only *)
	  | PTuple of term_e list
	  | PTestE of term_e * term_e * term_e
	  | PFindE of (Types.repl_index list ref(*to store replication indices*) * (ident * ident) list * (ident * term_e list) list * term_e * term_e) list * term_e * ident list
	  | PLetE of pattern_e * term_e * term_e * term_e option
	  | PResE of ident * ident * term_e
	  | PEventAbortE of ident
	  | PEventE of term_e * term_e
	  | PGetE of ident * (pattern_e list) * term_e option * term_e * term_e
	  | PInsertE of ident * term_e list * term_e
	  | PEqual of term_e * term_e
	  | PDiff of term_e * term_e
	  | POr of term_e * term_e
	  | PAnd of term_e * term_e

and term_e = term * Parsing_helper.extent

and pattern = PPatVar of ident * ident option(*optional type*)
  | PPatTuple of pattern_e list
  | PPatFunApp of ident * pattern_e list
  | PPatEqual of term_e

and pattern_e = pattern * Parsing_helper.extent

(* Processes *)

type progopt = PWrite of ident (*variable*) * ident (* file *)
             | PRead of ident * ident

and process =  PNil
             | PYield
	     | PEventAbort of ident
	     | PPar of process_e * process_e
	     | PRepl of Types.repl_index option ref(*to store replication index*) * ident option(*index*) * ident(*bound*) * process_e
 	     | PRestr of ident * ident(*type*) * process_e 
	     | PLetDef of ident
	     | PTest of term_e * process_e * process_e
	     | PFind of (Types.repl_index list ref(*to store replication indices*) * (ident * ident) list * (ident * term_e list) list * term_e * process_e) list * process_e * ident list
	     | PEvent of term_e * process_e
             | PInput of ident * pattern_e * process_e
             | POutput of bool * ident * term_e * process_e
	     | PLet of pattern_e * term_e * process_e * process_e
             | PGet of ident * (pattern_e list) * term_e option * process_e * process_e
             | PInsert of ident * term_e list * process_e
             | PBeginModule of ((ident * progopt list) * process_e)
(*
	     | PPhase of int * process_e
*)

and process_e = process * Parsing_helper.extent

(* Logical statements (most often equations) *)

type statement = (ident * ident(*type*)) list * term_e

(* Equivalence statements *)

type action =
    PAFunApp of ident
  | PAPatFunApp of ident
  | PAReplIndex
  | PAArrayAccess of int
  | PACompare of ident
  | PAAppTuple of ident list
  | PAPatTuple of ident list
  | PAAnd
  | PAOr
  | PANew of ident
  | PANewChannel
  | PAIf
  | PAFind of int
  | PAOut of ident list * ident
  | PAIn of int

type probabilityf = 
    PAdd of probabilityf_e * probabilityf_e
  | PSub of probabilityf_e * probabilityf_e
  | PProd of probabilityf_e * probabilityf_e
  | PDiv of probabilityf_e * probabilityf_e
  | PMax of probabilityf_e list
  | PPIdent of ident
  | PPFun of ident * probabilityf_e list
  | PPZero
  | PCard of ident
  | PCount of ident
  | PCst of int
  | PFloatCst of float
  | PTime
  | PActTime of action * probabilityf_e list 
  | PMaxlength of term_e
  | PLength of ident * probabilityf_e list 
  | PLengthTuple of ident list * probabilityf_e list 
  | PEpsFind
  | PEpsRand of ident
  | PPColl1Rand of ident
  | PPColl2Rand of ident

and probabilityf_e = probabilityf * Parsing_helper.extent

type ty =
    Tid of ident (* For normal types, designated by an ident *)
  | TBound of ident (* For interval types, designated by their bound *)

type fungroup =
    PReplRestr of (Types.repl_index option ref(*to store replication index*) * ident option(*index*) * ident(*repetitions*)) (*replication*) * 
	(ident * ident(*type*) * ident list(*options*)) list(*restrictions*) * fungroup list
  | PFun of ident ref * (ident * ty) list(*inputs*) * term_e * (int(*priority*) * ident list(*options*))

type eqmember = (fungroup * ident option * Parsing_helper.extent) list * Parsing_helper.extent


type eqstatement = Types.eqname * eqmember * eqmember * probabilityf_e * (int * ident list(*options*))

(* Collisions *)

type collision = (ident * ident) list(*restrictions*) * (ident * ident) list(*forall*) * term_e * probabilityf_e * term_e



(* Values of parameters *)

type pval = 
    S of ident
  | I of int

(* Queries *)

type query = 
    PQSecret of ident * ident list option
  | PQSecret1 of ident * ident list option
  | PQEvent of (ident * ty(*type*)) list * term_e * term_e

(* Implementation *)

type typeid = TypeSize of int | TypeName of ident

type typeopt = (ident * (ident list)) list
type funopt = (ident * ident) list

type impl = Type of ident * typeid * typeopt 
          | Function of ident * ident * funopt 
          | Constant of ident * ident
          | ImplTable of ident * ident

(* Declarations *)

type decl = FunDecl of ident * ident list(*types*) * ident (*type*) * ident list(* options *)
          | EventDecl of ident * ident list(*types*) 
          | ParamDecl of ident * ident list(*options*)
	  | ProbabilityDecl of ident
	  | ConstDecl of ident * ident(*type*)
	  | ChannelDecl of ident
	  | TypeDecl of ident * ident list(*options*)
	  | Statement of statement
	  | BuiltinEquation of ident * ident list
	  | EqStatement of eqstatement
	  | Collision of collision
	  | Setting of ident * pval
	  | PDef of ident * process_e
	  | Query of query list
	  | Define of ident * ident list * pall
	  | Expand of ident * ident list
	  | Proofinfo of ident list list
          | Implementation of impl list
          | TableDecl of ident * ident list
          | LetFun of ident * (ident * ident) list * term_e

and pall = (decl * Parsing_helper.extent) list


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
  | EProcess of process_e
  | ETable of Types.table

(* User info for cryptographic transformation *)

type var_term_mapping =
    PVarMapping of ident(*"variables"*) * (ident(*variable in game*) * ident(*variable in equivalence*)) list * bool (* bool is true when the list ends with "."
				    no other variable should be added by the transformation in this case *)
  | PTermMapping of ident(*"terms"*) * (int(*occurrence in game*) * ident(*oracle in equivalence*)) list * bool

type crypto_transf_user_info =
    PRepeat
  | PVarList of ident list * bool (* bool is true when the list ends with "."
				    no other variable should be added by the transformation in this case *)
  | PDetailed of var_term_mapping list 
