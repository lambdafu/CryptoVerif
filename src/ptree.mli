(* Terms *)

type ident = Types.ident

type ty =
    Tid of ident (* For normal types, designated by an ident *)
  | TBound of ident (* For interval types, designated by their bound *)

type term = PIdent of ident
          | PArray of ident * term_e list
          | PFunApp of ident * term_e list
	  | PQEvent of bool(*injective?*) * term_e (* For queries only *)
	  | PTuple of term_e list
	  | PTestE of term_e * term_e * term_e
	  | PFindE of (Types.repl_index list ref(*to store replication indices*) * (ident * ident * ident) list * (ident * term_e list) list * term_e * term_e) list * term_e * ident list
	  | PLetE of pattern_e * term_e * term_e * term_e option
	  | PResE of ident * ident * term_e
	  | PEventAbortE of ident
	  | PEventE of term_e * term_e
	  | PGetE of ident * (pattern_e list) * term_e option * term_e * term_e * ident list(*options [unique]*)
	  | PInsertE of ident * term_e list * term_e
	  | PEqual of term_e * term_e
	  | PDiff of term_e * term_e
	  | POr of term_e * term_e
	  | PAnd of term_e * term_e
	  | PIndepOf of ident * ident
	  | PBefore of term_e * term_e
		
and term_e = term * Parsing_helper.extent

and pattern = PPatVar of ident * ty option(*optional type*)
  | PPatTuple of pattern_e list
  | PPatFunApp of ident * pattern_e list
  | PPatEqual of term_e

and pattern_e = pattern * Parsing_helper.extent

(* Processes *)

type channel = ident * (ident list option)
      
type progopt = PWrite of ident (*variable*) * ident (* file *)
             | PRead of ident * ident

and process =  PNil
             | PYield
	     | PEventAbort of ident
	     | PPar of process_e * process_e
	     | PRepl of Types.repl_index option ref(*to store replication index*) * ident option(*index*) * ident(*bound*) * process_e
 	     | PRestr of ident * ident(*type*) * process_e 
	     | PLetDef of ident * term_e list
	     | PTest of term_e * process_e * process_e
	     | PFind of (Types.repl_index list ref(*to store replication indices*) * (ident * ident * ident) list * (ident * term_e list) list * term_e * process_e) list * process_e * ident list
	     | PEvent of term_e * process_e
             | PInput of channel * pattern_e * process_e
             | POutput of bool * channel * term_e * process_e
	     | PLet of pattern_e * term_e * process_e * process_e
             | PGet of ident * (pattern_e list) * term_e option * process_e * process_e * ident list(*options [unique]*)
             | PInsert of ident * term_e list * process_e
             | PBeginModule of ((ident * progopt list) * process_e)
(*
	     | PPhase of int * process_e
*)

and process_e = process * Parsing_helper.extent

(* Logical statements (most often equations) *)

type statement = (ident * ident(*type*)) list * term_e * term_e

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
  | PPower of probabilityf_e * int
  | PMax of probabilityf_e list
  | PMin of probabilityf_e list
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
  | POptimIf of probabilitycond_e * probabilityf_e * probabilityf_e

and probabilityf_e = probabilityf * Parsing_helper.extent

and probabilitycond =
  | POCProbaFun of ident * probabilityf_e list
  | POCBoolFun of ident * probabilitycond_e list

and probabilitycond_e = probabilitycond * Parsing_helper.extent
	
type fungroup =
    PReplRestr of (Types.repl_index option ref(*to store replication index*) * ident option(*index*) * ident(*repetitions*)) (*replication*) option * 
	(ident * ident(*type*) * ident list(*options*)) list(*restrictions*) * fungroup list
  | PFun of ident * (ident * ty) list(*inputs*) * term_e * (int(*priority*) * ident list(*options*))

type eqmember = (fungroup * ident option * Parsing_helper.extent) list * Parsing_helper.extent


type special_args_e = Types.special_args_e
      
type equiv_t =
  | EquivNormal of eqmember * eqmember * probabilityf_e
  | EquivSpecial of ident * special_args_e list
	
type eqstatement = Types.eqname * equiv_t * (int * ident list(*options*))

(* Collisions *)

type collision = (ident * ident) list(*restrictions*) * (ident * ident) list(*forall*) * term_e * probabilityf_e * term_e * term_e(*side condition*) * ident list(*options*)



(* Values of parameters *)

type pval = 
    S of ident
  | I of int

(* Queries *)

type query = 
    PQSecret of ident * ident list(*public variables*) * ident list(*options*)
  | PQEventQ of (ident * ty(*type*)) list * term_e * ident list(*public variables*)

(* Implementation *)

type typeid = TypeSize of int | TypeName of ident

type typeopt = (ident * (ident list)) list
type funopt = (ident * ident) list

type impl = Type of ident * typeid * typeopt 
          | Function of ident * ident * funopt 
          | Constant of ident * ident
          | ImplTable of ident * ident

(* Occurrences *)

type pocc =
    POccInt of int
  | POccBefore of ident
  | POccAfter of ident
  | POccBeforeNth of int * ident
  | POccAfterNth of int * ident
  | POccAt of int * ident
  | POccAtNth of int * int * ident

type poccext = pocc * Parsing_helper.extent
	
(* User info for cryptographic transformation *)

type var_term_mapping =
    PVarMapping of (ident(*variable in game*) * ident(*variable in equivalence*)) list * bool (* bool is true when the list ends with "."
				    no other variable should be added by the transformation in this case *)
  | PTermMapping of (pocc(*occurrence in game*) * ident(*oracle in equivalence*)) list * bool

type crypto_transf_user_info =
    PRepeat of bool (* true when **, which means repeat without simplify in between *)
  | PVarList of ident list * bool (* bool is true when the list ends with "."
				    no other variable should be added by the transformation in this case *)
  | PDetailed of var_term_mapping list 

type rem_opt_t =
    RemCst of Types.rem_set
  | RemBinders of ident list

type move_opt_t =
    MoveCst of Types.move_set
  | MoveBinders of ident list
  | MoveArray of ident * ident list

type pcoll_elim_t =
    PCollVars of ident list
  | PCollTypes of ident list
  | PCollTerms of pocc list

type peqname = 
    PCstName of ident
  | PParName of ident * ident
  | PNoName
  | PN of int * Parsing_helper.extent

type allowed_coll_t = 
  | Allowed_Coll_Asympt of ((ident * int) list * ident) list
  | Allowed_Coll_Exact of ident

type guess_arg_t =
  | CGuessId of ident * bool(*true when "and above"*)
  | CGuessOcc of pocc * bool(*true when "and above"*) * Parsing_helper.extent
	
type command =
    CInteractive of Parsing_helper.extent
  | CHelp
  | CForget_old_games
  | CRestart of Parsing_helper.extent
  | CUndo of int * Parsing_helper.extent
  | CAllowed_collisions of allowed_coll_t
  | CSetting of ident * pval
  | CAuto
  | COut_facts of ident * pocc
  | COut_state of ident
  | COut_game of ident * bool(*true when "occ"*)
  | COut_equiv of ident * peqname * special_args_e list * crypto_transf_user_info * Parsing_helper.extent
  | COut_commands of ident
  | CShow_facts of pocc
  | CShow_state
  | CShow_game of bool(*true when "occ"*)
  | CShow_equiv of peqname * special_args_e list * crypto_transf_user_info * Parsing_helper.extent
  | CShow_commands
  | CSuccesscom
  | CSuccessSimplify of pcoll_elim_t list
  | CQuit
  | CStart_from_other_end of Parsing_helper.extent
  | CCrypto of peqname * special_args_e list * crypto_transf_user_info * Parsing_helper.extent
  | CExpand
  | CAll_simplify
  | CGlobal_dep_anal of ident * pcoll_elim_t list
  | CSArename of ident
  | CMerge_branches
  | CMerge_arrays of ident list list * Parsing_helper.extent
  | CReplace of poccext * ident * Types.replace_check_opt_t
  | CInsert of poccext * ident
  | CInsert_event of ident * poccext
  | CSimplify of pcoll_elim_t list
  | CMove of move_opt_t
  | CRemove_assign of rem_opt_t
  | CUse_variable of ident list
  | CFocus of ident list
  | CUndoFocus of Parsing_helper.extent
  | CTag of ident
  | CUndoTag of ident
  | CGuess of guess_arg_t
	
(* Declarations *)

type dim_e = (int * int) * Parsing_helper.extent
	
type decl = FunDecl of ident * ident list(*types*) * ident (*type*) * ident list(* options *)
          | EventDecl of ident * ident list(*types*) 
          | ParamDecl of ident * ident list(*options*)
	  | ProbabilityDecl of ident * dim_e list option(*dimensions of args*) * ident list (*options*)
	  | ConstDecl of ident * ident(*type*)
	  | ChannelDecl of ident
	  | TypeDecl of ident * ident list(*options*)
	  | Statement of statement
	  | BuiltinEquation of ident * ident list
	  | EqStatement of eqstatement
	  | Collision of collision
	  | Setting of ident * pval
	  | PDef of ident * (ident * ty) list * process_e
	  | Query of (ident * ty(*type*)) list * query list
	  | Define of ident * ident list * decl list
	  | Expand of ident * ident list
	  | Proofinfo of command list * Parsing_helper.extent
          | Implementation of impl list
          | TableDecl of ident * ident list
          | LetFun of ident * (ident * ty) list * term_e
	  | LetProba of ident * (ident * dim_e) list * probabilityf_e

type pall = decl list

type final_process =
    PSingleProcess of process_e
  | PEquivalence of process_e * process_e * ident list(*public variables*)
  | PQueryEquiv of eqstatement
	
type special_equiv_coll_t =
    (ident * ident(*type*)) list(*bound variables*) *
      (ident * ident(*type*)) list(*random variables*) *
      term_e

type random_fun_coll_t =
  | CollIndepNew of special_equiv_coll_t
  | CollNewDep of special_equiv_coll_t
      
(* Information passed when generating an equivalence
   declared with "special" *)

type equiv_call_t =
  | AutoCall
  | ManualCall of special_args_e list * crypto_transf_user_info
