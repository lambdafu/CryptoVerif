%{

open Parsing_helper
open Types
open Ptree
exception Syntax

let cst_true = (PIdent ("true", dummy_ext), dummy_ext)
let cst_false = (PIdent ("false", dummy_ext), dummy_ext)

let dummy_channel = ("@dummy_channel", dummy_ext)

let return_channel = (dummy_channel, None)
%}

%token COMMA
%token LPAREN
%token RPAREN
%token LBRACKET
%token RBRACKET
%token BAR
%token SEMI
%token COLON
%token NEW
%token OUT
%token IN
%token <Ptree.ident> IDENT
%token <Ptree.ident> STRING
%token <int> INT
%token <float> FLOAT
%token REPL
%token FOREACH
%token DO
%token LEQ
%token IF
%token THEN
%token ELSE
%token FIND
%token ORFIND
%token SUCHTHAT
%token DEFINED
%token EQUAL
%token DIFF
%token FUN
%token FORALL
%token EQUATION
%token BUILTIN
%token PARAM
%token PROBA
%token TYPE
%token PROCESS
%token DOT
%token EOF
%token LET
%token QUERY
%token SECRET
%token PUBLICVARS
%token AND
%token OR
%token CONST
%token CHANNEL
%token EQUIV
%token EQUIVLEFT
%token EQUIVRIGHT
%token MAPSTO
%token DEF
%token LEFTARROW
%token RANDOM
%token RETURN
%token MUL
%token DIV
%token ADD
%token SUB
%token POWER
%token SET
%token COLLISION
%token EVENT
%token IMPLIES
%token TIME
%token YIELD
%token EVENT_ABORT
%token MAXLENGTH
%token LENGTH
%token MAX
%token COUNT
%token EPSFIND
%token EPSRAND
%token PCOLL1RAND
%token PCOLL2RAND
%token NEWCHANNEL
%token NEWORACLE
%token INJEVENT
%token DEFINE
%token EXPAND
%token LBRACE
%token RBRACE
%token PROOF
%token IMPLEMENTATION
%token READ
%token WRITE
%token GET
%token INSERT
%token TABLE
%token LETFUN
%token RUN
%token INDEPOF
%token EQUIVALENCE
%token QUERY_EQUIV
%token SPECIAL
  
  /* tokens for proofs */
%token AT
%token AT_NTH
%token BEFORE
%token BEFORE_NTH
%token AFTER
%token AFTER_NTH
%token TERMS
%token VARIABLES
%token REMOVE_ASSIGN
%token USE_VARIABLE
%token USELESS
%token FINDCOND
%token ALL
%token BINDER
%token MOVE
%token NOARRAYREF
%token RANDOM
%token RANDOM_NOARRAYREF
%token ASSIGN
%token ARRAY
%token SIMPLIFY
%token COLL_ELIM
%token INSERT_EVENT
%token REPLACE
%token MERGE_ARRAYS
%token MERGE_BRANCHES
%token SARENAME
%token GLOBAL_DEP_ANAL
%token ALL_SIMPLIFY
%token CRYPTO
%token START_FROM_OTHER_END
%token QUIT
%token SUCCESS
%token SHOW_GAME
%token OCC
%token SHOW_STATE
%token SHOW_FACTS
%token SHOW_EQUIV
%token OUT_GAME
%token OUT_STATE
%token OUT_FACTS
%token OUT_EQUIV
%token AUTO
%token ALLOWED_COLLISIONS
%token UNDO
%token RESTART
%token FORGET_OLD_GAMES
%token HELP
%token INTERACTIVE
%token TYPES      
%token FOCUS
%token TAG
      
/* Precedence (from low to high) and associativities */
%left BAR
%right OR
%right AND
%left ADD SUB
%left MUL DIV
%nonassoc EQUAL
%nonassoc DIFF
%nonassoc REPL
%nonassoc UNARYMINUS
    
%start all
%type <Ptree.decl list * Ptree.final_process> all

%start lib
%type <Ptree.decl list> lib

%start oall
%type <Ptree.decl list * Ptree.final_process> oall

%start olib
%type <Ptree.decl list> olib

%start instruct
%type <Ptree.process_e> instruct

%start cryptotransfinfo
%type <Ptree.crypto_transf_user_info> cryptotransfinfo

%start term
%type <Ptree.term_e> term

%start proofoptsemi
%type <Ptree.command list> proofoptsemi

    %start focusquery
    %type <(Ptree.ident * Ptree.ty(*type*)) list * Ptree.query list> focusquery

    %start move_array_coll
    %type <Ptree.special_equiv_coll_t> move_array_coll

    %start random_fun_coll
    %type <Ptree.ident * Ptree.random_fun_coll_t> random_fun_coll

    %start random_bij_coll
    %type <Ptree.ident * Ptree.special_equiv_coll_t> random_bij_coll
    
    %start cequiv
    %type <Ptree.eqstatement> cequiv
    
    %start oequiv
    %type <Ptree.eqstatement> oequiv

    %start special_args
    %type <Ptree.special_args_e list> special_args

    %start collision_matrix
    %type <(Ptree.ident list * Ptree.ident list) list> collision_matrix
    
%%

commonlibelem:
	FUN IDENT LPAREN identlist RPAREN COLON IDENT options DOT 
	{ [FunDecl($2, $4, $7, $8)] }
|       EVENT IDENT DOT 
        { [EventDecl($2, [])] }
|       EVENT IDENT LPAREN identlist RPAREN DOT
        { [EventDecl($2, $4)] }
|	EQUATION eqlist options DOT 
	{ $2 }
|       EQUATION BUILTIN IDENT LPAREN identlist RPAREN DOT
        { [BuiltinEquation($3, $5)] }
|       SET IDENT EQUAL IDENT DOT
        { [Setting($2,S $4)] }
|       SET IDENT EQUAL INT DOT
        { [Setting($2,I $4)] }
|       QUERY vartypeilist SEMI queryseq DOT
        { [Query($2, $4)] }
|       QUERY queryseq DOT
        { [Query([], $2)] }
|       PARAM neidentlist options DOT
        { List.map (fun x -> (ParamDecl(x, $3))) $2 }
|       PROBA IDENT options DOT 
        { [ProbabilityDecl($2, $3)] }
|       CONST neidentlist COLON IDENT DOT 
        { List.map (fun x -> (ConstDecl(x,$4))) $2 }
|       TYPE IDENT options DOT 
        { [TypeDecl($2,$3)] }
|       PROOF LBRACE proof RBRACE 
        { [Proofinfo($3, parse_extent())] }
|       IMPLEMENTATION impllist DOT 
        { [Implementation($2)] }
|       TABLE IDENT LPAREN neidentlist RPAREN DOT 
        { [TableDecl($2,$4)] }
|       LETFUN IDENT EQUAL term DOT 
        { [LetFun($2,[],$4)] }
|       LETFUN IDENT LPAREN vartypeilist RPAREN EQUAL term DOT 
        { [LetFun($2,$4,$7)] }
|       EXPAND IDENT LPAREN identlist RPAREN DOT
        { [Expand($2, $4)] }
|       EQUIV eqname SPECIAL IDENT LPAREN special_args RPAREN optpriority DOT
        { [EqStatement($2, EquivSpecial($4, $6), $8)] }

special_args:
    { [] }
|   ne_special_args
    { $1 }

ne_special_args:
    special_arg
    { [$1] }
|   special_arg COMMA ne_special_args
    { $1 :: $3 }

special_arg:
    IDENT
    { SpecialArgId $1, parse_extent() }
|   STRING
    { SpecialArgString $1, parse_extent() }
|   LPAREN special_args RPAREN
    { SpecialArgTuple $2, parse_extent() }
    
cequiv:
    EQUIV eqname eqmember EQUIVLEFT probaf EQUIVRIGHT optpriority eqmember DOT
    { ($2, EquivNormal($3, $8, $5), $7) }
    
lib:
        commonlibelem lib
        { $1 @ $2 }
|	LET IDENT EQUAL process DOT lib
	{ (PDef($2,[],$4)) :: $6 }
|	LET IDENT LPAREN vartypeilist RPAREN EQUAL process DOT lib
	{ (PDef($2,$4,$7)) :: $9 }
|       CHANNEL neidentlist DOT lib 
        { (List.map (fun x -> (ChannelDecl(x))) $2) @ $4 }
|       cequiv lib
        { (EqStatement $1) :: $2 }
|       COLLISION newlist options forallvartype RETURN LPAREN term RPAREN EQUIVLEFT probaf EQUIVRIGHT RETURN LPAREN term RPAREN indep_cond DOT lib
        { (Collision($2, $4, $7, $10, $14, $16, $3)) :: $18 }
|       DEFINE IDENT LPAREN identlist RPAREN LBRACE lib RBRACE lib
        { (Define($2, $4, $7)) :: $9 }
| 
        { [] }

indep_cond:

    { cst_true }
|   IF term
    { $2 }
    

impllist:
        impl
        { [$1] }
|       impl SEMI impllist
        { $1 :: $3 }
          
impl:
        TYPE IDENT EQUAL typeid typeoptions
        { Type($2,$4,$5) }
|       FUN IDENT EQUAL STRING functionoptions
        { Function($2,$4,$5) }
|       TABLE IDENT EQUAL STRING
        { ImplTable($2,$4) }
|       CONST IDENT EQUAL STRING
        { Constant($2,$4) }

typeid:
        INT
        { TypeSize ($1) }
|       STRING
        { TypeName ($1) }

stringlistne:
        STRING
        { [$1] }
|       STRING COMMA stringlistne
        { $1::$3 }

stringlist:
    stringlistne
    { $1 }
|
    { [] }

typeopt:
        IDENT EQUAL stringlistne
        { $1,$3 }

typeoptlist:
|       typeopt
        { [$1] }
|       typeopt SEMI typeoptlist
        { $1::$3 }

typeoptions:
|       LBRACKET typeoptlist RBRACKET
        { $2 }
| 
        { [] }

funopt:
        IDENT EQUAL STRING
        { $1,$3 }

funoptlist:
|       funopt
        { [$1] }
|       funopt SEMI funoptlist
        { $1::$3 }

functionoptions:
        LBRACKET funoptlist RBRACKET
        { $2 }
|       
        { [] }

programoptions:
        LBRACKET progoptlist RBRACKET
        { $2 }
|       
        { [] }

progoptlist:
        progopt
        { [$1] }
|       progopt COMMA progoptlist
        { $1 :: $3 }

progopt:
        IDENT WRITE IDENT
        { PWrite($1,$3) }
|       IDENT READ IDENT
        { PRead($1,$3) }


idst:
        IDENT
        { $1 }
|       STRING
        { $1 }

proofcommand:
    INTERACTIVE
    { CInteractive(parse_extent()) }
|   HELP
    { CHelp }
|   FORGET_OLD_GAMES
    { CForget_old_games }
|   RESTART
    { CRestart(parse_extent()) }
|   UNDO
    { CUndo (1,parse_extent()) }
|   UNDO INT
    { CUndo ($2,parse_extent()) }
|   UNDO idst
    { CUndoTag ($2) }
|   TAG idst
    { CTag ($2) }
|   ALLOWED_COLLISIONS allowed_coll
    { CAllowed_collisions($2) }
|   SET IDENT EQUAL IDENT
    { CSetting($2,S $4) }
|   SET IDENT EQUAL INT 
    { CSetting($2,I $4) }
|   AUTO
    { CAuto }
|   OUT_FACTS idst occ
    { COut_facts($2, $3) }
|   OUT_STATE idst
    { COut_state($2) }
|   OUT_GAME idst
    { COut_game($2, false) }
|   OUT_GAME idst OCC
    { COut_game($2, true) }
|   OUT_EQUIV idst
    { COut_equiv($2, PNoName, [], PVarList([], false), parse_extent()) }
|   OUT_EQUIV idst equiv special_args_opt cryptotransfinfo
    { COut_equiv($2, $3, $4, $5, parse_extent()) }
|   SHOW_FACTS occ
    { CShow_facts($2) }
|   SHOW_STATE
    { CShow_state }
|   SHOW_GAME
    { CShow_game(false) }
|   SHOW_GAME OCC
    { CShow_game(true) }
|   SHOW_EQUIV
    { CShow_equiv(PNoName, [], PVarList([], false), parse_extent()) }
|   SHOW_EQUIV equiv special_args_opt cryptotransfinfo
    { CShow_equiv($2, $3, $4, parse_extent()) }
|   SUCCESS
    { CSuccesscom }
|   SUCCESS SIMPLIFY optcollelim
    { CSuccessSimplify($3) }
|   QUIT
    { CQuit }
|   START_FROM_OTHER_END
    { CStart_from_other_end(parse_extent()) }
|   CRYPTO
    { CCrypto(PNoName, [], PVarList([], false), parse_extent()) }
|   CRYPTO equiv special_args_opt cryptotransfinfo
    { CCrypto($2, $3, $4, parse_extent()) }
|   EXPAND
    { CExpand }
|   ALL_SIMPLIFY
    { CAll_simplify }
|   GLOBAL_DEP_ANAL idst optcollelim
    { CGlobal_dep_anal($2, $3) }
|   SARENAME idst
    { CSArename($2) }
|   MERGE_BRANCHES
    { CMerge_branches }
|   MERGE_ARRAYS varlistlist
    { CMerge_arrays($2, parse_extent()) }
|   REPLACE occext STRING
    { CReplace($2, $3) }
|   INSERT occext STRING
    { CInsert($2, $3) }
|   INSERT_EVENT idst occext
    { CInsert_event($2, $3) }
|   SIMPLIFY optcollelim
    { CSimplify($2) }
|   MOVE move_opt
    { CMove($2) }
|   REMOVE_ASSIGN rem_opt
    { CRemove_assign($2) }
|   USE_VARIABLE neidentlistnosep
    { CUse_variable($2) }
|   FOCUS stringlistne
    { CFocus($2) }
|   UNDO FOCUS
    { CUndoFocus(parse_extent()) }

special_args_opt:
    SPECIAL LPAREN special_args RPAREN
    { $3 }
|
    { [] }
    
rem_opt:
    USELESS
    { RemCst(Minimal) }
|   FINDCOND
    { RemCst(FindCond) }
|   ALL
    { RemCst(All) }
|   BINDER neidentlistnosep
    { RemBinders($2) }
    
move_opt:
    ALL
    { MoveCst(MAll) }
|   NOARRAYREF
    { MoveCst(MNoArrayRef) }
|   RANDOM
    { MoveCst(MNew) }
|   RANDOM_NOARRAYREF
    { MoveCst(MNewNoArrayRef) }
|   ASSIGN
    { MoveCst(MLet) }
|   BINDER neidentlistnosep
    { MoveBinders($2) }
|   ARRAY idst stringlist
    { MoveArray($2,$3) }
    
varlistlist:
    neidentlistnosep
    { [$1] }
|   neidentlistnosep COMMA varlistlist
    { $1 :: $3 }
  
equiv:
    idst
    { PCstName($1) }
|   idst LPAREN idst RPAREN
    { PParName($1, $3) }
|   INT
    { PN($1, parse_extent()) }
    
optcollelim:

    { [] }
|   COLL_ELIM LPAREN colleliminfo RPAREN
    { $3 }

colleliminfo:
    onecolleliminfo
    { [$1] }
|   onecolleliminfo SEMI colleliminfo
    { $1 :: $3 }
    
onecolleliminfo:
    VARIABLES COLON neidstlist
    { PCollVars($3) }
|   TYPES COLON neidstlist
    { PCollTypes($3) }
|   TERMS COLON neocclist
    { PCollTerms($3) }

neocclist:
    occ
    { [$1] }
|   occ COMMA neocclist
    { $1::$3 }

neidstlist:
    idst
    { [$1] }
|   idst COMMA neidstlist
    { $1 :: $3 }
    
proof:
        proofcommand
	{ [$1] }
|       proofcommand SEMI proof
        { $1 :: $3 }

proofoptsemi:
        proofcommand
	{ [$1] }
|       proofcommand SEMI
        { [$1] }
|       proofcommand SEMI proofoptsemi
        { $1 :: $3 }

options:
        LBRACKET neidentlist RBRACKET
        { $2 }
| 
        { [] }

all:
        lib PROCESS process EOF
        { $1, PSingleProcess $3 }
|       lib EQUIVALENCE process process optpublicvars EOF
        { $1, PEquivalence($3, $4, $5) }
|       lib QUERY_EQUIV eqname eqmember EQUIVLEFT HELP EQUIVRIGHT optpriority eqmember EOF
        { $1, PQueryEquiv($3, EquivNormal($4, $9, (PPZero,parse_extent())), $8) }
    
identlist:
        
        { [] }
|       neidentlist
        { $1 }

neidentlist:
        IDENT 
        { [$1] }
|       IDENT COMMA neidentlist
        { $1 :: $3 }

newarg: /* For compatibility with ProVerif; ignored by CryptoVerif */
  
    { None }
| LBRACKET RBRACKET
    { Some [] }
| LBRACKET neidentlist RBRACKET
    { Some ($2) }

vartype:
    neidentlist COLON IDENT
    { List.map (fun x -> (x,$3)) $1 }
    
nevartypelist:
        vartype
        { $1 }
|       vartype COMMA nevartypelist
        { $1 @ $3 }

neforallvartype:
    FORALL nevartypelist SEMI
    { $2 }

forallvartype:
    neforallvartype
    { $1 }
|
    { [] }

/* Equations */

eqlist:
    one_eq  
    { [$1] }
|   one_eq SEMI eqlist
    { $1::$3 }

one_eq:
    forallvartype term  
    { Statement($1, $2, cst_true) }
|   forallvartype term IF term
    { Statement($1, $2, $4) }
    
    
funapp:
    IDENT
    { PFunApp($1, []), parse_extent() }
|   IDENT LPAREN termseq RPAREN
    { PFunApp($1, $3), parse_extent() }
    
term:
	IDENT LPAREN termseq RPAREN
	{ PFunApp ($1, $3), parse_extent() }
|       INJEVENT LPAREN funapp RPAREN 
        { PQEvent(true, $3), parse_extent() }
|       EVENT LPAREN funapp RPAREN 
        { PQEvent(false, $3), parse_extent() }
|	IDENT
	{ PIdent ($1), parse_extent() }
|       IDENT LBRACKET termseq RBRACKET
        { PArray ($1, $3), parse_extent() }
|	LPAREN termseq RPAREN
	{ match $2 with
	    [t] -> t (* Allow parentheses for priorities of infix operators;
			Tuples cannot have one element. *)
	  | l -> PTuple(l), parse_extent() }
|       IF findcond THEN term ELSE term
        { begin
	  match $2 with
	    ([],t) -> PTestE(t, $4, $6)
	  | (def_list, t) -> 
	      PFindE([(ref [], [], def_list, t, $4)], $6, [])
	  end, parse_extent() }
|       FIND options findlistterm ELSE term
        { PFindE($3, $5, $2), parse_extent() }
|       basicpattern LEFTARROW term SEMI term
        { PLetE($1,$3,$5,None), parse_extent() }
|       LET pattern EQUAL term IN term ELSE term
        { PLetE($2,$4,$6,Some $8), parse_extent() }
|       LET pattern EQUAL term IN term
        { PLetE($2,$4,$6,None), parse_extent() }
| 	restr SEMI term
	{ let (b,t) = $1 in PResE(b, t, $3), parse_extent() }
|       EVENT_ABORT IDENT
        { PEventAbortE($2), parse_extent() }
|       EVENT funapp newarg SEMI term
        { PEventE($2, $5), parse_extent() }
|       INSERT IDENT LPAREN termseq RPAREN SEMI term
        { PInsertE($2,$4,$7), parse_extent() }
|       GET IDENT LPAREN patternseq RPAREN SUCHTHAT term IN term ELSE term
        { PGetE($2,$4,Some $7,$9,$11), parse_extent() }
|       GET IDENT LPAREN patternseq RPAREN IN term ELSE term
        { PGetE($2,$4,None,$7,$9), parse_extent() }
|       term EQUAL term
        { PEqual($1, $3), parse_extent() }
|       term DIFF term
        { PDiff($1, $3), parse_extent() }
|       term OR term
        { POr($1, $3), parse_extent() }
|       term AND term
        { PAnd($1, $3), parse_extent() }
|       IDENT INDEPOF IDENT
        { PIndepOf($1, $3), parse_extent() }
    
vref:
    IDENT LBRACKET termseq RBRACKET
    { $1,$3 }
|   IDENT
    { $1, [] }
    
vreflist:
    vref
    { [$1] }
|   vref COMMA vreflist
    { $1::$3 }

findcond1:
|   DEFINED LPAREN vreflist RPAREN AND term
    { ($3, $6) }
|   DEFINED LPAREN vreflist RPAREN 
    { ($3, cst_true) }

findcond:
    findcond1
    { $1 }
|   term
    { ([], $1) }
|   LPAREN findcond1 RPAREN
    { $2 }

findoneterm:
    tidentseq SUCHTHAT findcond THEN term
    { let (def_list, t) = $3 in
      (ref [], $1, def_list, t, $5) }

findlistterm:
    findoneterm
    { [$1] }
|   findoneterm ORFIND findlistterm
    { $1 :: $3 }

tidentone:
    IDENT LEQ IDENT
    { ($1,$1,$3) }
|   IDENT EQUAL IDENT LEQ IDENT
    { ($1,$3,$5) }
    
netidentseq:
    tidentone
    { [$1] }
|   tidentone COMMA netidentseq
    { $1::$3 }

tidentseq:
    netidentseq
    { $1 }
| 
    { [] }

netermseq:
	term COMMA netermseq
	{ $1 :: $3 }
|	term 
	{ [$1] }

termseq:
        netermseq
        { $1 }
| 
        { [] }


progbegin:
        IDENT programoptions LBRACE
        {($1,$2)}

progend:
        RBRACE
        {true}
|
        {false}

repl:
  REPL IDENT
    { (None, $2) }
| REPL IDENT LEQ IDENT
    { (Some $2, $4) }
| FOREACH IDENT LEQ IDENT DO
    { (Some $2, $4) }

restr:
  NEW IDENT newarg COLON IDENT
    { ($2, $5) }
| IDENT RANDOM IDENT
    { ($1, $3) }
   
    
process:
        progbegin process
        { PBeginModule ($1,$2), parse_extent() }
|	LPAREN process RPAREN
	{ $2 }
|	IDENT
	{ PLetDef($1,[]), parse_extent() }
|	IDENT LPAREN termseq RPAREN
	{ PLetDef($1,$3), parse_extent() }
|	repl process %prec REPL
	{ let (i,n) = $1 in PRepl (ref None,i,n,$2), parse_extent() }
|	INT 
	{ let x = $1 in
	  if x = 0 then PNil, parse_extent() else 
          input_error ("The only integer in a process is 0 for the nil process") (parse_extent()) }
| 	restr optprocess
	{ let (b,t) = $1 in PRestr(b, t, $2), parse_extent() }
|	IF findcond THEN process optelse
        { match $2 with
	    ([], t) -> PTest(t, $4, $5), parse_extent()
	  | (def_list, t) -> 
	      PFind([(ref [], [], def_list, t, $4)], $5, []), parse_extent() }
|       FIND options findlistproc optelse
        { PFind($3,$4,$2), parse_extent() }
|       INSERT IDENT LPAREN termseq RPAREN optprocess
        { PInsert($2,$4,$6), parse_extent() }
|       GET IDENT LPAREN patternseq RPAREN SUCHTHAT term IN process optelse
        { PGet($2,$4,Some $7,$9,$10), parse_extent() }
|       GET IDENT LPAREN patternseq RPAREN IN process optelse
        { PGet($2,$4,None,$7,$8), parse_extent() }
|       EVENT funapp newarg optprocess
        { PEvent($2, $4), parse_extent() }
|       basicpattern LEFTARROW term optprocess
        { PLet($1,$3,$4,(PYield, parse_extent())), parse_extent() }
| 	LET pattern EQUAL term
	{ PLet($2,$4,(PYield, parse_extent()),(PYield, parse_extent())), parse_extent() }
| 	LET pattern EQUAL term IN process optelse
	{ PLet($2,$4,$6,$7), parse_extent() }
|	IN LPAREN channel COMMA pattern RPAREN optprocess
	{ PInput($3,$5,$7), parse_extent() }
|	OUT LPAREN channel COMMA term RPAREN progend optinputprocess
	{ POutput($7,$3,$5,$8), parse_extent() }
|       YIELD
        { PYield, parse_extent() }
|       EVENT_ABORT IDENT
        { PEventAbort($2), parse_extent() }
|	process BAR process
        { PPar($1,$3), parse_extent() }

channel:
    IDENT
    { $1, None }
|   IDENT LBRACKET identlist RBRACKET
    { $1, Some $3 }

findoneproc:
    tidentseq SUCHTHAT findcond THEN process
    { let (def_list, t) = $3 in
      (ref [], $1, def_list, t, $5) }

findlistproc:
    findoneproc
    { [$1] }
|   findoneproc ORFIND findlistproc
    { $1 :: $3 }

optprocess:
        SEMI process
        { $2 }
|       
        { PYield, parse_extent() }        

optinputprocess:
        SEMI process
        { $2 }
|       
        { PNil, parse_extent() }        

optelse:
        ELSE process
        { $2 }
|
        { PYield, parse_extent() }

basicpattern:
        IDENT
        { PPatVar($1,None), parse_extent() }
|       IDENT COLON IDENT
        { PPatVar($1, Some (Tid $3)), parse_extent() }
|       IDENT LEQ IDENT
        { PPatVar($1, Some (TBound $3)), parse_extent() }
    
pattern:
  basicpattern
    { $1 }
| IDENT LPAREN patternseq RPAREN
    { PPatFunApp($1,$3), parse_extent() }
| LPAREN patternseq RPAREN
    {  match $2 with
	    [t] -> t (* Allow parentheses for priorities of infix operators;
			Tuples cannot have one element. *)
	  | l -> PPatTuple($2), parse_extent() }
| EQUAL term
    { PPatEqual($2), parse_extent() }

nepatternseq:
  pattern COMMA nepatternseq
    { $1 :: $3 }
| pattern
    { [$1] }

patternseq:
  nepatternseq
    { $1 }
| 
    { [] }

queryseq:
    query
    { [$1] }
|   query SEMI queryseq
    { $1::$3 }

query:
    SECRET IDENT optpublicvars options
    { PQSecret ($2,$3,$4) }
|   term IMPLIES term optpublicvars
    { PQEventQ([], $1, $3, $4) }
|   term optpublicvars
    { (* "M" interpreted as "M ==> false" as in ProVerif *)
      PQEventQ([], $1, cst_false, $2) }
    
optpublicvars:
    
    { [] }
|   PUBLICVARS neidentlist
    { $2 }

procasterm:
        RETURN LPAREN term RPAREN
        { $3 }
|       LPAREN procasterm RPAREN
        { $2 }
|       IF findcond THEN procasterm ELSE procasterm
        { begin
	  match $2 with
	    ([], t) -> PTestE(t, $4, $6)
	  | (def_list, t) -> 
	      PFindE([(ref [], [], def_list, t, $4)], $6, [])
	  end, parse_extent() }
|       FIND options findlistprocasterm ELSE procasterm
        { PFindE($3, $5, $2), parse_extent() }
|       basicpattern LEFTARROW term SEMI procasterm
        { PLetE($1,$3,$5,None), parse_extent() }
|       LET pattern EQUAL term IN procasterm ELSE procasterm
        { PLetE($2,$4,$6,Some $8), parse_extent() }
|       LET pattern EQUAL term IN procasterm
        { PLetE($2,$4,$6,None), parse_extent() }
| 	restr SEMI procasterm
	{ let (b, t) = $1 in PResE(b, t, $3), parse_extent() }
|       EVENT_ABORT IDENT
        { PEventAbortE($2), parse_extent() }

findoneprocasterm:
    tidentseq SUCHTHAT findcond THEN procasterm
    { let (def_list, t) = $3 in
      (ref [], $1, def_list, t, $5) }

findlistprocasterm:
    findoneprocasterm
    { [$1] }
|   findoneprocasterm ORFIND findlistprocasterm
    { $1 :: $3 }

eqname:
    LPAREN IDENT RPAREN
    { CstName $2 }
|   LPAREN IDENT LPAREN IDENT RPAREN RPAREN
    { ParName($2,$4) }
|  
    { NoName }

eqmember:
    funmode
    { [$1], parse_extent() }
|   funmode BAR eqmember
    { $1 :: (fst $3), parse_extent() }

topfungroup:
    fungroup
    { $1 }
|   nenewlistfunlist
    { let (news,r) = $1 in
      PReplRestr(None, news, r) }
    
funmode:
    topfungroup
    { $1,None, parse_extent() }
|   topfungroup LBRACKET IDENT RBRACKET
    { $1,Some $3, parse_extent() }

newlist:
    
    { [] }
|   restr SEMI newlist
    { $1::$3 }

funlist:
    fungroup
    { [$1] }
|   fungroup BAR funlist
    { $1 :: $3 }

newlistfunlist:
    fungroup
    { [],[$1] }
|   LPAREN funlist RPAREN
    { [],$2 }
|   restr options SEMI newlistfunlist
    { let (b,t) = $1 in let (n,r) = $4 in ((b,t,$2)::n), r }

nenewlistfunlist:
    restr options SEMI newlistfunlist
    { let (b,t) = $1 in let (n,r) = $4 in ((b,t,$2)::n), r }
    
optpriority:
    LBRACKET neidentlist RBRACKET LBRACKET INT RBRACKET 
    { $5, $2 }
|   LBRACKET INT RBRACKET LBRACKET neidentlist RBRACKET 
    { $2, $5 }
|   LBRACKET INT RBRACKET
    { $2, [] }
|   LBRACKET neidentlist RBRACKET
    { 0, $2 }
|   
    { 0, [] }

vartypeilist:

        { [] }
|       nevartypeilist
        { $1 }

nevartypeilist:
        vartypei
        { $1 }
|       vartypei COMMA nevartypeilist
        { $1 @ $3 }

vartypei:
 /* We need to make explicit the first IDENT to avoid
    2 shift/reduce conflicts on COLON and LEQ between
    QUERY vartypeilist SEMI queryseq DOT
    QUERY queryseq DOT
    (queryseq can be term ... which can be x:T <- M ...
    so when we have "query x:T", it can be the beginning
    of both cases: it is the first case when it is followed
    by SEMI or COMMA, the second case when it is followed by LEFTARROW.
    We must not reduce neidentlist during the parsing of "query x:T".)
    */
        IDENT COLON IDENT
        { [$1, Tid $3] }
|       IDENT LEQ IDENT
        { [$1, TBound $3] }
|       IDENT COMMA neidentlist COLON IDENT
        { List.map (fun x -> (x, Tid $5)) ($1::$3) }
|       IDENT COMMA neidentlist LEQ IDENT
        { List.map (fun x -> (x, TBound $5)) ($1::$3) }
    
fungroup:
|   IDENT LPAREN vartypeilist RPAREN optpriority DEF procasterm 
    { PFun($1, $3, $7, $5) }
|   repl newlistfunlist 
    { let (i,n) = $1 in let (news,r) = $2 in
      PReplRestr(Some(ref None, i, n), news, r) }
    
probaf:
        LPAREN probaf RPAREN
        { $2 }
|       SUB probaf  %prec UNARYMINUS
        { PSub((PPZero, parse_extent()), $2), parse_extent() }
|       probaf ADD probaf
        { PAdd($1,$3), parse_extent() }
|       probaf SUB probaf
        { PSub($1, $3), parse_extent() }
|       probaf MUL probaf
        { PProd($1,$3), parse_extent() }
|       probaf DIV probaf
        { PDiv($1,$3), parse_extent() }
|       MAX LPAREN probaflist RPAREN
        { PMax($3), parse_extent() }
|       IDENT
        { (PPIdent $1), parse_extent() }
|       COUNT IDENT
        { (PCount $2), parse_extent() }
|       IDENT LPAREN probaflist RPAREN
        { (PPFun($1,$3)), parse_extent() }
|       BAR IDENT BAR
        { PCard($2), parse_extent() }
|       TIME
        { PTime, parse_extent() }
|       TIME LPAREN IDENT probaflistopt RPAREN
        { PActTime(PAFunApp $3, $4), parse_extent() }
|       TIME LPAREN LET IDENT probaflistopt RPAREN
        { PActTime(PAPatFunApp $4, $5), parse_extent() }
|       TIME LPAREN REPL RPAREN
        { PActTime(PAReplIndex, []), parse_extent() }
|       TIME LPAREN FOREACH RPAREN
        { PActTime(PAReplIndex, []), parse_extent() }
|       TIME LPAREN LBRACKET INT RBRACKET RPAREN
        { PActTime(PAArrayAccess $4, []), parse_extent() }
|       TIME LPAREN EQUAL IDENT probaflistopt RPAREN
        { PActTime(PACompare $4, $5), parse_extent() }
|       TIME LPAREN LPAREN identlist RPAREN probaflistopt RPAREN
        { PActTime(PAAppTuple $4, $6), parse_extent() }
|       TIME LPAREN LET LPAREN identlist RPAREN probaflistopt RPAREN
        { PActTime(PAPatTuple $5, $7), parse_extent() }
|       TIME LPAREN AND RPAREN
        { PActTime(PAAnd, []), parse_extent() }
|       TIME LPAREN OR RPAREN
        { PActTime(PAOr, []), parse_extent() }
|       TIME LPAREN NEW IDENT RPAREN
        { PActTime(PANew $4, []), parse_extent() }
|       TIME LPAREN RANDOM IDENT RPAREN
        { PActTime(PANew $4, []), parse_extent() }
|       TIME LPAREN NEWCHANNEL RPAREN
        { PActTime(PANewChannel, []), parse_extent() }
|       TIME LPAREN IF RPAREN
        { PActTime(PAIf, []), parse_extent() }
|       TIME LPAREN FIND INT RPAREN
        { PActTime(PAFind $4, []), parse_extent() }
|       TIME LPAREN OUT IDENT probaflistopt RPAREN
        { PActTime(PAOut([], $4), $5), parse_extent() }
|       TIME LPAREN OUT LBRACKET neidentlist RBRACKET IDENT probaflistopt RPAREN
        { PActTime(PAOut($5, $7), $8), parse_extent() }
|       TIME LPAREN IN INT RPAREN
        { PActTime(PAIn $4, []), parse_extent() }
|       INT
        { let x = $1 in
	  if x = 0 then (PPZero,parse_extent())  else 
          (PCst x,parse_extent())  }
|       FLOAT
        { let x = $1 in
	  if x = 0.0 then (PPZero,parse_extent())  else 
	  (PFloatCst x,parse_extent())  }
|       MAXLENGTH LPAREN term RPAREN
        { PMaxlength($3), parse_extent() }
|       LENGTH LPAREN IDENT probaflistopt RPAREN
        { PLength($3, $4), parse_extent() }
|       LENGTH LPAREN LPAREN identlist RPAREN probaflistopt RPAREN
        { PLengthTuple($4, $6), parse_extent() }
|       EPSFIND
        { PEpsFind, parse_extent() }
|       EPSRAND LPAREN IDENT RPAREN
        { PEpsRand($3), parse_extent() }
|       PCOLL1RAND LPAREN IDENT RPAREN
        { PPColl1Rand($3), parse_extent() }
|       PCOLL2RAND LPAREN IDENT RPAREN
        { PPColl2Rand($3), parse_extent() }

probaflistopt:
       COMMA probaflist 
       { $2 }
| 
       { [] }

probaflist:
       probaf
       { [$1] }
|      probaf COMMA probaflist
       { $1 :: $3 }

    /* Focus query */
focusquery:
|       QUERY vartypeilist SEMI queryseq 
        { ($2, $4) }
|       QUERY queryseq 
        { ([], $2) }
    
/* Instructions, for manual insertion of an instruction in a game */

instruct:

    { (PYield, parse_extent()) }
|   LPAREN instruct RPAREN
    { $2 }
|   restr optsemiinstruct
    { let (b,t) = $1 in PRestr(b, t, $2), parse_extent() }
|   IF findcond THEN instruct optelseinstruct
    { 
      match $2 with
	([], t) -> PTest(t, $4, $5), parse_extent()
      | (def_list, t) -> 
	  PFind([(ref [], [], def_list, t, $4)], $5, []), parse_extent()
    }
|   FIND options findlistins optelseinstruct
    { PFind($3, $4, $2), parse_extent() }
|   EVENT_ABORT IDENT
    { PEventAbort($2), parse_extent() }
|   basicpattern LEFTARROW term optsemiinstruct
    { PLet($1,$3,(PYield, parse_extent()),(PYield, parse_extent())), parse_extent() }
|   LET pattern EQUAL term IN instruct optelseinstruct
    { PLet($2,$4,$6,$7), parse_extent() }

findoneins:
    tidentseq SUCHTHAT findcond THEN instruct
    { let (def_list, t) = $3 in
      (ref [], $1, def_list, t, $5) }

findlistins:
    findoneins
    { [$1] }
|   findoneins ORFIND findlistins
    { $1 :: $3 }

optelseinstruct:

    { (PYield, parse_extent()) }
|   ELSE instruct
    { $2 }

optsemiinstruct:
    
    { (PYield, parse_extent()) }
|   SEMI instruct
    { $2 }
    
/* Limits on elimination of collisions */

factor:
    idst
    { ($1, 1) }
|   idst POWER INT
    { ($1, $3) }

num:
    factor MUL num
    { $1 :: $3 }
|   factor
    { [$1] }

quot:
    num DIV idst
    { ($1, Some $3) }
|   COLLISION MUL num
    { ($3, None) }

allowed_coll_asymptotic:
    quot
    { [$1] }
|   quot COMMA allowed_coll_asymptotic
    { $1 :: $3 }

allowed_coll:
    allowed_coll_asymptotic
    { Allowed_Coll_Asympt($1) }
|   idst
    { Allowed_Coll_Exact($1) }
    
/* User information for the cryptographic transformation */

identmapping:
    idst MAPSTO idst
    { [$1,$3] }
|   idst MAPSTO idst COMMA identmapping
    { ($1,$3)::$5 }

occ:
    INT
    { POccInt($1) }
| BEFORE STRING
    { POccBefore($2) }
| AFTER STRING 
    { POccAfter($2) }
| BEFORE_NTH INT STRING
    { POccBeforeNth($2, $3) }
| AFTER_NTH INT STRING
    { POccAfterNth($2, $3) }
| AT INT STRING
    { POccAt($2, $3) }
| AT_NTH INT INT STRING
    { POccAtNth($2, $3, $4) }

occext:
    occ
    { ($1, parse_extent()) }
    
occidentmapping:
    occ MAPSTO idst
    { [$1,$3] }
|   occ MAPSTO idst COMMA occidentmapping
    { ($1,$3)::$5 }

detailedinfo:
    VARIABLES COLON identmapping
    { PVarMapping($3, false) }
|   VARIABLES COLON identmapping DOT
    { PVarMapping($3, true) }
|   TERMS COLON occidentmapping
    { PTermMapping($3, false) }
|   TERMS COLON occidentmapping DOT
    { PTermMapping($3, true) }

detailedinfolist:
    detailedinfo
    { [$1] }
|   detailedinfo SEMI detailedinfolist
    { $1::$3 }

neidentlistnosep:
        idst
        { [$1] }
|       idst neidentlistnosep
        { $1 :: $2 }

cryptotransfinfo:
    
    { PVarList([],false) }
|   MUL
    { PRepeat(false) }
|   MUL MUL
    { PRepeat(true) }
|   neidentlistnosep
    { PVarList($1, false) }
|   neidentlistnosep DOT
    { PVarList($1, true) }
|   LBRACKET detailedinfolist RBRACKET
    { PDetailed($2) }

move_array_coll:
    forallvartype restr SEMI term
    { ($1, [$2], $4) }

random_collisions:
    neforallvartype restr SEMI term
    { CollIndepNew($1,[$2],$4) }
|   restr SEMI restr SEMI neforallvartype term
    { CollNewDep($5,[$1;$3],$6) }
|   restr SEMI neforallvartype term
    { CollNewDep($3,[$1],$4) }
|   term
    /* Solve the shift/reduce conflict that appears when
       the forallvartype part is empty in the two rules above.
       The restrictions may then be included in the term,
       because restrictions are allowed in the grammar of "term".
       However, restrictions are forbidden inside this particular term
       during a later pass, so we can disambiguate.
    */
    { match $1 with
    | PResE(b1,ty1,(PResE(b2,ty2, t), _)), _ -> CollNewDep([],[(b1,ty1);(b2,ty2)],t)
    | PResE(b,ty,t), _ -> CollNewDep([],[(b,ty)],t)
    | _ -> raise Parsing.Parse_error }
    
    
random_fun_coll:
    IDENT COLON random_collisions
    { $1, $3 }

random_bij_coll:
    IDENT COLON move_array_coll
    { $1, $3 }
  
/* Oracle front-end */

oprocess:
        progbegin oprocess
        { PBeginModule ($1,$2), parse_extent() }
|	LPAREN oprocess RPAREN
	{ $2 }
|	RUN IDENT
        { PLetDef($2,[]), parse_extent() }
|	RUN IDENT LPAREN termseq RPAREN
	{ PLetDef($2,$4), parse_extent() }    
|	repl oprocess %prec REPL
	{ let (i,n) = $1 in PRepl (ref None,i,n,$2), parse_extent() }
|	INT 
	{ let x = $1 in
	  if x = 0 then PNil, parse_extent() else 
          input_error ("The only integer in a process is 0 for the nil process") (parse_extent()) }
| 	restr optoprocess
	{ let (b,t) = $1 in PRestr(b, t, $2), parse_extent() }
|	IF findcond THEN oprocess optoelse
        { match $2 with
	    ([], t) -> PTest(t, $4, $5), parse_extent()
	  | (def_list, t) -> 
	      PFind([(ref [], [], def_list, t, $4)], $5, []), parse_extent() }
|       FIND options ofindlistproc optoelse
        { PFind($3,$4,$2), parse_extent() }
|       INSERT IDENT LPAREN termseq RPAREN optoprocess
        { PInsert($2,$4,$6), parse_extent() }
|       GET IDENT LPAREN patternseq RPAREN SUCHTHAT term IN oprocess optoelse
        { PGet($2,$4,Some $7,$9,$10), parse_extent() }
|       GET IDENT LPAREN patternseq RPAREN IN oprocess optoelse
        { PGet($2,$4,None,$7,$8), parse_extent() }
|       EVENT IDENT optoprocess
        { PEvent((PFunApp($2, []), parse_extent()), $3), parse_extent() }
|       EVENT IDENT LPAREN termseq RPAREN optoprocess
        { PEvent((PFunApp($2, $4), parse_extent()), $6), parse_extent() }
|       basicpattern LEFTARROW term optoprocess
        { PLet($1,$3,$4,(PYield, parse_extent())), parse_extent() }
| 	LET pattern EQUAL term
	{ PLet($2,$4,(PYield, parse_extent()),(PYield, parse_extent())), parse_extent() }
| 	LET pattern EQUAL term IN oprocess optoelse
	{ PLet($2,$4,$6,$7), parse_extent() }
|	IDENT LPAREN patternseq RPAREN DEF oprocess
	{ let (_,ext) = $1 in
	  PInput(($1,None),(PPatTuple $3, ext),$6), parse_extent() }
|	RETURN LPAREN termseq RPAREN progend optinputoprocess
	{ POutput($5,return_channel, (PTuple($3), parse_extent()),$6), parse_extent() }
|	RETURN progend optinputoprocess
	{ POutput($2,return_channel, (PTuple [], parse_extent()),$3), parse_extent() }
|       YIELD
        { PYield, parse_extent() }
|       EVENT_ABORT IDENT
        { PEventAbort($2), parse_extent() }
|	oprocess BAR oprocess
	{ PPar($1,$3), parse_extent() }

ofindoneproc:
    tidentseq SUCHTHAT findcond THEN oprocess
    { let (def_list, t) = $3 in
      (ref [], $1, def_list, t, $5) }

ofindlistproc:
    ofindoneproc
    { [$1] }
|   ofindoneproc ORFIND ofindlistproc
    { $1 :: $3 }

optoprocess:
        SEMI oprocess
        { $2 }
|       
        { PYield, parse_extent() }        

optinputoprocess:
        SEMI oprocess
        { $2 }
|       
        { PNil, parse_extent() }        

optoelse:
        ELSE oprocess
        { $2 }
|
        { PYield, parse_extent() }

    
oprobaf:
        LPAREN oprobaf RPAREN
        { $2 }
|       oprobaf ADD oprobaf
        { PAdd($1,$3), parse_extent() }
|       oprobaf SUB oprobaf
        { PSub($1, $3), parse_extent() }
|       oprobaf MUL oprobaf
        { PProd($1,$3), parse_extent() }
|       oprobaf DIV oprobaf
        { PDiv($1,$3), parse_extent() }
|       MAX LPAREN oprobaflist RPAREN
        { PMax($3), parse_extent() }
|       IDENT
        { (PPIdent $1), parse_extent() }
|       COUNT IDENT
        { (PCount $2), parse_extent() }
|       IDENT LPAREN oprobaflist RPAREN
        { (PPFun($1,$3)), parse_extent() }
|       BAR IDENT BAR
        { PCard($2), parse_extent() }
|       TIME
        { PTime, parse_extent() }
|       TIME LPAREN IDENT oprobaflistopt RPAREN
        { PActTime(PAFunApp $3, $4), parse_extent() }
|       TIME LPAREN LET IDENT oprobaflistopt RPAREN
        { PActTime(PAPatFunApp $4, $5), parse_extent() }
|       TIME LPAREN REPL RPAREN
        { PActTime(PAReplIndex, []), parse_extent() }
|       TIME LPAREN FOREACH RPAREN
        { PActTime(PAReplIndex, []), parse_extent() }
|       TIME LPAREN LBRACKET INT RBRACKET RPAREN
        { PActTime(PAArrayAccess $4, []), parse_extent() }
|       TIME LPAREN EQUAL IDENT oprobaflistopt RPAREN
        { PActTime(PACompare $4, $5), parse_extent() }
|       TIME LPAREN LPAREN identlist RPAREN oprobaflistopt RPAREN
        { PActTime(PAAppTuple $4, $6), parse_extent() }
|       TIME LPAREN LET LPAREN identlist RPAREN oprobaflistopt RPAREN
        { PActTime(PAPatTuple $5, $7), parse_extent() }
|       TIME LPAREN AND RPAREN
        { PActTime(PAAnd, []), parse_extent() }
|       TIME LPAREN OR RPAREN
        { PActTime(PAOr, []), parse_extent() }
|       TIME LPAREN NEW IDENT RPAREN
        { PActTime(PANew $4, []), parse_extent() }
|       TIME LPAREN RANDOM IDENT RPAREN
        { PActTime(PANew $4, []), parse_extent() }
|       TIME LPAREN NEWORACLE RPAREN
        { PActTime(PANewChannel, []), parse_extent() }
|       TIME LPAREN IF RPAREN
        { PActTime(PAIf, []), parse_extent() }
|       TIME LPAREN FIND INT RPAREN
        { PActTime(PAFind $4, []), parse_extent() }
|       INT
        { let x = $1 in
	  if x = 0 then (PPZero,parse_extent())  else 
          (PCst x,parse_extent())  }
|       FLOAT
        { let x = $1 in
	  if x = 0.0 then (PPZero,parse_extent())  else 
	  (PFloatCst x,parse_extent())  }
|       MAXLENGTH LPAREN term RPAREN
        { PMaxlength($3), parse_extent() }
|       LENGTH LPAREN IDENT oprobaflistopt RPAREN
        { PLength($3, $4), parse_extent() }
|       LENGTH LPAREN LPAREN identlist RPAREN oprobaflistopt RPAREN
        { PLengthTuple($4, $6), parse_extent() }
|       EPSFIND
        { PEpsFind, parse_extent() }
|       EPSRAND LPAREN IDENT RPAREN
        { PEpsRand($3), parse_extent() }
|       PCOLL1RAND LPAREN IDENT RPAREN
        { PPColl1Rand($3), parse_extent() }
|       PCOLL2RAND LPAREN IDENT RPAREN
        { PPColl2Rand($3), parse_extent() }

oprobaflistopt:
       COMMA oprobaflist 
       { $2 }
| 
       { [] }

oprobaflist:
       oprobaf
       { [$1] }
|      oprobaf COMMA oprobaflist
       { $1 :: $3 }

oequiv:
    EQUIV eqname eqmember EQUIVLEFT oprobaf EQUIVRIGHT optpriority eqmember DOT
    { ($2, EquivNormal($3, $8, $5), $7) }
    
olib:
        commonlibelem olib
        { $1 @ $2 }
|	LET IDENT EQUAL oprocess DOT olib
	{ (PDef($2,[],$4)) :: $6 }
|	LET IDENT LPAREN vartypeilist RPAREN EQUAL oprocess DOT olib
	{ (PDef($2,$4,$7)) :: $9 }
|       oequiv olib
        { (EqStatement $1) :: $2 }
|       COLLISION newlist options forallvartype RETURN LPAREN term RPAREN EQUIVLEFT oprobaf EQUIVRIGHT RETURN LPAREN term RPAREN indep_cond DOT olib
        { (Collision($2, $4, $7, $10, $14, $16, $3)) :: $18 }
|       DEFINE IDENT LPAREN identlist RPAREN LBRACE olib RBRACE olib
        { (Define($2, $4, $7)) :: $9 }
| 
        { [] }

oall:
        olib PROCESS oprocess EOF
        { $1, PSingleProcess $3 }
|       olib EQUIVALENCE oprocess oprocess optpublicvars EOF
        { $1, PEquivalence($3, $4, $5) }
|       olib QUERY_EQUIV eqname eqmember EQUIVLEFT HELP EQUIVRIGHT optpriority eqmember EOF
        { $1, PQueryEquiv($3, EquivNormal($4, $9, (PPZero,parse_extent())), $8) }

/* Collision matrix, for special equivalences */

collision_matrix:
    necollision_matrix
    { $1 }
|   IDENT IDENT EOF
    { match $1, $2 with
    | ("no",_), ("collisions",_) -> []
    | _ -> raise Parsing.Parse_error }
  
necollision_matrix:
    one_coll EOF
    { [ $1 ] }
|   one_coll SEMI necollision_matrix
    { $1 :: $3 }

one_coll:
    /* make explicit the first IDENT COMMA to avoid a shift reduce conflict */
    IDENT COMMA neidentlist IDENT IDENT IDENT IDENT neidentlist
    { match $4, $5, $6, $7 with
    | ("may",_), ("collide",_), ("with",_), ("previous",_) -> ($1::$3, $8)
    | _ -> raise Parsing.Parse_error }
|   IDENT IDENT IDENT IDENT IDENT neidentlist
    { match $2, $3, $4, $5 with
    | ("may",_), ("collide",_), ("with",_), ("previous",_) -> ([$1], $6)
    | _ -> raise Parsing.Parse_error }
