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
  
/* Precedence (from low to high) and associativities */
%left BAR
%right OR
%right AND
%left ADD SUB
%left MUL DIV
%nonassoc EQUAL
%nonassoc DIFF
%nonassoc REPL
    
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

%start allowed_coll
%type <((Ptree.ident * int) list * Ptree.ident option) list> allowed_coll

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
|       PROBA IDENT DOT 
        { [ProbabilityDecl($2)] }
|       CONST neidentlist COLON IDENT DOT 
        { List.map (fun x -> (ConstDecl(x,$4))) $2 }
|       TYPE IDENT options DOT 
        { [TypeDecl($2,$3)] }
|       PROOF LBRACE proof RBRACE 
        { [Proofinfo($3)] }
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
  
lib:
        commonlibelem lib
        { $1 @ $2 }
|	LET IDENT EQUAL process DOT lib
	{ (PDef($2,[],$4)) :: $6 }
|	LET IDENT LPAREN vartypeilist RPAREN EQUAL process DOT lib
	{ (PDef($2,$4,$7)) :: $9 }
|       CHANNEL neidentlist DOT lib 
        { (List.map (fun x -> (ChannelDecl(x))) $2) @ $4 }
|       EQUIV eqname eqmember EQUIVLEFT probaf EQUIVRIGHT optpriority eqmember DOT lib
        { (EqStatement($2, $3, $8, $5, $7)) :: $10 }
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


prooftoken:
        IDENT
        { $1 }
|       STRING
        { $1 }
|       INT
        { string_of_int $1, parse_extent() }
|       MUL
        { "*", parse_extent() }
|       DOT
        { ".", parse_extent() }
|       SET
        { "set", parse_extent() }
|       INSERT
        { "insert", parse_extent() }
|       EQUAL
        { "=", parse_extent() }
|       COMMA
        { ",", parse_extent() }
|       LPAREN
        { "(", parse_extent() }
|       RPAREN
        { ")", parse_extent() }

proofcommand:
        prooftoken
        { [$1] }
|       prooftoken proofcommand
        { $1 :: $2 }

proof:
        proofcommand
	{ [$1] }
|       proofcommand SEMI proof
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

nevartypelist:
        IDENT COLON IDENT
        { [($1, $3)] }
|       IDENT COLON IDENT COMMA nevartypelist
        { ($1, $3) :: $5 }

forallvartype:
        FORALL nevartypelist SEMI
        { $2 }
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
| 	NEW IDENT newarg COLON IDENT SEMI term
	{ PResE($2, $5, $7), parse_extent() }
| 	IDENT RANDOM IDENT SEMI term
	{ PResE($1, $3, $5), parse_extent() }
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
| 	NEW IDENT newarg COLON IDENT optprocess
	{ PRestr($2, $5, $6), parse_extent() }
| 	IDENT RANDOM IDENT optprocess
	{ PRestr($1, $3, $4), parse_extent() }
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
| vartypei
    { let (id, ty) = $1 in PPatVar(id,Some ty), parse_extent() }

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
| 	NEW IDENT COLON IDENT SEMI procasterm
	{ PResE($2, $4, $6), parse_extent() }
| 	IDENT RANDOM IDENT SEMI procasterm
	{ PResE($1, $3, $5), parse_extent() }
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


funmode:
    fungroup
    { $1,None, parse_extent() }
|   fungroup LBRACKET IDENT RBRACKET
    { $1,Some $3, parse_extent() }

newlist:
    
    { [] }
|   NEW IDENT COLON IDENT SEMI newlist
    { ($2,$4)::$6 }
|   IDENT RANDOM IDENT SEMI newlist
    { ($1,$3)::$5 }

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
|   NEW IDENT COLON IDENT options SEMI newlistfunlist
    { let (n,r) = $7 in (($2,$4,$5)::n), r }
|   IDENT RANDOM IDENT options SEMI newlistfunlist
    { let (n,r) = $6 in (($1,$3,$4)::n),r }

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
        { [$1] }
|       vartypei COMMA nevartypeilist
        { $1 :: $3 }

vartypei:
        IDENT COLON IDENT
        { ($1, Tid $3) }
|       IDENT LEQ IDENT
        { ($1, TBound $3) }
    
fungroup:
|   IDENT LPAREN vartypeilist RPAREN optpriority DEF procasterm 
    { PFun($1, $3, $7, $5) }
|   repl newlistfunlist 
    { let (i,n) = $1 in let (news,r) = $2 in
      PReplRestr((ref None, i, n), news, r) }

probaf:
        LPAREN probaf RPAREN
        { $2 }
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

/* Instructions, for manual insertion of an instruction in a game */

instruct:
    NEW IDENT COLON IDENT 
    { PRestr($2, $4, (PYield, parse_extent())), parse_extent() }
|   IDENT RANDOM IDENT 
    { PRestr($1, $3, (PYield, parse_extent())), parse_extent() }
|   IF findcond THEN
    { 
      let yield = (PYield, parse_extent()) in
      match $2 with
	([], t) -> PTest(t, yield, yield), parse_extent()
      | (def_list, t) -> 
	  PFind([(ref [], [], def_list, t, yield)], yield, []), parse_extent()
    }
|   FIND findlistins
    { PFind($2, (PYield, parse_extent()), []), parse_extent() }
|   EVENT IDENT
    { PEvent((PFunApp($2, []), parse_extent()), (PYield, parse_extent())), parse_extent() }
|   EVENT IDENT LPAREN termseq RPAREN 
    { PEvent((PFunApp($2, $4), parse_extent()), (PYield, parse_extent())), parse_extent() }
|   basicpattern LEFTARROW term 
    { PLet($1,$3,(PYield, parse_extent()),(PYield, parse_extent())), parse_extent() }
|   LET pattern EQUAL term IN
    { PLet($2,$4,(PYield, parse_extent()),(PYield, parse_extent())), parse_extent() }

findoneins:
    tidentseq SUCHTHAT findcond THEN 
    { let (def_list, t) = $3 in
      (ref [], $1, def_list, t, (PYield, parse_extent())) }

findlistins:
    findoneins
    { [$1] }
|   findoneins ORFIND findlistins
    { $1 :: $3 }

    
/* Limits on elimination of collisions */

factor:
    IDENT
    { ($1, 1) }
|   IDENT POWER INT
    { ($1, $3) }

num:
    factor MUL num
    { $1 :: $3 }
|   factor
    { [$1] }

quot:
    num DIV IDENT
    { ($1, Some $3) }
|   COLLISION MUL num
    { ($3, None) }

allowed_coll:
    quot
    { [$1] }
|   quot COMMA allowed_coll
    { $1 :: $3 }

/* User information for the cryptographic transformation */

identmapping:
    IDENT MAPSTO IDENT
    { [$1,$3] }
|   IDENT MAPSTO IDENT COMMA identmapping
    { ($1,$3)::$5 }

occ:
    INT
    { POccInt($1) }
| IDENT STRING /* "before regexp" or "after regexp" */
    { POccIdRegexp($1, $2) }
| IDENT INT STRING /* "before_nth n regexp", "after_nth n regexp", or "at m regexp" */
    { POccIdNRegexp($1, $2, $3) }
| IDENT INT INT STRING /* "at_nth n n' regexp" */
    { POccIdNNRegexp($1, $2, $3, $4) }
    
occidentmapping:
    occ MAPSTO IDENT
    { [$1,$3] }
|   occ MAPSTO IDENT COMMA occidentmapping
    { ($1,$3)::$5 }

detailedinfo:
    IDENT COLON identmapping
    { PVarMapping($1, $3, false) }
|   IDENT COLON identmapping DOT
    { PVarMapping($1, $3, true) }
|   IDENT COLON occidentmapping
    { PTermMapping($1, $3, false) }
|   IDENT COLON occidentmapping DOT
    { PTermMapping($1, $3, true) }

detailedinfolist:
    detailedinfo
    { [$1] }
|   detailedinfo SEMI detailedinfolist
    { $1::$3 }

neidentlistnosep:
        IDENT 
        { [$1] }
|       IDENT neidentlistnosep
        { $1 :: $2 }

cryptotransfinfo:
    
    { PVarList([],false) }
|   MUL
    { PRepeat }
|   neidentlistnosep
    { PVarList($1, false) }
|   neidentlistnosep DOT
    { PVarList($1, true) }
|   detailedinfolist
    { PDetailed($1) }

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
| 	NEW IDENT COLON IDENT optoprocess
	{ PRestr($2, $4, $5), parse_extent() }
| 	IDENT RANDOM IDENT optoprocess
	{ PRestr($1, $3, $4), parse_extent() }
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

olib:
        commonlibelem olib
        { $1 @ $2 }
|	LET IDENT EQUAL oprocess DOT olib
	{ (PDef($2,[],$4)) :: $6 }
|	LET IDENT LPAREN vartypeilist RPAREN EQUAL oprocess DOT olib
	{ (PDef($2,$4,$7)) :: $9 }
|       EQUIV eqname eqmember EQUIVLEFT oprobaf EQUIVRIGHT optpriority eqmember DOT olib
        { (EqStatement($2, $3, $8, $5, $7)) :: $10 }
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

