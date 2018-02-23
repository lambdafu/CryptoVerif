open Ptree
open Parsing_helper
open Types
open Terms

(* Parse a file *)

let parse filename =
  try
    let ic = open_in filename in
    let lexbuf = Lexing.from_channel ic in
    lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with 
                                  Lexing.pos_fname = filename };    
    let ptree =
      try
	if (!Settings.front_end) == Settings.Channels then
          Parser.all Lexer.token lexbuf
	else
	  Parser.oall Lexer.token lexbuf
      with 
	Parsing.Parse_error ->
          input_error "Syntax error" (extent lexbuf)
      |	Error(s,ext) ->
	  input_error s ext
    in
    close_in ic;
    ptree
  with Sys_error s ->
    user_error ("File error: " ^ s ^ "\n")

let parse_lib filename =
  let filename = filename ^ (if (!Settings.front_end) == Settings.Channels then ".cvl" else ".ocvl") in
  try
    let ic = open_in filename in
    let lexbuf = Lexing.from_channel ic in
    lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with 
                                  Lexing.pos_fname = filename };    
    let ptree =
      try
	if (!Settings.front_end) == Settings.Channels then
          Parser.lib Lexer.token lexbuf
	else
	  Parser.olib Lexer.token lexbuf
      with Parsing.Parse_error ->
        input_error "Syntax error" (extent lexbuf)
    in
    close_in ic;
    ptree
  with Sys_error s ->
    user_error ("File error: " ^ s ^ "\n")

let parse_with_lib filename =
  let l1 = parse_lib (!Settings.lib_name) in
  let (l,p) = parse filename in
  (l1 @ l, p)

(* Environment.
   May contain function symbols, variables, ...
   Is a map from strings to the description of the ident *)

open Stringmap
  
let init_env () =
  Terms.record_id "true" dummy_ext;
  Terms.record_id "false" dummy_ext;
  Terms.record_id "not" dummy_ext;
  Terms.record_id "bitstring" dummy_ext;
  Terms.record_id "bitstringbot" dummy_ext;
  Terms.record_id "bool" dummy_ext;
   let m = StringMap.empty in
   let m1 = StringMap.add "true" (EFunc Settings.c_true)
       (StringMap.add "false" (EFunc Settings.c_false)
	  (StringMap.add "not" (EFunc Settings.f_not) m)) in
   StringMap.add "bitstring" (EType Settings.t_bitstring)
     (StringMap.add "bitstringbot" (EType Settings.t_bitstringbot)
	(StringMap.add "bool" (EType Settings.t_bool) m1))

type location_type =
    InProcess
  | InEquivalence

let current_location = ref InProcess

(* Declarations *)

type macro_elem =
    Macro of Ptree.ident list * Ptree.decl list * string list * macro_elem Stringmap.StringMap.t
    
let macrotable = ref StringMap.empty
let statements = ref ([]: statement list)
let collisions = ref ([]: collision list)
let equivalences = ref ([]: equiv list)
let move_new_eq = ref ([]: (typet * equiv) list)
let queries_parse = ref ([]: Ptree.query list)
let proof = ref (None : Ptree.ident list list option)

let implementation = ref ([]: Ptree.impl list)
let impl_roles = ref StringMap.empty

let event_type_list = ref []

(* Check types *)

let check_type ext e t =
  if (e.t_type != t) && (e.t_type != Settings.t_any) && (t != Settings.t_any) then
    input_error ("This expression has type " ^ e.t_type.tname ^ " but expects type " ^ t.tname) ext

let check_bit_string_type ext t =
  match t.tcat with
    BitString -> ()
  | _ -> input_error "Some bitstring type expected" ext

let rec check_type_list ext pel el tl =
  match (pel, el, tl) with
    [],[],[] -> ()
  | (pe::pel, e::el, t::tl) ->
      check_type (snd pe) e t;
      check_type_list ext pel el tl
  | _ ->
      input_error ("Unexpected number of arguments") ext

let rec check_array_type_list ext pel el cur_array creation_array =
  match (pel, el, creation_array) with
    [],[],[] -> []
  | [],[],_ -> 
      (* Allow incomplete array arguments. They are automatically
         completed with cur_array *)
      let n = (List.length cur_array) - (List.length creation_array) in
      if n < 0 then 
	input_error "Unexpected number of array specifiers" ext;
      let cur_array_rest = skip n cur_array in
      if List.for_all2 (==) cur_array_rest creation_array then
	List.map Terms.term_from_repl_index cur_array_rest
      else
	input_error "Unexpected number of array specifiers" ext
  | (pe::pel, e::el, t::tl) ->
      check_type (snd pe) e t.ri_type;
      e::(check_array_type_list ext pel el cur_array tl)
  | _ ->
      input_error ("Unexpected number of array specifiers") ext

(**** First pass: build binder_env ****)

(* Check terms *)

(* Should the indexes bound by find be added in the environment
   for future array references? Yes for normal terms,
   no in terms of equivalences. *)
let add_find = ref true

let pinstruct_name = function
    PIdent _ -> "ident"
  | PArray _ -> "array reference"
  | PFunApp _ | PEqual _ | PDiff _ | PAnd _ | POr _ -> "function application"
  | PTuple _ -> "tuple"
  | PTestE _ -> "if"
  | PLetE _ -> "let"
  | PFindE _ -> "find"
  | PResE _ -> "new"
  | PEventAbortE _ -> "event_abort"
  | PEventE _ -> "event"
  | PGetE _ -> "get"
  | PInsertE _ -> "insert"
  | PQEvent _ -> "query event"
    
let rec check_simple_term1 ref = function
  | PIdent _, _ -> ()
  | (PArray(_,l) | PFunApp(_,l) | PTuple(l)), _ ->
      List.iter (check_simple_term1 ref) l
  | (PEqual(t1,t2) | PDiff(t1,t2) | PAnd(t1,t2) | POr(t1,t2)), _ ->
      check_simple_term1 ref t1; check_simple_term1 ref t2
  | t, ext ->
      Parsing_helper.input_error ((pinstruct_name t) ^ " should not occur in " ^ ref) ext

let check_br1 (_,tl) = 
  List.iter (check_simple_term1 "defined conditions") tl

let add_var_list env in_find_cond cur_array bindl =
  List.fold_left (fun env (s, tyopt) ->
    if in_find_cond then
      add_in_env1error env error_find_cond s
    else
      match tyopt with
	None -> add_in_env1error env error_no_type s
      | Some ty -> add_in_env1 env s ty cur_array
	    ) env bindl


(* [check_term1 binder_env in_find_cond cur_array t] returns
   a binder environment containing the variables of [binder_env]
   plus those defined by [t]. 
   [in_find_cond] is true when [t] is in a condition of find or get. *)
    
let rec check_term1 binder_env in_find_cond cur_array = function
    PIdent (s, ext), ext2 -> binder_env
  | (PArray(_, tl) | PFunApp(_, tl) | PTuple(tl)), ext -> 
      check_term_list1 binder_env in_find_cond cur_array tl
  | PTestE(t1, t2, t3), ext ->
      union_both
	(check_term1 binder_env in_find_cond cur_array t1)
	(union_exclude
	   (check_term1 empty_binder_env in_find_cond cur_array t2)
	   (check_term1 empty_binder_env in_find_cond cur_array t3))
  | PFindE(l0,t3,_), ext ->
      let env_branches = ref (check_term1 empty_binder_env in_find_cond cur_array t3) in
      let env_common = ref binder_env in
      List.iter (fun (bl_ref, bl,def_list,t1,t2) ->
	let bl_repl_index = 
	  List.map (fun ((s0,ext0),(s1,ext1),(s2,ext2)) ->
	    let p = get_param (!env) s2 ext2 in
	    let t = type_for_param p in
	    (* Create a replication index *)
	    Terms.create_repl_index s1 t
	      ) bl
	in
	bl_ref := bl_repl_index;
	let cur_array' = bl_repl_index @ cur_array in
	(* The defined condition defines no variable *)
	List.iter check_br1 def_list;
	(* The condition is evaluated in all branches *)
	env_common := check_term1 (!env_common) true cur_array' t1;
	(* The then branch and the variables storing the found indices
           are used only in the successful branch *)
	env_branches := union_exclude (!env_branches)
	     (List.fold_left2 (fun env ri ((s0,ext0),_,_) ->
	       let t = ri.ri_type in
	       if in_find_cond then
		 add_in_env1error env error_find_cond s0
	       else if !add_find then
		 add_in_env1 env s0 t cur_array
	       else 
		 add_in_env1error env error_find_index_in_equiv s0
		   ) (check_term1 empty_binder_env in_find_cond cur_array t2) bl_repl_index bl)
	     ) l0;
      union_both (!env_common) (!env_branches)
  | PLetE(pat, t1, t2, topt), ext ->
      let (env_pat, bindl) = check_pattern1 binder_env in_find_cond cur_array false pat in
      let env_cond_pat = check_term1 env_pat in_find_cond cur_array t1 in
      let env_in = check_term1 empty_binder_env in_find_cond cur_array t2 in
      let env_else = 
	match topt with
	  None -> empty_binder_env
	| Some t3 -> check_term1 empty_binder_env in_find_cond cur_array t3
      in
      union_both env_cond_pat
	(union_exclude
	   (add_var_list env_in in_find_cond cur_array bindl)
	   env_else)
  | PResE((s1,ext1),(s2,ext2),t), ext ->
      let ty' = get_type (!env) s2 ext2 in
      let env_new = 
	if in_find_cond then
	  add_in_env1error binder_env error_find_cond s1
	else
	  add_in_env1 binder_env s1 ty' cur_array
      in
      check_term1 env_new in_find_cond cur_array t
  | PEventAbortE(id), ext -> binder_env
  | PEventE(t,p), _ ->
      let env_t = check_term1 binder_env in_find_cond cur_array t in
      check_term1 env_t in_find_cond cur_array p
  | PGetE(tbl, patlist, topt, p1, p2), _ ->
      (* After conversion of get into find, patlist and topt will
	 appear in conditions of find. 
	 We must appropriately forbid array accesses to the variables they define,
	 so we set [in_find_cond] to true for them. *)
      let (env_pat, bindl) = check_pattern_list1 binder_env true cur_array false patlist in
      let env_cond_pat = 
	match topt with
	  Some t -> check_term1 env_pat true cur_array t
	| None -> env_pat
      in
      let env_in = check_term1 empty_binder_env in_find_cond cur_array p1 in
      let env_else = check_term1 empty_binder_env in_find_cond cur_array p2 in
      union_both
	env_cond_pat
	(union_exclude
	   (add_var_list env_in true cur_array bindl)
	   env_else)
  | PInsertE(tbl,tlist,p),_ ->
      let env_tlist = check_term_list1 binder_env in_find_cond cur_array tlist in
      check_term1 env_tlist in_find_cond cur_array p
  | (PEqual(t1,t2) | PDiff(t1,t2) | PAnd(t1,t2) | POr(t1,t2)), ext ->
      let env_t1 = check_term1 binder_env in_find_cond cur_array t1 in
      check_term1 env_t1 in_find_cond cur_array t2
  | PQEvent _,ext -> 
      Parsing_helper.input_error "event(...) and inj-event(...) allowed only in queries" ext

and check_term_list1 binder_env in_find_cond cur_array = function
    [] -> binder_env
  | t::l ->
      let env_t = check_term1 binder_env in_find_cond cur_array t in
      check_term_list1 env_t in_find_cond cur_array l

(* Check pattern
   [check_pattern1 binder_env in_find_cond cur_array needtype pat] returns
   a pair containing:
   - a binder environment containing the variables of [binder_env]
   plus those defined by terms [t] in subpatterns [=t] of [pat].
   - the list of variables bound by [pat], with their type [Some ty]
   or [None] when the type is not mentioned in the pattern.

   [in_find_cond] is true when [t] is in a condition of find or get.

   [needtype] is true when the type of the pattern cannot be inferred
   from the outside; in this case, when the pattern is a variable,
   its type must be explicitly given. *)

and check_pattern1 binder_env in_find_cond cur_array needtype = function
    PPatVar ((s1,ext1), tyopt), _ ->
      begin
	match tyopt with
	  None -> 
	    if needtype then
	      input_error "type needed for this variable" ext1
	    else
	      (binder_env, [s1, None])
	| Some ty ->
	    let (ty',_) = get_ty (!env) ty in
	    (binder_env, [s1, Some ty'])
      end
  | PPatTuple l, _ ->
      check_pattern_list1 binder_env in_find_cond cur_array true l
  | PPatFunApp(f,l), _ ->
      check_pattern_list1 binder_env in_find_cond cur_array false l
  | PPatEqual t, _ ->
      (check_term1 binder_env in_find_cond cur_array t, [])

and check_pattern_list1 binder_env in_find_cond cur_array needtype = function
    [] -> (binder_env, [])
  | pat1::patl ->
      let (env1, bind1) = check_pattern1 binder_env in_find_cond cur_array needtype pat1 in
      let (envl1, bindl) = check_pattern_list1 env1 in_find_cond cur_array needtype patl in
      (envl1, bind1 @ bindl)
	
(* Check equivalence statements *)

let check_binder1 cur_array binder_env ((s1,ext1),(s2,ext2),opt) = 
  let t = get_type (!env) s2 ext2 in
  add_in_env1 binder_env s1 t cur_array

let check_binderi1 cur_array binder_env ((s1,ext1),tyb) =
  let (ty, _) = get_ty (!env) tyb in
  add_in_env1 binder_env s1 ty cur_array

let rec check_fungroup1 cur_array binder_env = function
    PReplRestr((repl_index_ref, idopt, (rep,ext)), restrlist, funlist) ->
      let pn = get_param (!env) rep ext in
      let t = type_for_param pn in 
      let b = Terms.create_repl_index
	  (match idopt with 
	    None -> "i" 
	  | Some(id,ext) -> id) t
      in
      repl_index_ref := Some b;
      let cur_array' = b :: cur_array in
      let env_funlist = List.fold_left (check_fungroup1 cur_array') binder_env funlist in
      List.fold_left (check_binder1 cur_array') env_funlist restrlist
  | PFun(_, arglist, tres, _) ->
      List.fold_left (check_binderi1 cur_array) 
	(add_find := false;
	 let env_res = check_term1 binder_env false cur_array tres in
	 add_find := true;
	 env_res) arglist

let check_rm_restr1 cur_array restrlist0 binder_env ((s1,ext1),(s2,ext2),opt) =
  let t = get_type (!env) s2 ext2 in
  if t.toptions land Settings.tyopt_CHOOSABLE == 0 then
    input_error ("Cannot choose randomly a bitstring from " ^ t.tname) ext2;
  let (unchanged, ext) = 
    match opt with
      [] -> (false, Parsing_helper.dummy_ext)
    | ["unchanged", ext] -> (true, ext)
    | (_,ext)::_ -> 
	input_error "The only allowed option for restrictions is [unchanged]" ext
  in
  try
    (* When there is variable in the left-hand side with the same name, try to reuse that name *)
    let (_,(b0,_)) =
      List.find (fun (((s1',_),_,_), (b0,_)) ->
	s1' = s1 && b0.btype == t) restrlist0
    in
    add_in_env1reusename binder_env s1 b0 t cur_array
  with
    Not_found ->
      (* List.find failed *)
      if unchanged then 
	input_error "When a restriction is marked [unchanged] in the right-hand side,\nthere should exist a corresponding restriction of the same name in the\nleft-hand side" ext
      else
	add_in_env1 binder_env s1 t cur_array
  | Failure _ ->
      (* add_in_env1reusename failed *)
      if unchanged then 
	input_error "When a restriction is marked [unchanged] in the right-hand side,\nthere should exist a single variable with that name" ext
      else
	add_in_env1 binder_env s1 t cur_array

let rec check_rm_fungroup1 cur_array binder_env plm_fg lm_fg rm_fg =
  match (plm_fg, lm_fg, rm_fg) with
    PReplRestr(_, prestrlist0, pfunlist0),
    ReplRestr(_, restrlist0, funlist0),
    PReplRestr((repl_index_ref, idopt, (rep,ext)), restrlist, funlist) ->
      let pn = get_param (!env) rep ext in
      let t = type_for_param pn in 
      let b = Terms.create_repl_index
	  (match idopt with 
	    None -> "i" 
	  | Some(id,ext) -> id) t
      in
      repl_index_ref := Some b;
      let cur_array' = b :: cur_array in
      if List.length funlist != List.length funlist0 then
	input_error "Different number of functions in left and right sides of equivalence" ext;
      List.fold_left (check_rm_restr1 cur_array' (List.combine prestrlist0 restrlist0)) 
	(check_rm_fungroup_list1 cur_array' binder_env pfunlist0 funlist0 funlist) restrlist
  | _, _, PFun(_, arglist, tres, _) ->
      List.fold_left (check_binderi1 cur_array) 
	(add_find := false;
	 let env_res = check_term1 binder_env false cur_array tres in
	 add_find := true;
	 env_res) arglist
  | _, _, PReplRestr((_, _, (_,ext)), _,_) ->
      input_error "Left member is a function, right member is a replication" ext

and check_rm_fungroup_list1 cur_array binder_env pfunlist0 funlist0 funlist =
  match pfunlist0, funlist0, funlist with
    [],[],[] -> binder_env
  | a1::r1, a2::r2, a3::r3 ->
      let env_a = check_rm_fungroup1 cur_array binder_env a1 a2 a3 in
      check_rm_fungroup_list1 cur_array env_a r1 r2 r3
  | _ -> Parsing_helper.internal_error "Lists should have same length in check_rm_fungroup_list1"
	   
let rec check_rm_funmode_list binder_env pfunlist0 funlist0 funlist =
  match pfunlist0, funlist0, funlist with
    [],[],[] -> binder_env
  | (plm_fg,_,_) ::r1, (lm_fg,_)::r2, (fg, _, _):: r3 ->
      let env_a = check_rm_fungroup1 [] binder_env plm_fg lm_fg fg in
      check_rm_funmode_list env_a r1 r2 r3
  | _ -> Parsing_helper.internal_error "Lists should have same length in check_rm_funmode_list"

(* Check process *)

let rec check_process1 binder_env cur_array = function
  | PBeginModule (_,p),_ ->
      check_process1 binder_env cur_array p
  | PNil, _ -> binder_env
  | PPar(p1,p2), _ -> 
      let env_p1 = check_process1 binder_env cur_array p1 in
      check_process1 env_p1 cur_array p2
  | PRepl(repl_index_ref,idopt,(s2,ext2),p), _ ->
      let pn = get_param (!env) s2 ext2 in
      let t = type_for_param pn in 
      let b = Terms.create_repl_index
	  (match idopt with 
	      None -> "i" 
	    | Some(id,ext) -> id) t 
      in
      repl_index_ref := Some b;
      check_process1 binder_env (b::cur_array) p
  | PInput(c, pat, p), _ ->
      let (pat_env, bindl) = check_pattern1 binder_env false cur_array true pat in
      let env_cont_pat = check_oprocess1 pat_env cur_array p in
      add_var_list env_cont_pat false cur_array bindl
  | PLetDef((s,ext), args), _ ->
      let (env', vardecl, p) = get_process (!env) s ext in
      List.iter (check_simple_term1 "argument of a parametric input process") args;
      (* I will not be able to make array references to the arguments of the process. That's too tricky because we need to move the definition of these variables to an output process above or below. *)
      let env_var = 
	List.fold_left (fun binder_env ((s1,ext1), ty) ->
	  let _ = get_ty (!env) ty in
	  add_in_env1error binder_env error_in_input_process s1
	    ) binder_env vardecl
      in
      check_process1 env_var cur_array p
  | _, ext ->
      input_error "input process expected" ext

and check_oprocess1 binder_env cur_array = function
  | PYield, _ | PEventAbort(_), _ -> binder_env
  | PRestr((s1,ext1),(s2,ext2),p), _ ->
      let t = get_type (!env) s2 ext2 in
      let env_new = add_in_env1 binder_env s1 t cur_array in
      check_oprocess1 env_new cur_array p
  | PLetDef((s,ext), args), _ ->
      let (env', vardecl, p) = get_process (!env) s ext in
      let env_args = check_term_list1 binder_env false cur_array args in
      let env_args_vars =
	List.fold_left (fun binder_env ((s1,ext1), ty) ->
	  let (ty',_) = get_ty (!env) ty in
	  add_in_env1 binder_env s1 ty' cur_array
	    ) env_args vardecl
      in
      check_oprocess1 env_args_vars cur_array p
  | PTest(t,p1,p2), _ ->
      union_both
	(check_term1 binder_env false cur_array t)
	(union_exclude
	   (check_oprocess1 empty_binder_env cur_array p1)
	   (check_oprocess1 empty_binder_env cur_array p2))
  | PFind(l0,p2,_), _ ->
      let env_branches = ref (check_oprocess1 empty_binder_env cur_array p2) in
      let env_common = ref binder_env in
      List.iter (fun (bl_ref,bl,def_list,t,p1) ->
	let bl_repl_index = 
	  List.map (fun ((s0,ext0),(s1,ext1),(s2,ext2)) ->
	    let p = get_param (!env) s2 ext2 in
	    let t = type_for_param p in
	    (* Create a replication index *)
	    Terms.create_repl_index s1 t
	      ) bl
	in
	bl_ref := bl_repl_index;
	let cur_array' = bl_repl_index @ cur_array in
	(* The defined condition defines no variable *)
	List.iter check_br1 def_list;
	(* The condition is evaluated in all branches *)
	env_common := check_term1 (!env_common) true cur_array' t;
	(* The then branch and the variables storing the found indices
           are used only in the successful branch *)
	env_branches := union_exclude (!env_branches)
	     (List.fold_left2 (fun env ri ((s0,ext0),_,_) ->
	       let t = ri.ri_type in
	       add_in_env1 env s0 t cur_array
		 ) (check_oprocess1 empty_binder_env cur_array p1) bl_repl_index bl)
	     ) l0;
      union_both (!env_common) (!env_branches)
  | POutput(b,c,t2,p), _ ->
      let env_t = check_term1 binder_env false cur_array t2 in
      check_process1 env_t cur_array p
  | PLet(pat, t, p1, p2), _ ->
      let (env_pat, bindl) = check_pattern1 binder_env false cur_array false pat in
      let env_cond_pat = check_term1 env_pat false cur_array t in
      let env_in = check_oprocess1 empty_binder_env cur_array p1 in
      let env_else = check_oprocess1 empty_binder_env cur_array p2  in
      union_both env_cond_pat
	(union_exclude
	   (add_var_list env_in false cur_array bindl)
	   env_else)
  | PEvent(t,p), _ ->
      let env_t = check_term1 binder_env false cur_array t in
      check_oprocess1 env_t cur_array p
  | PGet(tbl, patlist, topt, p1, p2), _ ->
      (* After conversion of get into find, patlist and topt will
	 appear in conditions of find. 
	 We must appropriately forbid array accesses to the variables they define,
	 so we set [in_find_cond] to true for them. *)
      let (env_pat, bindl) = check_pattern_list1 binder_env true cur_array false patlist in
      let env_cond_pat = 
	match topt with
	  Some t -> check_term1 env_pat true cur_array t
	| None -> env_pat
      in
      let env_in = check_oprocess1 empty_binder_env cur_array p1 in
      let env_else = check_oprocess1 empty_binder_env cur_array p2 in
      union_both
	env_cond_pat
	(union_exclude
	   (add_var_list env_in true cur_array bindl)
	   env_else)
  | PInsert(tbl,tlist,p),_ ->
      let env_tlist = check_term_list1 binder_env false cur_array tlist in
      check_oprocess1 env_tlist cur_array p
  | _, ext -> 
      input_error "non-input process expected" ext

(**************************************************************)

(* I decided to do checks one after the another to easily disable just one of
   them. *)

(* Build a list of returns corresponding to an oracle/channel name.
   [h] is a hash table containing bindings from oracle names to returns.
   [name] is the current oracle/channel name. *)
let rec build_return_list_aux h name = function
  | PNil, _ | PYield, _ | PEventAbort _, _ -> ()
  | PPar (p1, p2), _ | PTest (_, p1, p2), _ | PLet (_, _, p1, p2), _
  | PGet(_, _, _, p1, p2), _ ->
    build_return_list_aux h name p1;
    build_return_list_aux h name p2
  | PRepl (_, _, _, p), _ | PRestr (_, _, p), _ | PEvent(_, p), _
  | PInsert(_, _, p),_ | PBeginModule (_, p),_ ->
    build_return_list_aux h name p
  | PLetDef((s,ext), _), _ ->
    let (env', vardecl, p) = get_process (!env) s ext in
    build_return_list_aux h name p 
  | PFind(l, p, _), _ ->
    build_return_list_aux h name p;
    List.iter (fun (_, _, _, _, p) -> build_return_list_aux h name p) l
  | POutput(_, _, _, p), ext as o ->
    begin
      match name with
        | Some name ->
          Hashtbl.add h name o;
          build_return_list_aux h None p
        | None ->
            (* This error should be catched by [check_process] *)
            match !Settings.front_end with
              | Settings.Channels ->
                  input_error "Out present in input process part (implementation)" ext
              | Settings.Oracles ->
                  input_error "Return present in oracle description part (implementation)" ext
    end
  | PInput(((name, _), _), _, p), _ ->
    build_return_list_aux h (Some name) p

let build_return_list p =
  let h = Hashtbl.create 10 in
  build_return_list_aux h None p;
  h

(* Check that the previous oracle before a role declaration has at most one
   return. *)
let rec check_role_aux error h name = function
  | PNil, _ | PYield, _ | PEventAbort _, _ -> ()
  | PPar (p1, p2), _ | PTest (_, p1, p2), _ | PLet (_, _, p1, p2), _
  | PGet(_, _, _, p1, p2), _ ->
    check_role_aux error h name p1;
    check_role_aux error h name p2
  | PRepl (_, _, _, p), _ | PRestr (_, _, p), _ | PEvent(_, p), _
  | PInsert(_, _, p),_ | POutput(_, _, _, p), _ ->
    check_role_aux error h name p
  | PLetDef((s,ext),_), _ ->
    let (env', vardecl, p) = get_process (!env) s ext in
    check_role_aux error h name p 
  | PFind(l, p, _), _ ->
    check_role_aux error h name p;
    List.iter (fun (_, _, _, _, p) -> check_role_aux error h name p) l
  | PBeginModule (((role, _), _), p), ext ->
    begin
      match name with
        | Some name ->
          let returns = Hashtbl.find_all h name in
          if List.length returns > 1 then
            let oracle = match !Settings.front_end with
              | Settings.Channels -> "in-out block"
              | Settings.Oracles -> "oracle"
            in
            let return = match !Settings.front_end with
              | Settings.Channels -> "out construct"
              | Settings.Oracles -> "return"
            in
            error
              (Printf.sprintf
                 "Role %s is defined after %s %s that has \
                  more than one %s (implementation)"
                 role
                 oracle
                 name
                 return)
              ext
        | None -> ()
    end;
    check_role_aux error h name p
  | PInput(((name, _), _), _, p), _ ->
    check_role_aux error h (Some name) p

let check_role error h p =
  check_role_aux error h None p

(* Check that an out followed by a role declaration closes the current
   oracle. This ensures that no oracle is between two roles.
   The boolean [role_possible] indicates whether a role declaration is
   possible here. *)
let rec check_role_continuity_aux error role_possible = function
  | PNil, _ | PYield, _ | PEventAbort _, _ -> ()
  | PPar (p1, p2), _ ->
    check_role_continuity_aux error role_possible p1;
    check_role_continuity_aux error role_possible p2;
  | PTest (_, p1, p2), _ | PLet (_, _, p1, p2), _
  | PGet(_, _, _, p1, p2), _ ->
    check_role_continuity_aux error false p1;
    check_role_continuity_aux error false p2
  | PRepl (_, _, _, p), _ ->
    check_role_continuity_aux error role_possible p
  | PRestr (_, _, p), _ | PEvent(_, p), _
  | PInsert(_, _, p),_ | PInput(_, _, p), _ ->
    check_role_continuity_aux error false p
  | PLetDef((s,ext),_), _ ->
    let (env', vardecl, p) = get_process (!env) s ext in
    check_role_continuity_aux error role_possible p
  | PFind(l, p, _), _ ->
    check_role_continuity_aux error false p;
    List.iter
      (fun (_, _, _, _, p) -> check_role_continuity_aux error false p)
      l
  | POutput(role_end, _, _, p), _ ->
    check_role_continuity_aux error role_end p
  | PBeginModule (((role, _), _), p), ext ->
    if not role_possible then
      begin
        let return = match !Settings.front_end with
          | Settings.Channels -> "an out construct"
          | Settings.Oracles -> "a return"
        in
        error
          (Printf.sprintf
             "Role %s is defined after %s that does not end the \
              previous role/is not in a role (implementation)"
             role
             return)
          ext
      end;
    check_role_continuity_aux error role_possible p

let check_role_continuity error p =
  check_role_continuity_aux error true p

let check_process2 p =
  (* Do not check implementation based requirements when not compiling
     the specification into an implementation, in the channel front-end. *)
  if (!Settings.get_implementation) || (!Settings.front_end = Settings.Oracles) then
    let h = build_return_list p in
    check_role input_error h p;
    check_role_continuity input_error p
  (* We could have a warning when we do not generate an implementation,
     as follows. However, in this case, we should also have a warning
     for other errors that happen at implementation time (e.g. type errors) 
  let error_function =
    if (!Settings.get_implementation) then
      input_error
    else
      input_warning
  in
  let h = build_return_list p in
  check_role error_function h p;
  check_role_continuity error_function p *)


(* Check the form of process p to signal inefficiencies.

   The check is done on the parse tree instead of processes in order to
   get locations for warnings. *)

let warn_replication_same_name p =
  let param_tbl = Hashtbl.create 20 in
  let repl, repl', repl'' = match !Settings.front_end with
    | Settings.Channels -> "Replication", "replication", "replications"
    | Settings.Oracles -> "Foreach", "foreach", "foreach"
  in
  let add_and_warn param loc =
    begin
      try
        let witness = Hashtbl.find param_tbl param in
        Parsing_helper.input_warning
          (Printf.sprintf "%s uses the same parameter %s as %s at %s. \
          Avoid reusing parameters for multiple %s to avoid losing precision \
          in the probability bound." repl param repl' (in_file_position loc witness) repl'')
          loc
      with Not_found -> ()
    end;
    Hashtbl.add param_tbl param loc
  in
  let rec gather_replication_params = function
    | PRepl(_, _, (bound, loc), p), _ ->
      add_and_warn bound loc;
      gather_replication_params p

    | PNil, _ | PYield, _ | PEventAbort _, _ -> ()
    | PPar(p1, p2), _
    | PTest(_, p1, p2), _ | PLet (_, _, p1, p2), _
    | PGet(_, _, _, p1, p2), _ ->
      gather_replication_params p1;
      gather_replication_params p2
    | PInput (_, _, p), _ | PRestr (_, _, p), _ | PEvent(_, p), _
    | PInsert(_, _, p),_ | PBeginModule (_, p),_ 
    | POutput(_, _, _, p), _ ->
      gather_replication_params p
    | PLetDef((s,ext),_), _ ->
      let (env', vardecl, p) = get_process (!env) s ext in
      gather_replication_params p
    | PFind(l, p, _), _ ->
      gather_replication_params p;
      List.iter
        (fun (_, _, _, _, p) -> gather_replication_params p)
        l
  in
  gather_replication_params p

let warn_parallel_or_replication_after_replication i =
  let repl = match !Settings.front_end with
    | Settings.Channels -> "replication"
    | Settings.Oracles -> "foreach"
  in
  let warn_parallel_after_replication locp locr =
    Parsing_helper.input_warning
      (Printf.sprintf "Parallel at %s after %s. To avoid \
         losing precision in the probability bound, you should \
         rather put a distinct replication above each component \
         of the parallel composition."
         (in_file_position locr locp)
         repl)
      locr
  in
  let warn_replication_after_replication locr1 locr2 =
    Parsing_helper.input_warning
      (Printf.sprintf "Useless %s at %s after %s. Avoid this to \
         avoid losing precision in the probability bound."
         repl
         (in_file_position locr2 locr1)
         repl)
      locr2
  in
  let rec aux after_repl = function
    | PRepl(_, _, _, p), loc ->
      begin
        match after_repl with
          | Some r -> warn_replication_after_replication loc r
          | None -> ()
      end;
      aux (Some loc) p

    | PPar(p1, p2), loc ->
      begin
        match after_repl with
          | Some r -> warn_parallel_after_replication loc r
          | None -> ()
      end;
      aux after_repl p1;
      aux after_repl p2

    | PInput (_, _, p), _ ->
      aux None p

    | PNil, _ | PYield, _ | PEventAbort _, _ -> ()
    | PTest(_, p1, p2), _ | PLet (_, _, p1, p2), _
    | PGet(_, _, _, p1, p2), _ ->
      aux after_repl p1;
      aux after_repl p2
    | PRestr (_, _, p), _ | PEvent(_, p), _
    | PInsert(_, _, p),_ | PBeginModule (_, p),_ 
    | POutput(_, _, _, p), _ ->
      aux after_repl p
    | PLetDef((s,ext),_), _ ->
      let (env', vardecl, p) = get_process (!env) s ext in
      aux after_repl p
    | PFind(l, p, _), _ ->
      aux after_repl p;
      List.iter
        (fun (_, _, _, _, p) -> aux after_repl p)
        l
  in
  aux None i

let warn_process_form p =
  warn_replication_same_name p;
  warn_parallel_or_replication_after_replication p



(**** Second pass: type check everything ****)

(* Add a binder in the environment *)

let add_in_env env s ext t cur_array =
  if (StringMap.mem s env) then
    input_warning ("identifier " ^ s ^ " rebound") ext;
  match get_global_binder_if_possible s with
    Some b -> 
      (StringMap.add s (EVar b) env, b)
  | None ->
      let b = Terms.create_binder s t cur_array in
      (StringMap.add s (EVar b) env, b)
	
(* Add a binder in the environment of a letfun. These binders are to be replaced by new binders when used *)

let add_in_env_letfun env s ext t =
  if (StringMap.mem s env) then
    input_warning ("identifier " ^ s ^ " rebound") ext;
  let b = Terms.create_binder0 s t [] in
  (StringMap.add s (EVar b) env, b)	

(* Check that t does not contain if/find/let/new/event/get/insert *)

let instruct_name t =
  match t.t_desc with
    Var _ -> "variable"
  | ReplIndex _ -> "replication index"
  | FunApp _ -> "function application"
  | TestE _ -> "if"
  | LetE _ -> "let"
  | FindE _ -> "find"
  | ResE _ -> "new"
  | EventAbortE _ -> "event_abort"
  | EventE _ -> "event"
  | GetE _ -> "get"
  | InsertE _ -> "insert"
    
let rec check_no_iffindletnewevent ref ext t =
  match t.t_desc with
  | Var (_,l) | FunApp(_,l) ->
      List.iter (check_no_iffindletnewevent ref ext) l
  | ReplIndex _ -> ()
  | TestE _ | LetE _ | FindE _ | ResE _ | EventAbortE _ | EventE _ | GetE _ | InsertE _ ->
      Parsing_helper.input_error ((instruct_name t) ^ " at " ^ (in_file_position ext t.t_loc) ^
				  " should not occur in "^ref) ext

(* Check that t does not contain new, event, insert *)

let rec check_no_new_event_insert ext is_get t =
  match t.t_desc with
  | Var (_,l) | FunApp(_,l) ->
      List.iter (check_no_new_event_insert ext is_get) l
  | ReplIndex _ -> ()
  | TestE(t1,t2,t3) ->
      check_no_new_event_insert ext is_get t1;
      check_no_new_event_insert ext is_get t2;
      check_no_new_event_insert ext is_get t3
  | LetE(pat,t1,t2,topt) ->
      check_no_new_event_insert_pat ext is_get pat;
      check_no_new_event_insert ext is_get t1;
      check_no_new_event_insert ext is_get t2;
      begin
	match topt with
	  None -> ()
	| Some t3 -> check_no_new_event_insert ext is_get t3
      end
  | FindE(l0,t3,_) ->
   (*   if is_get then
	begin
	  match l0 with
	    [([],def_list,_,_)] -> ()
	      (* This find is in fact a if, so ok *)
	  | _ ->
	      Parsing_helper.input_error ("find at " ^ (in_file_position ext t.t_loc) ^
					  " is not allowed in condition of get") ext
	end; *)
      List.iter (fun (bl,def_list,t1,t2) ->
	(* def_list will be checked by check_no_iffindletnew
	   when translating this find *)
	check_no_new_event_insert ext is_get t1;
	check_no_new_event_insert ext is_get t2) l0;
      check_no_new_event_insert ext is_get t3
  | GetE(table, patl, topt, t1,t2) ->
      List.iter (check_no_new_event_insert_pat ext is_get) patl;
      begin
	match topt with
	  None -> ()
	| Some t -> check_no_new_event_insert ext is_get t
      end;
      check_no_new_event_insert ext is_get t1;
      check_no_new_event_insert ext is_get t2
  | ResE _ | EventAbortE _ | EventE _ | InsertE _ -> 
      Parsing_helper.input_error ((instruct_name t) ^ " at " ^ (in_file_position ext t.t_loc) ^
				  " should not occur in condition of " ^
				  (if is_get then "get" else "find")) ext

and check_no_new_event_insert_pat ext is_get = function
    PatVar _ -> ()
  | PatTuple(_,l) -> List.iter (check_no_new_event_insert_pat ext is_get) l
  | PatEqual t -> check_no_new_event_insert ext is_get t

(* Check terms *)

let rec expand_letfun_term cur_array env' t0 =
  match t0.t_desc with
      Var (b,tl) ->
        (
          try 
            let b'=List.assq b env' in
            Terms.term_from_binder b'
          with
              Not_found -> Parsing_helper.internal_error "binder not found in environment"
        )
    | ReplIndex _ ->
	Parsing_helper.internal_error "Replication index unexpected in expand_letfun_term"
    | FunApp (f,tl) ->
        let tl' = List.map (expand_letfun_term cur_array env') tl in
	Terms.build_term3 t0 (FunApp (f,tl'))
    | TestE (t1,t2,t3) ->
	Terms.build_term3 t0
          (TestE (expand_letfun_term cur_array env' t1,
                  expand_letfun_term cur_array env' t2,
                  expand_letfun_term cur_array env' t3))
    | FindE _ -> Parsing_helper.internal_error "in expand_letfun_term, find elements should not appear"
    | LetE (pat, t1, t2, topt) ->
        let (pat',env'') = expand_letfun_pat cur_array env' pat in
        let t1' = expand_letfun_term cur_array env' t1 in
        let t2' = expand_letfun_term cur_array env'' t2 in
        let topt' = 
          (match topt with 
            Some t ->
              Some (expand_letfun_term cur_array env' t)
          | None -> None)
	in
	Terms.build_term3 t0 (LetE (pat', t1', t2', topt'))
    | ResE (b, t) ->
        let b' = Terms.create_binder b.sname b.btype cur_array in
        Terms.build_term3 t0 (ResE (b', expand_letfun_term cur_array ((b,b')::env') t))
    | EventAbortE f ->
	Terms.build_term3 t0 (EventAbortE(f))
    | EventE(t,p) ->
	begin
	  match t.t_desc with
	    FunApp(f, _::tl) ->
	      (* Events must be function applications.
		 The first argument is the tuple of replication indices.
		 Update it now. *)
	      let tupf = Settings.get_tuple_fun (List.map (fun ri -> ri.ri_type) cur_array) in
	      event_type_list := (f, tupf) :: (!event_type_list);
	      let tcur_array =
		Terms.new_term Settings.t_bitstring t0.t_loc
		  (FunApp(tupf, List.map Terms.term_from_repl_index cur_array))
	      in
              let tl' = List.map (expand_letfun_term cur_array env') tl in
	      let t' =
		Terms.build_term3 t (FunApp(f, tcur_array::tl'))
	      in
	      Terms.build_term3 t0 (EventE(t', expand_letfun_term cur_array env' p))
	  | _ ->
	      internal_error "Events must be function applications"
	end
    | GetE(table, patl, topt, t1,t2) ->
        let (patl',env'') = List.fold_left 
            (fun (pl',env'') p -> 
              let (p,env''') = expand_letfun_pat cur_array env'' p in
              (p::pl',env''')) ([],env') patl
	in
        let topt' = 
          (match topt with 
            Some t ->
              Some (expand_letfun_term cur_array env'' t)
          | None -> None)
	in
        let t1' = expand_letfun_term cur_array env'' t1 in
        let t2' = expand_letfun_term cur_array env' t2 in
	Terms.build_term3 t0 (GetE(table, patl', topt', t1', t2'))
    | InsertE(table, tl, t) ->
	let tl' = List.map (expand_letfun_term cur_array env') tl in
	let t' = expand_letfun_term cur_array env' t in
	Terms.build_term3 t0 (InsertE(table, tl', t'))
	
and expand_letfun_pat cur_array env' = function
    PatVar (b) ->
      let b' = Terms.create_binder b.sname b.btype cur_array in
        (PatVar (b'), (b,b')::env')
  | PatTuple (f,pl) ->
      let (pl',env'') = List.fold_left 
        (fun (pl',env'') p -> 
           let (p,env''') = expand_letfun_pat cur_array env'' p in
             (p::pl',env''')) ([],env') pl in
        (PatTuple (f,List.rev pl'),env'')
  | PatEqual (t) ->
      let t' = expand_letfun_term cur_array env' t in
        (PatEqual (t'),env')

let expand_letfun cur_array bl tl t =
  (* Create a term let bl' = tl in t[bl\bl'] *)
  let rec expand_letfun_rec env' bl tl = 
    match (bl,tl) with
        [],[] -> expand_letfun_term cur_array env' t
      | b::bl',t'::tl' -> 
          let b' = Terms.create_binder b.sname b.btype cur_array in
          let t1 = expand_letfun_rec ((b,b')::env')  bl' tl' in
          Terms.build_term3 t (LetE (PatVar(b'),t',t1,None))
      | _,_ -> Parsing_helper.internal_error "expand_letfun: bl and tl do not have the same size"
  in
    expand_letfun_rec [] bl tl

exception RemoveFindBranch
    
let rec check_term defined_refs_opt cur_array env = function
    PIdent (s, ext), ext2 ->
      begin
      try 
	match StringMap.find s env with
	  EVar(b) ->
	    Terms.new_term b.btype ext2 (Var(b,List.map Terms.term_from_repl_index b.args_at_creation))
	| EReplIndex(b) ->
	    Terms.new_term b.ri_type ext2 (ReplIndex(b))
	| EFunc(f) -> 
	    if fst (f.f_type) = [] then
              (*expand letfun functions*)
              let t'= Terms.new_term (snd f.f_type) ext2 (FunApp(f, [])) in
              begin
              match f.f_cat with
                  LetFunTerm (bl,t) ->
                    if (!Settings.get_implementation && f.f_impl <> No_impl) then
                      t'
                    else
                      expand_letfun cur_array bl [] t
                | _ -> t'
              end
	    else
	      input_error (s ^ " has no arguments but expects some") ext
	| _ -> input_error (s ^ " should be a variable or a function") ext
      with Not_found -> 
	let b = get_global_binder "outside its scope" (s, ext) in
	let tl'' = check_array_type_list ext2 [] [] cur_array b.args_at_creation in
	if (!current_location) <> InEquivalence then
	  begin
	    match defined_refs_opt with
	      None -> () (* We are in a [defined] condition: all array accesses are accepted *)
	    | Some defined_refs ->
		if not (List.exists (Terms.equal_binderref (b, tl'')) defined_refs) then
		  input_error ("Variable "^s^" is referenced outside its scope. It should be guarded by a defined condition") ext
	  end;
	Terms.new_term b.btype ext2 (Var(b,tl''))
      end
  | PArray(id, tl), ext2 ->
      let tl' = List.map (check_term defined_refs_opt cur_array env) tl in
      let b = get_global_binder "in an array reference" id in
      let tl'' = check_array_type_list ext2 tl tl' cur_array b.args_at_creation in
      if (!current_location) <> InEquivalence then
	begin
	  match defined_refs_opt with
	    None -> () (* We are in a [defined] condition: all array accesses are accepted *)
	  | Some defined_refs ->
	      if not (List.exists (Terms.equal_binderref (b, tl'')) defined_refs) then
		input_error "Array reference should be guarded by a defined condition" ext2
	end;
      Terms.new_term b.btype ext2 (Var(b,tl''))
  | PFunApp((s,ext), tl),ext2 ->
      let tl' = List.map (check_term defined_refs_opt cur_array env) tl in
      begin
      try 
	match StringMap.find s env with
	  EFunc(f) ->
	    check_type_list ext2 tl tl' (fst f.f_type);
	    let t' = Terms.new_term (snd f.f_type) ext2 (FunApp(f, tl')) in
              begin
              match f.f_cat with
                  LetFunTerm (bl,t) ->
                    if (!Settings.get_implementation && f.f_impl <> No_impl) then
                      t'
                    else
                      expand_letfun cur_array bl tl' t
                | _ -> t'
              end
	| _ -> input_error (s ^ " should be a function") ext
      with Not_found ->
	input_error (s ^ " not defined") ext
      end
  | PTuple(tl), ext2 ->
      let tl' = List.map (check_term defined_refs_opt cur_array env) tl in
      let f = Settings.get_tuple_fun (List.map (fun t -> t.t_type) tl') in
      check_type_list ext2 tl tl' (fst f.f_type);
      Terms.new_term (snd f.f_type) ext2 (FunApp(f, tl'))
  | PTestE(t1, t2, t3), ext ->
      let t1' = check_term defined_refs_opt cur_array env t1 in
      let t2' = check_term defined_refs_opt cur_array env t2 in
      let t3' = check_term defined_refs_opt cur_array env t3 in
      check_type (snd t1) t1' Settings.t_bool;
      if (t2'.t_type != t3'.t_type) && (t2'.t_type != Settings.t_any) && (t3'.t_type != Settings.t_any) then
	Parsing_helper.input_error "Both branches of a test should yield the same type" ext;
      Terms.new_term t2'.t_type ext (TestE(t1', t2', t3'))
  | PLetE(pat, t1, t2, topt), ext ->
      let t1' = check_term defined_refs_opt cur_array env t1 in
      let (env', pat') = check_pattern defined_refs_opt cur_array env (Some t1'.t_type) pat in
      let t2' = check_term defined_refs_opt cur_array env' t2 in
      let topt' = 
	match topt, pat with
	  Some t3, _ -> Some (check_term defined_refs_opt cur_array env t3)
	| None, (PPatVar _, _) -> None
	| None, _ -> Parsing_helper.input_error "When a let in an expression has no else part, it must be of the form let x = M in M'" ext
      in
      begin
	match topt' with
	  None -> ()
	| Some t3' -> if (t2'.t_type != t3'.t_type)  && (t2'.t_type != Settings.t_any) && (t3'.t_type != Settings.t_any) then
	    input_error "Both branches of a let should return the same type" ext
      end;
      Terms.new_term t2'.t_type ext (LetE(pat', t1', t2', topt'))
  | PResE((s1,ext1),(s2,ext2),t), ext ->
      let ty = get_type env s2 ext2 in
      if ty.toptions land Settings.tyopt_CHOOSABLE == 0 then
	input_error ("Cannot choose randomly a bitstring from " ^ ty.tname) ext2;
      let (env',b) = add_in_env env s1 ext1 ty cur_array in
      let t' = check_term defined_refs_opt cur_array env' t in
      Terms.new_term t'.t_type ext (ResE(b, t'))
  | PFindE(l0,t3,opt), ext ->
      let find_info = ref Nothing in
      List.iter (fun (s,ext_s) ->
        if s = "unique" then
	  begin
            find_info := Unique;
            if !current_location = InProcess then
              Parsing_helper.input_warning "The [unique] option is primarily intended for use in declarations of primitives. If you use it in processes, you must guarantee yourself that this find will have a unique successful branch/index." ext_s
	  end
        else
          Parsing_helper.input_error "The only option allowed for find is unique" ext_s
        ) opt;
      let t3' = check_term defined_refs_opt cur_array env t3 in
      let rec add env = function
	  [] -> (env,[])
	| ((s0,ext0),(s1,ext1),(s2,ext2))::bl ->
	    let p = get_param env s2 ext2 in
	    let (env',b) = add_in_env env s0 ext0 (type_for_param p) cur_array in
	    let (env'',bl') = add env' bl in
	    (env'',b::bl')
      in
      let l0' = List.fold_left (fun accu (bl_ref,bl,def_list,t1,t2) ->
	try 
	  let (env', bl') = add env bl in
	  let bl'' = !bl_ref in (* recover replication indices *)
	  let env'' = List.fold_left2 (fun env (_,(s1, ext1),_) b -> StringMap.add s1 (EReplIndex b) env) env bl bl'' in
	  let bl_bin = List.combine bl' bl'' in
	  let cur_array' = bl'' @ cur_array in
	  let def_list' = List.map (check_br cur_array' env'') def_list in
	  let (defined_refs_opt_t1, defined_refs_opt_t2) =
	    match defined_refs_opt with
	      None -> (None, None)
	    | Some defined_refs ->
		let (defined_refs_t1, defined_refs_t2) =
		  Terms.defined_refs_find bl_bin def_list' defined_refs
		in
		(Some defined_refs_t1, Some defined_refs_t2)
	  in
	  let t1' = check_term defined_refs_opt_t1 cur_array' env'' t1 in
	  check_no_new_event_insert (snd t1) false t1';
	  let t2' = check_term defined_refs_opt_t2 cur_array env' t2 in
	  check_type (snd t1) t1' Settings.t_bool;
	  if (t2'.t_type != t3'.t_type)  && (t2'.t_type != Settings.t_any) && (t3'.t_type != Settings.t_any) then
	    Parsing_helper.input_error "All branches of a if or find should return the same type" ext;
	  (bl_bin, def_list', t1', t2')::accu
	with RemoveFindBranch ->
	  accu
	    ) [] l0 
      in
      Terms.new_term t3'.t_type ext (FindE(List.rev l0', t3', !find_info))
  | PEventAbortE(s,ext2), ext ->
      begin
      try 
	match StringMap.find s env with
	  EEvent(f) ->
	    check_type_list ext2 [] [] (List.tl (fst f.f_type));
	    Terms.new_term Settings.t_any ext (EventAbortE(f))
	| _ -> input_error (s ^ " should be an event") ext
      with Not_found ->
	input_error (s ^ " not defined") ext
      end
  | PEventE((PFunApp((s,ext0),tl), ext), p), ext2 ->
      begin
        try 
	  match StringMap.find s env with
	      EEvent(f) ->
	        let tl' = List.map (check_term defined_refs_opt cur_array env) tl in
	        check_type_list ext tl tl' (List.tl (fst f.f_type));
	        let tupf = Settings.get_tuple_fun (List.map (fun ri -> ri.ri_type) cur_array) in
	        event_type_list := (f, tupf) :: (!event_type_list);
	        let tcur_array =
		  Terms.new_term Settings.t_bitstring ext2
		    (FunApp(tupf, List.map Terms.term_from_repl_index cur_array))
	        in
	        let p' = check_term defined_refs_opt cur_array env p in
                let event =
		  Terms.new_term Settings.t_bool ext2 (FunApp(f, tcur_array::tl'))
		in
	        Terms.new_term p'.t_type ext2 (EventE(event, p'))
	    | _ -> input_error (s ^ " should be an event") ext0
        with Not_found ->
	  input_error (s ^ " not defined") ext0
      end
  | PEventE _, ext2 ->
      input_error "events should be function applications" ext2
  | PGetE((id,ext),patl,topt,p1,p2),ext2 -> 
      let tbl = get_table env id ext in
      let p2' = check_term defined_refs_opt cur_array env p2 in
      let (env', patl') = check_pattern_list defined_refs_opt cur_array env (List.map (fun x->Some x) tbl.tbltype) patl in
      let topt' = 
	match topt with 
	  None -> None 
	| Some t -> 
	    let t' = check_term defined_refs_opt cur_array env' t in
	    check_no_new_event_insert (snd t) true t';
	    check_type (snd t) t' Settings.t_bool;
	    Some t'
      in
      let p1' = check_term defined_refs_opt cur_array env' p1 in
      if (p1'.t_type != p2'.t_type) && (p1'.t_type != Settings.t_any) && (p2'.t_type != Settings.t_any) then
	Parsing_helper.input_error "Both branches of a get should yield the same type" ext2;
      Terms.new_term p1'.t_type ext2 (GetE(tbl, patl',topt',p1', p2'))
          
  | PInsertE((id,ext),tl,p),ext2 ->
      let tbl = get_table env id ext in
      let tl' = List.map (check_term defined_refs_opt cur_array env) tl in
      check_type_list ext2 tl tl' tbl.tbltype;
      let p' = check_term defined_refs_opt cur_array env p in
      Terms.new_term p'.t_type ext2 (InsertE(tbl, tl', p'))
            
  | PEqual(t1,t2), ext ->
      let t1' = check_term defined_refs_opt cur_array env t1 in
      let t2' = check_term defined_refs_opt cur_array env t2 in
      if (t1'.t_type != t2'.t_type) && (t1'.t_type != Settings.t_any) && (t2'.t_type != Settings.t_any) then
	Parsing_helper.input_error "= expects expressions of the same type" ext;
      Terms.make_equal_ext ext t1' t2'
  | PDiff(t1,t2), ext ->
      let t1' = check_term defined_refs_opt cur_array env t1 in
      let t2' = check_term defined_refs_opt cur_array env t2 in
      if (t1'.t_type != t2'.t_type) && (t1'.t_type != Settings.t_any) && (t2'.t_type != Settings.t_any) then
	Parsing_helper.input_error "<> expects expressions of the same type" ext;
      Terms.make_diff_ext ext t1' t2'
  | PAnd(t1,t2), ext ->
      let t1' = check_term defined_refs_opt cur_array env t1 in
      let t2' = check_term defined_refs_opt cur_array env t2 in
      check_type (snd t1) t1' Settings.t_bool;
      check_type (snd t2) t2' Settings.t_bool;
      Terms.make_and_ext ext t1' t2'
  | POr(t1,t2), ext ->
      let t1' = check_term defined_refs_opt cur_array env t1 in
      let t2' = check_term defined_refs_opt cur_array env t2 in
      check_type (snd t1) t1' Settings.t_bool;
      check_type (snd t2) t2' Settings.t_bool;
      Terms.make_or_ext ext t1' t2'
  | PQEvent _,ext -> 
      Parsing_helper.input_error "event(...) and inj-event(...) allowed only in queries" ext

and check_br cur_array env ((_,ext) as id, tl) =
  try 
    let tl' = List.map (check_term None cur_array env) tl in
    List.iter2 (fun t t' -> check_no_iffindletnewevent "defined condition" (snd t) t') tl tl';
    let b = get_global_binder "in an array reference" id in
    let tl'' = check_array_type_list ext tl tl' cur_array b.args_at_creation in
    (b,tl'')
  with Undefined(i,ext) ->
    if !Settings.allow_undefined_var then
      begin
	input_warning (i ^ " not defined. Removing the find branch that requires its definition.") ext;
	raise RemoveFindBranch
      end
    else
      input_error (i ^ " not defined") ext


(* Check pattern *)

and check_pattern defined_refs_opt cur_array env tyoptres = function
    PPatVar ((s1,ext1), tyopt), _ ->
      begin
	match tyopt, tyoptres with
	  None, None ->
	    input_error "type needed for this variable" ext1
	| None, Some ty -> 
	    let (env',b) = add_in_env env s1 ext1 ty cur_array in
	    (env', PatVar b)
	| Some tyb, None -> 
	    let (ty',ext2) = get_ty env tyb in
	    begin
	      match ty'.tcat with
		Interv _ -> input_error "Cannot input a term of interval type or extract one from a tuple" ext2
	        (* This condition simplifies greatly the theory:
	           otherwise, one needs to compute which channels the adversary
	           knows...
		   8/12/2017: I no longer understand this comment, and I am
		   wondering if I could relax this condition. *)
	      |	_ -> ()
	    end;
	    let (env',b) = add_in_env env s1 ext1 ty' cur_array in
	    (env', PatVar b)	    
	| Some tyb, Some ty ->
	    let (ty',ext2) = get_ty env tyb in
	    if ty != ty' then
	      input_error ("Pattern is declared of type " ^ ty'.tname ^ " and should be of type " ^ ty.tname) ext2;
	    let (env',b) = add_in_env env s1 ext1 ty' cur_array in
	    (env', PatVar b)
      end
  | PPatTuple l, ext ->
      begin
	match tyoptres with
	  None -> ()
	| Some ty ->
	    if ty != Settings.t_bitstring then
	      input_error ("A tuple pattern has type bitstring but is here used with type " ^ ty.tname) ext
      end;
      let tl = List.map (fun _ -> None) l in
      let (env', l') = check_pattern_list defined_refs_opt cur_array env tl l in
      let tl' = List.map get_type_for_pattern l' in
      (env', PatTuple(Settings.get_tuple_fun tl', l'))
  | PPatFunApp((s,ext),l), ext2 -> 
      begin
      try 
	match StringMap.find s env with
	  EFunc(f) ->
	    if (f.f_options land Settings.fopt_COMPOS) == 0 then
	      input_error "Only [data] functions are allowed in patterns" ext;
	    begin
	      match tyoptres with
		None -> ()
	      |	Some ty ->
		  if ty != snd f.f_type then
		    input_error ("Pattern returns type " ^ (snd f.f_type).tname ^ " and should be of type " ^ ty.tname) ext2
	    end;
	    if List.length (fst f.f_type) != List.length l then
	      input_error ("Function " ^ f.f_name ^ " expects " ^ 
			   (string_of_int (List.length (fst f.f_type))) ^ 
			   " arguments but is here applied to " ^  
			   (string_of_int (List.length l)) ^ " arguments") ext;
	    let (env', l') = check_pattern_list defined_refs_opt cur_array env (List.map (fun t -> Some t) (fst f.f_type)) l in
	    (env', PatTuple(f, l'))
	| _ -> input_error (s ^ " should be a function") ext
      with Not_found ->
	input_error (s ^ " not defined") ext
      end
  | PPatEqual t, ext ->
      let t' = check_term defined_refs_opt cur_array env t in
      begin
	match tyoptres with
	  None -> ()
	| Some ty ->
	    if (t'.t_type != ty)  && (t'.t_type != Settings.t_any) && (ty != Settings.t_any) then
	      input_error ("Pattern has type " ^ (t'.t_type).tname ^ " and should be of type " ^ ty.tname) ext
      end;
      (env, PatEqual t')

and check_pattern_list defined_refs_opt cur_array env lty l = 
  match lty, l with
    [], [] -> (env,[])
  | (ty::lty),(a::l) ->
      let env', l' = check_pattern_list defined_refs_opt cur_array env lty l in
      let env'', a' = check_pattern defined_refs_opt cur_array env' ty a in
      (env'', a'::l')
  | _ -> Parsing_helper.internal_error "Lists have different length in check_pattern_list"



(* Check letfun terms *)

let rec check_term_letfun env = function
    PIdent (s, ext), ext2 ->
      begin
      try 
	match StringMap.find s env with
	  EVar(b) -> 
	    Terms.new_term b.btype ext2
	      (Var(b,List.map Terms.term_from_repl_index b.args_at_creation))
	| EFunc(f) -> 
	    if fst (f.f_type) = [] then
              (*expand letfun functions*)
              let t'= Terms.new_term (snd f.f_type) ext2 (FunApp(f, [])) in
              begin
              match f.f_cat with
                  LetFunTerm (bl,t) ->
                    if (!Settings.get_implementation && f.f_impl <> No_impl) then
                      t'
                    else
                      t
                | _ -> t'
              end
	    else
	      input_error (s ^ " has no arguments but expects some") ext
	| _ -> input_error (s ^ " should be a variable or a function") ext
      with Not_found ->
	input_error (s ^ " not defined") ext
      end
  | PFunApp((s,ext), tl),ext2 ->
      let tl' = List.map (check_term_letfun env) tl in
      begin
      try 
	match StringMap.find s env with
	  EFunc(f) ->
	    check_type_list ext2 tl tl' (fst f.f_type);
	    let t' = Terms.new_term (snd f.f_type) ext2 (FunApp(f, tl')) in
              begin
              match f.f_cat with
                  LetFunTerm (bl,t) ->
                    if (!Settings.get_implementation && f.f_impl <> No_impl) then
                      t'
                    else
                      subst3 (List.combine bl tl') t
                | _ -> t'
              end
	| _ -> input_error (s ^ " should be a function") ext
      with Not_found ->
	input_error (s ^ " not defined") ext
      end
  | PTuple(tl), ext2 ->
      let tl' = List.map (check_term_letfun env) tl in
      let f = Settings.get_tuple_fun (List.map (fun t -> t.t_type) tl') in
      check_type_list ext2 tl tl' (fst f.f_type);
      Terms.new_term (snd f.f_type) ext2 (FunApp(f, tl'))
  | PTestE(t1, t2, t3), ext ->
      let t1' = check_term_letfun env t1 in
      let t2' = check_term_letfun env t2 in
      let t3' = check_term_letfun env t3 in
      check_type (snd t1) t1' Settings.t_bool;
      if (t2'.t_type != t3'.t_type) && (t2'.t_type != Settings.t_any) && (t3'.t_type != Settings.t_any) then
	Parsing_helper.input_error "Both branches of a test should yield the same type" ext;
      Terms.new_term t2'.t_type ext (TestE(t1', t2', t3'))
  | PLetE(pat, t1, t2, topt), ext ->
      let t1' = check_term_letfun env t1 in
      let (env', pat') = check_pattern_letfun env (Some t1'.t_type) pat in
      let t2' = check_term_letfun env' t2 in
      let topt' = 
	match topt, pat with
	  Some t3, _ -> Some (check_term_letfun env t3)
	| None, (PPatVar _, _) -> None
	| None, _ -> Parsing_helper.input_error "When a let in an expression has no else part, it must be of the form let x = M in M'" ext
      in
      begin
	match topt' with
	  None -> ()
	| Some t3' -> if (t2'.t_type != t3'.t_type)  && (t2'.t_type != Settings.t_any) && (t3'.t_type != Settings.t_any) then
	    input_error "Both branches of a let should return the same type" ext
      end;
      Terms.new_term t2'.t_type ext (LetE(pat', t1', t2', topt'))
  | PResE((s1,ext1),(s2,ext2),t), ext ->
      let ty = get_type env s2 ext2 in
      if ty.toptions land Settings.tyopt_CHOOSABLE == 0 then
	input_error ("Cannot choose randomly a bitstring from " ^ ty.tname) ext2;
      let (env',b) = add_in_env_letfun env s1 ext1 ty in
      let t' = check_term_letfun env' t in
      Terms.new_term t'.t_type ext (ResE(b, t'))
  | (PFindE _ | PArray _), ext ->
      input_error "Find and array references are forbidden in letfun terms" ext
  | PEventAbortE(s,ext2), ext ->
      begin
      try 
	match StringMap.find s env with
	  EEvent(f) ->
	    check_type_list ext2 [] [] (List.tl (fst f.f_type));
	    Terms.new_term Settings.t_any ext (EventAbortE(f))
	| _ -> input_error (s ^ " should be an event") ext
      with Not_found ->
	input_error (s ^ " not defined") ext
      end
  | PEventE((PFunApp((s,ext0),tl), ext), p), ext2 ->
      begin
        try 
	  match StringMap.find s env with
	      EEvent(f) ->
	        let tl' = List.map (check_term_letfun env) tl in
	        check_type_list ext tl tl' (List.tl (fst f.f_type));
		(* We do not know the replication indices yet.
	           They will be updated later, in expand_letfun_term *)
	        let tupf = Settings.get_tuple_fun [] in
	        let tcur_array =
		  Terms.new_term Settings.t_bitstring ext2
		    (FunApp(tupf, []))
	        in
	        let p' = check_term_letfun env p in
                let event =
		  Terms.new_term Settings.t_bool ext2 (FunApp(f, tcur_array::tl'))
		in
	        Terms.new_term p'.t_type ext2 (EventE(event, p'))
	    | _ -> input_error (s ^ " should be an event") ext0
        with Not_found ->
	  input_error (s ^ " not defined") ext0
      end
  | PEventE _, ext2 ->
      input_error "events should be function applications" ext2
  | PGetE((id,ext),patl,topt,p1,p2),ext2 -> 
      let tbl = get_table env id ext in
      let p2' = check_term_letfun env p2 in
      let (env', patl') = check_pattern_list_letfun env (List.map (fun x->Some x) tbl.tbltype) patl in
      let topt' = 
	match topt with 
	  None -> None 
	| Some t -> 
	    let t' = check_term_letfun env' t in
	    check_no_new_event_insert (snd t) true t';
	    check_type (snd t) t' Settings.t_bool;
	    Some t'
      in
      let p1' = check_term_letfun env' p1 in
      if (p1'.t_type != p2'.t_type) && (p1'.t_type != Settings.t_any) && (p2'.t_type != Settings.t_any) then
	Parsing_helper.input_error "Both branches of a get should yield the same type" ext2;
      Terms.new_term p1'.t_type ext2 (GetE(tbl, patl',topt',p1', p2'))
          
  | PInsertE((id,ext),tl,p),ext2 ->
      let tbl = get_table env id ext in
      let tl' = List.map (check_term_letfun env) tl in
      check_type_list ext2 tl tl' tbl.tbltype;
      let p' = check_term_letfun env p in
      Terms.new_term p'.t_type ext2 (InsertE(tbl, tl', p'))
            
  | PEqual(t1,t2), ext ->
      let t1' = check_term_letfun env t1 in
      let t2' = check_term_letfun env t2 in
      if (t1'.t_type != t2'.t_type) && (t1'.t_type != Settings.t_any) && (t2'.t_type != Settings.t_any) then
	Parsing_helper.input_error "= expects expressions of the same type" ext;
      Terms.make_equal_ext ext t1' t2'
  | PDiff(t1,t2), ext ->
      let t1' = check_term_letfun env t1 in
      let t2' = check_term_letfun env t2 in
      if (t1'.t_type != t2'.t_type) && (t1'.t_type != Settings.t_any) && (t2'.t_type != Settings.t_any) then
	Parsing_helper.input_error "<> expects expressions of the same type" ext;
      Terms.make_diff_ext ext t1' t2'
  | PAnd(t1,t2), ext ->
      let t1' = check_term_letfun env t1 in
      let t2' = check_term_letfun env t2 in
      check_type (snd t1) t1' Settings.t_bool;
      check_type (snd t2) t2' Settings.t_bool;
      Terms.make_and_ext ext t1' t2'
  | POr(t1,t2), ext ->
      let t1' = check_term_letfun env t1 in
      let t2' = check_term_letfun env t2 in
      check_type (snd t1) t1' Settings.t_bool;
      check_type (snd t2) t2' Settings.t_bool;
      Terms.make_or_ext ext t1' t2'
  | PQEvent _,ext -> 
      Parsing_helper.input_error "event(...) and inj-event(...) allowed only in queries" ext

and check_pattern_letfun env tyoptres = function
    PPatVar ((s1,ext1), tyopt), _ ->
      begin
	match tyopt, tyoptres with
	  None, None ->
	    input_error "type needed for this variable" ext1
	| None, Some ty -> 
	    let (env',b) = add_in_env_letfun env s1 ext1 ty in
	    (env', PatVar b)
	| Some tyb, None -> 
	    let (ty',ext2) = get_ty env tyb in
	    begin
	      match ty'.tcat with
		Interv _ -> input_error "Cannot input a term of interval type or extract one from a tuple" ext2
	        (* This condition simplifies greatly the theory:
	           otherwise, one needs to compute which channels the adversary
	           knows...
		   8/12/2017: I no longer understand this comment, and I am
		   wondering if I could relax this condition. *)
	      |	_ -> ()
	    end;
	    let (env',b) = add_in_env_letfun env s1 ext1 ty' in
	    (env', PatVar b)	    
	| Some tyb, Some ty ->
	    let (ty',ext2) = get_ty env tyb in
	    if ty != ty' then
	      input_error ("Pattern is declared of type " ^ ty'.tname ^ " and should be of type " ^ ty.tname) ext2;
	    let (env',b) = add_in_env_letfun env s1 ext1 ty' in
	    (env', PatVar b)
      end
  | PPatTuple l, ext ->
      begin
	match tyoptres with
	  None -> ()
	| Some ty ->
	    if ty != Settings.t_bitstring then
	      input_error ("A tuple pattern has type bitstring but is here used with type " ^ ty.tname) ext
      end;
      let tl = List.map (fun _ -> None) l in
      let (env', l') = check_pattern_list_letfun env tl l in
      let tl' = List.map get_type_for_pattern l' in
      (env', PatTuple(Settings.get_tuple_fun tl', l'))
  | PPatFunApp((s,ext),l), ext2 -> 
      begin
      try 
	match StringMap.find s env with
	  EFunc(f) ->
	    if (f.f_options land Settings.fopt_COMPOS) == 0 then
	      input_error "Only [data] functions are allowed in patterns" ext;
	    begin
	      match tyoptres with
		None -> ()
	      |	Some ty ->
		  if ty != snd f.f_type then
		    input_error ("Pattern returns type " ^ (snd f.f_type).tname ^ " and should be of type " ^ ty.tname) ext2
	    end;
	    if List.length (fst f.f_type) != List.length l then
	      input_error ("Function " ^ f.f_name ^ " expects " ^ 
			   (string_of_int (List.length (fst f.f_type))) ^ 
			   " arguments but is here applied to " ^  
			   (string_of_int (List.length l)) ^ " arguments") ext;
	    let (env', l') = check_pattern_list_letfun env (List.map (fun t -> Some t) (fst f.f_type)) l in
	    (env', PatTuple(f, l'))
	| _ -> input_error (s ^ " should be a function") ext
      with Not_found ->
	input_error (s ^ " not defined") ext
      end
  | PPatEqual t, ext ->
      let t' = check_term_letfun env t in
      begin
	match tyoptres with
	  None -> ()
	| Some ty ->
	    if (t'.t_type != ty)  && (t'.t_type != Settings.t_any) && (ty != Settings.t_any) then
	      input_error ("Pattern has type " ^ (t'.t_type).tname ^ " and should be of type " ^ ty.tname) ext
      end;
      (env, PatEqual t')

and check_pattern_list_letfun env lty l = 
  match lty, l with
    [], [] -> (env,[])
  | (ty::lty),(a::l) ->
      let env', l' = check_pattern_list_letfun env lty l in
      let env'', a' = check_pattern_letfun env' ty a in
      (env'', a'::l')
  | _ -> Parsing_helper.internal_error "Lists have different length in check_pattern_list"

(* Check channels *)

let channel_env = (Hashtbl.create 7: (string, channel) Hashtbl.t)

let check_channel_id (s,ext) =
  try
    Hashtbl.find channel_env s 
  with Not_found -> 
    let c = { cname = s } in
    Hashtbl.add channel_env s c;
    c

let check_process_channel cur_array env (((s, ext) as id), idx_opt) = 
  if (!Settings.front_end) == Settings.Channels then
    begin
      begin
	match idx_opt with
	  None -> ()
	| Some l ->
	    if List.length l <> List.length cur_array then
	      input_error "The indices of a channel should be the current replication indices" ext;
	    List.iter2 (fun (id,ext) ri ->
	      try
		match StringMap.find id env with
		  EReplIndex ri' ->
		    if ri != ri' then
		      input_error "The indices of a channel should be the current replication indices in the right order" ext
		| _ ->
		    input_error (id ^ " should be a current replication index") ext
	      with Not_found ->
		input_error (id ^ " not defined") ext
	      ) l cur_array
      end;
      try 
	match StringMap.find s env with
	  EChannel(b) -> (b,List.map Terms.term_from_repl_index cur_array)
	| _ -> input_error (s ^ " should be a channel") ext
      with Not_found -> 
	input_error (s ^ " not defined") ext
    end
  else
    (check_channel_id id, List.map Terms.term_from_repl_index cur_array)

(* Check statement *)

let add_in_env_nobe env s ext t =
    let b = Terms.create_binder0 s t [] in
    if (StringMap.mem s env) then
      input_warning ("identifier " ^ s ^ " rebound") ext;
    (StringMap.add s (EVar b) env, b)

let rec check_binder_list env = function
    [] -> (env,[])
  | ((s1,ext1),(s2,ext2))::l ->
      let t = get_type env s2 ext2 in
      let (env',b) = add_in_env_nobe env s1 ext1 t in
      let (env'',l') = check_binder_list env' l in
      (env'', b::l')


let rec check_term_nobe env = function
    PIdent (s, ext), ext2 ->
      begin
      try 
	match StringMap.find s env with
	  EVar(b) ->
	    Terms.new_term b.btype ext2
	      (Var(b,List.map Terms.term_from_repl_index b.args_at_creation))
	| EFunc(f) ->
            begin 
              match f.f_cat with 
                  LetFunTerm _ -> input_error ("Letfun are not accepted here") ext
                | _ ->
      	            if fst (f.f_type) = [] then
	              Terms.new_term (snd f.f_type) ext2 (FunApp(f, []))
	            else
	              input_error (s ^ " has no arguments but expects some") ext
            end
	| _ -> input_error (s ^ " should be a variable or a function") ext
      with Not_found -> input_error (s ^ " not defined") ext
      end
  | PFunApp((s,ext), tl),ext2 ->
      let tl' = List.map (check_term_nobe env) tl in
      begin
      try 
	match StringMap.find s env with
	  EFunc(f) ->
            begin
              match f.f_cat with
                LetFunTerm _ -> input_error ("Letfun are not accepted here") ext
              | _ ->
	          check_type_list ext2 tl tl' (fst f.f_type);
	          Terms.new_term (snd f.f_type) ext2 (FunApp(f, tl'))
            end
	  | _ -> input_error (s ^ " should be a function") ext
      with Not_found ->
	input_error (s ^ " not defined") ext
      end
  | PTuple(tl), ext2 ->
      let tl' = List.map (check_term_nobe env) tl in
      let f = Settings.get_tuple_fun (List.map (fun t -> t.t_type) tl') in
      check_type_list ext2 tl tl' (fst f.f_type);
      Terms.new_term (snd f.f_type) ext2 (FunApp(f, tl'))
  | PEqual(t1,t2), ext ->
      let t1' = check_term_nobe env t1 in
      let t2' = check_term_nobe env t2 in
      if (t1'.t_type != t2'.t_type) && (t1'.t_type != Settings.t_any) && (t2'.t_type != Settings.t_any) then
	Parsing_helper.input_error "= expects expressions of the same type" ext;
      Terms.make_equal_ext ext t1' t2'
  | PDiff(t1,t2), ext ->
      let t1' = check_term_nobe env t1 in
      let t2' = check_term_nobe env t2 in
      if (t1'.t_type != t2'.t_type) && (t1'.t_type != Settings.t_any) && (t2'.t_type != Settings.t_any) then
	Parsing_helper.input_error "<> expects expressions of the same type" ext;
      Terms.make_diff_ext ext t1' t2'
  | PAnd(t1,t2), ext ->
      let t1' = check_term_nobe env t1 in
      let t2' = check_term_nobe env t2 in
      check_type (snd t1) t1' Settings.t_bool;
      check_type (snd t2) t2' Settings.t_bool;
      Terms.make_and_ext ext t1' t2'
  | POr(t1,t2), ext ->
      let t1' = check_term_nobe env t1 in
      let t2' = check_term_nobe env t2 in
      check_type (snd t1) t1' Settings.t_bool;
      check_type (snd t2) t2' Settings.t_bool;
      Terms.make_or_ext ext t1' t2'
  | (PArray _ | PTestE _ | PFindE _ | PLetE _ | PResE _ | PEventAbortE _ | PEventE _ | PGetE _ | PInsertE _), ext ->
      input_error "If, find, let, new, event, insert, get, and array references forbidden in forall statements" ext
  | PQEvent _,ext -> 
      Parsing_helper.input_error "event(...) and inj-event(...) allowed only in queries" ext

let check_statement env (l,t) =
  (* Note: This function uses check_binder_list, which calls
     Terms.create_binder0, so it does not rename the variables.
     That is why I do not save and restore the variable
     numbering state. *)
  let (env',l') = check_binder_list env l in
  let t' = check_term_nobe env' t in
  begin
    match t'.t_desc with
      FunApp(f, [t1;t2]) when f.f_cat == Equal ->
	if not (List.for_all (fun b -> Terms.refers_to b t1) l') then
	  input_error "In equality statements, all bound variables should occur in the left-hand side" (snd t)
    | _ -> ()
  end;
  check_type (snd t) t' Settings.t_bool;
  statements := (l',t') :: (!statements)

(* Check builtin equation statements *)

let get_fun env (s,ext) =
  try 
    match StringMap.find s env with
      EFunc(f) -> f
    | _ -> input_error (s ^ " should be a function") ext
  with Not_found ->
    input_error (s ^ " not defined") ext

let check_builtin_eq env (eq_categ, ext) l_fun_symb =
  let l_fun = List.map (get_fun env) l_fun_symb in
  match eq_categ with
    "commut" -> 
      begin
	match l_fun with
	  [f] -> 
	    begin
	      match fst f.f_type with
		[t1;t2] when t1 == t2 -> ()
	      |	_ -> input_error "A commutative function should have two arguments of the same type" ext
	    end;
	    if f.f_eq_theories = NoEq then
	      f.f_eq_theories <- Commut
	    else
	      input_error ("Function " ^ f.f_name ^ " already has an equational theory") ext
	| _ -> input_error "A commut declaration expects a single function symbol" ext
      end
  | "assoc" | "AC" ->
      begin
	match l_fun with
	  [f] -> 
	    begin
	      match f.f_type with
		([t1;t2], tres) when t1 == t2 && t1 == tres -> ()
	      |	_ -> input_error ("An " ^ eq_categ ^ " function should have two arguments of the same type as the result") ext
	    end;
	    if f.f_eq_theories = NoEq then
	      f.f_eq_theories <- if eq_categ = "AC" then AssocCommut else Assoc
	    else
	      input_error ("Function " ^ f.f_name ^ " already has an equational theory") ext
	| _ -> input_error ("An " ^ eq_categ ^ " declaration expects a single function symbol") ext
      end
  | "assocU" | "ACU" ->
      begin
	match l_fun with
	  [f;n] -> 
	    begin
	      match f.f_type, n.f_type with
		([t1;t2], tres), ([], tn) when t1 == t2 && t1 == tres && tn == tres -> ()
	      |	_ -> input_error ("An " ^ eq_categ ^ " function should have two arguments of the same type as the result, and a constant neutral element of the same type") ext
	    end;
	    if f.f_eq_theories = NoEq then
	      f.f_eq_theories <- if eq_categ = "ACU" then AssocCommutN(f,n) else AssocN(f,n)
	    else
	      input_error ("Function " ^ f.f_name ^ " already has an equational theory") ext
	| _ -> input_error ("An " ^ eq_categ ^ " declaration expects a single function symbol") ext
      end
  | "ACUN" ->
      begin
	match l_fun with
	  [f; n] -> 
	    begin
	      match f.f_type, n.f_type with
		([t1;t2], tres), ([], tneut) when t1 == t2 && t1 == tres && tneut == tres -> ()
	      |	_ -> input_error "An ACUN function should have two arguments, the result, and a constant neutral element of the same type" ext
	    end;
	    if f.f_eq_theories = NoEq then
	      f.f_eq_theories <- ACUN(f,n)
	    else
	      input_error ("Function " ^ f.f_name ^ " already has an equational theory") ext
	| _ -> input_error "An ACUN declaration expects two function symbols" ext
      end  
  | "group" | "commut_group" ->
      begin
	match l_fun with
	  [f; inv; n] -> 
	    begin
	      match f.f_type, inv.f_type, n.f_type with
		([t1;t2], tres), ([invarg], invres), ([], tneut) when t1 == t2 && t1 == tres && invarg == tres && invres == tres && tneut == tres -> ()
	      |	_ -> input_error "A group operation should be of type T,T -> T, with an inverse of type T -> T and a neutral element of type T" ext
	    end;
	    if f.f_eq_theories != NoEq then
	      input_error ("Function " ^ f.f_name ^ " already has an equational theory") ext
	    else if inv.f_eq_theories != NoEq then
	      input_error ("Function " ^ inv.f_name ^ " already has an equational theory") ext
	    else
	      begin
		let eq_th = 
		  if eq_categ = "group" 
		  then Group(f, inv, n) 
		  else CommutGroup(f, inv, n) 
		in
		f.f_eq_theories <- eq_th;
		inv.f_eq_theories <- eq_th
	      end
	| _ -> input_error ("A " ^ eq_categ ^ " declaration expects 3 function symbols") ext
      end  
  | _ -> input_error ("Equational theory " ^ eq_categ ^ " not implemented") ext	

(* Check equivalence statements *)

let rec check_term_proba env = function
    PIdent (s, ext), ext2 ->
      begin
      try 
	match StringMap.find s env with
	  EVar(b) ->
	    Terms.new_term b.btype ext2
	      (Var(b,List.map Terms.term_from_repl_index b.args_at_creation))
	| EFunc(f) ->
            begin
              match f.f_cat with
                | LetFunTerm _ -> input_error ("Letfun are not accepted here") ext
                | _->
	            if fst (f.f_type) = [] then
		      Terms.new_term (snd f.f_type) ext2 (FunApp(f, []))
	            else
	              input_error (s ^ " has no arguments but expects some") ext
            end
	| _ -> input_error (s ^ " should be a variable or a function") ext
      with Not_found -> 
	let b = get_global_binder "outside its scope" (s,ext) in
	let tl'' = check_array_type_list ext2 [] [] b.args_at_creation b.args_at_creation in
	Terms.new_term b.btype ext2 (Var(b,tl''))
      end
  | PFunApp((s,ext), tl),ext2 ->
      let tl' = List.map (check_term_proba env) tl in
      begin
      try 
	match StringMap.find s env with
	    EFunc(f) ->
              begin
                match f.f_cat with
                  LetFunTerm _ -> input_error ("Letfun are not accepted here") ext
                | _->
	            check_type_list ext2 tl tl' (fst f.f_type);
	            Terms.new_term (snd f.f_type) ext2 (FunApp(f, tl'))
              end
	  | _ -> input_error (s ^ " should be a function") ext
      with Not_found ->
	input_error (s ^ " not defined") ext
      end
  | PTuple(tl), ext2 ->
      let tl' = List.map (check_term_proba env) tl in
      let f = Settings.get_tuple_fun (List.map (fun t -> t.t_type) tl') in
      check_type_list ext2 tl tl' (fst f.f_type);
      Terms.new_term (snd f.f_type) ext2 (FunApp(f, tl'))
  | (PArray _ | PTestE _ | PLetE _ | PResE _ | PFindE _ | PEventAbortE _ | PEventE _ | PGetE _ | PInsertE _), ext ->
      Parsing_helper.input_error "Array accesses/if/let/find/new/event/get/insert not allowed in terms in probability formulas" ext
  | PEqual(t1,t2), ext ->
      let t1' = check_term_proba env t1 in
      let t2' = check_term_proba env t2 in
      if (t1'.t_type != t2'.t_type) && (t1'.t_type != Settings.t_any) && (t2'.t_type != Settings.t_any) then
	Parsing_helper.input_error "= expects expressions of the same type" ext;
      Terms.make_equal_ext ext t1' t2'
  | PDiff(t1,t2), ext ->
      let t1' = check_term_proba env t1 in
      let t2' = check_term_proba env t2 in
      if (t1'.t_type != t2'.t_type) && (t1'.t_type != Settings.t_any) && (t2'.t_type != Settings.t_any) then
	Parsing_helper.input_error "<> expects expressions of the same type" ext;
      Terms.make_diff_ext ext t1' t2'
  | PAnd(t1,t2), ext ->
      let t1' = check_term_proba env t1 in
      let t2' = check_term_proba env t2 in
      check_type (snd t1) t1' Settings.t_bool;
      check_type (snd t2) t2' Settings.t_bool;
      Terms.make_and_ext ext t1' t2'
  | POr(t1,t2), ext ->
      let t1' = check_term_proba env t1 in
      let t2' = check_term_proba env t2 in
      check_type (snd t1) t1' Settings.t_bool;
      check_type (snd t2) t2' Settings.t_bool;
      Terms.make_or_ext ext t1' t2'
  | PQEvent _,ext -> 
      Parsing_helper.input_error "event(...) and inj-event(...) allowed only in queries" ext


(* TO DO we should output an error message when a term in a probability
  formula depends on variables occurring in several different expressions
  of the left-hand side of the equivalence. (In such a case, no expression
  can instantiate all variables, so it will always have result 0, which
  is not the desired behaviour!) *)
      
(* returns the checked formula and its dimension as a power of probability
   and a power of time *)
let get_compatible ext d1 d2 =
  match (d1,d2) with
    None, _ -> d2
  | _, None -> d1
  | Some(dp1,dt1,dl1),Some(dp2,dt2,dl2) -> 
      if (dp1 != dp2) || (dt1 != dt2) || (dl1 != dl2) then
	input_error "values of incompatible dimensions" ext
      else
	d1

let compose_dim f d1 d2 =
  match (d1,d2) with
    None, _ -> None
  | _, None -> None
  | Some(dp1,dt1,dl1),Some(dp2,dt2,dl2) -> 
      Some (f dp1 dp2, f dt1 dt2, f dl1 dl2)

let rec check_types ext pl0 pl tl = 
  match (pl0, pl, tl) with
    [],[],[] -> []
  | _::pl0', (TypeMaxlength(ty'))::pl', ty::tl' when ty.toptions land Settings.tyopt_BOUNDED != 0 && ty == ty' -> 
      (* print_string ("Type max length " ^ ty.tname ^ "\n"); *)
      check_types ext pl0' pl' tl'
  | _, _, ty::tl' when ty.toptions land Settings.tyopt_BOUNDED != 0 -> 
      (* print_string ("Bounded type " ^ ty.tname ^ "\n"); *)
      check_types ext pl0 pl tl'
  | (_, ext)::pl0', pt::pl', ty::tl' ->
      let rec check_pt ty = function
	  Maxlength(_,t) ->
	    if t.t_type != ty then
	      input_error ("In a probability formula, time/length should be of form time/length(f, p1, ..., pn)\n" ^
			   "where p1...pn are probabilities pi ::= maxlength(ti) | length(fi, ...) | max(pi,pi)\n" ^
			   "for terms ti or result of fi of types the non-bounded arguments of f.\n" ^ 
			   "Type " ^ ty.tname ^ " expected, got " ^ t.t_type.tname ^ ".") ext
	| TypeMaxlength(t) ->
	    input_error ("In a probability formula, time/length should be of form time/length(f, p1, ..., pn)\n" ^
			 "where p1...pn are probabilities pi ::= maxlength(ti) | length(fi, ...) | max(pi,pi)\n" ^
			 "for terms ti or result of fi of types the non-bounded arguments of f.\n" ^ 
			 "Unbounded type " ^ ty.tname ^ " expected, got bounded type " ^ t.tname ^ ".") ext
	| Max(l) ->
	    List.iter (check_pt ty) l
	| Length(f,l) ->
	    if snd f.f_type != ty then
	      input_error ("In a probability formula, time/length should be of form time/length(f, p1, ..., pn)\n" ^
			   "where p1...pn are probabilities pi ::= maxlength(ti) | length(fi, ...) | max(pi,pi)\n" ^
			   "for terms ti or result of fi of types the non-bounded arguments of f.\n" ^ 
			   "Type " ^ ty.tname ^ " expected, got " ^ (snd f.f_type).tname ^ ".") ext
	    
	| _ ->
	    input_error ("In a probability formula, time/length should be of form time/length(f, p1, ..., pn)\n" ^
			 "where p1...pn are probabilities pi ::= maxlength(ti) | length(fi, ...) | max(pi,pi)\n" ^
			 "for terms ti or result of fi of types the non-bounded arguments of f.\n" ^ 
			 "maxlength or max expected.") ext
      in
      check_pt ty pt;
      pt :: (check_types ext pl0' pl' tl')
  | _ -> 
      input_error ("In a probability formula, time/length should be of form time/length(f, p1, ..., pn)\n" ^
		   "where p1...pn are probabilities pi ::= maxlength(ti) | length(fi, ...) | max(pi,pi)\n" ^
		   "for terms ti or result of fi of types the non-bounded arguments of f.\n" ^ 
		   "Unexpected number of arguments.") ext


let dummy_game = { proc = Terms.iproc_from_desc Nil; game_number = -1; current_queries = [] }

let rec check_probability_formula seen_ch seen_repl env = function
    PPIdent(s,ext), ext2 ->
      begin
	try 
	  match StringMap.find s env with
	    EParam p -> 
	      if not (List.exists (fun b -> p == Terms.param_from_type b) (!seen_repl)) then
		input_error ("The parameter " ^s^ " should occur in each member of the equivalence") ext;
	      Count p, Some(0, 0, 0)
	  | EProba p -> Proba(p,[]), Some(1, 0, 0)
	  | _ -> input_error (s ^ " should be a probability or a parameter") ext
	with Not_found ->
	  input_error (s ^ " is not defined") ext
      end
  | PCount(s,ext), ext2 ->
      begin
	try
	  OCount(List.find (fun ch -> ch.cname = s) seen_ch), Some(0, 0, 0)
	with Not_found -> 
	  input_error ("The oracle name " ^ s ^ " is not defined") ext
      end
  | PPFun((s,ext), l), ext2 ->
      let l' = List.map (fun p -> fst (check_probability_formula seen_ch seen_repl env p )) l in
      (* Remove "TypeMaxlength" arguments for simplicity; they are constants.
	 TO DO This removing is perhaps questionable *)
      let l' = List.filter (function 
	  TypeMaxlength _ -> false
	| _ -> true) l' in
      begin
	try 
	  match StringMap.find s env with
	  | EProba p -> Proba(p,l'), Some(1, 0, 0)
	  | _ -> input_error (s ^ " should be a probability") ext
	with Not_found ->
	  input_error (s ^ " is not defined") ext
      end
  | PAdd(p1,p2), ext ->
      let (p1', d1) = check_probability_formula seen_ch seen_repl env p1 in
      let (p2', d2) = check_probability_formula seen_ch seen_repl env p2 in
      (Add(p1',p2'), get_compatible ext d1 d2)
  | PSub(p1,p2), ext ->
      let (p1', d1) = check_probability_formula seen_ch seen_repl env p1 in
      let (p2', d2) = check_probability_formula seen_ch seen_repl env p2 in
      (Sub(p1',p2'), get_compatible ext d1 d2)
  | PMax(pl), ext ->
      let rec check_comp = function
	  [] -> ([], None)
	| (p::l) -> 
	    let (p', d) = check_probability_formula seen_ch seen_repl env p in
	    let (l', dl) = check_comp l in
	    if List.exists (Terms.equal_probaf p') l' then
	      (* remove duplicate elements for simplifying *)
	      (l',dl)
	    else
	      (p'::l', get_compatible ext d dl)
      in
      let (pl', d) = check_comp pl in
      begin
	(* The "max" is removed when the list contains a single element *)
	match pl' with
	  [p] -> (p, d)
	| _ -> (Max(pl'), d)
      end
  | PTime, ext ->
      (AttTime, Some(0, 1, 0))
  | PActTime(action, pl), ext ->
      begin
	let pl' = List.map (fun p -> fst (check_probability_formula seen_ch seen_repl env p)) pl in
	match action with
	  PAFunApp(s,ext') ->
	    begin
	    try 
	      match StringMap.find s env with
	      | EFunc f -> 
                  begin
                    match f.f_cat with
                        LetFunTerm _ -> input_error ("Letfun are not accepted here") ext
                      | _ ->
		          let pl' = check_types ext pl pl' (fst f.f_type) in
		            (ActTime(AFunApp f, pl'), Some(0, 1, 0))
                  end
	      | _ -> input_error (s ^ " should be a function symbol") ext'
	    with Not_found ->
	      input_error (s ^ " is not defined") ext'
	    end
	| PAPatFunApp(s,ext') ->
	    begin
	    try 
	      match StringMap.find s env with
	      | EFunc f -> 
                  begin
                    match f.f_cat with
                        LetFunTerm _ -> input_error ("Letfun are not accepted here") ext
                      | _ ->
		          let pl' = check_types ext pl pl' (fst f.f_type) in
		            (ActTime(APatFunApp f, pl'), Some(0, 1, 0))
                  end
	      | _ -> input_error (s ^ " should be a function symbol") ext'
	    with Not_found ->
	      input_error (s ^ " is not defined") ext'
	    end
	| PACompare(s,ext') ->
	    let t = get_type_or_param env s ext' in
	    let pl' = check_types ext pl pl' [t] in
	    (ActTime(AFunApp(Settings.f_comp Equal t t), pl'), Some(0, 1, 0))
	| PANew(s,ext') ->
	    let t = get_type env s ext' in
	    if pl != [] then 
	      internal_error "No length arguments for time(new)";
	    (ActTime(ANew t, pl'), Some(0, 1, 0))
	| PAAppTuple(tl) ->
	    let tl' = List.map (fun (s,ext') -> get_type env s ext') tl in
	    let f = Settings.get_tuple_fun tl' in
	    let pl' = check_types ext pl pl' (fst f.f_type) in
	    (ActTime(AFunApp f, pl'), Some(0, 1, 0))
	| PAPatTuple(tl) ->
	    let tl' = List.map (fun (s,ext') -> get_type env s ext') tl in
	    let f = Settings.get_tuple_fun tl' in
	    let pl' = check_types ext pl pl' (fst f.f_type) in
	    (ActTime(APatFunApp f, pl'), Some(0, 1, 0))
	| PAOut(l1,(s,ext')) ->
	    if (!Settings.front_end) == Settings.Channels then
	      begin
		let l1' = List.map (fun (s,ext') -> get_type_or_param env s ext') l1 in
		let t = get_type env s ext' in
		let pl' = check_types ext pl pl' (l1' @ [t]) in
		(ActTime(AOut(l1',t), pl'), Some(0, 1, 0))
	      end
	    else
	      internal_error "out action not allowed in oracles front-end"
	| _ ->
	    begin
	      if pl != [] then 
		internal_error "No length arguments for this action";
	      let action' = match action with
		PAReplIndex -> AReplIndex
	      |	PAArrayAccess n -> AArrayAccess n
	      |	PAAnd -> AFunApp(Settings.f_and)
	      |	PAOr -> AFunApp(Settings.f_or)
	      |	PAIf -> AIf
	      |	PANewChannel -> ANewChannel
	      |	PAFind n -> AFind n
	      |	PAIn n -> 
		  if (!Settings.front_end) == Settings.Channels then
		    AIn n
		  else
		    internal_error "in action not allowed in oracles front-end"
	      |	_ -> internal_error "Unexpected action (syntax.ml)"
	      in
	      (ActTime(action', pl'), Some(0, 1, 0))
	    end
      end
  | PMaxlength(t), ext ->
      let t' = check_term_proba env t in
      if t'.t_type.toptions land Settings.tyopt_BOUNDED != 0 then
	(TypeMaxlength(t'.t_type), Some (0,0,1))
      else
	(Maxlength(dummy_game, t'), Some (0,0,1))
  | PLength((s,ext'), pl), ext ->
      begin
	let pl' = List.map (fun p -> fst (check_probability_formula seen_ch seen_repl env p)) pl in
	try 
	  match StringMap.find s env with
	  | EFunc f -> 
              begin
                match f.f_cat with
                    LetFunTerm _ -> input_error ("Letfun are not accepted here") ext
                  | _ ->
	              let pl' = check_types ext pl pl' (fst f.f_type) in
	                if (snd f.f_type).toptions land Settings.tyopt_BOUNDED != 0 then
		          (TypeMaxlength (snd f.f_type), Some(0,0,1))
	                else
		          (Length(f, pl'), Some(0,0,1))
              end
	  | EType t ->
	      if pl != [] then
		input_error "the length of a type should have no additional argument" ext';
	      if t.toptions land Settings.tyopt_BOUNDED != 0 then
		(TypeMaxlength t, Some(0,0,1))
	      else
		input_error "the length of a type is allowed only when the type is bounded" ext'
	  | _ -> input_error (s ^ " should be a function symbol or a type") ext'
	with Not_found ->
	  input_error (s ^ " is not defined") ext'
      end
  | PLengthTuple(tl,pl), ext ->
      let pl' = List.map (fun p -> fst (check_probability_formula seen_ch seen_repl env p)) pl in
      let tl' = List.map (fun (s,ext') -> get_type env s ext') tl in
      let f = Settings.get_tuple_fun tl' in
      let pl' = check_types ext pl pl' (fst f.f_type) in
      (Length(f, pl'), Some(0,0,1))
  | PProd(p1,p2), ext ->
      let (p1', d1) = check_probability_formula seen_ch seen_repl env p1 in
      let (p2', d2) = check_probability_formula seen_ch seen_repl env p2 in
      (Mul(p1',p2'), compose_dim (+) d1 d2)
  | PDiv(p1,p2), ext ->
      let (p1', d1) = check_probability_formula seen_ch seen_repl env p1 in
      let (p2', d2) = check_probability_formula seen_ch seen_repl env p2 in
      (Div(p1',p2'), compose_dim (-) d1 d2)
  | PPZero, ext -> Zero, None
  | PCard (s,ext'), ext -> 
      begin
	try 
	  match StringMap.find s env with
	  | EType t -> 
	      if t.toptions land Settings.tyopt_BOUNDED != 0 then
		Card t, Some(-1, 0, 0)
	      else
		input_error (s ^ " should be bounded") ext'
	  | _ -> input_error (s ^ " should be a type") ext'
	with Not_found ->
	  input_error (s ^ " is not defined") ext'
      end
  | PCst i, ext ->
      Cst (float_of_int i), Some(0, 0, 0)
  | PFloatCst f, ext ->
      Cst f, Some(0, 0, 0)
  | PEpsFind, ext -> EpsFind, Some(1, 0, 0)
  | PEpsRand(s,ext'), ext ->
      begin
	try 
	  match StringMap.find s env with
	  | EType t -> 
	      if t.toptions land Settings.tyopt_NONUNIFORM != 0 then
		input_error (s ^ " should be bounded or fixed, it should not be nonuniform") ext'
	      else if t.toptions land Settings.tyopt_FIXED != 0 then
		Zero, Some(1, 0, 0)
	      else if t.toptions land Settings.tyopt_BOUNDED != 0 then
		EpsRand t, Some(1, 0, 0)
	      else
		input_error (s ^ " should be bounded or fixed") ext'
	  | _ -> input_error (s ^ " should be a type") ext'
	with Not_found ->
	  input_error (s ^ " is not defined") ext'
      end
  | PPColl1Rand(s,ext'), ext ->
      begin
	try 
	  match StringMap.find s env with
	  | EType t -> 
	      if t.toptions land Settings.tyopt_NONUNIFORM != 0 then
		PColl1Rand t, Some(1, 0, 0)
	      else if t.toptions land Settings.tyopt_FIXED != 0 then
		Div(Cst 1.0, Card t), Some(1, 0, 0)
	      else if t.toptions land Settings.tyopt_BOUNDED != 0 then
		Add(Div(Cst 1.0, Card t), EpsRand t), Some(1, 0, 0)
	      else 
		input_error (s ^ " should be fixed, bounded, or nonuniform") ext'
	  | _ -> input_error (s ^ " should be a type") ext'
	with Not_found ->
	  input_error (s ^ " is not defined") ext'
      end
  | PPColl2Rand(s,ext'), ext ->
      begin
	try 
	  match StringMap.find s env with
	  | EType t -> 
	      if t.toptions land Settings.tyopt_NONUNIFORM != 0 then
		PColl2Rand t, Some(1, 0, 0)
	      else if t.toptions land Settings.tyopt_FIXED != 0 then
		Div(Cst 1.0, Card t), Some(1, 0, 0)
	      else if t.toptions land Settings.tyopt_BOUNDED != 0 then
		Add(Div(Cst 1.0, Card t), EpsRand t), Some(1, 0, 0)
	      else 
		input_error (s ^ " should be fixed, bounded, or nonuniform") ext'
	  | _ -> input_error (s ^ " should be a type") ext'
	with Not_found ->
	  input_error (s ^ " is not defined") ext'
      end

let check_probability_formula2 seen_ch seen_repl env p =
  let (p', d) = check_probability_formula seen_ch seen_repl env p in
  begin
    match d with
      None -> ()
    | Some(dp,dt,dl) ->
	if (dp != 1) || (dt != 0) || (dl != 0) then 
	  input_error "The result of this formula is not a probability" (snd p)
  end;
  p'

let rec check_binder_list2 cur_array env = function
    [] -> (env,[])
  | ((s1,ext1),ty)::l ->
      let t = 
	match ty with
	  Tid (s2,ext2) -> get_type env s2 ext2 
	| TBound (s2,ext2) -> 
	    let p = get_param env s2 ext2 in
	    type_for_param p
      in
      (* Interval types now allowed in arguments of oracles
	 check_bit_string_type ext2 t; *)
      let (env',b) = add_in_env env s1 ext1 t cur_array in
      let (env'',l') = check_binder_list2 cur_array env' l in
      (env'', b::l')

let rec check_lm_restrlist cur_array env = function
    [] -> (env, [])
  | ((s1,ext1),(s2,ext2),opt)::l ->
      let t = get_type env s2 ext2 in
      if t.toptions land Settings.tyopt_CHOOSABLE == 0 then
	input_error ("Cannot choose randomly a bitstring from " ^ t.tname) ext2;
      begin
	match opt with
	  [] -> ()
	| (_,ext3)::_ ->
	    input_error ("Restrictions should have no options in the left-hand side of an equivalence") ext3
      end;
      let (env',b) = add_in_env env s1 ext1 t cur_array in
      let (env'',bl) = check_lm_restrlist cur_array env' l in
      (env'', (b, NoOpt)::bl)

let rec check_lm_fungroup2 cur_array cur_restr env seen_ch seen_repl = function
    PReplRestr((repl_index_ref, _, (rep,ext)), restrlist, funlist) ->
      let repl_count' = 
	match !repl_index_ref with
	  Some b -> b
	| None -> Parsing_helper.internal_error "Repl index should have been initialized in check_lm_fungroup2"
      in
      let cur_array' = repl_count' :: cur_array in
      let (env',restrlist') = check_lm_restrlist cur_array' env restrlist in
      if List.memq repl_count'.ri_type (!seen_repl) then
	Parsing_helper.input_error "In an equivalence, different functions must have a different number of repetitions" ext;
      seen_repl := repl_count'.ri_type :: (!seen_repl);
      let funlist' = List.map (check_lm_fungroup2 cur_array' (restrlist'::cur_restr) env' seen_ch seen_repl) funlist in
      (* Remove useless new *)
      let restrlist'' = List.filter (fun (b,_) -> List.exists (Terms.refers_to_fungroup b) funlist') restrlist' in
      if restrlist'' == [] then
	begin
	  match funlist' with
	    [Fun _] -> ()
	  | _ -> Parsing_helper.input_error "In equivalences, under a replication without new, there should be a single function" ext
	end;
      ReplRestr(repl_count', restrlist'', funlist')
  | PFun(((s, ext) as ch), arglist, tres, (priority, options)) ->
      let ch' = check_channel_id ch in
      if List.memq ch' (!seen_ch) then
	input_error ("Oracle name " ^ s ^ " already used in this equivalence") ext;
      seen_ch := ch' :: (!seen_ch);
      let (env', arglist') = check_binder_list2 cur_array env arglist in
      let tres' = check_term (Some []) cur_array env' tres in
      (* Note: restriction. Could be lifted, but simplifies cryptotransf.ml greatly 
	 Restriction partly lifted, by completing sequences of names with names already in the map.
      if not (List.for_all (List.for_all (fun b -> Terms.refers_to b tres')) cur_restr) then
	Parsing_helper.input_error ("In equivalences, each expression should use all names defined by\n" ^
				    "restrictions above it. This is a simplifying restriction.") (snd tres);
      *)
      check_bit_string_type (snd tres) tres'.t_type;
      List.iter2 (fun ((argname,ext),_) arg' ->
	if not (Terms.refers_to arg' tres') then
	  if (!Settings.front_end) == Settings.Channels then
            Parsing_helper.input_error ("Variable " ^ argname ^ " is not used in the result of the function") ext
	  else
	    Parsing_helper.input_error ("Variable " ^ argname ^ " is not used in the result of the oracle") ext
	      ) arglist arglist';
      let options' = ref StdOpt in
      List.iter (fun (s,ext) ->
	if s = "useful_change" then options' := UsefulChange else
	Parsing_helper.input_error ("Unrecognized option " ^ s ^ ". Only \"useful_change\" is allowed.") ext) options;
      Fun(ch', arglist', tres', (priority, !options'))


let rec check_rm_restrlist options2 cur_array env restrlist0 = function
    [] -> (env, [])
  | ((s1,ext1),(s2,ext2),opt)::l ->
      let t = get_type env s2 ext2 in
      if t.toptions land Settings.tyopt_CHOOSABLE == 0 then
	input_error ("Cannot choose randomly a bitstring from " ^ t.tname) ext2;
      let (env',b) = add_in_env env s1 ext1 t cur_array in
      let opt' = ref NoOpt in
      List.iter (fun (s,ext) ->
	if s = "unchanged" then 
	  if options2 = Computational then
	    if List.exists (fun (b',_) -> 
	      (b.sname = b'.sname) &&
	      (b.vname == b'.vname) &&
	      (b.btype == b'.btype)
	      ) restrlist0 then
	      opt' := Unchanged 
	    else
	      input_error "When a restriction is marked [unchanged] in the right-hand side,\nthere should exist a corresponding restriction of the same name in the\nleft-hand side" ext
	  else
	    input_error "The option [unchanged] is allowed only for computational equivalences" ext
	else
	  input_error "The only allowed option for restrictions is [unchanged]" ext
	  ) opt;
      let (env'',bl) = check_rm_restrlist options2 cur_array env' restrlist0 l in
      (env'', (b, !opt')::bl)

let rec check_rm_fungroup2 options2 cur_array env fg0 fg = 
  match (fg0, fg) with
    ReplRestr(repl_count0, restrlist0, funlist0),
    PReplRestr((repl_index_ref, _, (rep,ext)), restrlist, funlist) ->
      let repl_count' = 
	match !repl_index_ref with
	  Some b -> b
	| None -> Parsing_helper.internal_error "Repl index should have been initialized in check_rm_fungroup2"
      in
      let cur_array' = repl_count' :: cur_array in
      let (env',restrlist') = check_rm_restrlist options2 cur_array' env restrlist0 restrlist in
      if List.length funlist != List.length funlist0 then
	input_error "Different number of functions in left and right sides of equivalence" ext;
      if repl_count'.ri_type != repl_count0.ri_type then
	input_error "Different number of repetitions in left and right members of equivalence" ext;
      ReplRestr(repl_count', restrlist', List.map2 (check_rm_fungroup2 options2 cur_array' env') funlist0 funlist)
  | Fun(ch0, arglist0, tres0, priority0), PFun((ch, ext), arglist, tres, _) ->
      let (env', arglist') = check_binder_list2 cur_array env arglist in
      if List.length arglist' != List.length arglist0 then
	input_error "Argument lists have different lengths in left and right members of equivalence" (snd tres);
      List.iter2 (fun b b' ->
	if b.btype != b'.btype then
	  input_error "Incompatible types of arguments between left and right members of equivalence" (snd tres)
	    ) arglist' arglist0;
      let tres' = check_term (Some []) cur_array env' tres in
      (* Check that the type of the right member is the same as
	 the type of the corresponding left member. This is required
	 so that after transformation, the process remains well-typed. *)
      check_type (snd tres) tres' tres0.t_type;
      if ch <> ch0.cname then
	input_error "Oracle names should be the same in the left and right members of the equivalence" ext;
      (* The priority is ignored in the right-hand side; one takes
         the priority of the left-hand side *)
      Fun(ch0, arglist', tres', priority0)
  | _, PReplRestr((_, _, (_,ext)), _,_) ->
      input_error "Left member is a function, right member is a replication" ext
  | _, PFun(ch, arglist, tres, _) ->
      input_error "Left member is a replication, right member is a function" (snd tres)

let check_mode right = function
    Some (modes, ext) -> 
      if right then
	Parsing_helper.input_error "Modes can be specified only in the left-hand side of an equivalence" ext;
      if modes = "all" then AllEquiv else 
      if modes = "exist" then ExistEquiv else
      Parsing_helper.input_error "Only modes all and exist can be specified" ext
  | None -> ExistEquiv

let check_eqstatement (name, (mem1, ext1), (mem2, ext2), proba, (priority, options)) =
  let var_num_state = Terms.get_var_num_state() in
  let options' = ref StdEqopt in
  let options2' = ref Decisional in
  if priority != 0 then options' := PrioEqopt priority;
  List.iter (fun (s,ext) ->
    if s = "manual" then
      if !options' == StdEqopt then 
	options' := ManualEqopt 
      else
	Parsing_helper.input_error ("Conflicting options : you cannot specify both a priority and \"manual\"") ext 
    else if s = "computational" then 
      options2' := Computational 
    else
      Parsing_helper.input_error ("Unrecognized option " ^ s ^ ". Only \"manual\" is allowed.") ext
      ) options;
  let seen_repl = ref [] in
  let seen_ch = ref [] in
  set_binder_env 
    (List.fold_left (fun env (fg, _, _) -> check_fungroup1 [] env fg) empty_binder_env mem1); (* Builds binder_env *)
  let count_exist = ref 0 in
  let mem1' = List.map (fun (fg, mode, ext) ->
    let res = (check_lm_fungroup2 [] [] (!env) seen_ch seen_repl fg,
	       check_mode false mode)
    in
    match res with
      (ReplRestr(_,[],_), ExistEquiv) ->
	input_error "In equivalences, a function without any name should always be in mode [all]" ext
    | (_,ExistEquiv) -> incr count_exist; res
    | _ -> res
    ) mem1
  in
  (* The probability formula must be checked in the binder_env for the
     left-hand side of the equivalence. Arguments of Maxlength may use
     variables of the left-hand side of the equivalence. *)
  let proba' = check_probability_formula2 (!seen_ch) seen_repl (!env) proba in
  (*if !count_exist > 1 then
    input_error "In equivalences, there should be at most one function group without mode [all]" ext1;*)
  set_binder_env
    (check_rm_funmode_list empty_binder_env mem1 mem1' mem2); (* Builds binder_env *)
  let mem2' = List.map2 (fun (fg0, _) (fg, mode, _) -> 
    check_rm_fungroup2 (!options2') [] (!env) fg0 fg, check_mode true mode) mem1' mem2 
  in
  equivalences := (name, mem1',mem2', (if proba' = Zero then [] else [SetProba proba' ]), !options', !options2') :: (!equivalences);
  (* The variables defined in the equivalence are local,
     we can reuse the same numbers in other equivalences or
     in the process. *)
  Terms.set_var_num_state var_num_state

(* Check collision statement *)

let check_collision env (restr, forall, t1, proba, t2) =
  (* Note: This function uses check_binder_list, which calls
     Terms.create_binder0, so it does not rename the variables.
     That is why I do not save and restore the variable
     numbering state. *)
  set_binder_env empty_binder_env;
  let (env',restr') = check_binder_list env restr in
  List.iter2 (fun b (_,(_,ext)) ->
    if b.btype.toptions land Settings.tyopt_CHOOSABLE == 0 then
      input_error ("Cannot choose randomly a bitstring from " ^ b.btype.tname) ext
      ) restr' restr;
  let (env'',forall') = check_binder_list env' forall in
  let proba' = check_probability_formula2 [] (ref []) env'' proba in
  let t1' = check_term_nobe env'' t1 in
  if not (List.for_all (fun b -> Terms.refers_to b t1') (restr' @ forall')) then
    input_error "In collision statements, all bound variables should occur in the left-hand side" (snd t1);
  let t2' = check_term_nobe env'' t2 in
  check_bit_string_type (snd t1) t1'.t_type;
  if t1'.t_type != t2'.t_type then 
    input_error "Both sides of a collision statement should have the same type" (snd t2);
  collisions := (restr', forall', t1', proba', t2') :: (!collisions)


(* Check process
   check_process returns the process, as well as a list of oracles with their
   types (oracle name, list of index types, list of args types, list of result types)
   check_oprocess returns the process, as well as a list of oracles with their
   types and the list of result types returned by this process
 *)

let eqtypes tl1 tl2 = 
  (List.length tl1 == List.length tl2) &&
  (List.for_all2 (fun t1 t2 -> (t1 == t2) || (t1 != Settings.t_any) || (t2 != Settings.t_any)) tl1 tl2)

exception IncompatibleTypes

let mergetypesopt topt1 topt2 = 
  match topt1,topt2 with
    None,_ -> topt2
  | _,None -> topt1
  | Some tl1,Some tl2 -> 
      if not (eqtypes tl1 tl2) then 
	raise IncompatibleTypes
      else
	topt1

let mergeres ext topt1 topt2 =
  try
    mergetypesopt topt1 topt2
  with IncompatibleTypes ->
    input_error "Several branches of a process have incompatible return types" ext

let rec check_distinct ext l1 = function
    [] -> ()
  | (ch,_,_,_)::l -> 
      if List.exists (fun (ch',_,_,_) -> ch == ch') l1 then
	input_error ("Duplicate definitions of oracle " ^ ch.cname) ext
      else
	check_distinct ext l1 l

let rec check_compatible ext l1 = function
    [] -> l1
  | (ch,tindex,targs,tres)::l ->
      let l1' = check_compatible ext l1 l in
      begin
      try
	let (ch',tindex',targs',tres') = List.find (fun (ch',_,_,_) -> ch == ch') l1 in
	if not (eqtypes tindex tindex') then
	  input_error ("Definitions of oracle " ^ ch.cname ^ " with different replication indexes types") ext;
	if not (eqtypes targs targs') then
	  input_error ("Definitions of oracle " ^ ch.cname ^ " with different argument types") ext;
	try
	  let tres'' = mergetypesopt tres tres' in
	  (ch,tindex,targs,tres'') :: (List.filter (fun (ch',_,_,_) -> ch != ch') l1')
	with IncompatibleTypes ->
	  input_error ("Definitions of oracle " ^ ch.cname ^ " with different result types") ext
      with Not_found -> 
	(ch,tindex,targs,tres)::l1'
      end

let dummy_channel = { cname = "dummy_channel" }


(* Add a role *)

let check_opt opt =
  List.map (function
      PRead (id,(f,ext')) ->
	let b = get_global_binder "in read variables" id in
	Read (b,f)
    | PWrite (id,(f,ext')) ->
	let b = get_global_binder "in written variables" id in
	Write (b,f)
          ) opt
    
let add_role ((id,ext),opt) ip =
  try 
    let _=StringMap.find id !impl_roles in
      input_error ("Role " ^ id ^ " has already been defined") ext
  with Not_found ->
    impl_roles := StringMap.add id (ip,check_opt opt) !impl_roles

(* when t is a variable b0 with current repl. ind. and
   b has no array accesses, use b0 instead of b *)
let add_in_env_reuse_var env s ext ty cur_array t =
  match t.t_desc with
    Var(b0,l) when Terms.is_args_at_creation b0 l ->
      begin
	if (StringMap.mem s env) then
	  input_warning ("identifier " ^ s ^ " rebound") ext;
	match get_global_binder_if_possible s with
	  Some b -> 
	    (StringMap.add s (EVar b) env, [PatVar b, t])
	| None ->
	    (StringMap.add s (EVar b0) env, [])
      end
  | ReplIndex b0 ->
      begin
	if (StringMap.mem s env) then
	  input_warning ("identifier " ^ s ^ " rebound") ext;
	match get_global_binder_if_possible s with
	  Some b -> 
	    (StringMap.add s (EVar b) env, [PatVar b, t])
	| None ->
	    (StringMap.add s (EReplIndex b0) env, [])
      end
  | _ ->
      let (env', b) = add_in_env env s ext ty cur_array in
      (env', [PatVar b, t])
    

let rec check_args cur_array env vardecl args =
  match (vardecl, args) with
    [], [] -> (env, [])
  | [], _ | _, [] ->
      Parsing_helper.internal_error "Syntax.check_args vardecl and args should have the same length"
  | ((s1, ext1), tyb)::rvardecl, t::rargs ->
      let ty = t.t_type in 
      let (ty', ext2) = get_ty env tyb in
      if ty != ty' then
	input_error ("Process expects an argument of type " ^ ty'.tname ^ " but is here given an argument of type " ^ ty.tname) t.t_loc;
      let (env',letopt) = add_in_env_reuse_var env s1 ext1 ty' cur_array t in
      (* when t is a variable b0 with current repl. ind. and
	 b has no array accesses, use b0 instead of b *)
      let (env'', rlets) = check_args cur_array env' rvardecl rargs in
      (env'', letopt @ rlets)

let rec check_process defined_refs cur_array env prog = function
    PBeginModule (a,p), ext ->
      if (prog <> None) then
         input_error "Roles cannot be nested" ext
      else
        let (p,oracle,ip) = check_process defined_refs cur_array env (Some a) p in
          add_role a ip;
          (p,oracle,ip)
  | PNil, _ -> (iproc_from_desc Nil, [], iproc_from_desc Nil)
  | PPar(p1,p2), ext -> 
      let (p1',oracle1,ip1) = check_process defined_refs cur_array env prog p1 in
      let (p2',oracle2,ip2) = check_process defined_refs cur_array env prog p2 in
        check_distinct ext oracle1 oracle2;
        (iproc_from_desc (Par(p1',p2')), oracle1 @ oracle2, iproc_from_desc (Par(ip1,ip2)))
  | PRepl(repl_index_ref,idopt,(s2,ext2),p), _ ->
      let b' = 
	match !repl_index_ref with
	  Some b -> b
	| None -> Parsing_helper.internal_error "Repl index should have been initialized in check_process"
      in
      let env' =
	match idopt with
	  None -> env
	| Some(id,ext) -> StringMap.add id (EReplIndex b') env
      in
      let (p',oracle,ip) = check_process defined_refs (b'::cur_array) env' prog p in
      (iproc_from_desc (Repl(b', p')), oracle, iproc_from_desc (Repl(b',ip)))
  | PInput(t, pat, p), ext ->
      let ((c, _) as t') = check_process_channel cur_array env t in
      let (env', pat') = check_pattern (Some defined_refs) cur_array env None pat in
      let (p', tres, oracle,ip) = check_oprocess defined_refs cur_array env' prog p in
        if (!Settings.front_end) == Settings.Channels then
	  (iproc_from_desc (Input(t', pat', p')), oracle, iproc_from_desc (Input(t',pat',ip)))
        else
	  begin
	    if List.exists (fun (c',_,_,_) -> c' == c) oracle then
	      input_error ("Duplicate definitions of oracle " ^ c.cname ^ 
			   "\n(The second definition is located under the return of the first one.)") ext;
	    match pat' with
	        PatTuple(_,patl) ->
	          (iproc_from_desc (Input(t', pat', p')), 
	           (c, List.map (fun ri -> ri.ri_type) cur_array, 
		    List.map get_type_for_pattern patl, tres)::oracle,
                   iproc_from_desc (Input(t',pat',ip)))
	      | _ -> internal_error "One can only have a tuple as argument"
	  end
  | PLetDef((s,ext),args), _ ->
      let (env', vardecl, p) = get_process env s ext in
      if List.length vardecl != List.length args then
	Parsing_helper.input_error ("Process "^s^" expects "^(string_of_int (List.length vardecl))^" argument(s), but is here given "^(string_of_int (List.length args))^" argument(s)") ext;
      let args' = List.map (check_term (Some defined_refs) cur_array env) args in
      (* Only simple terms (variables, replication indices, and function 
	 applications) are allowed in arguments. *)
      List.iter (fun t ->
	check_no_iffindletnewevent "argument of a parametric input process" t.t_loc t) args';
      let (env'', lets) = check_args cur_array env' vardecl args' in
      let (p', oracles, ip) = check_process [] cur_array env'' prog p in
      (* Array accesses are forbidden for the arguments of the process.
	 (This is guaranteed in check_process1.)
	 So we just replace the variables with their values. *)
      Terms.auto_cleanup (fun () ->
	List.iter (function
	    PatVar b, t -> Terms.link b (TLink t)
	  | _ -> Parsing_helper.internal_error "PLetDef: lets should bind variables"
		) lets;
	let p_inst' = copy_process Links_Vars p' in
	let ip_inst = copy_process Links_Vars ip in
	(p_inst', oracles, ip_inst)
	  )
  | _, ext ->
      input_error "input process expected" ext

and check_oprocess defined_refs cur_array env prog = function
    PYield, _ -> (oproc_from_desc Yield, None, [], oproc_from_desc Yield)
  | PEventAbort(s,ext), _ -> 
      begin
      try 
	match StringMap.find s env with
	  EEvent(f) ->
	    check_type_list ext [] [] (List.tl (fst f.f_type));
	    let p_desc = EventAbort(f) in
	    (oproc_from_desc p_desc, None, [], oproc_from_desc p_desc)
	| _ -> input_error (s ^ " should be an event") ext
      with Not_found ->
	input_error (s ^ " not defined") ext
      end
  | PRestr((s1,ext1),(s2,ext2),p), _ ->
      let t = get_type env s2 ext2 in
        if t.toptions land Settings.tyopt_CHOOSABLE == 0 then
	  input_error ("Cannot choose randomly a bitstring from " ^ t.tname) ext2;
        let (env',b) = add_in_env env s1 ext1 t cur_array in
        let (p', tres, oracle,ip') = check_oprocess defined_refs cur_array env' prog p in
          (oproc_from_desc (Restr(b, p')), tres, oracle,
           oproc_from_desc (Restr(b, ip')))
  | PLetDef((s,ext), args), _ ->
      let (env', vardecl, p) = get_process env s ext in
      if List.length vardecl != List.length args then
	Parsing_helper.input_error ("Process "^s^" expects "^(string_of_int (List.length vardecl))^" argument(s), but is here given "^(string_of_int (List.length args))^" argument(s)") ext;
      let args' = List.map (check_term (Some defined_refs) cur_array env) args in
      let (env'', lets) = check_args cur_array env' vardecl args' in
      let (p', tres, oracle, ip')  = check_oprocess [] cur_array env'' prog p in
      (Terms.put_lets lets p' (Terms.oproc_from_desc Yield), tres, oracle,
       Terms.put_lets lets ip' (Terms.oproc_from_desc Yield))
  | PTest(t,p1,p2), ext ->
      let t' = check_term (Some defined_refs) cur_array env t in
        check_type (snd t) t' Settings.t_bool;
        let (p1',tres1,oracle1,ip1') = check_oprocess defined_refs cur_array env prog p1 in
        let (p2',tres2,oracle2,ip2') = check_oprocess defined_refs cur_array env prog p2 in
          (oproc_from_desc (Test(t', p1', p2')),
           mergeres ext tres1 tres2, check_compatible ext oracle1 oracle2,
           oproc_from_desc (Test(t', ip1', ip2')))
  | PFind(l0,p2,opt), ext ->
      let find_info = ref Nothing in
      List.iter (fun (s,ext_s) ->
	if s = "unique" then
          begin
            find_info := Unique;
            if !current_location = InProcess then
              Parsing_helper.input_warning "The [unique] option is primarily intended for use in declarations of primitives. If you use it in processes, you must guarantee yourself that this find will have a unique successful branch/index." ext_s
          end
	else
          Parsing_helper.input_error "The only option allowed for find is unique" ext_s
	    ) opt;
      let (p2', tres2, oracle2,ip2') = check_oprocess defined_refs cur_array env prog p2 in
      let trescur = ref tres2 in
      let oraclecur = ref oracle2 in
      let rec add env = function
	  [] -> (env,[])
	| ((s0,ext0),(s1,ext1),(s2,ext2))::bl ->
	    let p = get_param env s2 ext2 in
	    let (env',b) = add_in_env env s0 ext0 (type_for_param p) cur_array in
	    let (env'',bl') = add env' bl in
	      (env'',b::bl')
      in
      let (l0',il0') = List.fold_left (fun (accu, iaccu) (bl_ref,bl,def_list,t,p1) ->
	try 
	  let (env', bl') = add env bl in
	  let bl'' = !bl_ref in (* recover replication indices *)
	  let env'' = List.fold_left2 (fun env (_,(s1, ext1),_) b -> StringMap.add s1 (EReplIndex b) env) env bl bl'' in
	  let cur_array' = bl'' @ cur_array in
	  let bl_bin = List.combine bl' bl'' in
	  let def_list' = List.map (check_br cur_array' env'') def_list in
	  let (defined_refs_t, defined_refs_p1) = Terms.defined_refs_find bl_bin def_list' defined_refs in
	  let t' = check_term (Some defined_refs_t) cur_array' env'' t in
	  check_no_new_event_insert (snd t) false t';
	  check_type (snd t) t' Settings.t_bool;
	  let (p1', tres1, oracle1,ip1') = check_oprocess defined_refs_p1 cur_array env' prog p1 in
	  trescur := mergeres ext tres1 (!trescur);
	  oraclecur := check_compatible ext oracle1 (!oraclecur);
	  (bl_bin, def_list', t', p1')::accu,(bl_bin, def_list', t', ip1')::iaccu
	with RemoveFindBranch ->
	  accu, iaccu
	    ) ([],[]) l0
      in
      (oproc_from_desc (Find(List.rev l0', p2',!find_info)), (!trescur), (!oraclecur),
       oproc_from_desc (Find(List.rev il0',ip2', !find_info)))
  | POutput(rt,t1,t2,p), ext ->
      let t2' = check_term (Some defined_refs) cur_array env t2 in
      begin
        match t2'.t_type.tcat with
	  Interv _ -> input_error "Cannot output a term of interval type" (snd t2)
        |	_ -> ()
      end;
      if rt && prog = None then
	input_error "Cannot close inexistent role" ext;
      let (p', oracle,ip'') = check_process defined_refs cur_array env (if rt then None else prog) p in
      let ip'=if rt then (iproc_from_desc Nil) else ip'' in
      if (!Settings.front_end) == Settings.Channels then
	let t1' = check_process_channel cur_array env t1 in
	(oproc_from_desc (Output(t1', t2', p')), None, oracle,oproc_from_desc (Output(t1', t2', ip')))
      else
	begin
	  match t2'.t_desc with
	    FunApp(_,tl) ->
	      (oproc_from_desc (Output((dummy_channel, []), t2', p')), 
	       Some (List.map (fun t -> t.t_type) tl), oracle,
               oproc_from_desc (Output((dummy_channel, []), t2', ip')))
	  | _ -> 
	      internal_error "One can only return a tuple"
	end
  | PLet(pat, t, p1, p2), ext ->
      let t' = check_term (Some defined_refs) cur_array env t in
      let (env', pat') = check_pattern (Some defined_refs) cur_array env (Some t'.t_type) pat in
      let (p1',tres1,oracle1,ip1') = check_oprocess defined_refs cur_array env' prog p1 in
      let (p2',tres2,oracle2,ip2') = check_oprocess defined_refs cur_array env prog p2 in
        (oproc_from_desc (Let(pat', t', p1', p2')), 
         mergeres ext tres1 tres2, check_compatible ext oracle1 oracle2,
         oproc_from_desc (Let(pat', t', ip1', ip2')))
  | PEvent((PFunApp((s,ext0),tl), ext), p), ext2 ->
      begin
        try 
	  match StringMap.find s env with
	      EEvent(f) ->
	        let tl' = List.map (check_term (Some defined_refs) cur_array env) tl in
	          check_type_list ext tl tl' (List.tl (fst f.f_type));
	          let tupf = Settings.get_tuple_fun (List.map (fun ri -> ri.ri_type) cur_array) in
	            event_type_list := (f, tupf) :: (!event_type_list);
	          let tcur_array =
		    Terms.new_term Settings.t_bitstring ext2
		     (FunApp(tupf, List.map Terms.term_from_repl_index cur_array))
	          in
	          let (p', tres, oracle,ip') = check_oprocess defined_refs cur_array env prog p in
                  let event =
		    Terms.new_term Settings.t_bool ext2 (FunApp(f, tcur_array::tl'))
		  in
	          (oproc_from_desc 
	             (EventP(event, p')), tres, oracle,
                   oproc_from_desc (EventP(event, ip')))
	    | _ -> input_error (s ^ " should be an event") ext0
        with Not_found ->
	  input_error (s ^ " not defined") ext0
      end
  | PGet((id,ext),patl,topt,p1,p2),_ -> 
      let tbl = get_table env id ext in
      let (p2',tres2,oracle2,ip2') = check_oprocess defined_refs cur_array env prog p2 in
      let (env', patl') = check_pattern_list (Some defined_refs) cur_array env (List.map (fun x->Some x) tbl.tbltype) patl in
      let topt' = 
	match topt with 
	  None -> None 
	| Some t -> 
	    let t' = check_term (Some defined_refs) cur_array env' t in
	    check_no_new_event_insert (snd t) true t';
	    check_type (snd t) t' Settings.t_bool;
	    Some t'
      in
      let (p1',tres1,oracle1,ip1') = check_oprocess defined_refs cur_array env' prog p1 in
        (oproc_from_desc (Get(tbl, patl',topt',p1', p2')),
         mergeres ext tres1 tres2, check_compatible ext oracle1 oracle2,
         oproc_from_desc (Get(tbl, patl',topt',ip1', ip2')))
          
  | PInsert((id,ext),tl,p),ext2 ->
      let tbl = get_table env id ext in
      let t' = List.map (check_term (Some defined_refs) cur_array env) tl in
        check_type_list ext2 tl t' tbl.tbltype;
        let (p',tres,oracle,ip') = check_oprocess defined_refs cur_array env prog p in
          (oproc_from_desc (Insert(tbl, t', p')), tres, oracle,
           oproc_from_desc (Insert(tbl, t', ip')))
            
  | _, ext -> 
      input_error "non-input process expected" ext
        
(* Macro expansion *)

let rename_table = ref StringMap.empty

let get_rename_state() =
  (!rename_table, Terms.get_var_num_state())

let set_rename_state (rename_tbl, var_num_state) =
  rename_table := rename_tbl;
  Terms.set_var_num_state var_num_state
    
let rename_ident i = 
  try
    StringMap.find i (!rename_table)
  with Not_found ->
    let r = Terms.fresh_id i in
    rename_table := StringMap.add i r (!rename_table);
    r

let rename_ie (i,ext) = (rename_ident i, ext)

let rename_channel (i, idx_opt) =
  (rename_ie i,
   match idx_opt with
     None -> None
   | Some l -> Some (List.map rename_ie l))
    
let rename_ty = function
    Tid i -> Tid (rename_ie i)
  | TBound n -> TBound (rename_ie n)
    
let rec rename_term (t,ext) = 
  let t' = match t with
    PIdent i -> PIdent (rename_ie i)
  | PArray(i,l) -> PArray(rename_ie i, List.map rename_term l)
  | PFunApp(f,l) -> PFunApp(rename_ie f, List.map rename_term l)
  | PQEvent(inj,t) -> PQEvent(inj, rename_term t)
  | PTuple(l) -> PTuple(List.map rename_term l)
  | PTestE(t1,t2,t3) -> PTestE(rename_term t1, rename_term t2, rename_term t3)
  | PFindE(l,t,opt) -> PFindE(List.map (fun (_,bl, def_list, c,t) ->
      (ref [], 
       List.map (fun (x,y,t) -> (rename_ie x, rename_ie y, rename_ie t)) bl,
       List.map rename_br def_list,
       rename_term c,
       rename_term t)) l, rename_term t, opt)
  | PLetE(pat, t1, t2, topt) ->
      PLetE(rename_pat pat, rename_term t1, rename_term t2, match topt with
	None -> None
      |	Some t -> Some (rename_term t))
  | PResE(i,ty,t) -> PResE(rename_ie i, rename_ie ty, rename_term t)
  | PEventAbortE(i) -> PEventAbortE(rename_ie i)
  | PEventE(t,p) -> PEventE(rename_term t, rename_term p)
  | PGetE(id, patlist, topt, p1, p2) ->
      PGetE(rename_ie id, List.map rename_pat patlist, (match topt with None -> None|Some t -> Some (rename_term t)), rename_term p1, rename_term p2)
  | PInsertE(id, tlist, p) ->
      PInsertE(rename_ie id, List.map rename_term tlist, rename_term p)
  | PEqual(t1,t2) -> PEqual(rename_term t1, rename_term t2)
  | PDiff(t1,t2) -> PDiff(rename_term t1, rename_term t2)
  | POr(t1,t2) -> POr(rename_term t1, rename_term t2)
  | PAnd(t1,t2) -> PAnd(rename_term t1, rename_term t2)
  in
  (t',ext)

and rename_pat = function
    PPatVar(i,topt), ext -> PPatVar(rename_ie i, match topt with
      None -> None
    | Some t -> Some (rename_ty t)), ext
  | PPatTuple(l), ext -> PPatTuple(List.map rename_pat l), ext
  | PPatFunApp(f,l), ext -> PPatFunApp(rename_ie f, List.map rename_pat l), ext
  | PPatEqual t, ext -> PPatEqual(rename_term t), ext

and rename_br (b, tl) = (rename_ie b, List.map rename_term tl)

let rec rename_proc (p, ext) = 
  let p' = match p with
    PNil -> PNil
  | PYield -> PYield
  | PEventAbort id -> PEventAbort(rename_ie id)
  | PPar(p1,p2) -> PPar(rename_proc p1, rename_proc p2)
  | PRepl(i, idopt, id, p) -> PRepl(ref None, (match idopt with
      None -> None
    | Some id -> Some (rename_ie id)), rename_ie id, rename_proc p)
  | PRestr(id,t,p) -> PRestr(rename_ie id, rename_ie t, rename_proc p)
  | PLetDef(x, tl) -> PLetDef(rename_ie x, List.map rename_term tl)
  | PTest(t,p1,p2) -> PTest(rename_term t, rename_proc p1, rename_proc p2)
  | PFind(l,p,opt) -> PFind(List.map (fun (_, bl, def_list, c,p1) ->
      (ref [],
       List.map (fun (x,y,t) -> (rename_ie x, rename_ie y, rename_ie t)) bl,
       List.map rename_br def_list,
       rename_term c,
       rename_proc p1)) l, rename_proc p, opt)
  | PEvent(t,p) -> PEvent(rename_term t, rename_proc p)
  | PInput(c,tpat,p) -> PInput(rename_channel c, rename_pat tpat, rename_proc p)
  | POutput(b,c,t2,p) -> POutput(b,rename_channel c, rename_term t2, rename_proc p)
  | PLet(pat, t, p1, p2) -> PLet(rename_pat pat, rename_term t, rename_proc p1, rename_proc p2)
  | PGet(id, patlist, sto, p1,p2) -> PGet(rename_ie id, List.map rename_pat patlist, (match sto with None -> None|Some t -> Some (rename_term t)), rename_proc p1, rename_proc p2)
  | PInsert(id, tlist, p) -> PInsert(rename_ie id, List.map rename_term tlist, rename_proc p)
  | PBeginModule ((id,opt),p) -> PBeginModule ((id,opt),rename_proc p)
  in
    (p', ext)

let rename_act = function
    PAFunApp i -> PAFunApp (rename_ie i)
  | PAPatFunApp i -> PAPatFunApp (rename_ie i)
  | (PAReplIndex | PAArrayAccess _ | PACompare _ |
     PAAnd | PAOr | PANewChannel | PAIf | PAFind _ | PAIn _) as x -> x
  | PAAppTuple l -> PAAppTuple (List.map rename_ie l)
  | PAPatTuple l -> PAPatTuple (List.map rename_ie l)
  | PANew i -> PANew  (rename_ie i)
  | PAOut (l, t) -> PAOut(List.map rename_ie l, rename_ie t)

let rec rename_probaf (p,ext) =
  let p' = match p with
    PAdd(p1,p2) -> PAdd(rename_probaf p1, rename_probaf p2)
  | PSub(p1,p2) -> PSub(rename_probaf p1, rename_probaf p2)
  | PProd(p1,p2) -> PProd(rename_probaf p1, rename_probaf p2)
  | PDiv(p1,p2) -> PDiv(rename_probaf p1, rename_probaf p2)
  | PMax l -> PMax (List.map rename_probaf l)
  | PPIdent i -> PPIdent (rename_ie i)
  | PCount i -> PCount (rename_ie i)
  | PPFun(i,l) -> PPFun(rename_ie i, List.map rename_probaf l)
  | (PPZero | PCst _ | PFloatCst _ | PTime) as x -> x
  | PCard i -> PCard (rename_ie i)
  | PActTime(act, l) -> PActTime(rename_act act, List.map rename_probaf l)
  | PMaxlength t -> PMaxlength (rename_term t)
  | PLength(i,l) -> PLength(rename_ie i, List.map rename_probaf l)
  | PLengthTuple(il,l) -> PLengthTuple(List.map rename_ie il, 
				       List.map rename_probaf l)
  | PEpsFind -> PEpsFind
  | PEpsRand i -> PEpsRand (rename_ie i)
  | PPColl1Rand i -> PPColl1Rand (rename_ie i)
  | PPColl2Rand i -> PPColl2Rand (rename_ie i)
  in
  (p', ext)

let rec rename_fungroup = function
    PReplRestr((n, iopt, i), lres, lfg) ->
      PReplRestr((ref None, 
		  (match iopt with
		    None -> None
		  | Some i1 -> Some (rename_ie i1)), rename_ie i),
		 List.map (fun (x,t,opt) -> (rename_ie x, rename_ie t,opt)) lres,
		 List.map rename_fungroup lfg)
  | PFun(i, larg, r, n) ->
      PFun(rename_ie i,
	   List.map (fun (x,t) -> (rename_ie x, rename_ty t)) larg,
	   rename_term r, n)

let rename_eqname = function
    CstName i -> CstName i
  | ParName(i,p) -> ParName(i, rename_ie p)
  | NoName -> NoName

let rename_eqmember (l,ext1) =
  (List.map (fun (fg, mode, ext) -> (rename_fungroup fg, mode, ext)) l, ext1) (* Do not rename the mode! *)

let rename_query = function
    PQSecret (i, pub_vars, options) -> PQSecret (rename_ie i, List.map rename_ie pub_vars, options)
  | PQEventQ(decl,t1,t2, pub_vars) -> 
      PQEventQ(List.map (fun (x,t) -> (rename_ie x, rename_ty t)) decl, 
	      rename_term t1, rename_term t2, List.map rename_ie pub_vars)



let rename_impl = function
  | Type(t,s,o) -> Type(rename_ie t, s, o)
  | Function(name,f,fo) -> 
      Function(rename_ie name,f,fo)
  | Constant(name,c) ->
      Constant(rename_ie name,c)
  | ImplTable(tbl,file) -> ImplTable(rename_ie tbl,file)

let rename_decl = function
    ParamDecl((s,ext), options) ->
      ParamDecl((rename_ident s, ext), options)
  | ProbabilityDecl(s,ext) ->
      ProbabilityDecl(rename_ident s, ext)
  | TypeDecl(s,options) ->
      TypeDecl(rename_ie s, options)
  | ConstDecl(s1,s2) ->
      ConstDecl(rename_ie s1, rename_ie s2)
  | ChannelDecl(s1,ext1) ->
      ChannelDecl(rename_ident s1, ext1)
  | Setting((p,ext),v) -> Setting((p,ext),v)
  | FunDecl(s1,l,sr,f_options) ->
      FunDecl(rename_ie s1,
	      List.map rename_ie l,
	      rename_ie sr,f_options)
  | EventDecl(s1, l) ->
      EventDecl(rename_ie s1, List.map rename_ie l)
  | Statement(l, t) ->
      (* Variables created in the statement are local, 
         I can reuse their names later *)
      let rename_state = get_rename_state() in
      let renamed_statement =
	Statement(List.map (fun (i,t) -> (rename_ie i, rename_ie t)) l,
		  rename_term t)
      in
      set_rename_state rename_state;
      renamed_statement
  | BuiltinEquation(eq_categ, l_fun_symb) ->
      BuiltinEquation(eq_categ, List.map rename_ie l_fun_symb)
  | EqStatement(n, l,r,p,options) ->
      let n' = rename_eqname n in
      (* Variables created in the statement are local, 
         I can reuse their names later *)
      let rename_state = get_rename_state() in
      let renamed_eq_statement =
	EqStatement(n', rename_eqmember l, rename_eqmember r, rename_probaf p, options)
      in
      set_rename_state rename_state;
      renamed_eq_statement
  | Collision(restr, forall,  t1, p, t2) ->
      (* Variables created in the statement are local, 
         I can reuse their names later *)
      let rename_state = get_rename_state() in
      let renamed_coll_statement =
	Collision(List.map (fun (x,t) -> (rename_ie x, rename_ie t)) restr,
		  List.map (fun (x,t) -> (rename_ie x, rename_ie t)) forall,
		  rename_term t1,
		  rename_probaf p,
		  rename_term t2)
      in
      set_rename_state rename_state;
      renamed_coll_statement      
  | Query (vars, l) ->
      (* For queries, some variables are local (those in correspondence
         queries), but some are global (those in secrecy queries and
         public variables). For simplicity, I do not allow reusing
         the same names for any of these variables *)
      Query(List.map (fun (x,t) -> (rename_ie x, rename_ty t)) vars,
	    List.map rename_query l)
  | PDef(s,vardecl,p) ->
      PDef(rename_ie s,
	   List.map (fun (x,t) -> (rename_ie x, rename_ty t)) vardecl,
	   rename_proc p)
  | Proofinfo(pr) ->
      begin
	match pr with
	  ((_, ext)::_)::_ ->
	    input_error "Proof indications not allowed in macros" ext
	| _ -> internal_error "empty proof"
      end
  | Define((s1,ext1),argl,def) ->
      input_error "macro definitions are not allowed inside macro definitions" ext1
  | Expand((s1,ext1),argl) ->
      Expand((s1,ext1), List.map rename_ie argl)
  | Expanded _ ->
      internal_error "expanded macros should be subject to renaming"
  | Implementation(ilist) ->
      Implementation(List.map rename_impl ilist)
  | TableDecl (id, tlist) ->
      TableDecl(rename_ie id, List.map rename_ie tlist)
  | LetFun(name,l,t) ->
      (* The defined function is global, it must not be reused *)
      let name' = rename_ie name in
      (* Variables created in the statement are local, 
         I can reuse their names later *)
      let rename_state = get_rename_state() in
      let renamed_letfun_statement =
	LetFun(name',
	       List.map (fun (b,t) -> (rename_ie b,rename_ty t)) l,
	       rename_term t)
      in
      set_rename_state rename_state;
      renamed_letfun_statement      
	

let apply argl paraml already_def def =
  rename_table := StringMap.empty;
  List.iter (fun s -> 
    rename_table := StringMap.add s s (!rename_table)) already_def;
  List.iter2 (fun (a,_) (p,_) -> 
    rename_table := StringMap.add p a (!rename_table)) argl paraml;
  let def' = List.map rename_decl def in
  rename_table := StringMap.empty;
  def'


(* Check declarations *)

let add_not_found s ext v =
  if StringMap.mem s (!env) then
    input_error (s ^ " already defined.") ext
  else
    env := StringMap.add s v (!env)

let rec write_type_options typ = function
  | ((i,ext), l)::l' ->
      begin
        if i = "pred" then
          match l with 
            | [ (pr,ext) ] -> 
                if typ.timplsize != None then
                  input_error ("Cannot set predicate for type "^typ.tname^".\n(Predicate already determined by the size.)") ext
                else
                  typ.tpredicate <- Some pr
            | _ ->
                input_error "Wrong format for the pred option" ext
        else
        if i = "serial" then
          match l with 
            | [(s,ext); (d,ext')] ->
                typ.tserial <- Some(s,d)
            | _ ->
                input_error "Wrong format for the serial option" ext
        else
        if i = "random" then
          match l with
            | [ (r,ext) ] ->
                if (typ.timplsize <> None) && (typ.toptions land Settings.tyopt_NONUNIFORM == 0) then
                  input_error ("Cannot set random generator function for type "^typ.tname^".\n(Function already determined by the size and the generator is uniform.)") ext
                else if typ.toptions land Settings.tyopt_CHOOSABLE == 0 then
		  input_error ("One cannot generate random values from type  "^typ.tname^".\nYou should not specify the random generator.") ext
		else
                  typ.trandom <- Some r
            | _ -> 
                input_error "Wrong format for the random option" ext
        else
          input_error ("Type option "^i^" not recognized") ext
      end;
      write_type_options typ l'
  | [] -> ()

let rec write_fun_options fu = function
  | ((i,ext), (j,ext'))::l' ->
      begin
        if i = "inverse" then
          if (fu.f_options land Settings.fopt_COMPOS) <> 0 then
            fu.f_impl_inv <- Some(j)
          else
            input_error (fu.f_name^" is not composable and an inverse is given.") ext' 
        else
          input_error ("Fun option "^i^" not recognized") ext
      end;
      write_fun_options fu l'
  | [] -> ()


let rec check_one = function
    ParamDecl((s,ext), options) ->
      let size =
	match options with
	  [] -> Settings.psize_DEFAULT
	| ["noninteractive",_] -> Settings.psize_NONINTERACTIVE
	| ["passive",_] -> Settings.psize_PASSIVE
	| [sopt,extopt] -> (* option "size<n>" where <n> is an integer *)
	    begin
	      try
		if (String.sub sopt 0 4) <> "size" then raise Not_found;
		int_of_string (String.sub sopt 4 (String.length sopt - 4))
	      with _ ->
		Parsing_helper.input_error ("Unknown parameter option " ^ sopt) extopt
	    end
	| _::_::_ -> Parsing_helper.input_error "Parameters accept a single size option" ext
      in
      add_not_found s ext (EParam{ pname = s; psize = size })
  | ProbabilityDecl(s,ext) ->
      add_not_found s ext (EProba{ prname = s })
  | TableDecl((s,ext),st) ->
      add_not_found s ext (ETable ({ tblname = s; tbltype = List.map (fun (s,ext)   -> get_type (!env) s ext) st; tblfile = None }))
  | TypeDecl((s1,ext1),options) ->
	let opt = ref 0 in
	let size = ref Settings.tysize_SMALL in
	List.iter (fun (sopt, extopt) ->
	  match sopt with
	    "fixed" -> opt := (!opt) lor Settings.tyopt_FIXED lor Settings.tyopt_BOUNDED
	  | "bounded" -> opt := (!opt) lor Settings.tyopt_BOUNDED
	  | "nonuniform" -> opt := (!opt) lor Settings.tyopt_NONUNIFORM
	  | _ -> (* options large, password, size<n> *)
	      try
		let r = Settings.parse_type_size sopt in
		if (!size) <> Settings.tysize_SMALL then
		  Parsing_helper.input_error ("Types options large, password, and size<n> are incompatible") ext1;
		size := r
	      with Not_found ->
		Parsing_helper.input_error ("Unknown type option " ^ sopt) extopt
	      ) options;
	let ty = { tname = s1;
		   tcat = BitString;
		   toptions = !opt;
		   tsize = !size;
                   timplsize = None;
                   tpredicate = None;
                   timplname = None;
                   tserial = None;
                   trandom = None }
	in
	add_not_found s1 ext1 (EType ty);
	(* register the "move array" transformation for that type *)
	if (!opt) land Settings.tyopt_CHOOSABLE != 0 then
	  begin
	    try
	      let Macro(paraml, def, already_def, _) = StringMap.find "move_array_internal_macro" (!macrotable) in
	      if List.length paraml != 1 then
		input_error ("Macro move_array_internal_macro should expect one argument but expects " ^ (string_of_int (List.length paraml)) ^ " arguments.") ext1;
	      let old_equivalences = !equivalences in
	      let old_env = !env in
	      List.iter check_one (apply [(s1,ext1)] paraml already_def def);
	      env := old_env;
	      match !equivalences with
		[] -> input_error ("Macro move_array_internal_macro should define an equivalence.") ext1
	      |	(eq::rest) ->
		  if rest != old_equivalences then
		    input_error ("Macro move_array_internal_macro should define exactly one equivalence.") ext1;
		  equivalences := old_equivalences;
		  move_new_eq := (ty, eq) :: (!move_new_eq)
	    with Not_found -> 
	      (* Macro move_array_internal_macro not defined *)
	      ()
	  end
  | ConstDecl((s1,ext1),(s2,ext2)) ->
      let s2' = get_type (!env) s2 ext2 in
      add_not_found s1 ext1 (EFunc{ f_name = s1;
				    f_type = [], s2';
				    f_cat = Std;
				    f_options = 0;
				    f_statements = [];
				    f_collisions = [];
				    f_eq_theories = NoEq;
                                    f_impl = No_impl;
                                    f_impl_inv = None })
  | ChannelDecl(s1,ext1) ->
      if (!Settings.front_end) == Settings.Channels then
	add_not_found s1 ext1 (EChannel{ cname = s1 })
      else
	internal_error "ChannelDecl not allowed in oracles front-end"
  | Setting((p,ext),v) ->
      begin
	try 
	  Settings.do_set p v 
	with Not_found -> 
	  input_error  ("Bad setting " ^ p ^ "=" ^
                        (match v with S (s,_) -> s | I n -> string_of_int n)) ext
      end
  | FunDecl((s1,ext1),l,(sr,extr),f_options) ->
      let sr' = get_type (!env) sr extr in
      let l' = List.map (fun (s,ext) ->
	get_type (!env) s ext) l 
      in
      let opt = ref 0 in
      List.iter (fun (sopt, extopt) ->
	  if sopt = "decompos" || sopt = "projection" then 
	    begin
	      opt := (!opt) lor Settings.fopt_DECOMPOS;
	      if List.length l' != 1 then
		Parsing_helper.input_error "A [decompos] or [projection] function should be unary" extopt
	    end
	  else if sopt = "uniform" then
	    begin
	      opt := (!opt) lor Settings.fopt_UNIFORM;
	      if List.length l' != 1 then
		Parsing_helper.input_error "A uniform function should be unary" extopt;
	      if sr'.toptions land Settings.tyopt_CHOOSABLE == 0 then
		Parsing_helper.input_error "A uniform function should have a result that can be randomly chosen" extopt;
	      if (List.hd l').toptions land Settings.tyopt_CHOOSABLE == 0 then
		Parsing_helper.input_error "A uniform function should have an argument that can be randomly chosen" extopt
	    end
	  else if sopt = "compos" || sopt = "data" then 
	    opt := (!opt) lor Settings.fopt_COMPOS
	  else
	    Parsing_helper.input_error ("Unknown function option " ^ sopt) extopt
	      ) f_options;
      add_not_found s1 ext1 (EFunc{ f_name = s1;
				    f_type = l',sr';
				    f_cat = Std;
				    f_options = !opt;
				    f_statements = [];
				    f_collisions = [];
				    f_eq_theories = NoEq;
                                    f_impl = No_impl;
                                    f_impl_inv = None })
  | LetFun((s1,ext1), l, s2) ->
      let (bl, tl,env')=
        List.fold_right (fun ((s1, ext1), tyb) (bl,tl,env') ->
                           if (StringMap.mem s1 env') then
                             Parsing_helper.input_error ("The name "^s1^" already defined before cannot be used here") ext1
                           else
                             let (t,_) = get_ty env' tyb in
                             let (env'',b)=add_in_env_letfun env' s1 ext1 t in
                               (b::bl,t::tl,env'')) l ([],[],!env) in
      let t = check_term_letfun env' s2 in
        add_not_found s1 ext1 (EFunc{ f_name = s1;
                                      f_type = tl, t.t_type;
                                      f_cat  = LetFunTerm(bl,t);
				      f_options = 0;
				      f_statements = [];
				      f_collisions = [];
				      f_eq_theories = NoEq;
                                      f_impl = No_impl;
                                      f_impl_inv = None })
          
  | EventDecl((s1,ext1), l) ->
      let l' = List.map (fun (s,ext) ->
	get_type_or_param (!env) s ext) l 
      in
      add_not_found s1 ext1 (EEvent{ f_name = s1;
				     (* Add a bitstring argument to store the current indexes *)
				     f_type = (Settings.t_bitstring :: l'),Settings.t_bool;
				     f_cat = Event;
				     f_options = 0;
				     f_statements = [];
				     f_collisions = [];
				     f_eq_theories = NoEq;
                                     f_impl = No_impl;
                                     f_impl_inv = None })
  | Statement s ->
      check_statement (!env) s
  | BuiltinEquation(eq_categ, l_fun_symb) ->
      check_builtin_eq (!env) eq_categ l_fun_symb
  | EqStatement s ->
      current_location := InEquivalence;
      check_eqstatement s
  | Collision s ->
      check_collision (!env) s
  | Query (vars, l) ->
      (* The bound variables are defined globally for the group of queries [l].
	 Put them for each queries that uses bound variables, that is, [PQEventQ] queries *)
      queries_parse := (List.map (function
	  PQEventQ(vars', t1, t2, pub_vars) ->
	    assert(vars' == []);
	    PQEventQ(vars, t1, t2, pub_vars)
	| q -> q
	      ) l) @ (!queries_parse)
  | PDef((s1,ext1),vardecl,p) ->
      add_not_found s1 ext1 (EProcess (!env, vardecl, p))
  | Proofinfo(pr) ->
      if !proof != None then
	match pr with
	  ((_, ext)::_)::_ ->
	    input_error "Proof indications already given before" ext
	| _ -> internal_error "empty proof"
      else
	proof := Some pr
  | Implementation(impl) ->
      (* adding implementation informations *)
      List.iter 
        (function 
           | Type ((t,ext), tid, opts) ->
               let typ = get_type !env t ext in
	       if typ.timplname != None then
		 Parsing_helper.input_error ("Type " ^ t ^ " already has implementation informations") ext;
               begin
                 match tid with
                   TypeSize (size) -> 
                     begin
                       typ.timplsize <- Some(size);
		       if size = 1 then
			 begin
                           typ.tpredicate <- Some "always_true";
                           typ.timplname <- Some "bool";
                           (* writing default serializers *)
                           typ.tserial   <- Some ("bool_to","bool_from");
                           typ.trandom   <- Some ("rand_bool")
			 end
                       else if size mod 8 = 0 then 
			 begin
                           typ.tpredicate <- Some ("(sizep "^(string_of_int (size/8))^")");
 			   typ.timplname <- Some "string";
			     (* writing default serializers *)
			   typ.tserial <- Some ("id","(size_from "^(string_of_int (size/8))^")");
                           typ.trandom <- Some ("(rand_string "^(string_of_int (size/8))^")")
			 end
                       else 
			 Parsing_helper.input_error "Fixed-length types of size different from 1 and non-multiple of 8 not supported" ext
                     end
                 | TypeName (n,ext) ->
                     begin
		       if typ.toptions land Settings.tyopt_FIXED != 0 then
			 Parsing_helper.input_error "The implementation of fixed types should be given by specifying their size" ext;
                       typ.timplname <- Some(n);
                       typ.tpredicate <- Some ("always_true")
                     end
               end;
               (* Parse options *)
               write_type_options typ opts
           | Function((f,ext),(i,ext1),fopts) ->
               let fu=get_function !env f ext in
	       if fu.f_impl != No_impl then
		 Parsing_helper.input_error ("Function " ^ f ^ " already has implementation informations") ext;
                fu.f_impl <- Func i;
               write_fun_options fu fopts
           | Constant((f,ext),(i,ext')) ->
               let fu=get_function !env f ext in
 	       if fu.f_impl != No_impl then
		 Parsing_helper.input_error ("Function " ^ f ^ " already has implementation informations") ext;
               if (fst fu.f_type <> []) then
                 input_error (fu.f_name^" is not a function without arguments.") ext
               else
                 fu.f_impl <- Const i
           | ImplTable((tbl,ext),(file,ext')) ->
               let t=get_table !env tbl ext in
 	       if t.tblfile != None then
		 Parsing_helper.input_error ("Table " ^ tbl ^ " already has implementation informations") ext;
               t.tblfile <- Some file;
        ) impl;
      implementation := impl @ (!implementation)
  | Define _ ->
      internal_error "macros should have been expanded"
  | Expand((s,ext),_) ->
      input_error "macros should have been expanded, and the macro move_array_internal_macro should not contain expansions of other macros" ext
  | Expanded(argl, l) ->
      let env_before = !env in
      List.iter check_one l;
      let env_after = !env in
      (* After expanding a macro, we keep in the environment only the 
         identifiers passed as argument to the macro.
	 The identifiers internal to the macro are considered as not defined.
	 They are renamed to identifiers different from existing declarations
	 during macro expansion, but they could clash with identifiers
	 used without proper definition. They would then be erroneously
	 considered as defined. *)
      env := env_before;
      List.iter (fun (arg,_) ->
	if StringMap.mem arg env_before then
	  ()
	else
	  try
	    let argval = StringMap.find arg env_after in
	    env := StringMap.add arg argval (!env)
	  with Not_found -> ()
	      ) argl

let rec check_all (l,p) = 
  List.iter check_one l;
  current_location := InProcess;
  set_binder_env (check_process1 empty_binder_env [] p); (* Builds binder_env *)
  let result = check_process [] [] (!env) None p in
  check_process2 p; (* Checks oracles that finish roles contain only
                       one return *)
  warn_process_form p; (* Warns user if form of process is not optimal *)
  result

let new_bitstring_binder() = 
  let b = Terms.create_binder "!l" Settings.t_bitstring []
  in
  Terms.term_from_binder b

(* Check that when injective events occur several times, they
   occur in different branches of if/find. *)

let several_occ_events = ref []

let rec sym_diff l1 = function
    [] -> l1
  | (a::l) ->
      if List.memq a l1 then
	begin
	  several_occ_events := a :: (!several_occ_events);
          sym_diff (List.filter (fun x -> x != a) l1) l
	end
      else
	a::(sym_diff l1 l)

let rec count_occ_eventst t =
  match t.t_desc with
    Var(_,tl) | FunApp(_, tl) ->
      count_occ_eventstl tl
  | ReplIndex _ -> []
  | EventAbortE f -> [f]
  | ResE(_,p) -> count_occ_eventst p
  | TestE(t,p1,p2) ->
      sym_diff (count_occ_eventst t)
	(Terms.unionq (count_occ_eventst p1) (count_occ_eventst p2))
  | FindE(l0,p2,_) ->
      let l = ref (count_occ_eventst p2) in
      List.iter (fun (_,_,_,p1) ->
	(* There must be no events in conditions of find *)
	l := Terms.unionq (!l) (count_occ_eventst p1)) l0;
      (!l)
  | LetE(pat,t,p1,p2opt) ->
      sym_diff (count_occ_eventspat pat)
	(sym_diff (count_occ_eventst t) 
	   (let p1e = count_occ_eventst p1 in
	   match p2opt with
	     None -> p1e
	   | Some p2 -> Terms.unionq p1e (count_occ_eventst p2)))
  | GetE(_,patl,_,p1,p2) ->
      (* There must be no event in the condition of get *)
      sym_diff (count_occ_eventspatl patl)
	(Terms.unionq (count_occ_eventst p1) (count_occ_eventst p2))
  | InsertE(_,tl,p) ->
      sym_diff (count_occ_eventstl tl) (count_occ_eventst p)
  | EventE(t,p) -> 
      let l = count_occ_eventst p in
      match t.t_desc with
	FunApp(f,tl) ->
	  let l' =
	    if List.memq f l then
	      begin
		several_occ_events := f :: (!several_occ_events);
		l
	      end
	    else
	      f :: l
	  in
	  sym_diff (count_occ_eventstl tl) l'
      |	_ -> Parsing_helper.internal_error "Events must be function applications"

and count_occ_eventstl = function
    [] -> []
  | (a::l) ->
      sym_diff (count_occ_eventst a) (count_occ_eventstl l)

and count_occ_eventspat = function
    PatVar _ -> []
  | PatTuple (f,patl) ->
      count_occ_eventspatl patl
  | PatEqual t ->
      count_occ_eventst t

and count_occ_eventspatl = function
    [] -> []
  | (a::l) ->
      sym_diff (count_occ_eventspat a) (count_occ_eventspatl l)
    
let rec count_occ_events p = 
  match p.i_desc with
    Nil -> []
  | Par(p1,p2) -> sym_diff (count_occ_events p1) (count_occ_events p2)
  | Repl(_,p) -> count_occ_events p
  | Input(_,pat,p) ->
      (* There must be no events in channels *)
      sym_diff (count_occ_eventspat pat) (count_occ_eventso p)

and count_occ_eventso p = 
  match p.p_desc with
    Yield -> []
  | EventAbort f -> [f]
  | Restr(_,p) -> count_occ_eventso p
  | Test(t,p1,p2) ->
      sym_diff (count_occ_eventst t)
	(Terms.unionq (count_occ_eventso p1) (count_occ_eventso p2))
  | Find(l0,p2,_) ->
      let l = ref (count_occ_eventso p2) in
      List.iter (fun (_,_,_,p1) ->
	(* There must be no events in conditions of find *)
	l := Terms.unionq (!l) (count_occ_eventso p1)) l0;
      (!l)
  | Output(_,t,p) ->
      (* There must be no events in channels *)
      sym_diff (count_occ_eventst t) (count_occ_events p)
  | Let(pat,t,p1,p2) ->
      sym_diff (count_occ_eventspat pat)
	(sym_diff (count_occ_eventst t) 
	   (Terms.unionq (count_occ_eventso p1) (count_occ_eventso p2)))
  | Get(_,patl,_,p1,p2) ->
      (* There must be no event in the condition of get *)
      sym_diff (count_occ_eventspatl patl)
	(Terms.unionq (count_occ_eventso p1) (count_occ_eventso p2))
  | Insert(_,tl,p) ->
      sym_diff (count_occ_eventstl tl) (count_occ_eventso p)
  | EventP(t,p) -> 
      let l = count_occ_eventso p in
      match t.t_desc with
	FunApp(f,tl) ->
	  let l' =
	    if List.memq f l then
	      begin
		several_occ_events := f :: (!several_occ_events);
		l
	      end
	    else
	      f :: l
	  in
	  sym_diff (count_occ_eventstl tl) l'
      |	_ -> Parsing_helper.internal_error "Events must be function applications"

let diff_types f =
  try
    let t = List.assq f (!event_type_list) in
    not (List.for_all (fun (f',t') -> (f' != f) || (t == t')) (!event_type_list))
  with Not_found -> false

let rec check_term_query1 env = function
  | PQEvent(inj, (PFunApp((s,ext), tl), ext2)),ext3 ->
      let tl' = List.map (check_term_nobe env) tl in
      begin
      try 
	match StringMap.find s env with
	  EEvent(f) ->
	    if inj then
	      begin
		if List.memq f (!several_occ_events) then
		  input_error "Injective events should occur at most once in each branch of if/find/let" ext3;
		if diff_types f then
		  input_error "Injective events should be under replications of the same type" ext3
	      end;
	    check_type_list ext2 tl tl' (List.tl (fst f.f_type));
	    [inj, Terms.new_term (snd f.f_type) ext2 (FunApp(f, (new_bitstring_binder()) :: tl'))]
	| _ -> input_error (s ^ " should be an event") ext
      with Not_found ->
	input_error (s ^ " not defined") ext
      end
  | PQEvent _, ext ->
      input_error "Events should be function applications" ext
  | PAnd(t1,t2), ext ->
      (check_term_query1 env t1) @ (check_term_query1 env t2)
  | _,ext2 -> input_error "the left-hand side of a correspondence query should be an event or a conjunction of events" ext2

let rec check_term_query2 env = function
    (PIdent (s, ext), ext2) as x ->
      begin
      try 
	match StringMap.find s env with
	  EVar(b) -> 
	    let x' =
	      Terms.new_term b.btype ext2
		(Var(b,List.map Terms.term_from_repl_index b.args_at_creation))
	    in
	    check_type (snd x) x' Settings.t_bool;	    
	    QTerm x'
	| EFunc(f) ->
            begin
              match f.f_cat with
                  LetFunTerm _ -> input_error ("Letfun are not accepted here") ext
                | _ ->
	            if fst (f.f_type) = [] then
	              let x' = Terms.new_term (snd f.f_type) ext2 (FunApp(f, [])) in
	              check_type (snd x) x' Settings.t_bool;
	              QTerm x'
	            else
	              input_error (s ^ " has no arguments but expects some") ext
            end
	| _ -> input_error (s ^ " should be a variable or a function") ext
      with Not_found -> 
	input_error (s ^ " not defined") ext
      end
  | (PFunApp((s,ext), tl),ext2) as x ->
      let tl' = List.map (check_term_nobe env) tl in
      begin
      try 
	match StringMap.find s env with
	  EFunc(f) ->
            begin
              match f.f_cat with
                  LetFunTerm _ -> input_error ("Letfun are not accepted here") ext
                | _ ->
                    check_type_list ext2 tl tl' (fst f.f_type);
	            let x' = Terms.new_term (snd f.f_type) ext2 (FunApp(f, tl')) in
	            check_type (snd x) x' Settings.t_bool;
	            QTerm x'
            end
	| _ -> input_error (s ^ " should be a function") ext
      with Not_found ->
	input_error (s ^ " not defined") ext
      end
  | PQEvent(inj, (PFunApp((s,ext), tl), ext2)),ext3 ->
      let tl' = List.map (check_term_nobe env) tl in
      begin
      try 
	match StringMap.find s env with
	  EEvent(f) ->
	    if inj then
	      begin
		if List.memq f (!several_occ_events) then
		  input_error "Injective events should occur at most once in each branch of if/find/let" ext3;
		if diff_types f then
		  input_error "Injective events should be under replications of the same type" ext3
	      end;
	    check_type_list ext2 tl tl' (List.tl (fst f.f_type));
	    QEvent (inj, Terms.new_term (snd f.f_type) ext2 (FunApp(f, (new_bitstring_binder()) :: tl')))
	| _ -> input_error (s ^ " should be a an event") ext
      with Not_found ->
	input_error (s ^ " not defined") ext
      end
  | PQEvent _, ext ->
      input_error "Events should be function applications" ext
  | PAnd(t1,t2), ext ->
      QAnd(check_term_query2 env t1, check_term_query2 env t2)
  | POr(t1,t2), ext ->
      QOr(check_term_query2 env t1, check_term_query2 env t2)
  | x -> 
      let x' = check_term_nobe env x in
      check_type (snd x) x' Settings.t_bool;
      QTerm x'

let rec find_inj = function
    QAnd(t1,t2) | QOr(t1,t2) -> find_inj t1 || find_inj t2
  | QEvent(b,t) -> b
  | QTerm t -> false

let get_qpubvars l = List.map (get_global_binder "in public variables of a query") l

let rec check_binder_list_typaram env = function
    [] -> (env,[])
  | ((s1,ext1),ty)::l ->
      let t =
	match ty with
	  Tid (s2,ext2) -> get_type env s2 ext2 
	| TBound (s2,ext2) -> 
	    let p = get_param env s2 ext2 in
	    type_for_param p
      in
      let (env',b) = add_in_env_nobe env s1 ext1 t in
      let (env'',l') = check_binder_list_typaram env' l in
      (env'', b::l')

	
let check_query = function
    PQSecret (i, pub_vars, options) ->
      let onesession = ref false in
      List.iter (fun (s,ext) ->
	if s = "onesession" then
	  onesession := true
	else
	  input_error "The only allowed option for secret is onesession" ext) options;
      QSecret (get_global_binder "in a secrecy query" i,
	       get_qpubvars pub_vars, !onesession)
  | PQEventQ (vl,t1,t2, pub_vars) -> 
      let (env',l') = check_binder_list_typaram (!env) vl in
      let t1' = check_term_query1 env' t1 in
      let t2' = check_term_query2 env' t2 in
      let has_inj_before_impl = List.exists (fun (b,_) -> b) t1' in
      let has_inj_after_impl = find_inj t2' in
      if has_inj_before_impl && not has_inj_after_impl then
	input_error "In this query, inj: is present before ==> but not after ==>.\ninj: should be present either both before and after ==> or not at all." (snd t1);
      if (not has_inj_before_impl) && has_inj_after_impl then
	input_error "In this query, inj: is present after ==> but not before ==>.\ninj: should be present either both before and after ==> or not at all." (snd t2);
      QEventQ(t1',t2', get_qpubvars pub_vars)

let get_impl ()=
  StringMap.fold (fun s (p,opt) l -> (s,opt,p)::l) !impl_roles []

let declares = function
  | ParamDecl((s,ext), _)
  | ProbabilityDecl(s,ext)
  | TableDecl((s,ext),_)
  | TypeDecl((s,ext),_)
  | ConstDecl((s,ext),_)
  | ChannelDecl(s,ext)
  | FunDecl((s,ext),_,_,_)
  | LetFun((s,ext),_,_)
  | EventDecl((s,ext), _)
  | PDef((s,ext),_,_) ->
      Some (s,ext)
  | _ -> None
    
let rec record_ids l = 
  List.iter (fun decl ->
    match declares decl with
      Some (s,ext) -> Terms.record_id s ext
    | None -> ()
	  ) l

(* [add_already_def argl expanded_macro already_def] adds to [already_def]
   the identifiers defined in [expanded_macro] that also occur in [argl].
   [argl] is supposed to represent the arguments of the macro before expansion.
   The idenfifiers in [argl] defined by the macro can be used after the
   macro. This function is useful to compute the value of [already_def]
   after the macro. *)

let rec add_already_def argl expanded_macro already_def =
  match expanded_macro with
    [] -> already_def
  | a::l ->
      let already_def' = 
	match declares a with
	| Some (s,_) ->
	    if List.exists (fun (s',_) -> s' = s) argl then
	      s::already_def
	    else
	      already_def
	| None ->
	    already_def
      in
      add_already_def argl l already_def'

let rec check_no_dup = function
    [] -> ()
  | (arg,ext)::l ->
      List.iter (fun (arg',ext') ->
	if arg = arg' then
	  input_error ("Macro contains twice the argument " ^ arg ^
		       ". It already appears at " ^
		       (in_file_position ext' ext)) ext'
	    ) l;
      check_no_dup l
	
let rec expand_macros macro_table already_def = function
    [] -> []
  | a::l ->
      match a with
      | Expanded _ ->
	  Parsing_helper.internal_error "Expanded macros should not occur initially"
      | Define((s1,ext1),argl,def) ->
	  if StringMap.mem s1 macro_table then
	    input_error ("Macro " ^ s1 ^ " already defined.") ext1
          else
	    begin
	      check_no_dup argl;
	      let macro_table' = StringMap.add s1 (Macro(argl, def, already_def, macro_table)) macro_table in
	      (* Store the new macro table globally 
		 This is ok before macro definitions cannot be included inside macros, so macro_table' contains all macros defined so far. *)
	      macrotable := macro_table';
	      expand_macros macro_table' already_def l
	    end
      | Expand((s1,ext1),argl) ->
          begin
	    try 
	      let Macro(paraml, def, old_already_def, old_macro_table) = StringMap.find s1 macro_table in
	      if List.length argl != List.length paraml then
		input_error ("Macro " ^ s1 ^ " expects " ^ (string_of_int (List.length paraml)) ^
			     " arguments, but is here given " ^ (string_of_int (List.length argl)) ^ " arguments.") ext1;
	      let applied_macro = apply argl paraml old_already_def def in
	      record_ids applied_macro;
	      let expanded_macro = expand_macros old_macro_table old_already_def applied_macro in
	      let already_def_after_macro = add_already_def argl expanded_macro already_def in
	      Expanded(argl, expanded_macro)::(expand_macros macro_table already_def_after_macro l)
	    with Not_found ->
	      input_error ("Macro " ^ s1 ^ " not defined.") ext1
	  end
      | _ ->
	  let already_def' = 
	    match declares a with
	      Some(s,_) -> s::already_def
	    | None -> already_def
	  in
	  a::(expand_macros macro_table already_def' l)

let read_file f =
  try 
    let (l,p) = parse_with_lib f in
    env := init_env();
  (* Record top-level identifiers, to make sure that we will not need to 
     rename them. *)
    record_ids l;
    let already_def = ref [] in
    StringMap.iter (fun s _ -> already_def := s :: (!already_def)) (!env);
    let l' = expand_macros StringMap.empty (!already_def) l in
    let (p',_,_) = check_all (l',p) in
    let _ = count_occ_events p' in
    (!statements, !collisions, !equivalences, !move_new_eq,
     List.map check_query (!queries_parse), !proof, (get_impl ()), p')
  with Undefined(i,ext) ->
    input_error (i ^ " not defined") ext
