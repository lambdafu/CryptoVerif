open Ptree
open Types
open Stringmap
open Parsing_helper
open Lexing

let whole_game = ref Terms.empty_game
let new_queries = ref []
let has_unique_to_prove = ref false
    
(*
Get the environment computed in syntax.ml/osyntax.ml.
=> Stringmap.env
One pass on the initial game p, to build a hash table that
maps strings to binders or to "FindCond" for variables
defined in the condition of find (finds are forbidden on
such variables). 
=> hash_binders
Also indicate whether there is an array ref. on the other variables.
=> array_ref, array_ref_def
*)

type hash_elem =
  | FindCond (* Defined in a find condition *)
  | Std of binder
  | NoType
  | NoDef (* Occurs in a defined condition but is never defined; the defined condition will always be wrong *)

let hash_binders = Hashtbl.create 7

let add b =
  let s = Display.binder_to_string b in
  try 
    match Hashtbl.find hash_binders s with
      NoDef -> 
	Hashtbl.replace hash_binders s (Std b)
    | FindCond ->
	Parsing_helper.internal_error "Variable in find condition defined several times"
    | _ -> ()
  with Not_found -> 
    Hashtbl.add hash_binders s (Std b)

let add_find_cond b =
  let s = Display.binder_to_string b in
  try 
    match Hashtbl.find hash_binders s with
      NoDef -> 
	Hashtbl.replace hash_binders s FindCond
    | _ ->
	Parsing_helper.internal_error "Variable in find condition defined several times"
  with Not_found -> 
    Hashtbl.add hash_binders s FindCond

let add_nodef b =
  let s = Display.binder_to_string b in
  if not (Hashtbl.mem hash_binders s) then
    Hashtbl.add hash_binders s NoDef

let rec find_binders_br (b,l) =
  List.iter find_binders_term_def_list l;
  add_nodef b

and find_binders_term_def_list t =
  match t.t_desc with
    Var(b,l) -> 
      List.iter find_binders_term_def_list l;
      add_nodef b
  | FunApp(_,l) ->
      List.iter find_binders_term_def_list l
  | ReplIndex _ -> ()
  | _ -> 
      Parsing_helper.internal_error "if/let/find/new/insert/get forbidden in def_list"

let rec find_binders_find_cond t =
  match t.t_desc with
    Var _ | FunApp _ | ReplIndex _ | EventAbortE _ -> ()
  | TestE(t1,t2,t3) ->
      find_binders_find_cond t2;
      find_binders_find_cond t3
  | FindE(l0,t3,_) ->
      List.iter (fun (bl,def_list,t1,t2) ->
	List.iter (fun (b,_) -> add_find_cond b) bl;
        List.iter find_binders_br def_list;
	find_binders_find_cond t1;
	find_binders_find_cond t2) l0;
      find_binders_find_cond t3
  | ResE(b,t) ->
      add_find_cond b;
      find_binders_find_cond t
  | InsertE _ | GetE _ | EventE _ ->
      Parsing_helper.internal_error "insert/get/event/event_abort should not occur as term"
  | LetE(pat, t1, t2, topt) ->
      let pat_vars = Terms.vars_from_pat [] pat in
      List.iter add_find_cond pat_vars;
      find_binders_find_cond t2;
      match topt with
	None -> ()
      |	Some t3 -> find_binders_find_cond t3
            

let rec find_binders_rec p =
  match p.i_desc with
    Nil -> ()
  | Par(p1,p2) -> 
      find_binders_rec p1;
      find_binders_rec p2
  | Repl(b,p) -> 
      find_binders_rec p
  | Input((c, tl),pat,p) ->
      let pat_vars = Terms.vars_from_pat [] pat in
      List.iter add pat_vars;
      find_binders_reco p

and find_binders_reco p =
  match p.p_desc with
    Yield | EventAbort _ -> ()
  | Restr(b,p) -> 
      add b;
      find_binders_reco p
  | Test(t,p1,p2) ->
      find_binders_reco p1;
      find_binders_reco p2
  | Find(l0,p2,_) ->
      List.iter (fun (bl,def_list,t,p1) ->
	List.iter (fun (b,_) -> add b) bl;
        List.iter find_binders_br def_list;
	find_binders_find_cond t;
	find_binders_reco p1) l0;
      find_binders_reco p2
  | Output((c, tl),t2,p) ->
      find_binders_rec p
  | Let(pat, t, p1, p2) ->
      let pat_vars = Terms.vars_from_pat [] pat in
      List.iter add pat_vars;
      find_binders_reco p1;
      find_binders_reco p2
  | EventP(t,p) ->
      find_binders_reco p
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

(* Add variables defined in the inserted code to [hash_binders] *)

let add_var find_cond (s_b, ext_b) ty_opt cur_array =
  if find_cond then
    begin
      if Hashtbl.mem hash_binders s_b then
	raise (Error(s_b ^ " already defined, so cannot be redefined in a find condition", ext_b));
      (* Variable not already defined *)
      match ty_opt with
      | None -> raise (Error("type needed for the declaration of " ^ s_b, ext_b));
      | Some ty ->
	  Hashtbl.add hash_binders s_b FindCond
    end
  else
    begin
      try
	match Hashtbl.find hash_binders s_b with
	| FindCond -> raise (Error(s_b ^ " already defined in a find condition, so cannot have several definitions", ext_b))
	| NoDef -> raise (Error(s_b ^ " already exists and the fact that it is defined is tested", ext_b))
	| NoType ->
	    (* Variable defined in the inserted code, without a type.
	       Array accesses with be forbidden *)
	    ()
	| Std b ->
	    if Array_ref.has_array_ref_q b (!whole_game).current_queries then
	      raise (Error(s_b ^ " already defined and has array references or is used in queries", ext_b));
	    begin
	      match ty_opt with
		None -> ()
	      | Some ty ->
		  if ty != b.btype then
		    raise (Error(s_b ^ " already defined with type " ^ b.btype.tname ^ ", so cannot be redefined with type " ^ ty.tname, ext_b))
	    end;
	    if not (Terms.equal_lists (==) b.args_at_creation cur_array) then
	      raise (Error(s_b ^ " already defined, but under different replications", ext_b))
      with Not_found ->
        (* Variable not already defined *)
	match ty_opt with
	| None ->
	    Hashtbl.add hash_binders s_b NoType
	| Some ty ->
	    let b = Terms.create_binder s_b ty cur_array in
	    Hashtbl.add hash_binders s_b (Std b)
    end
	
let rec check_pattern1 find_cond cur_array env tyoptres = function
    PPatVar (id_und, tyopt), _ ->
      begin
	let tyopt =
	  match tyopt, tyoptres with
	    None, None -> None
	  | None, Some ty -> Some ty
	  | Some tyb, None -> 
	      let (ty',ext2) = get_ty env tyb in
	      begin
		match ty'.tcat with
		  Interv _ -> raise (Error("Cannot input a term of interval type or extract one from a tuple", ext2))
	        (* This condition simplifies greatly the theory:
	           otherwise, one needs to compute which channels the adversary
	           knows...
		   8/12/2017: I no longer understand this comment, and I am
		   wondering if I could relax this condition. *)
		|	_ -> ()
	      end;
	      Some ty'
	  | Some tyb, Some ty ->
	      let (ty',ext2) = get_ty env tyb in
	      if ty != ty' then
		raise (Error("Pattern is declared of type " ^ ty'.tname ^ " and should be of type " ^ ty.tname, ext2));
	      Some ty
	in
	match id_und with
	| Underscore _ -> ()
	| Ident id ->
	    add_var find_cond id tyopt cur_array 
      end
  | PPatTuple l, ext ->
      begin
	match tyoptres with
	  None -> ()
	| Some ty ->
	    if ty != Settings.t_bitstring then
	      raise (Error("A tuple pattern has type bitstring but is here used with type " ^ ty.tname, ext))
      end;
      let tl = List.map (fun _ -> None) l in
      List.iter2 (check_pattern1 find_cond cur_array env) tl l
  | PPatFunApp((s,ext),l), ext2 ->
      let f = get_function_no_letfun env s ext in
      if (f.f_options land Settings.fopt_COMPOS) == 0 then
	raise (Error("Only [data] functions are allowed in patterns", ext));
      begin
	match tyoptres with
	  None -> ()
	| Some ty ->
	    if ty != snd f.f_type then
	      raise (Error("Pattern returns type " ^ (snd f.f_type).tname ^ " and should be of type " ^ ty.tname, ext2))
      end;
      if List.length (fst f.f_type) != List.length l then
	raise (Error("Function " ^ f.f_name ^ " expects " ^ 
		     (string_of_int (List.length (fst f.f_type))) ^ 
		     " arguments but is here applied to " ^  
		     (string_of_int (List.length l)) ^ "arguments", ext));
      List.iter2 (check_pattern1 find_cond cur_array env) (List.map (fun t -> Some t) (fst f.f_type)) l
  | PPatEqual t, ext ->
      ()


	
let rec check_find_cond1 cur_array env = function
    PTestE(t1, t2, t3), ext ->
      check_find_cond1 cur_array env t2;
      check_find_cond1 cur_array env t3
  | PLetE(pat, t1, t2, topt), ext ->
      check_pattern1 true cur_array env None pat;
      check_find_cond1 cur_array env t2;
      begin
	match topt, pat with
	  Some t3, _ -> check_find_cond1 cur_array env t3
	| None, (PPatVar _, _) -> ()
	| None, _ -> raise (Error("When a let in an expression has no else part, it must be of the form let x = M in M'", ext))
      end
  | PResE((s_b,ext_b),(s_ty,ext_ty),t), ext ->
      check_find_cond1 cur_array env t;
      let ty = get_type env s_ty ext_ty in
      if ty.toptions land Settings.tyopt_CHOOSABLE == 0 then
	raise (Error("Cannot choose randomly a bitstring from " ^ ty.tname ^ " with uniform distribution", ext_ty));
      add_var true (s_b, ext_b) (Some ty) cur_array 
  | PEventAbortE _, ext ->
      ()
  | PEventE _, ext ->
      raise (Error("event should not appear as term", ext))
  | PInsertE _, ext ->
      raise (Error("insert should not appear as term", ext))
  | PGetE _, ext ->
      raise (Error("get should not appear as term", ext))
  | PFindE(l0,t3,opt), ext ->
      check_find_cond1 cur_array env t3;
      let add env l =
	List.map (fun ((s0,ext0),(s1,ext1),(s2,ext2)) ->
	  let p = get_param env s2 ext2 in
	  let t = Terms.type_for_param p in
	  add_var true (s0,ext0) (Some t) cur_array;
	  (* Create a replication index *)
	  Terms.create_repl_index s1 t
	    ) l
      in
      List.iter (fun (bl_ref,bl,def_list,t1,t2) ->
	let bl'' = add env bl in
	bl_ref := bl'';
	check_find_cond1 (bl'' @ cur_array) env t1;
	check_find_cond1 cur_array env t2 
	  ) l0 
  | x -> ()


let rec check_ins1 cur_array env (ins, ext) =
  match ins with
  | PYield ->
      ()
  | PRestr((s_b, ext_b), (s_ty, ext_ty), rest) ->
      check_ins1 cur_array env rest;
      let ty = get_type env s_ty ext_ty in
      if ty.toptions land Settings.tyopt_CHOOSABLE == 0 then
	raise (Error("Cannot choose randomly a bitstring from " ^ ty.tname ^ " with uniform distribution", ext_ty));
      add_var false (s_b, ext_b) (Some ty) cur_array 
  | PEventAbort _ -> ()
  | PTest(t, rest1, rest2) ->
      check_ins1 cur_array env rest1;
      check_ins1 cur_array env rest2
  | PLet(pat, t, rest1, rest2) ->
      check_ins1 cur_array env rest1;
      check_ins1 cur_array env rest2;
      check_pattern1 false cur_array env None pat
  | PFind(l0, rest, opt) ->
      check_ins1 cur_array env rest;
      let add env l =
	List.map (fun ((s0,ext0),(s1,ext1),(s2,ext2)) ->
	  let p = get_param env s2 ext2 in
	  let t = Terms.type_for_param p in
	  add_var false (s0,ext0) (Some t) cur_array;
	  (* Create a replication index *)
	  Terms.create_repl_index s1 t
	    ) l
      in
      List.iter (fun (bl_ref,bl,def_list,t1,rest) ->
	let bl'' = add env bl in
	bl_ref := bl'';
	check_find_cond1 (bl'' @ cur_array) env t1;
	check_ins1 cur_array env rest
	  ) l0 
  | _ ->
      Parsing_helper.internal_error "Unexpected inserted instruction"

(*
One pass on the initial game up to the program point occ to
- compute cur_array (current replication indices)
- compute the list defined_refs of allowed variable references
- update the environment env with variables bound above occ.
When reaching occ, add the instruction defined by the string s.
In contrast to the initial game, only code that satisfies the
invariants is accepted:
- variables defined at several places are not renamed
- terms if/let/find/new are not expanded, so they are allowed only in
conditions of find

A new definition for an existing variable can be added only when there
is no array ref. on this variable. We have to check that the new definition
is in a different branch of if/let/find, under the same replications,
and of the same type. To check that, return at the point the set of defined
variables.
*)

let check_noninter d1 d2 =
  List.iter (fun b1 ->
    if List.memq b1 d2 then
      raise (Error("Same variable " ^ (Display.binder_to_string b1) ^ " defined twice", Parsing_helper.dummy_ext))
	) d1

let rec check_single_var l ext = 
  match l with
    [] -> ()
  | (a::r) -> 
      if List.memq a r then
	raise (Error("Variable " ^ (Display.binder_to_string a) ^ " defined several times in this pattern", ext));
      check_single_var r ext

let is_yield (p,_) =
  if p != PYield then 
    Parsing_helper.internal_error "Yield process expected"

let get_var find_cond env (s_b, ext_b) ty_opt cur_array =
  if find_cond then

  try 
    match StringMap.find s_b env with
      _ -> 
	raise (Error(s_b ^ " already defined, so cannot be redefined in a find condition", ext_b))
  with Not_found ->
    try
      (* The variable is inserted in hash_binders in the first pass *)
      assert (Hashtbl.find hash_binders s_b = FindCond);
      match ty_opt with
	None -> raise (Error("type needed for the declaration of " ^ s_b, ext_b));
      | Some ty ->
	  Terms.create_binder s_b ty cur_array
    with Not_found ->
      assert false

  else

  try 
    match StringMap.find s_b env with
      EVar b -> 
	if Array_ref.has_array_ref_q b (!whole_game).current_queries then
	  raise (Error(s_b ^ " already defined and has array references or is used in queries", ext_b));
	begin
	  match ty_opt with
	    None -> ()
	  | Some ty ->
	      if ty != b.btype then
		raise (Error(s_b ^ " already defined with type " ^ b.btype.tname ^ ", so cannot be redefined with type " ^ ty.tname, ext_b))
	end;
	if not (Terms.equal_lists (==) b.args_at_creation cur_array) then
	  raise (Error(s_b ^ " already defined, but under different replications", ext_b));
	b
    | _ -> raise (Error(s_b ^ " already defined and not a variable", ext_b))
  with Not_found ->
    try
      match Hashtbl.find hash_binders s_b with
	FindCond -> raise (Error(s_b ^ " already defined in a find condition, so cannot have several definitions", ext_b))
      | NoDef -> raise (Error(s_b ^ " already exists and the fact that it is defined is tested", ext_b))
      | NoType ->
	  begin
            (* Variable defined without type *)
	    match ty_opt with
	      None -> raise (Error("type needed for the declaration of " ^ s_b, ext_b));
	    |	Some ty ->
		let b = Terms.create_binder s_b ty cur_array in
		Hashtbl.add hash_binders s_b (Std b);
		b
	  end
      | Std b ->
	  if Array_ref.has_array_ref_q b (!whole_game).current_queries then
	    raise (Error(s_b ^ " already defined and has array references or is used in queries", ext_b));
	  begin
	    match ty_opt with
	      None -> ()
	    | Some ty ->
		if ty != b.btype then
		  raise (Error(s_b ^ " already defined with type " ^ b.btype.tname ^ ", so cannot be redefined with type " ^ ty.tname, ext_b))
	  end;
	  if not (Terms.equal_lists (==) b.args_at_creation cur_array) then
	    raise (Error(s_b ^ " already defined, but under different replications", ext_b));
	  b
    with Not_found ->
      (* Should have been added to hash_binders in the first pass *)
      assert false

let get_event ev_id =
  let (f, add_query) =
    Transf_insert_event.get_event (!whole_game).current_queries ev_id
  in
  if add_query then
    new_queries := f :: (!new_queries);
  f
	
let check_type ext e t =
  if e.t_type != t then
    raise (Error("This expression has type " ^ e.t_type.tname ^ " but expects type " ^ t.tname, ext))

let check_bit_string_type ext t =
  match t.tcat with
    BitString -> ()
  | _ -> raise (Error("Some bitstring type expected", ext))

let rec check_type_list ext pel el tl =
  match (pel, el, tl) with
    [],[],[] -> ()
  | (pe::pel, e::el, t::tl) ->
      check_type (snd pe) e t;
      check_type_list ext pel el tl
  | _ ->
      raise (Error("Unexpected number of arguments", ext))

let rec check_array_type_list ext pel el cur_array creation_array =
  match (pel, el, creation_array) with
    [],[],[] -> []
  | [],[],_ -> 
      (* Allow incomplete array arguments. They are automatically
         completed with cur_array *)
      let n = (List.length cur_array) - (List.length creation_array) in
      if n < 0 then 
	raise (Error("Unexpected number of array specifiers", ext));
      let cur_array_rest = Terms.skip n cur_array in
      if List.for_all2 (==) cur_array_rest creation_array then
	List.map Terms.term_from_repl_index creation_array
      else
	raise (Error("Unexpected number of array specifiers", ext))
  | (pe::pel, e::el, t::tl) ->
      check_type (snd pe) e t.ri_type;
      e::(check_array_type_list ext pel el cur_array tl)
  | _ ->
      raise (Error("Unexpected number of array specifiers", ext))


let rec check_term defined_refs cur_array env = function
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
	      Terms.new_term (snd f.f_type) ext2 (FunApp(f, []))
	    else
	      raise (Error(s ^ " has no arguments but expects some", ext))
	| d -> raise (Error(s ^ " was previously declared as a " ^ (decl_name d) ^". Expected a variable, a replication index, or a function", ext))
      with Not_found -> try
	match Hashtbl.find hash_binders s with
	  Std b -> 
	    let tl'' = check_array_type_list ext2 [] [] cur_array b.args_at_creation in 
	    begin
	      match defined_refs with
		None -> () (* Do not check whether the reference is defined;
			      useful when parsing def_list *)
	      |	Some defined_refs' ->
		  if not (Terms.mem_binderref (b,tl'') defined_refs') then
		    raise (Error("The definition of an out of scope reference should be guaranteed by a defined condition", ext));
	    end;
	    Terms.new_term b.btype ext2 (Var(b,tl''))
	| NoType | NoDef | FindCond ->
	    raise (Error(s ^ " is referenced outside its scope and is either\ndefined in a condition of find, without type, or never defined", ext))
      with Not_found ->
	raise (Error(s ^ " not defined", ext))
      end
  | PArray((s, ext), tl), ext2 ->
      let (b, tl'') = check_br defined_refs cur_array env ((s,ext),tl) in
      Terms.new_term b.btype ext2 (Var(b,tl''))
  | PFunApp((s,ext), tl),ext2 ->
      let tl' = List.map (check_term defined_refs cur_array env) tl in
      let f = get_function_no_letfun env s ext in
      check_type_list ext2 tl tl' (fst f.f_type);
      Terms.new_term (snd f.f_type) ext2 (FunApp(f, tl'))
  | PTuple(tl), ext2 ->
      let tl' = List.map (check_term defined_refs cur_array env) tl in
      let f = Settings.get_tuple_fun (List.map (fun t -> t.t_type) tl') in
      check_type_list ext2 tl tl' (fst f.f_type);
      Terms.new_term (snd f.f_type) ext2 (FunApp(f, tl'))
  | (PTestE _ | PLetE _ | PFindE _ | PResE _ | PEventAbortE _), ext ->
      raise (Error("if/let/find/new/event_abort should appear as terms only in conditions of find", ext))
  | PInsertE _, ext ->
      raise (Error("insert should not appear as term", ext))
  | PGetE _, ext ->
      raise (Error("get should not appear as term", ext))
  | PEventE _, ext ->
      raise (Error("event should not appear as term", ext))
  | PEqual(t1,t2), ext ->
      let t1' = check_term defined_refs cur_array env t1 in
      let t2' = check_term defined_refs cur_array env t2 in
      if t1'.t_type != t2'.t_type then
	raise (Error("= expects expressions of the same type", ext));
      Terms.make_equal_ext ext t1' t2'
  | PDiff(t1,t2), ext ->
      let t1' = check_term defined_refs cur_array env t1 in
      let t2' = check_term defined_refs cur_array env t2 in
      if t1'.t_type != t2'.t_type then
	raise (Error("<> expects expressions of the same type", ext));
      Terms.make_diff_ext ext t1' t2'
  | PAnd(t1,t2), ext ->
      let t1' = check_term defined_refs cur_array env t1 in
      let t2' = check_term defined_refs cur_array env t2 in
      check_type (snd t1) t1' Settings.t_bool;
      check_type (snd t2) t2' Settings.t_bool;
      Terms.make_and_ext ext t1' t2'
  | POr(t1,t2), ext ->
      let t1' = check_term defined_refs cur_array env t1 in
      let t2' = check_term defined_refs cur_array env t2 in
      check_type (snd t1) t1' Settings.t_bool;
      check_type (snd t2) t2' Settings.t_bool;
      Terms.make_or_ext ext t1' t2'
  | PQEvent _,ext -> 
      raise (Error("event(...) and inj-event(...) allowed only in queries", ext))
  | PBefore _,ext ->
      raise_error "==> allowed only in queries" ext
  | PExists _, ext ->
      raise_error "exists allowed only in queries" ext
  | PIndepOf _, ext ->
      raise (Error("independent-of allowed only in side-conditions of collisions", ext))

and check_br defined_refs cur_array env ((s,ext), tl) =
  let tl' = List.map (check_term defined_refs cur_array env) tl in
  try
    match Hashtbl.find hash_binders s with
      Std b -> 
	let tl'' = check_array_type_list ext tl tl' cur_array b.args_at_creation in
	begin
	  match defined_refs with
	    None -> () (* Do not check whether the reference is defined;
			  useful when parsing def_list *)
	  | Some defined_refs' ->
	      if not (Terms.mem_binderref (b,tl'') defined_refs') then
		raise (Error("The definition of an array reference should be guaranteed by a defined condition", ext));
	end;
	(b,tl'')
    | NoType | NoDef | FindCond ->
	raise (Error(s ^ " is referenced in an array reference and is either\ndefined in a condition of find, or defined without type, or never defined", ext))
  with Not_found ->
    raise (Error(s ^ " not defined", ext))

let rec check_pattern find_cond defined_refs cur_array env tyoptres = function
    PPatVar (id_und, tyopt), _ ->
      begin
	let tyopt =
	  match tyopt, tyoptres with
	    None, None -> None
	  | None, Some ty -> Some ty
	  | Some tyb, None -> 
	      let (ty',ext2) = get_ty env tyb in
	      begin
		match ty'.tcat with
		  Interv _ -> raise (Error("Cannot input a term of interval type or extract one from a tuple", ext2))
	        (* This condition simplifies greatly the theory:
	           otherwise, one needs to compute which channels the adversary
	           knows...
		   8/12/2017: I no longer understand this comment, and I am
		   wondering if I could relax this condition. *)
		|	_ -> ()
	      end;
	      Some ty'
	  | Some tyb, Some ty ->
	      let (ty',ext2) = get_ty env tyb in
	      if ty != ty' then
		raise (Error("Pattern is declared of type " ^ ty'.tname ^ " and should be of type " ^ ty.tname, ext2));
	      Some ty
	in
	let (s1,b) =
	  match id_und with
	  | Ident ((s1,_) as id) ->
	      let b = get_var find_cond env id tyopt cur_array in
	      (s1,b)
	  | Underscore ext1 ->
	      match tyopt with
	      | None -> raise (Error("type needed for _", ext1))
	      | Some ty ->
		  let s1 = Settings.underscore_var_name in
		  let b = Terms.create_binder s1 ty cur_array in
		  (s1, b)
	in
	let env' = StringMap.add s1 (EVar b) env in
	(env', PatVar b)
      end
  | PPatTuple l, ext ->
      begin
	match tyoptres with
	  None -> ()
	| Some ty ->
	    if ty != Settings.t_bitstring then
	      raise (Error("A tuple pattern has type bitstring but is here used with type " ^ ty.tname, ext))
      end;
      let tl = List.map (fun _ -> None) l in
      let (env', l') = check_pattern_list find_cond defined_refs cur_array env tl l in
      let tl' = List.map Terms.get_type_for_pattern l' in
      (env', PatTuple(Settings.get_tuple_fun tl', l'))
  | PPatFunApp((s,ext),l), ext2 ->
      let f = get_function_no_letfun env s ext in
      if (f.f_options land Settings.fopt_COMPOS) == 0 then
	raise (Error("Only [data] functions are allowed in patterns", ext));
      begin
	match tyoptres with
	  None -> ()
	| Some ty ->
	    if ty != snd f.f_type then
	      raise (Error("Pattern returns type " ^ (snd f.f_type).tname ^ " and should be of type " ^ ty.tname, ext2))
      end;
      if List.length (fst f.f_type) != List.length l then
	raise (Error("Function " ^ f.f_name ^ " expects " ^ 
		     (string_of_int (List.length (fst f.f_type))) ^ 
		     " arguments but is here applied to " ^  
		     (string_of_int (List.length l)) ^ "arguments", ext));
      let (env', l') = check_pattern_list find_cond defined_refs cur_array env (List.map (fun t -> Some t) (fst f.f_type)) l in
      (env', PatTuple(f, l'))
  | PPatEqual t, ext ->
      let t' = check_term (Some defined_refs) cur_array env t in
      begin
	match tyoptres with
	  None -> ()
	| Some ty ->
	    if t'.t_type != ty then
	      raise (Error("Pattern has type " ^ (t'.t_type).tname ^ " and should be of type " ^ ty.tname, ext))
      end;
      (env, PatEqual t')

and check_pattern_list find_cond defined_refs cur_array env lty l = 
  match lty, l with
    [], [] -> (env,[])
  | (ty::lty),(a::l) ->
      let env', l' = check_pattern_list find_cond defined_refs cur_array env lty l in
      let env'', a' = check_pattern find_cond defined_refs cur_array env' ty a in
      (env'', a'::l')
  | _ -> Parsing_helper.internal_error "Lists have different length in check_pattern_list"


let rec check_find_cond defined_refs cur_array env = function
    PTestE(t1, t2, t3), ext ->
      let t1' = check_term (Some defined_refs) cur_array env t1 in
      let t2' = check_find_cond defined_refs cur_array env t2 in
      let t3' = check_find_cond defined_refs cur_array env t3 in
      check_type (snd t1) t1' Settings.t_bool;
      if t2'.t_type != t3'.t_type then
	raise (Error("Both branches of a test should yield the same type", ext));
      Terms.new_term t2'.t_type ext (TestE(t1', t2', t3'))
  | PLetE(pat, t1, t2, topt), ext ->
      let t1' = check_term (Some defined_refs) cur_array env t1 in
      let (env', pat') = check_pattern true defined_refs cur_array env (Some t1'.t_type) pat in
      let def2 = Terms.vars_from_pat [] pat' in
      let defined_refs' = (List.map Terms.binderref_from_binder def2) @ defined_refs in
      let t2' = check_find_cond defined_refs' cur_array env' t2 in
      let topt' = 
	match topt, pat with
	  Some t3, _ -> Some (check_find_cond defined_refs cur_array env t3)
	| None, (PPatVar _, _) -> None
	| None, _ -> raise (Error("When a let in an expression has no else part, it must be of the form let x = M in M'", ext))
      in
      begin
	match topt' with
	  None -> ()
	| Some t3' -> if t2'.t_type != t3'.t_type then
	    raise (Error("Both branches of a let should return the same type", ext))
      end;
      Terms.new_term t2'.t_type ext (LetE(pat', t1', t2', topt'))
  | PResE((s1,ext1),(s2,ext2),t), ext ->
      let ty = get_type env s2 ext2 in
      if ty.toptions land Settings.tyopt_CHOOSABLE == 0 then
	raise (Error("Cannot choose randomly a bitstring from " ^ ty.tname ^ " with uniform distribution", ext2));
      let b = get_var true env (s1, ext1) (Some ty) cur_array in
      let env' = StringMap.add s1 (EVar b) env in
      let t' = check_find_cond defined_refs cur_array env' t in
      Terms.new_term t'.t_type ext (ResE(b, t'))
  | PEventAbortE id, ext ->
      let f = get_event id in
      Terms.new_term Settings.t_any ext (EventAbortE f)
  | PFindE(l0,t3,opt), ext ->
      let find_info =
	match opt with
	  ["unique",_] ->
	    let e = Terms.create_nonunique_event () in
	    has_unique_to_prove := true;
	    new_queries := e ::(!new_queries);
	    UniqueToProve e
	| [] -> Nothing
	| _ ->
	    raise (Error("The only option allowed for find is unique", ext))
      in
      let rec add env = function
	  [] -> (env,[])
	| ((s0,ext0),(s1,ext1),(s2,ext2))::bl ->
	    let p = get_param env s2 ext2 in
	    let b = get_var true env (s0,ext1) (Some (Terms.type_for_param p)) cur_array in
	    let env' = StringMap.add s0 (EVar b) env in
	    let (env'',bl') = add env' bl in
	    if List.memq b bl' then
	      raise (Error("Variable " ^ (Display.binder_to_string b) ^ " defined several times in the same find", ext1));
	    (env'',b::bl')
      in
      let rec add_ri env bl ril =
	match bl, ril with
	  [],[] -> env
	| ((s0,ext0),(s1,ext1),(s2,ext2))::bl, ri::ril ->
	    let env' = StringMap.add s1 (EReplIndex ri) env in
	    add_ri env' bl ril
	| _ -> assert false
      in
      let t3' = check_find_cond defined_refs cur_array env t3 in
      let l0' = List.map (fun (bl_ref,bl,def_list,t1,t2) ->
	let (env', bl') = add env bl in
	let bl'' = !bl_ref in
	let env'' = add_ri env bl bl'' in
	let def_list' = List.map (check_br None (bl'' @ cur_array) env'') def_list in
	let bl_comb = List.combine bl' bl'' in
	let (defined_refs_t1, defined_refs_t2) = Terms.defined_refs_find bl_comb def_list' defined_refs in
	let t1' = check_find_cond defined_refs_t1 (bl'' @ cur_array) env'' t1 in
	let t2' = check_find_cond defined_refs_t2 cur_array env' t2 in
	check_type (snd t1) t1' Settings.t_bool;
	if t2'.t_type != t3'.t_type then
	  raise (Error("All branches of a if or find should return the same type", ext));
	(bl_comb, def_list', t1', t2')) l0 
      in
      Terms.new_term t3'.t_type ext (FindE(l0', t3', find_info))
  | x -> check_term (Some defined_refs) cur_array env x


let rec insert_rec ((p', def) as r) (ins, ext) env defined_refs cur_array =
  match ins with
  | PYield ->
      r
  | PRestr((s_b, ext_b), (s_ty, ext_ty), rest) ->
      let ty = get_type env s_ty ext_ty in
      if ty.toptions land Settings.tyopt_CHOOSABLE == 0 then
	raise (Error("Cannot choose randomly a bitstring from " ^ ty.tname ^ " with uniform distribution", ext_ty));
      let b = get_var false env (s_b, ext_b) (Some ty) cur_array in
      let env' = StringMap.add s_b (EVar b) env in
      let (rest', def') = insert_rec (p', def) rest env' ((Terms.binderref_from_binder b)::defined_refs) cur_array in
      check_noninter def' [b];
      (Terms.new_oproc (Restr(b, rest')) ext, b::def')
  | PEventAbort id ->
      let f = get_event id in
      (Terms.new_oproc (EventAbort(f)) ext, [])
  | PTest(t, rest1, rest2) ->
      let (rest1', def1') = insert_rec (p', def) rest1 env defined_refs cur_array in
      let (rest2', def2') = insert_rec (p', def) rest2 env defined_refs cur_array in
      let t' = check_term (Some defined_refs) cur_array env t in
      (Terms.new_oproc (Test(t', rest1', rest2')) ext, Terms.unionq def1' def2')
  | PLet(pat, t, rest1, rest2) ->
      let t' = check_term (Some defined_refs) cur_array env t in
      let (env', pat') = check_pattern false defined_refs cur_array env (Some t'.t_type) pat in
      let def_pat = Terms.vars_from_pat [] pat' in
      check_single_var def_pat (snd pat);
      let defined_refs' = (List.map Terms.binderref_from_binder def_pat) @ defined_refs in
      let (rest1', def1') = insert_rec (p', def) rest1 env' defined_refs' cur_array in
      let (rest2', def2') = insert_rec (p', def) rest2 env defined_refs cur_array in
      check_noninter def1' def_pat;
      let def' = def_pat @ def1' in
      begin
      match pat' with
	PatVar b ->
	  (Terms.new_oproc (Let(pat', t', rest1', Terms.oproc_from_desc Yield)) ext, def')
      |	_ ->
	  (Terms.new_oproc (Let(pat', t', rest1', rest2')) ext, Terms.unionq def' def2')
      end
  | PFind(l0, rest, opt) ->
      let find_info =
	match opt with
	  ["unique",_] ->
	    let e = Terms.create_nonunique_event () in
	    has_unique_to_prove := true;
	    new_queries := e ::(!new_queries);
	    UniqueToProve e
	| [] -> Nothing
	| _ ->
	    raise (Error("The only option allowed for find is unique", ext))
      in
      let (rest', def') = insert_rec (p', def) rest env defined_refs cur_array in
      let def_accu = ref def' in
      let rec add env = function
	  [] -> (env,[])
	| ((s0,ext0),(s1,ext1),(s2,ext2))::bl ->
	    let p = get_param env s2 ext2 in
	    let b = get_var false env (s0,ext0) (Some (Terms.type_for_param p)) cur_array in
	    let env' = StringMap.add s0 (EVar b) env in
	    let (env'',bl') = add env' bl in
	    if List.memq b bl' then
	      raise (Error("Variable " ^ (Display.binder_to_string b) ^ " defined several times in the same find", ext1));
	    (env'',b::bl')
      in
      let rec add_ri env bl ril =
	match bl, ril with
	  [],[] -> env
	| ((s0,ext0),(s1,ext1),(s2,ext2))::bl, ri::ril ->
	    let env' = StringMap.add s1 (EReplIndex ri) env in
	    add_ri env' bl ril
	| _ -> assert false
      in
      let l0' = List.map (fun (bl_ref,bl,def_list,t1,rest) ->
	let (env', bl') = add env bl in
	let bl'' = !bl_ref in
	let env'' = add_ri env bl bl'' in
	let bl_vars = List.combine bl' bl'' in 
	let def_list' = List.map (check_br None (bl'' @ cur_array) env'') def_list in
	(* Compute the defined references in the condition t1 and in rest *)
	let (defined_refs_t1, defined_refs_rest) =
	  Terms.defined_refs_find bl_vars def_list' defined_refs
	in
	let t1' = check_find_cond defined_refs_t1 (bl'' @ cur_array) env'' t1 in
	check_type (snd t1) t1' Settings.t_bool;
	let (rest', def') = insert_rec (p', def) rest env' defined_refs_rest cur_array in
	check_noninter bl' def';
	def_accu := Terms.unionq def' (Terms.unionq bl' (!def_accu));
	(List.combine bl' bl'', def_list', t1', rest')) l0 
      in
      (Terms.new_oproc (Find(l0', rest', find_info)) ext, !def_accu)
  | _ ->
      Parsing_helper.internal_error "Unexpected inserted instruction"

  
	

let rec insert_ins count occ ins env cur_array p =
  let (p_desc', def) = 
  match p.i_desc with
    Nil -> (Nil, [])
  | Par(p1,p2) ->
      let (p1', def1) = insert_ins count occ ins env cur_array p1 in
      let (p2', def2) = insert_ins count occ ins env cur_array p2 in
      check_noninter def1 def2;
      (Par(p1',p2'), def1 @ def2)
  | Repl(b,p) ->
      let env' = StringMap.add (Display.repl_index_to_string b) (EReplIndex b) env in
      let (p', def) = insert_ins count occ ins env' (b::cur_array) p in
      (Repl(b,p'), def)
  | Input((c,tl),pat, p) ->
      let def2 = Terms.vars_from_pat [] pat in
      let env' = List.fold_left (fun env1 b -> StringMap.add (Display.binder_to_string b) (EVar b) env1) env def2 in
      let (p', def) = insert_inso count occ ins env' cur_array p in
      check_noninter def def2;
      (Input((c,tl),pat,p'), def @ def2)
  in
  (Terms.iproc_from_desc_loc p p_desc', def)

and insert_inso count occ ins env cur_array p =
  let (p_desc', def) =
    match p.p_desc with
      Yield -> (Yield, [])
    | EventAbort f -> (EventAbort f, [])
    | Restr(b,p) ->
	let env' = StringMap.add (Display.binder_to_string b) (EVar b) env in
	let (p', def) = insert_inso count occ ins env' cur_array p in
	check_noninter def [b];
	(Restr(b,p'), b::def)
    | Test(t,p1,p2) ->
	let (p1', def1) = insert_inso count occ ins env cur_array p1 in
	let (p2', def2) = insert_inso count occ ins env cur_array p2 in
	(Test(t,p1',p2'), Terms.unionq def1 def2)
    | EventP(t,p) ->
	let (p', def) = insert_inso count occ ins env cur_array p in
	(EventP(t,p'), def)
    | Let(pat,t,p1,p2) ->
	let def2 = Terms.vars_from_pat [] pat in
	let env' = List.fold_left (fun env1 b -> StringMap.add (Display.binder_to_string b) (EVar b) env1) env def2 in
	let (p1', def1) = insert_inso count occ ins env' cur_array p1 in
	check_noninter def1 def2;
	let (p2', def3) = insert_inso count occ ins env cur_array p2 in
	(Let(pat,t,p1',p2'), Terms.unionq (def2 @ def1) def3)
    | Find(l0,p3,find_info) ->
	let (p3', def3) = insert_inso count occ ins env cur_array p3 in
	let accu = ref def3 in
	let l0' = List.fold_right (fun (bl, def_list, t, p1) laccu ->
	  let vars = List.map fst bl in
	  let env' = List.fold_left (fun env1 b -> StringMap.add (Display.binder_to_string b) (EVar b) env1) env vars in	
	  (* I will check that the newly added definitions do not concern 
	     variables defined in the condition of find, so I do not need
	     to add the variables defined in t to def *)
	  let count_before = !count in
	  let (p1', def) = insert_inso count occ ins env' cur_array p1 in
	  let count_after = !count in
	  try
	    let find_branch' = 
	      if (count_before == 0) && (count_after == 1) then
		let already_defined = Facts.get_def_vars_at (DProcess p) in
		let newly_defined = Facts.def_vars_from_defined (Facts.get_initial_history (DProcess p)) def_list in
		Facts.update_def_list_process already_defined newly_defined bl def_list t p1'
	      else
		(bl, def_list, t, p1')
	    in
	    check_noninter def vars;
	    accu := Terms.unionq (vars @ def) (!accu);
	    find_branch' :: laccu
	  with Contradiction ->
	    (* The variables in the defined condition cannot be defined,
	       we can just remove the branch *)
	    laccu
	  ) l0 []
	in
	(Find(l0',p3',find_info), !accu)
    | Output((c,tl),t,p) ->
	let (p', def) = insert_ins count occ ins env cur_array p in
	(Output((c,tl),t,p'), def)
    | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"
  in
  let r = (Terms.oproc_from_desc_loc p p_desc', def) in
  if p.p_occ == occ then
    begin
      incr count;
      let defined_refs = 
	try 
	  Facts.get_def_vars_at (DProcess p)
	with Contradiction ->
	  raise (Error("The occurrence " ^ (string_of_int occ) ^ " at which you are inserting an instruction is in fact unreachable", snd ins))
      in
      check_ins1 cur_array env ins;
      insert_rec r ins env defined_refs cur_array
    end
  else
    r


let insert_instruct occ ext_o s ext_s g =
  if not g.expanded then
    raise (Error ("insert does not support non-expanded games", ext_s));
  let g_proc = Terms.get_process g in
  whole_game := g;
  new_queries := [];
  has_unique_to_prove := false; 
  let ins = Syntax.parse_from_string Parser.instruct (s,ext_s) in
  Array_ref.array_ref_process g_proc;
  Improved_def.improved_def_game None false g;
  Hashtbl.clear hash_binders;
  find_binders_rec g_proc;
  let count = ref 0 in
  let cleanup() =
    Array_ref.cleanup_array_ref();
    Improved_def.empty_improved_def_game false g;
    whole_game := Terms.empty_game;
    new_queries := [];
    Hashtbl.clear hash_binders
  in
  let (p',_) = 
    try
      insert_ins count occ ins (!Stringmap.env) [] g_proc 
    with Error(mess, extent) ->
      cleanup();
      raise (Error(mess, extent))
  in
  let queries_to_add = !new_queries in
  cleanup();
  if (!count) = 0 then 
    raise (Error("Occurrence " ^ (string_of_int occ) ^ " not found. You should use the command show_game occ to determine the desired occurrence.", ext_o))
  else if (!count > 1) then
    raise (Error("Occurrence " ^ (string_of_int occ) ^ " ambiguous. You should use the command show_game occ to determine the desired occurrence.", ext_o))
  else
    begin
      Settings.changed := true;
      let g' = Terms.build_transformed_game p' g in
      (* Add the queries for the inserted event_abort and find[unique] *)
      let pub_vars = Settings.get_public_vars g.current_queries in
      let q_new = 
	List.map (fun f ->
	  let query = Terms.build_event_query f pub_vars in
	  ((query, g'), ref ToProve)
	    ) queries_to_add
      in
      g'.current_queries <- q_new @
	 (List.map (fun (q, poptref) -> (q, ref (!poptref))) g.current_queries);

      let (g'', proba', done_transfos') = Transf_auto_sa_rename.auto_sa_rename g' in
      let (g''', proba'', done_transfos'') = 
	if !has_unique_to_prove then
	  begin
	    Terms.move_occ_game g'';
	    Unique.prove_unique_game false g'' 
	  end
	else
	  (g'', [], [])
      in
      (* Update the game in which the query should be proved: it is g'''
	 (g' will not be displayed)
	 If the query is an old one, make sure it is physically preserved.
	 (Important for Success.update_full_proof) *)
      g'''.current_queries <- List.map (fun (((q,q_g),q_proof) as q0) ->
	if q_g == g' then ((q,g'''),q_proof) else q0) g'''.current_queries;
      let proba =
	List.map2 (fun f (_,q_proof) ->
	  SetEvent(f, g''', pub_vars, q_proof)) queries_to_add q_new
      in
      (g''', proba'' @ proba' @ proba, done_transfos'' @ done_transfos' @  [DInsertInstruct(s, occ)])
    end
     
(**** Replace a term with an equal term ****)

type state_ty =
    RepToDo of int * Parsing_helper.extent * Ptree.term_e * Parsing_helper.extent * replace_check_opt_t
  | RepDone of setf list * int * term * term * Parsing_helper.extent

let may_be_inside count min_occ max_occ =
  match !count with
  | RepToDo(occ,_,_,_,_) ->
      (min_occ <= occ) && (occ <= max_occ)
  | RepDone(_,occ,_,_,_) ->
      if (min_occ <= occ) && (occ <= max_occ) then
	Parsing_helper.internal_error "Ambiguous occurrence. That should never happen";
      false

let rec replace_tt count env facts cur_array t =
  match !count with
    RepToDo (occ, ext_o, ins, ext_s,check_opt) when occ == t.t_occ ->
      if not (Terms.check_simple_term t) then
	raise (Error("The term at " ^ (string_of_int occ) ^ "contains if, let, find, new, or event; you cannot replace it", ext_o));
      let defined_refs = 
	try 
	  Facts.get_def_vars_at (DTerm t)
	with Contradiction ->
	  raise (Error("The occurrence " ^ (string_of_int occ) ^ " at which you are replacing a term is in fact unreachable", ext_o))
      in
      let t' = check_term (Some defined_refs) cur_array env ins in
      if t'.t_type != t.t_type then
	raise (Error("You are trying to replace a term of type " ^ t.t_type.tname ^ " with a term of type " ^ t'.t_type.tname, ext_s));
      begin
	match check_opt with
	| Check ->
	    Depanal.reset [] (!whole_game);
	    let r = 
	      try 
		let facts' = Facts.get_facts_at (DTerm t) in
		let simp_facts = Terms.auto_cleanup (fun () -> Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) (facts'@facts)) in
		let facts'' = 
		  if !Settings.elsefind_facts_in_replace then
		    Facts_of_elsefind.get_facts_of_elsefind_facts (!whole_game) cur_array simp_facts defined_refs 
		  else
		    []
		in
		let simp_facts' = Terms.auto_cleanup (fun () -> Facts.simplif_add_list Facts.no_dependency_anal simp_facts facts'') in
		Facts.check_equal t t' simp_facts' 
	      with Contradiction ->
          (*   print_string "Got contradiction";
	       print_newline ();*)
          (* May happen when the program point of t is in fact unreachable
	     I say true anyway because the program point is unreachable. *)
		true
	    in
	    if not r then
	      raise (Error("I cannot prove that the term you want to put is equal to the term at " ^ (string_of_int occ), ext_s));
	    count := RepDone(Depanal.final_add_proba(), occ, t, t', ext_o);
	    t'
	| Assume ->
	    count := RepDone([SetAssume], occ, t, t', ext_o);
	    t'
      end
  | RepDone(_,occ,_,_,ext_o) when occ == t.t_occ -> 
      Parsing_helper.internal_error ("Occurrence " ^ (string_of_int occ) ^ " ambiguous. That should never happen")
  | _ ->
      if not (may_be_inside count t.t_occ t.t_max_occ) then
	t
      else
      Terms.build_term t 
	(match t.t_desc with
	  Var(b,l) ->
	    (* Do not allow rewriting implicit replication indices.
	       That would cause bugs with missing or misplaced defined
               conditions, because we do not expect to require a defined
               condition for a variable that is in scope. *)
	    let rec avoid_common_prefix lt li =
	      match (lt,li) with
	      |	({t_desc = ReplIndex ri1; t_occ = occ'}::lt',ri2::li')
		  when ri1 == ri2 ->
		    begin
		      match !count with
		      |	RepToDo (occ, ext_o, ins, ext_s,check_opt)
			  when occ == occ' ->
			    raise (Error("Cannot replace an implicit replication index at " ^ (string_of_int occ), ext_s))
		      | _ -> ()
		    end;
		    avoid_common_prefix lt' li'
	      | _ -> ()
	    in
	    avoid_common_prefix (List.rev l) (List.rev b.args_at_creation);
	    Var(b, List.map (replace_tt count env facts cur_array) l)
	| (ReplIndex _ | EventAbortE _) as x -> x
	| FunApp(f,[t1;t2]) when f == Settings.f_and ->
	    (* This is correct because the replacement is done either in t1 or in t2,
	       but not in both! 
	       If the replacement is done in t2, we consider that the expression is
	       evaluated as t1 && t2, so that t2 is evaluated only when t1 holds.
	       If the replacement is done in t1, we consider that the expression is
	       evaluated as t2 && t1, so that t1 is evaluated only when t2 holds. *)
	    FunApp(f, [ replace_tt count env (t2::facts) cur_array t1;
			replace_tt count env (t1::facts) cur_array t2])
	| FunApp(f,[t1;t2]) when f == Settings.f_or ->
	    (* This is correct because the replacement is done either in t1 or in t2,
	       but not in both! 
	       If the replacement is done in t2, we consider that the expression is
	       evaluated as t1 || t2, so that t2 is evaluated only when t1 is false.
	       If the replacement is done in t1, we consider that the expression is
	       evaluated as t2 || t1, so that t1 is evaluated only when t2 is false. *)
	    FunApp(f, [ replace_tt count env ((Terms.make_not t2)::facts) cur_array t1;
			replace_tt count env ((Terms.make_not t1)::facts) cur_array t2])
	| FunApp(f,l) -> FunApp(f, List.map (replace_tt count env facts cur_array) l)
	| ResE(b,p) ->
	    let env' = StringMap.add (Display.binder_to_string b) (EVar b) env in
	    ResE(b, replace_tt count env' facts cur_array p)
	| EventE(t1,p) ->
	    EventE(replace_tt count env facts cur_array t1,
		   replace_tt count env facts cur_array p)
	| GetE _ | InsertE _ ->
	    Parsing_helper.internal_error "get, insert should not occur as term"
	| TestE(t1,t2,t3) ->
	    let t2' = replace_tt count env facts cur_array t2 in
	    let t3' = replace_tt count env facts cur_array t3 in
	    let t1' = replace_tt count env facts cur_array t1 in
	    TestE(t1',t2',t3')
	| LetE(pat,t1,t2,topt) ->
	    let def2 = Terms.vars_from_pat [] pat in
	    let env' = List.fold_left (fun env1 b -> StringMap.add (Display.binder_to_string b) (EVar b) env1) env def2 in
	    let t2' = replace_tt count env' facts cur_array t2 in
	    let topt' = 
	      match topt with
		None -> None
	      | Some t3 -> Some (replace_tt count env facts cur_array t3)
	    in
	    let pat' = replace_tpat count env facts cur_array pat  in
	    let t1' = replace_tt count env facts cur_array t1 in
	    LetE(pat',t1',t2',topt')
	| FindE(l0,t3, find_info) ->
	    let t3' = replace_tt count env facts cur_array t3 in
	    let l0' = List.fold_right (fun (bl, def_list, tc, p) laccu ->
	      let vars = List.map fst bl in
	      let repl_indices = List.map snd bl in
	      
	      (* Compute the environment in the then branch p *)
	      let env_p = List.fold_left (fun env1 b -> StringMap.add (Display.binder_to_string b) (EVar b) env1) env vars in	
	      (* Compute the environment in the condition tc *)
	      let env_tc = List.fold_left (fun env1 b -> StringMap.add (Display.repl_index_to_string b) (EReplIndex b) env1) env repl_indices in
	      let count_before = !count in
	      let p' = replace_tt count env_p facts cur_array p in
	      let tc' = replace_tt count env_tc facts cur_array tc in
	      let count_after = !count in
	      (* Update def_list if needed *)
	      try 
		let find_branch' = 
		  match count_before, count_after with
		    RepToDo _, RepDone _ -> 
		      let already_defined = Facts.get_def_vars_at (DTerm t) in
		      let newly_defined = Facts.def_vars_from_defined (Facts.get_initial_history (DTerm t)) def_list in
		      Facts.update_def_list_term already_defined newly_defined bl def_list tc' p'
		  | _ -> (bl, def_list, tc', p')
		in
		find_branch' :: laccu
	      with Contradiction ->
	        (* The variables in the defined condition cannot be defined,
		   I can just remove the branch *)
		laccu
		  ) l0 []
	    in
	    FindE(l0',t3',find_info))

and replace_tpat count env facts cur_array = function
  | PatVar b -> PatVar b
  | PatTuple(f,l) -> PatTuple(f, List.map (replace_tpat count env facts cur_array) l)
  | PatEqual t -> PatEqual(replace_tt count env facts cur_array t)


let rec replace_t count env cur_array p =
  if not (may_be_inside count p.i_occ p.i_max_occ) then
    p
  else
  let p_desc' =
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) ->
      Par(replace_t count env cur_array p1,
	  replace_t count env cur_array p2)
  | Repl(b,p) ->
      Repl(b, replace_t count env (b::cur_array) p)
  | Input((c,tl),pat, p) ->
      let def2 = Terms.vars_from_pat [] pat in
      let env' = List.fold_left (fun env1 b -> StringMap.add (Display.binder_to_string b) (EVar b) env1) env def2 in
      let p' = replace_to count env' cur_array p in
      let pat' = replace_tpat count env [] cur_array pat in
      let tl' = List.map (replace_tt count env [] cur_array) tl in
      Input((c,tl'),pat',p')
  in
  Terms.iproc_from_desc_loc p p_desc'

and replace_to count env cur_array p =
  if not (may_be_inside count p.p_occ p.p_max_occ) then
    p
  else
  let p_desc' =
    match p.p_desc with
      Yield -> Yield
    | EventAbort f -> EventAbort f
    | Restr(b,p) ->
	let env' = StringMap.add (Display.binder_to_string b) (EVar b) env in
	Restr(b, replace_to count env' cur_array p)
    | Test(t,p1,p2) ->
	let p1' = replace_to count env cur_array p1 in
	let p2' = replace_to count env cur_array p2 in
	let t' = replace_tt count env [] cur_array t in
	Test(t',p1',p2')
    | EventP(t,p) ->
	let p' = replace_to count env cur_array p in
	let t' = replace_tt count env [] cur_array t in
	EventP(t',p')
    | Let(pat,t,p1,p2) ->
	let def2 = Terms.vars_from_pat [] pat in
	let env' = List.fold_left (fun env1 b -> StringMap.add (Display.binder_to_string b) (EVar b) env1) env def2 in
	let p1' = replace_to count env' cur_array p1 in
	let p2' = replace_to count env cur_array p2 in
	let pat' = replace_tpat count env [] cur_array pat  in
	let t' = replace_tt count env [] cur_array t in
	Let(pat',t',p1',p2')
    | Find(l0,p3,find_info) ->
	let p3' = replace_to count env cur_array p3 in
	let l0' = List.fold_right (fun (bl, def_list, t, p1) laccu ->
	  let vars = List.map fst bl in
	  let repl_indices = List.map snd bl in

	  (* Compute the environment in the then branch p1 *)
	  let env_p1 = List.fold_left (fun env1 b -> StringMap.add (Display.binder_to_string b) (EVar b) env1) env vars in	
	  (* Compute the environment in the condition t *)
	  let env_t = List.fold_left (fun env1 b -> StringMap.add (Display.repl_index_to_string b) (EReplIndex b) env1) env repl_indices in
	  let count_before = !count in
	  let p1' = replace_to count env_p1 cur_array p1 in
	  let t' = replace_tt count env_t [] cur_array t in
	  let count_after = !count in
	  (* Update def_list if needed *)
	  try
	    let find_branch' = 
	      match count_before, count_after with
		RepToDo _, RepDone _ ->
		  let already_defined = Facts.get_def_vars_at (DProcess p) in
		  let newly_defined = Facts.def_vars_from_defined (Facts.get_initial_history (DProcess p)) def_list in
		  Facts.update_def_list_process already_defined newly_defined bl def_list t' p1'
	      | _ -> (bl, def_list, t', p1')
	    in
	    find_branch' :: laccu
	  with Contradiction ->
	    (* The variables in the defined condition cannot be defined,
	       I can just remove the branch *)
	    laccu
	  ) l0 []
	in
	Find(l0',p3',find_info)
    | Output((c,tl),t,p) ->
	let p' = replace_t count env cur_array p in
	let t' = replace_tt count env [] cur_array t in
	let tl' = List.map (replace_tt count env [] cur_array) tl in
	Output((c,tl'),t',p')
    | Get _ | Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"
  in
  Terms.oproc_from_desc_loc p p_desc'

let replace_term occ ext_o s ext_s check_opt g =
  let g_proc = Terms.get_process g in
  let rep_term = Syntax.parse_from_string Parser.term (s,ext_s) in
  Array_ref.array_ref_process g_proc;
  Improved_def.improved_def_game None true g;
  Hashtbl.clear hash_binders;
  find_binders_rec g_proc;
  whole_game := g;
  let count = ref (RepToDo (occ, ext_o, rep_term, ext_s, check_opt)) in
  let cleanup() =
    Array_ref.cleanup_array_ref();
    Hashtbl.clear hash_binders;
    Improved_def.empty_improved_def_game true g;
    whole_game := Terms.empty_game
  in
  let p' = 
    try
      replace_t count (!Stringmap.env) [] g_proc 
    with Error(mess, extent) ->
      cleanup();
      raise (Error(mess, extent))
  in
  cleanup();
  match !count with
    RepToDo _ ->
      raise (Error("Occurrence " ^ (string_of_int occ) ^ " not found. You should use the command show_game occ to determine the desired occurrence.", ext_o))
  | RepDone(sets,_,t,t',_) ->
      Settings.changed := true;
      (Terms.build_transformed_game p' g, sets, [DReplaceTerm(t,t',occ)])
