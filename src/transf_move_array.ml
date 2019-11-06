open Types
open Stringmap
open Parsing_helper
  
let parse_and_check_collision (s,ext_s) =
  let lexbuf = Lexing.from_string s in
  Parsing_helper.set_start lexbuf ext_s;
  let coll = 
    try 
      Parser.move_array_coll Lexer.token lexbuf
    with
      Parsing.Parse_error -> raise (Error("Syntax error", extent lexbuf))
  in
  let env = ref (!Stringmap.env) in
  Terms.TypeHashtbl.iter (fun _ f ->
      env := Stringmap.StringMap.add f.f_name (EFunc f) (!env))
    Terms.cst_for_type_table;
  let (forall, restr, t1) = Syntax.check_move_array_coll (!env) coll in
  let depinfo =
    { args_at_creation_only = true;
      dep = [restr, (Decompos(Some []), Some [], ())];
      other_variables = false;
      nodep = [] }
  in
  let bdepinfo = (restr, depinfo) in
  let rec dependency_collision_rec t1 t2 t =
    match t.t_desc with
      Var(b,l) when (b == restr) && (Proba.is_large_term t) ->
	begin
	  assert (l == []);
	  let t' = Depanal.remove_dep_array_index bdepinfo t in
	  let st = Depanal.find_compos Terms.simp_facts_id bdepinfo (Some []) t' in
	  match Depanal.extract_from_status t' st with
	  | None -> None
	  | Some(probaf, t1'',_) ->
	      try 
		let (t2', dep_types, indep_types) = Depanal.is_indep Terms.simp_facts_id bdepinfo t2 in
	        (* We eliminate collisions because t1 characterizes restr and t2 does not depend on restr *)
	        (* add probability; returns true if small enough to eliminate collisions, false otherwise. *)
		if Depanal.add_term_collisions ([], [], [], Terms.make_true()) t1'' t2' b (Some []) (probaf, dep_types, t2.t_type, indep_types) then
		  Some (Terms.make_false())
		else
                  None
	      with Not_found -> None
	end 
    | FunApp(f,l) ->
	Terms.find_some (dependency_collision_rec t1 t2) l
    | _ -> None
  in
  let dependency_anal =
    let indep_test simp_facts t (b,l) =
      assert(l == []);
      let dep_info =
	if (b == restr) then
	  depinfo
	else
	  Facts.nodepinfo
      in
      Facts.default_indep_test dep_info simp_facts t (b,l)
    in
    let collision_test simp_facts t1 t2 =
      Depanal.try_two_directions dependency_collision_rec t1 t2
    in
    (indep_test, collision_test)
  in
  Depanal.reset [] (Terms.empty_game);(* TODO may need to use a game that outputs t1 *)
  let t2 = Facts.simplify_term dependency_anal Terms.simp_facts_id t1 in
  let proba = Depanal.final_add_proba() in
  Depanal.reset [] (Terms.empty_game);
  if Terms.refers_to restr t2 then
    raise (Error("Cannot eliminate the dependency on "^(Display.binder_to_string restr), ext_s));
  (forall, restr, t1, proba, t2)


let move_array ext2 bl collisions =
  let ty =
    match bl with
    | [] -> Parsing_helper.internal_error "At least one variable should be found"
    | b::rest ->
	let ty = b.btype in
	if List.exists (fun b' -> b'.btype != ty) rest then
	  raise (Error("In \"move array\", all identifiers should have the same type", ext2));
	ty
  in
  if (ty.toptions land Settings.tyopt_CHOOSABLE) == 0 then
    raise (Error("Transformation \"move array\" is allowed only for fixed, bounded, or nonuniform types",ext2));
  let collisions' =
    if collisions == [] then
      begin
	if not (Proba.is_large ty) then
	  raise (Error("Transformation \"move array\" is allowed only for large types", ext2));
	let b = Terms.create_binder0 "X'" ty [] in
	let restr = Terms.create_binder0 "X" ty [] in
	let t1 = Terms.make_equal (Terms.term_from_binder b) (Terms.term_from_binder restr) in
	let t2 = Terms.make_false() in
	let proba = Proba.pcoll1rand ty in
	[[b],restr,t1,[SetProba proba],t2]
      end
    else
      List.map (fun ((_,ext) as coll) ->
	let (_,restr,_,_,_) as coll' = parse_and_check_collision coll in
	if restr.btype != ty then
	  raise (Error("Random values in collisions in \"move array\" should have the same type as the variable(s) we move", ext));
	coll'
	  ) collisions
  in
  let nx = { pname = "NX";
	     psize = Settings.psize_DEFAULT }
  in
  let tnx = Terms.type_for_param nx in
  let counter = ref 1 in
  let collisions_with_oracle = List.map (fun coll ->
    let neq = { pname = "Neq"^(string_of_int (!counter));
		psize = Settings.psize_DEFAULT }
    in
    let oeq = { cname = "Oeq"^(string_of_int (!counter)) } in
    incr counter;
    (neq, oeq, coll)) collisions
  in
  let x = Terms.create_binder0 "X" ty [] in
  let iX1 = Terms.create_repl_index "iX" tnx in
  let iX2 = Terms.create_repl_index "iX" tnx in
  let oX = { cname = "OX" } in
  let lhs = ReplRestr(None, [x, NoOpt],
		      (ReplRestr(Some iX1, [], [Fun(oX, [], Terms.build_term_type ty (Var(x,[])), (0, StdOpt))]))::
		      [(* TODO oracles for collisions; add repl index to the terms of the collision! *)])
  in
  
    ()
