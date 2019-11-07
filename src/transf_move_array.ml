open Types
open Stringmap
open Parsing_helper
  
let parse_and_check_collision var_X (s,ext_s) =
  let coll = Syntax.parse_from_string Parser.move_array_coll (s, ext_s) in
  let (forall, restr, t1) = Syntax.check_move_array_coll (!Stringmap.env) var_X coll in
  let depinfo =
    { args_at_creation_only = true;
      dep = [restr, (Decompos(Some []), Some [], ())];
      other_variables = false;
      nodep = [] }
  in
  let bdepinfo = (restr, depinfo) in
  let dependency_collision t1 t2 _ =
    if not (Proba.is_large restr.btype && Terms.refers_to restr t1) then None else
    let t1' = Depanal.remove_dep_array_index bdepinfo t1 in
    let st = Depanal.find_compos Terms.simp_facts_id bdepinfo (Some []) t1' in
    match Depanal.extract_from_status t1' st with
    | None -> None
    | Some(probaf, t1'',_) ->
	try 
	  let (t2', dep_types, indep_types) = Depanal.is_indep Terms.simp_facts_id bdepinfo t2 in
	  (* We eliminate collisions because t1 characterizes restr and t2 does not depend on restr *)
	  (* add probability; returns true if small enough to eliminate collisions, false otherwise. *)
	  if Depanal.add_term_collisions ([], [], [], Terms.make_true()) t1'' t2' restr (Some []) (probaf, dep_types, t2.t_type, indep_types) then
	    Some (Terms.make_false())
	  else
            None
	with Not_found -> None
  in
  let dependency_anal =
    let indep_test simp_facts t (b,l) =
      assert(l == []);
      let dep_info =
	if b == restr then depinfo else Facts.nodepinfo
      in
      Facts.default_indep_test dep_info simp_facts t (b,l)
    in
    let collision_test simp_facts t1 t2 =
      Depanal.try_two_directions dependency_collision t1 t2
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


let subst var img t =
  Terms.auto_cleanup (fun () ->
    Terms.link var (TLink img);
    Terms.copy_term Links_Vars t)

let move_array_equiv ext2 bl collisions =
  let var_num_state = Terms.get_var_num_state() in
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
  let id_N = Terms.fresh_id "N" in
  let param_N = { pname = id_N;
		  psize = Settings.psize_DEFAULT }
  in
  let id_NX = Terms.fresh_id "NX" in
  let param_NX = { pname = id_NX;
		   psize = Settings.psize_DEFAULT }
  in
  let t_NX = Terms.type_for_param param_NX in
  let idx = Terms.create_repl_index "ix" t_NX in
  let var_X = Terms.create_binder "X" ty [] in
  let id_X = Display.binder_to_string var_X in
  let var_Y = Terms.create_binder "Y" ty [idx] in
  let id_Y = Display.binder_to_string var_Y in
  let var_j = Terms.create_binder "j" t_NX [] in
  let term_j = Terms.term_from_binder var_j in
  let id_j = Display.binder_to_string var_j in
  let term_Y_j = Terms.term_from_binderref (var_Y, [term_j]) in
  let id_T = ty.tname in
  let id_OX = Terms.fresh_id "OX" in
  let collisions' =
    if collisions == [] then
      begin
	if not (Proba.is_large ty) then
	  raise (Error("Transformation \"move array\" is allowed only for large types", ext2));
	let b = Terms.create_binder "X'" ty [] in
	let restr = var_X in
	let t1 = Terms.make_equal (Terms.term_from_binder b) (Terms.term_from_binder restr) in
	let t2 = Terms.make_false() in
	let proba = Proba.pcoll1rand ty in
	[[b],restr,t1,[SetProba proba],t2]
      end
    else
      List.map (parse_and_check_collision var_X) collisions
  in
  let collisions_with_oracle = List.map (fun coll ->
    (Terms.fresh_id "Neq", Terms.fresh_id "Oeq", coll)) collisions'
  in
  (* Create the equivalence as a string, inside a buffer *)
  let b = Buffer.create 500 in
  let print = Buffer.add_string b in
  Display.fun_out print (fun () ->
    print ("equiv(move_array("^id_T^"))\n");
    print ("      !"^id_N^" "^id_X^" <-R "^id_T^"; (");
    print ("!"^id_NX^" "^id_OX^"() := return("^id_X^")");
    List.iter (fun (id_Neq, id_Oeq, (forall, restr, t1, _, _)) ->
      print (" |\n !"^id_Neq^" "^id_Oeq^"(");
      Display.display_list Display.display_binder_with_type forall;
      print (") := return(");
      Display.display_term t1;
      print ")"
	) collisions_with_oracle;
    print ")\n<=(";
    let first = ref true in
    List.iter (fun (id_Neq, id_Oeq, (_, _, _, proba, _)) ->
      if not (!first) then print " + ";
      if proba != [] then
	begin
	  first := false;
	  print ("#"^id_Oeq^" * (");
	  Display.display_set proba;
	  print ")"
	end
	) collisions_with_oracle;
    if !first then print "0";
    print (")=>\n      !"^id_N^" (");
    print ("!"^id_NX^" "^id_OX^"() := find[unique] "^
			 id_j^"<="^id_NX^" suchthat defined(");
    Display.display_term term_Y_j;
    print ") then return(";
    Display.display_term term_Y_j;
    print (") else "^id_Y^" <-R "^id_T^"; return("^id_Y^")");
    List.iter (fun (id_Neq, id_Oeq, (forall, restr, t1, _, t2)) ->
      print (" |\n !"^id_Neq^" "^id_Oeq^"(");
      Display.display_list Display.display_binder_with_type forall;
      print (") := find[unique] "^id_j^"<="^id_NX^" suchthat defined(");
      Display.display_term term_Y_j;
      print ") then return(";
      Display.display_term (subst var_X term_Y_j t1);
      print ") else return(";
      Display.display_term t2;
      print ")"
	) collisions_with_oracle;
    print ").\n"
      );
  let equiv_string = Buffer.contents b in
  (* Debug *)
  print_string equiv_string;
  (* Parse the equivalence *)
  let pequiv = Syntax.parse_from_string (if !Settings.front_end = Channels then Parser.cequiv else Parser.oequiv) (equiv_string, dummy_ext) in
  (* Create the environment for checking the equivalence *)
  let env = Stringmap.env in
  let old_env = !env in
  env := StringMap.add id_N (EParam param_N) (!env);
  env := StringMap.add id_NX (EParam param_NX) (!env);
  List.iter (fun (id_Neq, _, _) ->
    let param_Neq = { pname = id_Neq;
		      psize = Settings.psize_DEFAULT }
    in
    env := StringMap.add id_Neq (EParam param_Neq) (!env)
	 ) collisions_with_oracle;
  (* Check the equivalence *)
  let equiv = Syntax.check_eqstatement pequiv in
  (* Restore the old environement and variable state *)
  env := old_env;
  Terms.set_var_num_state var_num_state;
  equiv
