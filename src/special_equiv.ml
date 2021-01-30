open Types
open Stringmap
open Parsing_helper


(* [instan_time get_time p] 
   - removes [Time(g,t)], keeping just [t] instead
   - instantiates the runtime of the adversary [AttTime], using the 
   runtime of the current context returned by [get_time()], 
   - instantiates variables in [Maxlength(g,t)] according to links
   - replaces the game [g] in [Maxlength(g,t)] with [Terms.lhs_game_nodisplay],
   so that [Maxlength(g,t)] is displayed "maxlength(t)",
   in the probability [p] *)
    
let rec instan_time get_time p =
  let rec aux = function
    | AttTime -> Add(AttTime, get_time())
    | Time(_,t) -> aux t
    | (Cst _ | Count _ | OCount _ | Zero | Card _ | TypeMaxlength _
      | EpsFind | EpsRand _ | PColl1Rand _ | PColl2Rand _) as x -> x
    | Proba(p,l) -> Proba(p, List.map aux l)
    | ActTime(f,l) -> ActTime(f, List.map aux l)
    | (Max _ | Maxlength _) as y ->
	let accu = ref Polynom.empty_minmax_accu in
	let rec add_max = function
	  | Max(l) -> List.iter add_max l
	  | Maxlength(g,t) ->
	      Computeruntime.make_length_term accu Terms.lhs_game_nodisplay
		(Terms.copy_term Terms.Links_Vars t)	      
	  | x -> Polynom.add_max accu (aux x)
	in
	add_max y;
	Polynom.p_max (!accu)
    | Min(l) -> 
	let accu = ref Polynom.empty_minmax_accu in
	let rec add_min = function
	  | Min(l) -> List.iter add_min l
	  | x -> Polynom.add_min accu (aux x)
	in
	List.iter add_min l;
	Polynom.p_min (!accu)
    | Length(f,l) -> Length(f, List.map aux l)
    | Mul(x,y) -> Mul(aux x, aux y)
    | Add(x,y) -> Add(aux x, aux y)
    | Sub(x,y) -> Sub(aux x, aux y)
    | Div(x,y) -> Div(aux x, aux y)
  in
  Polynom.p_sum (List.map (function
    | SetProba p -> aux p
    | SetEvent _ | SetAssume -> assert false) p)

(* Generate the equivalence for the command "move array" *)
  
let simplify_indep_new (s,ext_s) (forall, restr_l, t1) =
  let restr =
    match restr_l with
    | [restr] -> restr
    | _ -> assert false
  in
  (* Build a game in(c, forall); new restr; out(c, t1).
     We use it to compute the runtime of the adversary when we simplify t1,
     and to set the definition points of variables. *)
  let c = {cname = "c"} in
  let tuple = Settings.get_tuple_fun (List.map (fun b -> b.btype) forall) in
  let pout = Terms.oproc_from_desc (Output((c,[]), t1, Terms.iproc_from_desc Nil)) in
  let prestr = Terms.oproc_from_desc (Restr(restr, pout)) in
  let p = Terms.iproc_from_desc
      (Input((c,[]), PatTuple(tuple, List.map (fun b -> PatVar b) forall), prestr))
  in
  let g = { proc = RealProcess p; expanded = true; game_number = -1; current_queries = [] } in
  (* Set definition points of variables *)
  let nodein = Terms.set_def forall (DInputProcess p) (DProcess prestr) None in
  ignore (Terms.set_def [restr] (DProcess prestr) (DProcess pout) (Some nodein));
  (* Dependency analysis *)
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
	  if Depanal.add_term_collisions ([], [], Terms.make_true()) t1'' t2' restr (Some []) (probaf, dep_types, t2.t_type, indep_types) then
	    Some (Terms.make_false())
	  else
            None
	with Not_found -> None
  in
  let dependency_anal =
    let get_dep_info (b,l) =
      assert(l == []);
      if b == restr then depinfo else Facts.nodepinfo
    in
    let collision_test simp_facts t1 t2 =
      Depanal.try_two_directions dependency_collision t1 t2
    in
    (Facts.default_indep_test get_dep_info, collision_test)
  in
  Depanal.reset [] g;
  (* Try to simplify t1 *)
  let t2 = Facts.simplify_term dependency_anal Terms.simp_facts_id t1 in
  let proba = Depanal.final_add_proba() in
  Depanal.reset [] (Terms.empty_game);
  if Terms.refers_to restr t2 then
    raise (Error("Cannot eliminate the dependency on the random value when simplifying "^s, ext_s));
  (forall, restr, t1, proba, t2)
  
let parse_and_check_indep_new var_X s_ext =
  let coll = Syntax.parse_from_string Parser.move_array_coll s_ext in
  let coll' = Syntax.check_special_equiv_coll (!Stringmap.env) (ExpectVar var_X) coll in
  simplify_indep_new s_ext coll'
      
let subst var img t =
  Terms.auto_cleanup (fun () ->
    Terms.link var (TLink img);
    Terms.copy_term Terms.Links_Vars t)

let get_time_lhs_except_one_coll collisions coll =
  Polynom.p_sum (List.map (fun ((id_Neq, id_Oeq, (_, _, t1, _, _)) as coll') ->
    let nrep =
      if coll == coll' then
	Sub(OCount { cname = id_Oeq }, Cst 1.0)
      else
	OCount { cname = id_Oeq }
    in
    Polynom.p_mul(nrep, Computeruntime.compute_runtime_for_term Terms.lhs_game_nodisplay t1)
      ) collisions)
    
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
	  raise (Error("Transformation \"move array\" is allowed only for types large enough, so that collisions between a random element of the type and an independent value can be eliminated", ext2));
	let b = Terms.create_binder "X'" ty [] in
	let restr = var_X in
	let t1 = Terms.make_equal (Terms.term_from_binder b) (Terms.term_from_binder restr) in
	let t2 = Terms.make_false() in
	let proba = Proba.pcoll1rand ty in
	[[b],restr,t1,[SetProba proba],t2]
      end
    else
      List.map (parse_and_check_indep_new var_X) collisions
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
    let proba' =
      Polynom.p_sum (List.map (fun ((id_Neq, id_Oeq, (_, _, _, proba, _)) as coll) ->
	let get_time() = get_time_lhs_except_one_coll collisions_with_oracle coll in
	let proba' = instan_time get_time proba in
	Polynom.p_mul (OCount { cname = id_Oeq }, proba')
	  ) collisions_with_oracle)
    in
    Display.display_proba 0 proba';	       
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
  (* print_string equiv_string; *)
  (* Restore the old variable state. That allows check_eqstatement
     to reuse the same variable names. That function also saves and
     restores the variable state. *)
  Terms.set_var_num_state var_num_state;
  (* Parse the equivalence *)
  let pequiv = Syntax.parse_from_string (if !Settings.front_end = Settings.Channels then Parser.cequiv else Parser.oequiv) (equiv_string, dummy_ext) in
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
  let equiv = Syntax.check_eqstatement true pequiv in
  (* Restore the old environment *)
  env := old_env;
  equiv

(* Generate the equivalence for random functions (ROM, PRF, PRP) *)

let dependency_anal_no_info =
  let collision_test simp_facts t1 t2 = Depanal.try_two_directions
      (Depanal.dependency_collision_rec [] simp_facts 
	 (fun _ -> Facts.nodepinfo)) t1 t2
  in
  (Facts.indep_test_noinfo, collision_test)

let simplify_newl_dep (forall, restrl, t1) =
  (* Build a game in(c, ()); new restrl; ; out(c, (restrl)); in(c, forall); out(c, t1).
     We use it to compute the runtime of the adversary when we simplify t1,
     and to set the definition points of variables. *)
  let c = {cname = "c"} in
  let tuple_forall = Settings.get_tuple_fun (List.map (fun b -> b.btype) forall) in
  let out_term =
    match restrl with
    | [restr] -> Terms.term_from_binder restr
    | _ ->
	let tuple_restr = Settings.get_tuple_fun (List.map (fun b -> b.btype) restrl) in
	Terms.app tuple_restr (List.map Terms.term_from_binder restrl)
  in
  let pout_t1 = Terms.oproc_from_desc (Output((c,[]), t1, Terms.iproc_from_desc Nil)) in
  let pin_forall = Terms.iproc_from_desc
      (Input((c,[]), PatTuple(tuple_forall, List.map (fun b -> PatVar b) forall), pout_t1))
  in
  let pout_restr = Terms.oproc_from_desc (Output((c,[]), out_term, pin_forall)) in
  let prestr = List.fold_left (fun p restr -> Terms.oproc_from_desc (Restr(restr, p)))
      pout_restr restrl in
  let p = Terms.iproc_from_desc (Input((c,[]), PatTuple(Settings.empty_tuple, []), prestr)) in
  let g = { proc = RealProcess p; expanded = true; game_number = -1; current_queries = [] } in
  (* Set definition points of variables *)
  let rec put_restr_def node_opt p =
    match p.p_desc with
    | Restr(b,p') ->
	b.def <- [];
	let n' = Terms.set_def [b] (DProcess p) (DProcess p') node_opt in
	put_restr_def (Some n') p'
    | _ -> node_opt
  in
  let node_restr_opt = put_restr_def None prestr in
  List.iter (fun b -> b.def <- []) forall;
  ignore (Terms.set_def forall (DInputProcess pin_forall) (DProcess pout_t1) node_restr_opt);
  (* Try to simplify t1 *)
  Depanal.reset [] g;
  let t2 = Facts.simplify_term dependency_anal_no_info Terms.simp_facts_id t1 in
  let proba = Depanal.final_add_proba() in
  Depanal.reset [] (Terms.empty_game);
  if List.exists (fun b -> Terms.refers_to b t2) restrl then
    None
  else
    Some(proba, t2)

type checked_coll =
  | IndepNew of (binder list * binder * term * setf list * term)
  | NewDep of binder * binder list * term * setf list * term
  | NewNewDep of binder * binder * binder list * term * setf list * term * setf list * term
      
let parse_and_check_fun_coll ty ((s, ext_s) as s_ext) =
  let name, coll = Syntax.parse_from_string Parser.random_fun_coll s_ext in
  match coll with
  | Ptree.CollIndepNew coll1 ->
      let coll' = Syntax.check_special_equiv_coll (!Stringmap.env) (ExpectType ty) coll1 in
      name, IndepNew (simplify_indep_new s_ext coll')
  | Ptree.CollNewDep coll2 ->
      let (forall, restr_l, t1) as coll' = Syntax.check_special_equiv_coll (!Stringmap.env) (ExpectType ty) coll2 in
      match restr_l with
      | [restr] ->
	  begin
	    match simplify_newl_dep coll' with
	    | None ->
		raise (Error("Cannot eliminate the dependency on the random value when simplifying "^s, ext_s))
	    | Some(proba, t2) ->
		name, NewDep(restr, forall, t1, proba, t2)
	  end
      | [restr1;restr2] ->
	  begin
	    let (proba_indep, t2_indep) =
	      match simplify_newl_dep coll' with
	      | None ->
		  raise (Error("Cannot eliminate the dependency on one of two random values when simplifying "^s, ext_s))
	      | Some x -> x
	    in
	    let t1_same = subst restr2 (Terms.term_from_binder restr1) t1 in
	    let (proba_same, t2_same) =
	      match simplify_newl_dep (forall, [restr1], t1_same) with
	      | None ->
		  raise (Error("Cannot eliminate the dependency on the random value when simplifying "^
			       s^" assuming "^(Display.binder_to_string restr1)^" = "^
			       (Display.binder_to_string restr2), ext_s))
	      | Some x -> x
	    in
	    name, NewNewDep(restr1, restr2, forall, t1, proba_indep, t2_indep, proba_same, t2_same)
	  end
      | _ -> assert false


let parse_and_check_bij_coll ty ((s, ext_s) as s_ext) =
  let name, coll = Syntax.parse_from_string Parser.random_bij_coll s_ext in
  let coll' = Syntax.check_special_equiv_coll (!Stringmap.env) (ExpectType ty) coll in
  name, IndepNew (simplify_indep_new s_ext coll')

	    
(* Oracles: *)

type partial_oracle_t =
  | Leave
  | Normal
	    
type random_fun_oracle_t =
  | Basic of partial_oracle_t
  | Coll of checked_coll * partial_oracle_t (* [partial_oracle_t] is used only when [checked_coll = IndepNew _] *)

let get_list1 = function
  | [a1] -> a1
  | _ -> assert false

let get_list2 = function
  | [a1; a2] -> a1, a2
  | _ -> assert false

let get_list3 = function
  | [a1; a2; a3] -> a1, a2, a3
  | _ -> assert false
	
let get_some = function
  | Some x -> x
  | None -> assert false

let max_pos p1 p2 =
  match (p1, p2) with
  | (Zero | Cst 0.0), _ -> p2
  | _, (Zero | Cst 0.0) -> p1
  | _ -> if Terms.equal_probaf p1 p2 then p1 else Max [p1; p2]

(* Oracle names consist of 2 parts: 
   <coll name>_<suffix>
   where <coll_name> must not contain _.
   When there is no _, the suffix is empty.
   *)
let get_name_suffix o_name =
  try 
    let i = String.index o_name '_' in
    String.sub o_name (i+1) (String.length o_name - i - 1)
  with Not_found ->
    ""
      
let get_suffix (o_name, o_ty, idx, b_idx, param, args, res, _, _, _) =
  get_name_suffix o_name
  
let get_suffix_ o_name = 
  try 
    let i = String.index o_name '_' in
    String.sub o_name i (String.length o_name - i)
  with Not_found ->
    ""

let rec filter_unbounded tyargs all_maxlength =
  match tyargs, all_maxlength with
  | [], [] -> []
  | ty::tyr, ml::mlr ->
      let mlr' = filter_unbounded tyr mlr in
      if ty.toptions land Settings.tyopt_BOUNDED != 0 then
	mlr'
      else
	ml::mlr'
  | _ -> assert false

let nth_rest n l =
  assert (n >= 0);
  let rec aux n accu = function
    | [] -> assert false
    | a::l ->
	if n = 0 then
	  (a, List.rev_append accu l)
	else
	  aux (n-1) (a::accu) l
  in
  aux n [] l

let put_nth n a l =
  assert (n >= 0);
  let rec aux n accu l =
    if n = 0 then
      List.rev_append accu (a::l)
    else
      match l with
      | [] -> assert false
      | b::lb ->
	  aux (n-1) (b::accu) lb
  in
  aux n [] l
      
let make_random_fun_equiv f key_pos ((id_k, ext_k), id_r, id_x, id_y, id_z, id_u) proba_fun (oracles : (string * random_fun_oracle_t) list) collision_matrix =
  let var_num_state = Terms.get_var_num_state() in
  let (tyallargs, tyres) = f.f_type in
  let (tykey,tyargs) = nth_rest key_pos tyallargs in
  let k =
    (* check that id_k is not already in the environment *)
    if Stringmap.StringMap.mem id_k (!Stringmap.env) then
      let k = Terms.create_binder id_k tykey [] in
      Parsing_helper.input_warning ("Special equivalence: the identifier "^id_k^" that you specified for the key is already used. Using "^(Display.binder_to_string k)^" instead.") ext_k;
      k
    else
      Terms.create_binder0 id_k tykey []
  in
  let callf args =
    Terms.app f (List.map Terms.term_from_binder (put_nth key_pos k args))
  in
  let oracles_with_args = List.map (fun (o_name, o_ty) ->
    let id_param = Terms.fresh_id ("N_"^o_name) in
    let param =
      { pname = id_param;
	psize = Settings.psize_DEFAULT }
    in
    let t_param = Terms.type_for_param param in
    let idx = Terms.create_repl_index ("i_"^o_name) t_param in
    let b_idx = Terms.create_binder (id_u^"_"^o_name) t_param [] in
    let args, lhs_result_term, rhs_result_opt = 
      match o_ty with
      | Basic _ ->
	  let f_args = List.map (fun ty -> Terms.create_binder (id_x^"_"^o_name) ty [idx]) tyargs in
	  [ f_args ], callf f_args, None
      | Coll (IndepNew (forall, restr, t1, proba, t2), _)
      | Coll (NewDep(restr, forall, t1, proba, t2), _) ->
	  let f_args = List.map (fun ty -> Terms.create_binder (id_x^"_"^o_name) ty [idx]) tyargs in
	  let forall_args = List.map (fun b -> Terms.create_binder (b.sname^"_"^o_name) b.btype [idx]) forall in
	  let lhs_result_term, rhs_result_term =
	    Terms.auto_cleanup (fun () ->
	      List.iter2 (fun b b' ->
		Terms.link b (TLink (Terms.term_from_binder b'))) forall forall_args;
	      Terms.link restr (TLink (callf f_args));
	      Terms.copy_term Terms.Links_Vars t1,
	      Terms.copy_term Terms.Links_Vars t2)
	  in
	  [ f_args; forall_args ], lhs_result_term, Some rhs_result_term
      | Coll (NewNewDep(restr1, restr2, forall, t1, proba_indep, t2_indep, proba_same, t2_same), _) ->
	  let f_args1 = List.map (fun ty -> Terms.create_binder (id_y^"_"^o_name) ty [idx]) tyargs in
	  let f_args2 = List.map (fun ty -> Terms.create_binder (id_z^"_"^o_name) ty [idx]) tyargs in
	  let forall_args = List.map (fun b -> Terms.create_binder (b.sname^"_"^o_name) b.btype [idx]) forall in
	  let eq_vars b1 b2 =
	    Terms.make_equal (Terms.term_from_binder b1) (Terms.term_from_binder b2)
	  in
	  let lhs_result_term, rhs_result_term =
	    Terms.auto_cleanup (fun () ->
	      List.iter2 (fun b b' ->
		Terms.link b (TLink (Terms.term_from_binder b'))) forall forall_args;
	      Terms.link restr1 (TLink (callf f_args1));
	      Terms.link restr2 (TLink (callf f_args2));
	      Terms.copy_term Terms.Links_Vars t1,
	      let cond = Terms.make_and_list (List.map2 eq_vars f_args1 f_args2) in
	      let tthen = Terms.copy_term Terms.Links_Vars t2_same in
	      let telse = Terms.copy_term Terms.Links_Vars t2_indep in
	      if Terms.is_false telse then
		Terms.make_and cond tthen
	      else
		Terms.build_term_type t1.t_type (TestE(cond, tthen, telse))
		)
	  in
	  [ f_args1; f_args2; forall_args ], lhs_result_term, Some rhs_result_term
    in
    let res =
      match o_ty with
      | Basic Leave | Coll _ -> None
      | Basic Normal -> Some (Terms.create_binder (id_r^(get_suffix_ o_name)) tyres [idx])
    in
    let lhs_result_time = Computeruntime.compute_runtime_for_term Terms.lhs_game_nodisplay lhs_result_term in
    (o_name, o_ty, idx, b_idx, param, args, res, lhs_result_term, lhs_result_time, rhs_result_opt)
      ) oracles
  in
  let ev_coll = Terms.fresh_id "ev_coll" in
  let ev_coll_f = Terms.create_event ev_coll [] in
  (* Create the equivalence as a string, inside a buffer *)
  let b = Buffer.create 500 in
  let print = Buffer.add_string b in
  let display_oracle_call (o_name, o_ty, idx, b_idx, param, args, res, _, _, _) =
    print ("!"^param.pname^" "^o_name^"(");
    let first = ref true in
    List.iter (List.iter (fun b ->
      if !first then
	first := false
      else
	print ", ";
      Display.display_binder b; print ": "; print b.btype.tname)) args;
    print ") := "
  in
  let coll() =
    print "event_abort ";
    print ev_coll
  in
  let return t =
    print "return(";
    Display.display_term t;
    print ")"
  in    
  let may_collide suffix1 suffix2 =
    match collision_matrix with
    | Some collision_info_list ->
	List.exists (fun (l1, l2) ->
	  (List.mem suffix1 l1 && List.mem suffix2 l2)
	    ) collision_info_list
    | None -> 
	StringPlus.starts_with suffix1 "leave" ||
	StringPlus.starts_with suffix2 "leave" ||
	suffix1 = suffix2
  in
  (* Makes a [find] on all oracles in [oracles_with_args] of type [desired_ty].
     [f_args] is the list of arguments of the function [f] in the current oracle
     [oracle] is the current oracle
     [prev_res_fun oracle'] is the result to return when the arguments [args] of
     [f] in the current oracle are equal to the arguments of [f] in a previous call to [oracle'] *)
  let make_find desired_ty f_args oracle prev_res_fun =
    let first = ref true in
    List.iter (fun ((o_name', o_ty', idx', b_idx', param', args', res', _, _, _) as oracle') ->
      if o_ty' = Basic desired_ty then
	begin
	  if !first then
	    begin
	      first := false;
	      print (if desired_ty == Normal then "find[unique] " else "find ")
	    end
	  else
	    print (if desired_ty == Normal then "orfind " else "else find ");
	  Display.display_binder b_idx';
	  print " <= ";
	  print param'.pname;
	  print " suchthat defined(";
	  let args' = get_list1 args' in
	  Display.display_list (fun b' ->
	    Display.display_binder b';
	    print "[";
	    Display.display_binder b_idx';
	    print "]"
	      ) args';
	  begin
	    match res' with
	    | Some res'' ->
		print ", ";
		Display.display_binder res'';
		print "[";
		Display.display_binder b_idx';
		print "]"
	    | None -> ()
	  end;
	  print ")";
	  List.iter2 (fun b b' ->
	    print " && ";
	    Display.display_binder b;
	    print " = ";
	    Display.display_binder b';
	    print "[";
	    Display.display_binder b_idx';
	    print "]"
	      ) f_args args';
	  print " then ";
	  if may_collide (get_suffix oracle) (get_suffix oracle') then
	    return (prev_res_fun oracle')
	  else
	    coll();
	  print "\n";
	end
	  ) oracles_with_args;
    if not (!first) then
      print "else\n"
  in
  let prev_res (o_name', o_ty', idx', b_idx', param', args', res', _, _, _) =
    match res' with
    | Some res'' ->
	Terms.build_term_type tyres (Var(res'', [Terms.term_from_binder b_idx']))
    | None ->
	Terms.app f (put_nth key_pos (Terms.term_from_binder k)
		     (List.map (fun b -> Terms.build_term_type b.btype (Var(b, [Terms.term_from_binder b_idx']))) (get_list1 args')))
  in
  let get_time_lhs_except_one_oracle oracle' =
    Polynom.p_sum (List.map (fun ((o_name, o_ty, idx, b_idx, param, args, res, _, lhs_result_time, _) as oracle) ->
      let nrep =
	if oracle == oracle' then
	  Sub(Count param, Cst 1.0)
	else
	  Count param
      in
      Polynom.p_mul(nrep, lhs_result_time)
	) oracles_with_args)
  in
  Display.fun_out print (fun () ->
    print "equiv\n";
    Display.display_binder k;
    print " <-R ";
    print tykey.tname;
    print "; (\n";
    let first_oracle = ref true in
    List.iter (fun ((o_name, o_ty, idx, b_idx, param, args, res, lhs_result_term, _, _) as oracle) ->
      if !first_oracle then
	first_oracle := false
      else
	print " | \n";
      display_oracle_call oracle;
      return lhs_result_term
	) oracles_with_args;
    print ")\n<=(";
    (* Probability: count the number of calls and maximum length *)
    let all_calls = ref [] in
    let all_maxlength_accu = List.map (fun _ -> ref Polynom.empty_minmax_accu) tyargs in
    let proba_coll = ref [] in
    let add_call f_args =
      List.iter2 (fun arg prev_maxlength ->
	Polynom.add_max prev_maxlength (Maxlength(Terms.lhs_game_nodisplay, Terms.term_from_binder arg))
	  ) f_args all_maxlength_accu
    in
    List.iter (fun ((o_name, o_ty, idx, b_idx, param, args, res, _, _, _) as oracle) ->
      match o_ty with
      | Basic Normal ->
	  all_calls := (Count param) :: (!all_calls);
	  let f_args = get_list1 args in
	  add_call f_args
      | Basic _ ->
	  all_calls := (Count param) :: (!all_calls);
	  let f_args = get_list1 args in
	  add_call f_args	  
      |	Coll(IndepNew(forall, restr, _, proba, _),_)
      | Coll(NewDep(restr, forall, _, proba, _),_) ->
	  all_calls := (Count param) :: (!all_calls);
	  let (f_args, forall_args) = get_list2 args in
	  add_call f_args;
	  let get_time() = get_time_lhs_except_one_oracle oracle in
	  let proba' = 
	    Terms.auto_cleanup (fun () ->
	      List.iter2 (fun b b' ->
		Terms.link b (TLink (Terms.term_from_binder b'))) forall forall_args;
	      Terms.link restr (TLink (callf f_args));
	      instan_time get_time proba)
	  in
	  proba_coll := Polynom.p_mul (Count param, proba')
	     :: (!proba_coll) 
      | Coll(NewNewDep(restr1, restr2, forall, _, proba_indep, _, proba_same, _),_) ->
	  all_calls := (Mul(Cst 2.0, Count param)) :: (!all_calls);
	  let (f_args1, f_args2, forall_args) = get_list3 args in
	  add_call f_args1;
	  add_call f_args2;
	  let get_time() = get_time_lhs_except_one_oracle oracle in
	  let proba' = 
	    Terms.auto_cleanup (fun () ->
	      List.iter2 (fun b b' ->
		Terms.link b (TLink (Terms.term_from_binder b'))) forall forall_args;
	      Terms.link restr1 (TLink (callf f_args1));
	      Terms.link restr2 (TLink (callf f_args2));
	      max_pos (instan_time get_time proba_indep)
		(instan_time get_time proba_same)
		)
	  in
	  proba_coll := Polynom.p_mul (Count param, proba')
	     :: (!proba_coll) 
	    ) oracles_with_args;
    let all_maxlength = 
	(filter_unbounded tyargs
	   (List.map (fun accu -> Polynom.p_max (!accu)) all_maxlength_accu))
    in
    let all_calls = Polynom.p_sum (!all_calls) in
    let proba_coll = Polynom.p_sum (!proba_coll) in
    let total_proba = Polynom.p_add (proba_fun all_calls all_maxlength, proba_coll) in
    Display.display_proba 0 total_proba;
    print ")=>\n";
    let key_needed =
      List.exists (fun (o_name, o_ty, idx, b_idx, param, args, res, _, _, _) ->
	match o_ty with
	| Basic Leave | Coll (IndepNew _, Leave) -> true
	| Basic Normal | Coll (IndepNew _, Normal)
	| Coll((NewDep _ | NewNewDep _), _) -> false
	      ) oracles_with_args
    in
    if key_needed then
      begin
	Display.display_binder k;
	print " <-R ";
	print tykey.tname;
	print "; (\n"
      end;
    let first_oracle = ref true in
    List.iter (fun ((o_name, o_ty, idx, b_idx, param, args, res, lhs_result_term, lhs_result_time, rhs_result_opt) as oracle) ->
      if !first_oracle then
	first_oracle := false
      else
	print " | \n";
      display_oracle_call oracle;
      begin
	match o_ty with
	| Basic partial_ty ->
	    let args = get_list1 args in
	    make_find Normal args oracle prev_res;
	    begin
	      match partial_ty with
	      | Leave ->
		  return lhs_result_term
	      | Normal ->
		  make_find Leave args oracle prev_res;
		  let res = get_some res in
		  Display.display_binder res;
		  print " <-R ";
		  print tyres.tname;
		  print "; return(";
		  Display.display_binder res;
		  print ")"
	    end
	| Coll(IndepNew (forall, restr, t1, proba, t2), partial_ty) ->
	    let (f_args, forall_args) = get_list2 args in
	    let prev_res_fun oracle' = 
	      Terms.auto_cleanup (fun () ->
		List.iter2 (fun b b' ->
		  Terms.link b (TLink (Terms.term_from_binder b'))) forall forall_args;
		Terms.link restr (TLink (prev_res oracle'));
		Terms.copy_term Links_Vars t1)
	    in
	    make_find Normal f_args oracle prev_res_fun;
	    begin
	      match partial_ty with
	      | Leave ->
		  return lhs_result_term
	      | Normal ->
		  make_find Leave f_args oracle prev_res_fun;
		  return (get_some rhs_result_opt)
	    end		  
	| Coll ((NewDep _ | NewNewDep _), _) ->
	    return (get_some rhs_result_opt)
      end
	) oracles_with_args;
    if key_needed then print ")";
    print ".\n"    
      );
  let equiv_string = Buffer.contents b in
  (* Debug 
     print_string equiv_string;*)
  if (!Settings.equiv_output) <> "" then
    begin
      let equiv_out = open_out_gen [ Open_wronly; Open_append; Open_creat ] 0o640 (!Settings.equiv_output) in
      output_string equiv_out equiv_string;
      output_string equiv_out "\n";
      close_out equiv_out
    end;
  (* Restore the old variable state. That allows check_eqstatement
     to reuse the same variable names. That function also saves and
     restores the variable state. *)
  Terms.set_var_num_state var_num_state;
  (* Parse the equivalence *)
  let pequiv = Syntax.parse_from_string (if !Settings.front_end = Settings.Channels then Parser.cequiv else Parser.oequiv) (equiv_string, dummy_ext) in
  (* Create the environment for checking the equivalence *)
  let env = Stringmap.env in
  let old_env = !env in
  List.iter (fun (o_name, o_ty, idx, b_idx, param, args, res, _, _, _) ->
    env := StringMap.add param.pname (EParam param) (!env)
	 ) oracles_with_args;
  env := StringMap.add ev_coll (EEvent ev_coll_f) (!env);
  (* Check the equivalence *)
  let equiv = Syntax.check_eqstatement true pequiv in
  (* Restore the old environment *)
  env := old_env;
  equiv
  

(* Arguments:
   1/ key position ("key_first" or "key_last")
   2/ the function 
   3/ the proba function (for PRF and PRP)
   4/ identifiers: key (hk/k), result (r), arguments (x, y, z), find index (u)
   5/ collisions *)

type f_type_t =
  | ROM
  | PRF
  | PRP

let random_fun f_type is_partial (equiv_name, gen_ext) args_at_equiv call =
  let var_num_state = Terms.get_var_num_state() in
  let expected_args() =
    "Special equivalence "^equiv_name^" expects to be called as "^equiv_name^"(key_pos, f, "^
    (if f_type == ROM then "" else "proba, ")^
    "(k, r, x, "^ (if f_type == PRP then "" else "y, z, ")^"u), collisions)\nwhere
- key_pos is either \"key_first\", \"key_last\", or \"key <n>\" for some integer <n> between 1 and the number of arguments of the function, depending on the position of the key argument in function f
- f is a function\n"^
    (if f_type == ROM then "" else "- proba(t, N, l1, ..., ln) is the probability that an adversary breaks the "^(if f_type == PRP then "PRP" else "PRF")^" assumption
  in time t, with at most N queries to the function, with arguments of lengths at most l1, ..., ln (the length is omitted when the corresponding type is bounded)\n")^
    "- k is the identifier of the key
- r is the identifier of the random result of f after game transformation
- x is the identifier used for arguments of f in most oracles\n"^
(if f_type == PRP then "" else "- y and z are the identifiers used for arguments of the two calls to f in oracles generated by the collision \"Ocoll: new r1:T; new r2:T; forall a1:T1...an:Tn; t\"\n")^
"- u is the identifier used for find indices 
- collisions describes collisions and must be a tuple of strings
The arguments (k, r, x, "^ (if f_type == PRP then "" else "y, z, ")^"u) and collisions may be omitted."
  in
  let key_pos_string, r_args_at_equiv =
    match args_at_equiv with
    | (SpecialArgString (s, ext), _)::rest ->
	(s, ext), rest
    | (_, ext)::rest ->
	raise (Error(expected_args(), ext))
    | _ ->
	raise (Error(expected_args(), gen_ext))
  in
  let f, ext_f, r_args_at_equiv =
    match r_args_at_equiv with
    | (SpecialArgId (f_id, ext), _)::rest ->
	begin
	  try
	    match Stringmap.StringMap.find f_id (!Stringmap.env) with
	    | EFunc f -> f, ext, rest
	    | _ -> raise (Error("Special equivalence "^equiv_name^": "^f_id^" must be a function", ext))
	  with Not_found ->
	    raise (Error("Special equivalence "^equiv_name^": "^f_id^" not declared; it must be a function", ext))
	end
    | (_, ext)::rest ->
	raise (Error(expected_args(), ext))
    | _ ->
	raise (Error(expected_args(), gen_ext))
  in
  let (ty_all_args, ty_res) = f.f_type in
  if List.length ty_all_args < 2 then
    raise (Error("Special equivalence "^equiv_name^": the function "^f.f_name^" must have "^(if f_type == PRP then "" else "at least ") ^"two arguments", ext_f));
  let key_pos =
    match key_pos_string with
    | ("key_first", _) -> 0
    | ("key_last", _) -> List.length ty_all_args - 1
    | (s, ext) ->
	if StringPlus.starts_with s "key " then
	  try 
	    let pos_string = String.sub s 4 (String.length s - 4) in
	    let key_pos = int_of_string pos_string - 1 in
	    if key_pos < 0 || key_pos > List.length ty_all_args - 1 then
	      raise (Error("Key position should be between 1 and the number of arguments of the function, here "^(string_of_int (List.length ty_all_args))^"; "^(string_of_int key_pos)^" is not correct", ext));
	    key_pos
	  with Failure _ ->
	    raise (Error("Key position should be \"key_first\", \"key_last\", or \"key <n>\" for some integer <n> between 1 and the number of arguments of the function", ext))
	else
	  raise (Error("Key position should be \"key_first\", \"key_last\", or \"key <n>\" for some integer <n> between 1 and the number of arguments of the function", ext))
  in
  if ty_res.toptions land Settings.tyopt_CHOOSABLE == 0 then
    raise (Error("Special equivalence "^equiv_name^": one must be able to choose randomly a bitstring from the type "^ty_res.tname^" (result of "^f.f_name^")", ext_f));
  if f_type == PRP && not (Proba.is_large ty_res) then
    raise (Error("Special equivalence "^equiv_name^": the domain "^ty_res.tname^" of this PRP must be large enough, so that collisions between a random element of the domain and an independent value can be eliminated (because we model a PRF and apply the PRF/PRP switching lemma)", ext_f));
  let (ty_key, ty_args) = nth_rest key_pos ty_all_args in
  let key_pos_string =
    match key_pos with
    | 0 -> "first"
    | 1 -> "second"
    | n -> (string_of_int (n+1))^"-th"
  in
  if ty_key.toptions land Settings.tyopt_CHOOSABLE == 0 then
    raise (Error("Special equivalence "^equiv_name^": one must be able to choose randomly a bitstring from the key type "^ty_key.tname^" ("^key_pos_string^" argument of "^f.f_name^")", ext_f));
  begin
    if f_type == PRP then
      match ty_args with
      | [ ty_arg ] when ty_arg == ty_res -> ()
      | _ ->
	  raise (Error("Special equivalence "^equiv_name^": the function "^f.f_name^" must have two arguments, the "^key_pos_string^" argument is a key, and its other argument must have the same type as its result (domain of the permutation)", ext_f))
  end;
  let proba_fun, r_args_at_equiv =
    match r_args_at_equiv, f_type with
    | _, ROM ->
	(fun _ _ -> Zero),  r_args_at_equiv
    | (SpecialArgId (proba_f, ext), _)::rest, (PRF | PRP) ->
	begin
	  try
	    match Stringmap.StringMap.find proba_f (!Stringmap.env) with
	    | EProba p ->
		(fun all_calls all_maxlength ->
		  let proba_f = Proba(p, AttTime :: all_calls :: all_maxlength) in
		  if f_type == PRF then
		    proba_f
		  else
		    Add(proba_f, Mul(all_calls, Mul(Sub(all_calls, Cst 1.0), Proba.pcoll2rand ty_res)))
		    ), rest
	    | _ ->
		raise (Error("Special equivalence "^equiv_name^": "^proba_f^" must be a probability", ext))
	  with Not_found ->
	    raise (Error("Special equivalence "^equiv_name^": "^proba_f^" not declared; it must be a probability", ext))
	end
    | (_, ext)::rest, _ ->
	raise (Error(expected_args(), ext))	  
    | _ ->
	raise (Error(expected_args(), gen_ext))
  in
  let get_id_prefix (s, ext) =
    fst (Terms.get_id_n s)
  in
  let ids, r_args_at_equiv =
    match r_args_at_equiv with
    | (SpecialArgTuple [ SpecialArgId id_k, _; SpecialArgId id_r, _; SpecialArgId id_x, _; SpecialArgId id_y, _; SpecialArgId id_z, _; SpecialArgId id_u, _ ], _) :: rest when f_type != PRP ->
	(id_k, get_id_prefix id_r, get_id_prefix id_x, get_id_prefix id_y, get_id_prefix id_z, get_id_prefix id_u), rest
    | (SpecialArgTuple [ SpecialArgId id_k, _; SpecialArgId id_r, _; SpecialArgId id_x, _; SpecialArgId id_u, _ ], _) :: rest when f_type == PRP ->
	(id_k, get_id_prefix id_r, get_id_prefix id_x, "y", "z", get_id_prefix id_u), rest (* y, z are not used for PRP, since only collisions IndepNew are allowed *)
    | [ ] ->
	((Terms.fresh_id "hk", Parsing_helper.dummy_ext), "r", "x", "y", "z", "u"), []
    | (_,ext)::rest ->
	raise (Error(expected_args(), ext))
  in
  let collisions_from_equiv = 
    match r_args_at_equiv with
    | [ collisions ] ->
	collisions
    | [ ] ->
	(SpecialArgTuple [], Parsing_helper.dummy_ext)
    | _::(_,ext)::_ -> (* Too many arguments *)
	raise (Error(expected_args(), ext))
  in
  let is_collisions = function
    | SpecialArgTuple _,_ -> true
    | _ -> false
  in
  let collisions, collision_matrix =
    if is_partial then
      match call with
      | Ptree.AutoCall | ManualCall([],_) ->
	  collisions_from_equiv, None
      | ManualCall( [ arg1 ], _) ->
	  if is_collisions arg1 then
	    arg1, None
	  else
	    collisions_from_equiv, Some arg1
      | ManualCall( [ arg1; arg2 ], _) ->
	  if is_collisions arg1 then
	    arg1, Some arg2
	  else
	    arg2, Some arg1
      | _ ->
	  raise (Error("Special equivalence "^equiv_name^" accepts at most two special arguments at the crypto command, which must be collision left-hand-sides, represented by a tuple of strings, and a collision matrix represented by a string \"<suffix1>, ..., <suffixn> may collide with previous <suffix1'>, ..., <suffixn'>; ...\" or \"no collisions\"", gen_ext))
    else
      match call with
      | Ptree.AutoCall | ManualCall([],_) ->
	  collisions_from_equiv, None
      | ManualCall( [ arg1 ], _) ->
	    arg1, None
      | _ ->
	  raise (Error("Special equivalence "^equiv_name^" accepts at most one special arguments at the crypto command, which must be collision left-hand-sides, represented by a tuple of strings", gen_ext))
  in
  let checked_collisions =
    match collisions with
    | SpecialArgTuple [SpecialArgString ("large", ext2),_], _ ->
	if not (Proba.is_large ty_res) then
	  raise (Error("Special equivalence "^equiv_name^": collision argument (\"large\") is allowed only for types large enough, so that collisions between a random element of the type and an independent value can be eliminated", ext2));
	let indep_new_coll = 
	  let b = Terms.create_binder "X" ty_res [] in
	  let restr = Terms.create_binder "Y" ty_res []  in
	  let t1 = Terms.make_equal (Terms.term_from_binder b) (Terms.term_from_binder restr) in
	  let t2 = Terms.make_false() in
	  let proba = Proba.pcoll1rand ty_res in
	  "Oeq", IndepNew([b],restr,t1,[SetProba proba],t2)
	in
	if f_type == PRP then
	  [indep_new_coll]
	else
	  let new_new_dep_coll =
	    let restr1 = Terms.create_binder "X" ty_res [] in
	    let restr2 = Terms.create_binder "Y" ty_res []  in
	    let t1 = Terms.make_equal (Terms.term_from_binder restr1) (Terms.term_from_binder restr2) in
	    let t2_indep = Terms.make_false() in
	    let t2_same = Terms.make_true() in
	    "Ocoll", NewNewDep(restr1, restr2, [], t1, [SetProba(Proba.pcoll2rand ty_res)], t2_indep, [], t2_same)
	  in
	  [indep_new_coll; new_new_dep_coll]
    | SpecialArgTuple l, _ ->
	let checked_coll = 
	  List.map (function
	    | SpecialArgString coll_id,_ ->
		if f_type == PRP then
		  parse_and_check_bij_coll ty_res coll_id
		else
		  parse_and_check_fun_coll ty_res coll_id
	    | _,ext ->
		raise (Error("Special equivalence "^equiv_name^": the collision argument must be a tuple of strings", ext))
		  ) l
	in
        (* Check that collision names do not contain _,
           are different from "O" and pairwise distinct *)
	let seen_names = ref [] in
	List.map (fun ((name,ext), coll) ->
	  if String.contains name '_' then
	    raise (Error("Special equivalence "^equiv_name^": collision name "^name^" should not contain _", ext));
	  if name = "O" then
	    raise (Error("Special equivalence "^equiv_name^": collision names must not be O", ext));
	  if List.mem name (!seen_names) then
	    raise (Error("Special equivalence "^equiv_name^": collision names must be pairwise distinct; "^name^" is repeated", ext));
	  seen_names := name :: (!seen_names);
	  (name, coll)) checked_coll
    | _,ext ->
	raise (Error("Special equivalence "^equiv_name^": the collision argument must be a tuple of strings", ext))
  in
  let oracles =
    if is_partial then
      let needed_oracles =
	match call with
	| Ptree.AutoCall ->
	    raise (Error("Special equivalence "^equiv_name^": a partial equivalence cannot be applied automatically, you must declare it [manual]", gen_ext))
	| ManualCall(_,(PRepeat _ | PVarList _)) -> []
	| ManualCall(_,PDetailed l) ->
	    List.concat (List.map (function
	      | Ptree.PVarMapping _ -> []
	      | PTermMapping(l,_) -> List.map snd l
		    ) l)
      in
      let leave_oracles = 
	("O_leave", Basic Leave) :: (List.map (function
	  | (name, ((IndepNew _) as coll)) -> (name^"_leave", Coll(coll, Leave))
	  | (name, coll) -> (name, Coll(coll, Normal))
		) checked_collisions)
      in
      let change_oracles = 
	List.fold_left (fun accu (oracle_name, ext) ->
	  if List.exists (fun (name, _) -> name = oracle_name) accu ||
	     List.exists (fun (name, _) -> name = oracle_name) leave_oracles
	  then
	    accu
	  else
	    if StringPlus.starts_with oracle_name "O_leave" then
	      (oracle_name, Basic Leave) :: accu
	    else if StringPlus.starts_with oracle_name "O_" then
	      begin
		(* check that oracle_name contains characters after name_ *)
		if String.length oracle_name = 2 then
		  raise (Error("Special equivalence "^equiv_name^": oracle name "^oracle_name^" should contain a non-empty suffix after _", ext));
		(oracle_name, Basic Normal) :: accu
	      end
	    else
	      try 
		let (name, coll) =
		  List.find (function
		    | (name, IndepNew _) -> StringPlus.starts_with oracle_name (name^"_")
		    | _ -> false
		      ) checked_collisions
		in
	        (* check that oracle_name contains characters after name_ *)
		if String.length oracle_name = String.length name + 1 then
		  raise (Error("Special equivalence "^equiv_name^": oracle name "^oracle_name^" should contain a non-empty suffix after _", ext));
		if StringPlus.starts_with oracle_name (name^"_leave") then
		  (oracle_name, Coll(coll, Leave)) :: accu
		else
		  (oracle_name, Coll(coll, Normal)) :: accu
	      with Not_found ->
		let msg = Buffer.create 200 in
		Buffer.add_string msg "Special equivalence ";
		Buffer.add_string msg equiv_name;
		Buffer.add_string msg ": oracle name ";
		Buffer.add_string msg oracle_name;
		Buffer.add_string msg " not found. It should start with O_ or with the name of a collision \"<name>: forall ...; new x:T; M\" followed by _";
		if f_type != PRP then
		  Buffer.add_string msg ", or be exactly the name of the collision for other collisions";
		Buffer.add_string msg ". The allowed oracles are then: O_*";
		List.iter (fun (name, coll) ->
		  Buffer.add_string msg ", ";
		  Buffer.add_string msg name;
		  match coll with
		  | IndepNew _ -> Buffer.add_string msg "_*"
		  | _ -> ()
			) checked_collisions;
		Buffer.add_string msg " where * stands for any non-empty identifier.";
		raise (Error(Buffer.contents msg, ext))
		  ) [] needed_oracles
      in
      (* put [leave_oracles] first, so that they are used by default *)
      leave_oracles @ change_oracles
    else
      ("O", Basic Normal) :: (List.map (fun (name, coll) -> (name, Coll(coll, Normal))) checked_collisions)
  in
  let checked_collision_matrix =
    match collision_matrix with
    | None -> None
    | Some (SpecialArgString id,_) ->
	let matrix = Syntax.parse_from_string Parser.collision_matrix ~lex:Lexer.collision_matrix id in
	let check_suffix (suffix, ext) =
	  if not (List.exists (fun (o_name,_) -> suffix = get_name_suffix o_name) oracles) then
	    raise (Error("In the collision matrix, the oracles must be designated by their suffix. "^suffix^" is not the suffix of an oracle name." , ext));
	  suffix
	in
	Some (List.map (fun (l1,l2) ->
	  (List.map check_suffix l1, List.map check_suffix l2)
	    ) matrix)
    | Some(_,ext) ->
	raise (Error("Special equivalence "^equiv_name^": the collision matrix argument must be a string", ext))
  in
  (* Restore the old variable state. *)
  Terms.set_var_num_state var_num_state;
  make_random_fun_equiv f key_pos ids proba_fun oracles checked_collision_matrix

(* Generate the equivalence for ICM and SPRP *)

type arg_t =
  | Key
  | Msg
  | LocalKey

type dir_t =
  | Enc
  | Dec

type random_bij_oracle_t =
  | BijBasic
  | BijColl of (binder list * binder * term * setf list * term)

(* Oracle names consist of 3 parts: 
   <coll name>_<enc/dec>_<suffix>
   or just 
   <coll_name>_<enc/dec>
   where <coll_name> must not contain _.
   In the second case, the suffix is empty.
   *)
let get_name_suffix2 o_name =
  try 
    let i = String.index o_name '_' in
    let i' = String.index_from o_name (i+1) '_' in
    String.sub o_name (i'+1) (String.length o_name - i' - 1)
  with Not_found ->
    ""

let get_suffix2 (o_name, o_ty, idx, b_idx, param, msg, ctx, lk, args, lhs_result_term, lhs_result_time, rhs_result_opt) =
  get_name_suffix2 o_name
  
let get_suffix2_ o_name = 
  try 
    let i = String.index o_name '_' in
    let i' = String.index_from o_name (i+1) '_' in
    String.sub o_name i' (String.length o_name - i')
  with Not_found ->
    ""

let make_random_bij_equiv enc dec arg_order ((id_k, ext_k), id_lk, id_m, id_c, id_u) proba_fun (oracles : (string * (random_bij_oracle_t * dir_t)) list) collision_matrix =
  let var_num_state = Terms.get_var_num_state() in
  let (tyargs, tyres) = enc.f_type in
  let ty_l_assoc = List.combine arg_order tyargs in
  let tykey = List.assq Key ty_l_assoc in
  let tylkey =
    try
      Some (List.assq LocalKey ty_l_assoc)
    with Not_found ->
      None
  in
  let k =
    (* check that id_k is not already in the environment *)
    if Stringmap.StringMap.mem id_k (!Stringmap.env) then
      let k = Terms.create_binder id_k tykey [] in
      Parsing_helper.input_warning ("Special equivalence: the identifier "^id_k^" that you specified for the key is already used. Using "^(Display.binder_to_string k)^" instead.") ext_k;
      k
    else
      Terms.create_binder0 id_k tykey []
  in
  let call o_dir msg ctx lk =
    let f =
      match o_dir with
      | Enc -> enc
      | Dec -> dec
    in
    let args = List.map (fun v ->
      Terms.term_from_binder
	(match v with
	| Key -> k
	| LocalKey -> get_some lk
	| Msg -> 
	    match o_dir with
	    | Enc -> get_some msg
	    | Dec -> get_some ctx
		  )
	) arg_order
    in
    Terms.app f args
  in
  let oracles_with_args = List.map (fun (o_name, (o_ty, o_dir)) ->
    let id_param = Terms.fresh_id ("N_"^o_name) in
    let param =
      { pname = id_param;
	psize = Settings.psize_DEFAULT }
    in
    let t_param = Terms.type_for_param param in
    let idx = Terms.create_repl_index ("i_"^o_name) t_param in
    let b_idx = Terms.create_binder (id_u^"_"^o_name) t_param [] in
    let msg =
      match (o_ty, o_dir) with
      | (BijColl _, Dec) -> None
      | _ -> Some (Terms.create_binder (id_m^"_"^o_name) tyres [idx])
    in
    let ctx =
      match (o_ty, o_dir) with
      | (BijColl _, Enc) -> None
      | _ -> Some (Terms.create_binder (id_c^"_"^o_name) tyres [idx])
    in
    let lk =
      match tylkey with
      | None -> None
      | Some ty -> Some (Terms.create_binder (id_lk^"_"^o_name) ty [idx])
    in
    let arg_lk =
      match lk with
      | None -> []
      | Some arg_lk -> [arg_lk]
    in
    let arg_msg_lk =
      (match o_dir with
      | Enc -> get_some msg
      | Dec -> get_some ctx) :: arg_lk
    in
    let args, lhs_result_term, rhs_result_opt = 
      match o_ty with
      | BijBasic ->
	  [ arg_msg_lk ], call o_dir msg ctx lk, None
      | BijColl (forall, restr, t1, proba, t2) ->
	  let forall_args = List.map (fun b -> Terms.create_binder (b.sname^"_"^o_name) b.btype [idx]) forall in
	  let lhs_result_term, rhs_result_term =
	    Terms.auto_cleanup (fun () ->
	      List.iter2 (fun b b' ->
		Terms.link b (TLink (Terms.term_from_binder b'))) forall forall_args;
	      Terms.link restr (TLink (call o_dir msg ctx lk));
	      Terms.copy_term Terms.Links_Vars t1,
	      Terms.copy_term Terms.Links_Vars t2)
	  in
	  [ arg_msg_lk; forall_args ], lhs_result_term, Some rhs_result_term
    in
    let lhs_result_time = Computeruntime.compute_runtime_for_term Terms.lhs_game_nodisplay lhs_result_term in
    (o_name, (o_ty, o_dir), idx, b_idx, param, msg, ctx, lk, args, lhs_result_term, lhs_result_time, rhs_result_opt)
      ) oracles
  in
  let ev_coll = Terms.fresh_id "ev_coll" in
  let ev_coll_f = Terms.create_event ev_coll [] in
  (* Create the equivalence as a string, inside a buffer *)
  let b = Buffer.create 500 in
  let print = Buffer.add_string b in
  let display_oracle_call (o_name, o_ty, idx, b_idx, param, _,_,_,args, _, _, _) =
    print ("!"^param.pname^" "^o_name^"(");
    let first = ref true in
    List.iter (List.iter (fun b ->
      if !first then
	first := false
      else
	print ", ";
      Display.display_binder b; print ": "; print b.btype.tname)) args;
    print ") := "
  in
  let coll() =
    print "event_abort ";
    print ev_coll
  in
  let return t =
    print "return(";
    Display.display_term t;
    print ")"
  in    
  let may_collide suffix1 suffix2 =
    match collision_matrix with
    | Some collision_info_list ->
	List.exists (fun (l1, l2) ->
	  (List.mem suffix1 l1 && List.mem suffix2 l2)
	    ) collision_info_list
    | None -> 
	suffix1 = "default" ||
	suffix2 = "default" ||
	suffix1 = suffix2
  in
  let get_res o_dir (o_name', o_ty', idx', b_idx', param', msg', ctx', lk', args', lhs_result_term', lhs_result_time', rhs_result_opt') =
    match o_dir with
    | Enc -> get_some ctx'
    | Dec -> get_some msg'
  in
  let get_arg o_dir (o_name', o_ty', idx', b_idx', param', msg', ctx', lk', args', lhs_result_term', lhs_result_time', rhs_result_opt') =
    match o_dir with
    | Enc -> get_some msg'
    | Dec -> get_some ctx'
  in
  (* Makes a [find] on all oracles in [oracles_with_args] of type [desired_ty].
     [f_args] is the list of arguments of the function [f] in the current oracle
     [oracle] is the current oracle
     [prev_res_fun oracle'] is the result to return when the arguments [args] of
     [f] in the current oracle are equal to the arguments of [f] in a previous call to [oracle'] *)
  let make_find o_dir f_args oracle prev_res_fun =
    let first = ref true in
    List.iter (fun ((o_name', (o_ty', o_dir'), idx', b_idx', param', msg', ctx', lk', args', lhs_result_term', lhs_result_time', rhs_result_opt') as oracle') ->
      if o_ty' = BijBasic then
	begin
	  if !first then
	    begin
	      first := false;
	      print "find[unique] " 
	    end
	  else
	    print "orfind ";
	  Display.display_binder b_idx';
	  print " <= ";
	  print param'.pname;
	  print " suchthat defined(";
	  let arg_lk' =  
	    match lk' with
	    | None -> []
	    | Some lk -> [lk]
	  in
	  let arg' = (get_arg o_dir oracle') :: arg_lk' in
	  let res' = get_res o_dir oracle' in
	  Display.display_list (fun b' ->
	    Display.display_binder b';
	    print "[";
	    Display.display_binder b_idx';
	    print "]"
	      ) (res' :: arg');
	  print ")";
	  List.iter2 (fun b b' ->
	    print " && ";
	    Display.display_binder b;
	    print " = ";
	    Display.display_binder b';
	    print "[";
	    Display.display_binder b_idx';
	    print "]"
	      ) f_args arg';
	  print " then ";
	  if may_collide (get_suffix2 oracle) (get_suffix2 oracle') then
	    return (prev_res_fun o_dir oracle')
	  else
	    coll();
	  print "\n";
	end
	  ) oracles_with_args;
    if not (!first) then
      print "else\n"
  in
  let prev_res o_dir ((o_name', o_ty', idx', b_idx', param', msg', ctx', lk', args', lhs_result_term', lhs_result_time', rhs_result_opt') as oracle')  =
    let res = get_res o_dir oracle' in
    Terms.build_term_type tyres (Var(res, [Terms.term_from_binder b_idx']))
  in
  let get_time_lhs_except_one_oracle oracle' =
    Polynom.p_sum (List.map (fun ((o_name, _, idx, b_idx, param, msg, ctx, lk, args, lhs_result_term, lhs_result_time, rhs_result_opt) as oracle) ->
      let nrep =
	if oracle == oracle' then
	  Sub(Count param, Cst 1.0)
	else
	  Count param
      in
      Polynom.p_mul(nrep, lhs_result_time)
	) oracles_with_args)
  in
  Display.fun_out print (fun () ->
    print "equiv\n";
    Display.display_binder k;
    print " <-R ";
    print tykey.tname;
    print "; (\n";
    let first_oracle = ref true in
    List.iter (fun ((o_name, (o_ty, o_dir), idx, b_idx, param, msg, ctx, lk, args, lhs_result_term, lhs_result_time, rhs_result_opt) as oracle) ->
      if !first_oracle then
	first_oracle := false
      else
	print " | \n";
      display_oracle_call oracle;
      return lhs_result_term
	) oracles_with_args;
    print ")\n<=(";
    (* Probability: count the number of calls and maximum length *)
    let enc_calls = ref [] in
    let dec_calls = ref [] in
    let max_length_msg = ref Polynom.empty_minmax_accu in
    let max_length_ctx = ref Polynom.empty_minmax_accu in
    let proba_coll = ref [] in
    let add_max accu v =
      Polynom.add_max accu (Maxlength(Terms.lhs_game_nodisplay, Terms.term_from_binder (get_some v)))
    in
    List.iter (fun ((o_name, (o_ty, o_dir), idx, b_idx, param, msg, ctx, lk, args, lhs_result_term, lhs_result_time, rhs_result_opt) as oracle) ->
      begin
	match o_dir with
	| Enc -> 
	    enc_calls := (Count param) :: (!enc_calls);
	    add_max max_length_msg msg
	| Dec ->
	    dec_calls := (Count param) :: (!dec_calls);
	    add_max max_length_ctx ctx
      end;
      begin
	match o_ty with
	| BijBasic -> ()
	| BijColl(forall, restr, _, proba, _) -> 
	    let (f_args, forall_args) = get_list2 args in
	    let get_time() = get_time_lhs_except_one_oracle oracle in
	    let proba' = 
	      Terms.auto_cleanup (fun () ->
		List.iter2 (fun b b' ->
		  Terms.link b (TLink (Terms.term_from_binder b'))) forall forall_args;
		Terms.link restr (TLink (call o_dir msg ctx lk));
		instan_time get_time proba)
	    in
	    proba_coll := Polynom.p_mul (Count param, proba')
	       :: (!proba_coll)
      end
		    ) oracles_with_args;
    let max_length_msg = Polynom.p_max (!max_length_msg) in
    let max_length_ctx = Polynom.p_max (!max_length_ctx) in
    let enc_calls = Polynom.p_sum (!enc_calls) in
    let dec_calls = Polynom.p_sum (!dec_calls) in
    let proba_coll = Polynom.p_sum (!proba_coll) in
    let total_proba = Polynom.p_add (proba_fun enc_calls dec_calls max_length_msg max_length_ctx, proba_coll) in
    Display.display_proba 0 total_proba;
    print ")=>\n";
    let first_oracle = ref true in
    List.iter (fun ((o_name, (o_ty, o_dir), idx, b_idx, param, msg, ctx, lk, args, lhs_result_term, lhs_result_time, rhs_result_opt) as oracle) ->
      if !first_oracle then
	first_oracle := false
      else
	print " | \n";
      display_oracle_call oracle;
      begin
	match o_ty with
	| BijBasic ->
	    let args = get_list1 args in
	    make_find o_dir args oracle prev_res;
	    let res = get_res o_dir oracle in
	    Display.display_binder res;
	    print " <-R ";
	    print tyres.tname;
	    print "; return(";
	    Display.display_binder res;
	    print ")"
	| BijColl(forall, restr, t1, proba, t2) ->
	    let (f_args, forall_args) = get_list2 args in
	    let prev_res_fun o_dir' oracle' = 
	      Terms.auto_cleanup (fun () ->
		List.iter2 (fun b b' ->
		  Terms.link b (TLink (Terms.term_from_binder b'))) forall forall_args;
		Terms.link restr (TLink (prev_res o_dir' oracle'));
		Terms.copy_term Links_Vars t1)
	    in
	    make_find o_dir f_args oracle prev_res_fun;
	    return (get_some rhs_result_opt)
      end
	) oracles_with_args;
    print ".\n"    
      );
  let equiv_string = Buffer.contents b in
  (* Debug 
     print_string equiv_string;*)
  if (!Settings.equiv_output) <> "" then
    begin
      let equiv_out = open_out_gen [ Open_wronly; Open_append; Open_creat ] 0o640 (!Settings.equiv_output) in
      output_string equiv_out equiv_string;
      output_string equiv_out "\n";
      close_out equiv_out
    end;
  (* Restore the old variable state. That allows check_eqstatement
     to reuse the same variable names. That function also saves and
     restores the variable state. *)
  Terms.set_var_num_state var_num_state;
  (* Parse the equivalence *)
  let pequiv = Syntax.parse_from_string (if !Settings.front_end = Settings.Channels then Parser.cequiv else Parser.oequiv) (equiv_string, dummy_ext) in
  (* Create the environment for checking the equivalence *)
  let env = Stringmap.env in
  let old_env = !env in
  List.iter (fun (o_name, (o_ty, o_dir), idx, b_idx, param, msg, ctx, lk, args, lhs_result_term, lhs_result_time, rhs_result_opt) ->
    env := StringMap.add param.pname (EParam param) (!env)
	 ) oracles_with_args;
  env := StringMap.add ev_coll (EEvent ev_coll_f) (!env);
  (* Check the equivalence *)
  let equiv = Syntax.check_eqstatement true pequiv in
  (* Restore the old environment *)
  env := old_env;
  equiv

(* Arguments:
   1/ argument order ("msg", "key", and for ICM, "local_key" in any order)
   2/ the encryption function 
   3/ the decryption function
   4/ the proba function (for SPRP)
   5/ identifiers: key (hk/k), local key (lk), message (m), ciphertext (c), find index (u)
   6/ collisions *)

type bij_type_t =
  | ICM
  | SPRP

let random_bij bij_type is_partial (equiv_name, gen_ext) args_at_equiv call =
  let var_num_state = Terms.get_var_num_state() in
  let expected_args() =
    "Special equivalence "^equiv_name^" expects to be called as "^equiv_name^"(arg_order, enc, dec, "^
    (if bij_type == SPRP then "" else "proba, ")^
    "(k, "^(if bij_type == ICM then "lk, " else "") ^"m, c, u), collisions)\nwhere
- arg_order is a tuple that contains \"msg\""^(if bij_type == SPRP then " and \"key\"" else ", \"key\", and \"local_key\"")^" in the order expected by the encryption function
- enc is the encryption function
- dec is the decryption function\n"^
    (if bij_type == ICM then "" else "- proba(t, N, N', l, l') is the probability that an adversary breaks the SPRP assumption
  in time t, with at most N queries to the encryption function of length at most l, N' queries to the decryption function of length at most l' (lengths are omitted when the type is bounded)\n")^
    "- k is the identifier of the key\n"^
(if bij_type == ICM then "- lk is the identifier of the local key\n" else "")^
"- m is the identifier for cleartext messages
- c is the identifier for ciphertexts
- u is the identifier used for find indices 
- collisions describes collisions and must be a tuple of strings
The arguments (k, "^(if bij_type == ICM then "lk, " else "") ^"m, c, u) and collisions may be omitted."
  in
  let arg_order, r_args_at_equiv =
    match args_at_equiv with
    | (SpecialArgTuple l, ext)::rest ->
	let count =
	  if bij_type == ICM then 
	    ["key", (Key, ref false); "msg", (Msg, ref false); "local_key", (LocalKey, ref false)]
	  else
	    ["key", (Key, ref false); "msg", (Msg, ref false)]
	in
	let arg_order = List.map (function
	  | SpecialArgString(s,ext), _ ->
	      begin
		try
		  let (v, seen) = List.assoc s count in
		  if !seen then
		    raise (Error("Special equivalence "^equiv_name^": arg_order contains \""^s^"\" several times", ext));
		  seen := true;
		  v
		with Not_found -> 
		  raise (Error("Special equivalence "^equiv_name^": arg_order should contain the strings \"msg\""^(if bij_type == SPRP then " and \"key\"" else ", \"key\", and \"local_key\""), ext))
	      end
	  | _, ext ->
	      raise (Error("Special equivalence "^equiv_name^": arg_order should be a tuple of strings", ext))
		) l
	in
	List.iter (fun (s, (v, seen)) ->
	  if not (!seen) then
	    raise (Error("Special equivalence "^equiv_name^": arg_order should contain the strings \"msg\""^(if bij_type == SPRP then " and \"key\"" else ", \"key\", and \"local_key\""), ext))
	      ) count;
	arg_order, rest
    | (_, ext)::rest ->
	raise (Error(expected_args(), ext))
    | _ ->
	raise (Error(expected_args(), gen_ext))
  in
  let enc, ext_enc, r_args_at_equiv =
    match r_args_at_equiv with
    | (SpecialArgId (f_id, ext), _)::rest ->
	begin
	  try
	    match Stringmap.StringMap.find f_id (!Stringmap.env) with
	    | EFunc f -> f, ext, rest
	    | _ -> raise (Error("Special equivalence "^equiv_name^": "^f_id^" must be a function", ext))
	  with Not_found ->
	    raise (Error("Special equivalence "^equiv_name^": "^f_id^" not declared; it must be a function", ext))
	end
    | (_, ext)::rest ->
	raise (Error(expected_args(), ext))
    | _ ->
	raise (Error(expected_args(), gen_ext))
  in
  let dec, ext_dec, r_args_at_equiv =
    match r_args_at_equiv with
    | (SpecialArgId (f_id, ext), _)::rest ->
	begin
	  try
	    match Stringmap.StringMap.find f_id (!Stringmap.env) with
	    | EFunc f -> f, ext, rest
	    | _ -> raise (Error("Special equivalence "^equiv_name^": "^f_id^" must be a function", ext))
	  with Not_found ->
	    raise (Error("Special equivalence "^equiv_name^": "^f_id^" not declared; it must be a function", ext))
	end
    | (_, ext)::rest ->
	raise (Error(expected_args(), ext))
    | _ ->
	raise (Error(expected_args(), gen_ext))
  in
  let (enc_ty_args, enc_ty_res) = enc.f_type in
  let (dec_ty_args, dec_ty_res) = dec.f_type in
  if enc_ty_res != dec_ty_res || not (Terms.equal_lists (==) enc_ty_args dec_ty_args) then
    raise (Error("Special equivalence "^equiv_name^": "^enc.f_name^" and "^dec.f_name^" should have the same type", ext_dec));
  if List.length enc_ty_args != List.length arg_order then
    raise (Error("Special equivalence "^equiv_name^": function "^enc.f_name^" should have "^(string_of_int (List.length arg_order))^" arguments", ext_enc));
  List.iter2 (fun v ty ->
    match v with
    | Key ->
	if ty.toptions land Settings.tyopt_CHOOSABLE == 0 then
	  raise (Error("Special equivalence "^equiv_name^": one must be able to choose randomly a bitstring from the key type "^ty.tname^" (key argument of "^enc.f_name^")", ext_enc))
    | Msg ->
	if ty != enc_ty_res then
	  raise (Error("Special equivalence "^equiv_name^": the message argument of "^enc.f_name^" should have the same type as its result", ext_enc))
    | LocalKey -> ()
	  ) arg_order enc_ty_args;
  if enc_ty_res.toptions land Settings.tyopt_CHOOSABLE == 0 then
    raise (Error("Special equivalence "^equiv_name^": one must be able to choose randomly a bitstring from the type "^enc_ty_res.tname^" (result of "^enc.f_name^")", ext_enc));
  if not (Proba.is_large enc_ty_res) then
    raise (Error("Special equivalence "^equiv_name^": the domain "^enc_ty_res.tname^" of this permutation must be large enough, so that collisions between a random element of the domain and an independent value can be eliminated", ext_enc));
  let proba_fun, r_args_at_equiv =
    match r_args_at_equiv, bij_type with
    | _, ICM ->
	(fun enc_calls dec_calls _ _ ->
	  let all_calls = Polynom.p_add(enc_calls, dec_calls) in
	  Mul(all_calls, Mul(Sub(all_calls, Cst 1.0), Proba.pcoll2rand enc_ty_res))),  r_args_at_equiv
    | (SpecialArgId (proba_f, ext), _)::rest, SPRP ->
	begin
	  try
	    match Stringmap.StringMap.find proba_f (!Stringmap.env) with
	    | EProba p ->
		(fun enc_calls dec_calls max_length_msg max_length_ctx ->
		  let proba_f =
		    if enc_ty_res.toptions land Settings.tyopt_BOUNDED != 0 then
		      Proba(p, [AttTime; enc_calls; dec_calls])
		    else
		      Proba(p, [AttTime; enc_calls; dec_calls; max_length_msg; max_length_ctx])
		  in
		  let all_calls = Polynom.p_add(enc_calls, dec_calls) in
		  Add(proba_f, Mul(all_calls, Mul(Sub(all_calls, Cst 1.0), Proba.pcoll2rand enc_ty_res)))
		    ), rest
	    | _ ->
		raise (Error("Special equivalence "^equiv_name^": "^proba_f^" must be a probability", ext))
	  with Not_found ->
	    raise (Error("Special equivalence "^equiv_name^": "^proba_f^" not declared; it must be a probability", ext))
	end
    | (_, ext)::rest, _ ->
	raise (Error(expected_args(), ext))	  
    | _ ->
	raise (Error(expected_args(), gen_ext))
  in
  let get_id_prefix (s, ext) =
    fst (Terms.get_id_n s)
  in
  let ids, r_args_at_equiv =
    match r_args_at_equiv, bij_type with
    | (SpecialArgTuple [ SpecialArgId id_k, _; SpecialArgId id_lk, _; SpecialArgId id_m, _; SpecialArgId id_c, _; SpecialArgId id_u, _ ], _) :: rest, ICM ->
	(id_k, get_id_prefix id_lk, get_id_prefix id_m, get_id_prefix id_c, get_id_prefix id_u), rest
    | (SpecialArgTuple [ SpecialArgId id_k, _; SpecialArgId id_m, _; SpecialArgId id_c, _; SpecialArgId id_u, _ ], _) :: rest, SPRP ->
	(id_k, "lk", get_id_prefix id_m, get_id_prefix id_c, get_id_prefix id_u), rest (* lk is not used by SPRP *)
    | [ ], _ ->
	((Terms.fresh_id "hk", Parsing_helper.dummy_ext), "lk", "m", "c", "u"), []
    | (_,ext)::rest, _ ->
	raise (Error(expected_args(), ext))
  in
  let collisions_from_equiv = 
    match r_args_at_equiv with
    | [ collisions ] ->
	collisions
    | [ ] ->
	(SpecialArgTuple [], Parsing_helper.dummy_ext)
    | _::(_,ext)::_ -> (* Too many arguments *)
	raise (Error(expected_args(), ext))
  in
  let is_collisions = function
    | SpecialArgTuple _,_ -> true
    | _ -> false
  in
  let collisions, collision_matrix =
    if is_partial then
      match call with
      | Ptree.AutoCall | ManualCall([],_) ->
	  collisions_from_equiv, None
      | ManualCall( [ arg1 ], _) ->
	  if is_collisions arg1 then
	    arg1, None
	  else
	    collisions_from_equiv, Some arg1
      | ManualCall( [ arg1; arg2 ], _) ->
	  if is_collisions arg1 then
	    arg1, Some arg2
	  else
	    arg2, Some arg1
      | _ ->
	  raise (Error("Special equivalence "^equiv_name^" accepts at most two special arguments at the crypto command, which must be collision left-hand-sides, represented by a tuple of strings, and a collision matrix represented by a string \"<suffix1>, ..., <suffixn> may collide with previous <suffix1'>, ..., <suffixn'>; ...\" or \"no collisions\"", gen_ext))
    else
      match call with
      | Ptree.AutoCall | ManualCall([],_) ->
	  collisions_from_equiv, None
      | ManualCall( [ arg1 ], _) ->
	    arg1, None
      | _ ->
	  raise (Error("Special equivalence "^equiv_name^" accepts at most one special arguments at the crypto command, which must be collision left-hand-sides, represented by a tuple of strings", gen_ext))
  in
  let checked_collisions =
    match collisions with
    | SpecialArgTuple [SpecialArgString ("large", ext2),_], _ ->
	if not (Proba.is_large enc_ty_res) then
	  raise (Error("Special equivalence "^equiv_name^": collision argument (\"large\") is allowed only for types large enough, so that collisions between a random element of the type and an independent value can be eliminated", ext2));
	let indep_new_coll = 
	  let b = Terms.create_binder "X" enc_ty_res [] in
	  let restr = Terms.create_binder "Y" enc_ty_res []  in
	  let t1 = Terms.make_equal (Terms.term_from_binder b) (Terms.term_from_binder restr) in
	  let t2 = Terms.make_false() in
	  let proba = Proba.pcoll1rand enc_ty_res in
	  "Oeq", IndepNew([b],restr,t1,[SetProba proba],t2)
	in
	[indep_new_coll]
    | SpecialArgTuple l, _ ->
	let checked_coll = 
	  List.map (function
	    | SpecialArgString coll_id,_ ->
		parse_and_check_bij_coll enc_ty_res coll_id
	    | _,ext ->
		raise (Error("Special equivalence "^equiv_name^": the collision argument must be a tuple of strings", ext))
		  ) l
	in
        (* Check that collision names do not contain _,
           are different from "O" and pairwise distinct *)
	let seen_names = ref [] in
	List.map (fun ((name,ext), coll) ->
	  if String.contains name '_' then
	    raise (Error("Special equivalence "^equiv_name^": collision name "^name^" should not contain _", ext));
	  if name = "O" then
	    raise (Error("Special equivalence "^equiv_name^": collision names must not be O", ext));
	  if List.mem name (!seen_names) then
	    raise (Error("Special equivalence "^equiv_name^": collision names must be pairwise distinct; "^name^" is repeated", ext));
	  seen_names := name :: (!seen_names);
	  (name, coll)) checked_coll
    | _,ext ->
	raise (Error("Special equivalence "^equiv_name^": the collision argument must be a tuple of strings", ext))
  in
  let oracles =
    let basic_oracles =
      ("O_enc", (BijBasic, Enc)) ::
      ("O_dec", (BijBasic, Dec)) ::
      (List.fold_left (fun accu (name, c) ->
	match c with
	| IndepNew coll ->
	    (name^"_enc", (BijColl(coll), Enc)) ::
	    (name^"_dec", (BijColl(coll), Dec)) :: accu
	| _ -> assert false
	      ) [] checked_collisions)
    in
    if is_partial then
      let needed_oracles =
	match call with
	| Ptree.AutoCall ->
	    raise (Error("Special equivalence "^equiv_name^": a partial equivalence cannot be applied automatically, you must declare it [manual]", gen_ext))
	| ManualCall(_,(PRepeat _ | PVarList _)) -> []
	| ManualCall(_,PDetailed l) ->
	    List.concat (List.map (function
	      | Ptree.PVarMapping _ -> []
	      | PTermMapping(l,_) -> List.map snd l
		    ) l)
      in
      let default_oracles =
	List.map (fun (name, oracle) -> (name^"_default", oracle)) basic_oracles
      in
      let ondemand_oracles = 
	List.fold_left (fun accu (oracle_name, ext) ->
	  if List.exists (fun (name, _) -> name = oracle_name) accu ||
	     List.exists (fun (name, _) -> name = oracle_name) default_oracles
	  then
	    accu
	  else
	    let oracle_error() =
	      let msg = Buffer.create 200 in
	      Buffer.add_string msg "Special equivalence ";
	      Buffer.add_string msg equiv_name;
	      Buffer.add_string msg ": oracle name ";
	      Buffer.add_string msg oracle_name;
	      Buffer.add_string msg " not found. It should start with O_enc_, O_dec_, or with the name of a collision \"<name>: forall ...; new x:T; M\" followed by _enc_ or _dec_";
	      Buffer.add_string msg ". The allowed oracles are then: O_enc_*, O_dec_*";
	      List.iter (fun (name, _) ->
		Buffer.add_string msg ", ";
		Buffer.add_string msg name;
		Buffer.add_string msg "_enc_*, ";
		Buffer.add_string msg name;
		Buffer.add_string msg "_dec_*"
		  ) checked_collisions;
	      Buffer.add_string msg " where * stands for any non-empty identifier.";
	      raise (Error(Buffer.contents msg, ext))
	    in
	    let (name, coll) =
	      if StringPlus.starts_with oracle_name "O_" then
		("O", BijBasic)
	      else
		try 
		  match
		    List.find (function
		      | (name, _) -> StringPlus.starts_with oracle_name (name^"_")
			    ) checked_collisions
		  with
		  | (name, IndepNew coll) -> (name, BijColl coll)
		  | _ -> assert false	
		with Not_found ->
		  oracle_error()
	    in
	    if StringPlus.starts_with oracle_name (name ^ "_enc_") then
	      begin
		(* check that oracle_name contains characters after name_enc_ *)
		if String.length oracle_name = String.length name + 5 then
		  raise (Error("Special equivalence "^equiv_name^": oracle name "^oracle_name^" should contain a non-empty suffix after _enc_", ext));
		(oracle_name, (coll, Enc)) :: accu
	      end
	    else if StringPlus.starts_with oracle_name (name ^ "_dec_") then
	      begin
		(* check that oracle_name contains characters after name_dec_ *)
		if String.length oracle_name = String.length name + 5 then
		  raise (Error("Special equivalence "^equiv_name^": oracle name "^oracle_name^" should contain a non-empty suffix after _dec_", ext));
		(oracle_name, (coll, Dec)) :: accu
	      end
	    else
	      oracle_error()
		  ) [] needed_oracles
      in
      (* put [default_oracles] first, so that they are used by default *)
      default_oracles @ ondemand_oracles
    else
      basic_oracles
  in
  let checked_collision_matrix =
    match collision_matrix with
    | None -> None
    | Some (SpecialArgString id,_) ->
	let matrix = Syntax.parse_from_string Parser.collision_matrix ~lex:Lexer.collision_matrix id in
	let check_suffix (suffix, ext) =
	  if not (List.exists (fun (o_name,_) -> suffix = get_name_suffix2 o_name) oracles) then
	    raise (Error("In the collision matrix, the oracles must be designated by their suffix. "^suffix^" is not the suffix of an oracle name." , ext));
	  suffix
	in
	Some (List.map (fun (l1,l2) ->
	  (List.map check_suffix l1, List.map check_suffix l2)
	    ) matrix)
    | Some(_,ext) ->
	raise (Error("Special equivalence "^equiv_name^": the collision matrix argument must be a string", ext))
  in
  (* Restore the old variable state. *)
  Terms.set_var_num_state var_num_state;
  make_random_bij_equiv enc dec arg_order ids proba_fun oracles checked_collision_matrix




    
let special_equiv_list =
  [ "rom", random_fun ROM false;
    "rom_partial", random_fun ROM true;
    "prf", random_fun PRF false;
    "prf_partial", random_fun PRF true;
    "prp", random_fun PRP false;
    "prp_partial", random_fun PRP true;
    "icm", random_bij ICM false;
    "icm_partial", random_bij ICM true;
    "sprp", random_bij SPRP false;
    "sprp_partial", random_bij SPRP true ]
    
    
let generate equiv call =
  match equiv, call with
  | { eq_special = None }, _ 
  | { eq_fixed_equiv = Some _ }, Ptree.AutoCall -> equiv
  | { eq_special = Some((s,ext) as special_name, args) }, _ ->
      let new_equiv =
	try
	  let gen_fun = List.assoc s special_equiv_list in
	  if (!Settings.equiv_output) <> "" then
	    begin
	      let equiv_out = open_out_gen [ Open_wronly; Open_append; Open_creat ] 0o640 (!Settings.equiv_output) in
	      let out_f = output_string equiv_out in
	      Display.fun_out out_f (fun () ->
		out_f "Generating ";
		Display.display_special_equiv equiv;
		Display.display_call call;
		out_f "\n\n");
	      close_out equiv_out
	    end;
	  gen_fun special_name args call
	with Not_found -> 
	  raise (Error ("Unknown special equivalence " ^ s, ext))
      in
      if call = Ptree.AutoCall then
	begin
	  equiv.eq_fixed_equiv <- new_equiv.eq_fixed_equiv;
	  equiv.eq_name_mapping <- new_equiv.eq_name_mapping;
	  equiv
	end
      else
	{ new_equiv with eq_name = equiv.eq_name }
	   

      
