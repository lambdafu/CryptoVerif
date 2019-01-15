(* Verify that the invariants are maintained by game transformations *)

open Types

let whole_game = ref Terms.empty_game

let expanded = ref true


(* Invariant 1: single definition; two definitions of the same variable
are in different branches of if/let/find.
Variables have as args_at_creation the current indices.
Used replication indices are defined above.
Returns the list of defined variables *)

let check_noninter d1 d2 =
  List.iter (fun b1 ->
    if List.memq b1 d2 then
      Parsing_helper.internal_error ("Same variable " ^ (Display.binder_to_string b1) ^ " defined twice\n")
	) d1

let ok_cur_array cur_array b =
  if not (Terms.equal_lists (==) b.args_at_creation cur_array) then 
    Parsing_helper.internal_error ("Bad args_at_creation for " ^ (Display.binder_to_string b))

let rec inv1t_deflist cur_array t =
  match t.t_desc with
  | Var(_,l) | FunApp(_,l) -> List.iter (inv1t_deflist cur_array) l
  | ReplIndex b -> 
     if not (List.memq b cur_array) then
       Parsing_helper.internal_error ("When I refer to a replication index (" ^
                                        (Display.repl_index_to_string b) ^
                                          "), it should be an element of cur_array")
  | ResE _ | FindE _ | TestE _ | LetE _ | EventAbortE _ | EventE _ | GetE _ | InsertE _ ->
     Parsing_helper.internal_error "If/let/new/find/event_abort/event/get/insert should not occur in deflist nor in channels of inputs"

                                  
let rec inv1t_fc expect_expanded in_find_cond cur_array t =
  match t.t_desc with
    Var(_,l) | FunApp(_,l) -> inv1t_fc_list true in_find_cond cur_array l
  | ReplIndex b -> 
      if not (List.memq b cur_array) then
	Parsing_helper.internal_error ("When I refer to a replication index (" ^
				       (Display.repl_index_to_string b) ^
				         "), it should be an element of cur_array");
      []
  | ResE _ | FindE _ | TestE _ | LetE _ | EventAbortE _ | EventE _ | GetE _ | InsertE _ ->
     if (!expanded) && expect_expanded then
       Parsing_helper.internal_error "If/let/new/find/event_abort/event/get/insert should have been expanded"
     else
       match t.t_desc with
       | Var _ | FunApp _ | ReplIndex _ -> assert false (* Handled above *)
       | TestE(t1,p1,p2) ->
          let def0 = inv1t_fc true in_find_cond cur_array t1 in
          let def1 = inv1t_fc false in_find_cond cur_array p1 in
          let def2 = inv1t_fc false in_find_cond cur_array p2 in
          let def12 = Terms.unionq def1 def2 in
          check_noninter def0 def12;
          def0 @ def12
       | ResE(b,p) ->
          if in_find_cond then
            Parsing_helper.internal_error "new should not appear in condition of find";
          let def = inv1t_fc false in_find_cond cur_array p in
          check_noninter def [b];
          ok_cur_array cur_array b;
          b :: def
       | EventAbortE f ->
          if in_find_cond then
            Parsing_helper.internal_error "event_abort should not appear in condition of find";
          []
       | EventE(t,p) ->
          if in_find_cond then
            Parsing_helper.internal_error "event should not appear in condition of find";
          let deft = inv1t_fc true in_find_cond cur_array t in
          let defp = inv1t_fc false in_find_cond cur_array p in
          check_noninter deft defp;
          deft @ defp
       | GetE _ | InsertE _ ->
          Parsing_helper.internal_error "event, event_abort, get, insert should not appear as term"
       | LetE(pat,t,p1,topt) ->
          let deft = inv1t_fc true in_find_cond cur_array t in
          let defpat = inv1pat in_find_cond cur_array pat in
          check_noninter deft defpat;
          let deftpat = deft @ defpat in
          let def1 = inv1t_fc false in_find_cond cur_array p1 in
          let def2 = Terms.vars_from_pat [] pat in
          List.iter (ok_cur_array cur_array) def2;
          check_noninter def1 def2;
          let def3 = 
	    match topt with
	      Some p2 -> inv1t_fc false in_find_cond cur_array p2
	    | None -> []
          in
          let deffin = Terms.unionq (def2 @ def1) def3 in
          check_noninter deftpat deffin;
          deftpat @ deffin
       | FindE(l0,p3,_) ->
          let def3 = inv1t_fc false in_find_cond cur_array p3 in
          let accu = ref def3 in
          List.iter (fun (bl,def_list,t,p) ->
	      let vars = List.map fst bl in
	      let repl_indices = List.map snd bl in
	      List.iter (ok_cur_array cur_array) vars;
	      let cur_array_cond = repl_indices @ cur_array in
	      List.iter (fun (b,l) -> List.iter (inv1t_deflist cur_array_cond) l) def_list;
	      let deft = inv1fc cur_array_cond t in
	      let defp = inv1t_fc false in_find_cond cur_array p in
	      check_noninter deft defp;
	      check_noninter deft vars;
	      check_noninter defp vars;
	      accu := Terms.unionq (vars @ deft @ defp) (!accu)
	    ) l0;
          !accu

and inv1t_fc_list expect_expanded in_find_cond cur_array = function
    [] -> []
  | a::l ->
     let defa = inv1t_fc expect_expanded in_find_cond cur_array a in
     let defl = inv1t_fc_list expect_expanded in_find_cond cur_array l in
     check_noninter defa defl;
     defa @ defl

and inv1pat in_find_cond cur_array = function
  | PatVar b -> []
  | PatTuple(_,l) -> inv1pat_list in_find_cond cur_array l
  | PatEqual t -> inv1t_fc true in_find_cond cur_array t

and inv1pat_list in_find_cond cur_array = function
  | [] -> []
  | a::l ->
     let defa = inv1pat in_find_cond cur_array a in
     let defl = inv1pat_list in_find_cond cur_array l in
     check_noninter defa defl;
     defa @ defl
     
                  
and inv1fc cur_array t =
  inv1t_fc false true cur_array t

and inv1t cur_array t =
  inv1t_fc true false cur_array t

let rec inv1 cur_array p = 
  match p.i_desc with
    Nil -> []
  | Par(p1,p2) ->
      let def1 = inv1 cur_array p1 in
      let def2 = inv1 cur_array p2 in
      check_noninter def1 def2;
      def1 @ def2
  | Repl(b,p) ->
      inv1 (b::cur_array) p 
  | Input((c,tl),pat, p) ->
      List.iter (inv1t_deflist cur_array) tl;
      let def1 = inv1o cur_array p in
      let defpat = inv1pat false cur_array pat in 
      let def2 = Terms.vars_from_pat [] pat in
      List.iter (ok_cur_array cur_array) def2;
      check_noninter def1 def2;
      let deffin = def1 @ def2 in
      check_noninter defpat deffin;
      defpat @ deffin

and inv1o cur_array p =
  match p.p_desc with
    Yield | EventAbort _ -> []
  | Restr(b,p) ->
      let def = inv1o cur_array p in
      check_noninter def [b];
      ok_cur_array cur_array b;
      b :: def
  | Test(t,p1,p2) ->
      let def0 = inv1t cur_array t in
      let def1 = inv1o cur_array p1 in
      let def2 = inv1o cur_array p2 in
      let def12 = Terms.unionq def1 def2 in
      check_noninter def0 def12;
      def0 @ def12
  | EventP(t,p) ->
      let deft = inv1t cur_array t in
      let defp = inv1o cur_array p in
      check_noninter deft defp;
      deft @ defp
  | Let(pat,t,p1,p2) ->
      let deft = inv1t cur_array t in
      let defpat = inv1pat false cur_array pat in
      check_noninter deft defpat;
      let deftpat = deft @ defpat in
      let def1 = inv1o cur_array p1 in
      let def2 = Terms.vars_from_pat [] pat in
      List.iter (ok_cur_array cur_array) def2;
      check_noninter def1 def2;
      let def3 = inv1o cur_array p2 in
      let deffin = Terms.unionq (def2 @ def1) def3 in
      check_noninter deftpat deffin;
      deftpat @ deffin
  | Find(l0,p3,_) ->
      let def3 = inv1o cur_array p3 in
      let accu = ref def3 in
      List.iter (fun (bl,def_list,t,p) ->
	let vars = List.map fst bl in
	let repl_indices = List.map snd bl in
	List.iter (ok_cur_array cur_array) vars;
	let cur_array_cond = repl_indices @ cur_array in
	List.iter (fun (b,l) -> List.iter (inv1t_deflist cur_array_cond) l) def_list;
	let deft = inv1fc cur_array_cond t in
	let defp = inv1o cur_array p in
	check_noninter deft defp;
	check_noninter deft vars;
	check_noninter defp vars;
	accu := Terms.unionq (vars @ deft @ defp) (!accu)
	) l0;
      !accu
  | Output((c,tl),t,p) ->
      let deftl = inv1t_fc_list true false cur_array tl in
      let deft = inv1t cur_array t in
      let defp = inv1 cur_array p in
      check_noninter deft defp;
      check_noninter deft deftl;
      check_noninter defp deftl;
      deftl @ deft @ defp
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"



(* Invariant 2: variables accessed are defined 
   Invariant 3: the process is well-typed
   plus
- if a variable access refers to an index at creation, all the 
rest of the indices must be the indices at creation
- terms never contain new/if/let/find except in conditions of find
(but not in defined)
- new does not occur in find conditions.
- variables defined in conditions of find have no array references and a single
definition
- restrictions are done only on "fixed" types
- in terms, else branch of let can be omitted only when the pattern is a variable.
*)

let no_array_ref in_find_cond b =
  if in_find_cond then
    begin
      if Terms.has_array_ref_q b (!whole_game).current_queries then
	Parsing_helper.internal_error ("Variable " ^ (Display.binder_to_string b) ^ " is defined in a condition of find; it should have no array reference.");
      match b.def with
	[] -> Parsing_helper.internal_error ("No definition for " ^ (Display.binder_to_string b))
      | [_] -> ()
      | _::_::_ -> Parsing_helper.internal_error ("Variable " ^ (Display.binder_to_string b) ^ " is defined in a condition of find; it should have a single definition.")
    end

let rec check_indices all_args args l =
  match args,l with
    [],[] -> ()
  | _::rargs, i::rl -> 
      begin
	match i.t_desc with
	  ReplIndex i' when List.memq i' all_args ->
	    List.iter2 (fun arg i -> 
	      match i.t_desc with
		ReplIndex i' when i' == arg -> ()
	      |	_ -> Parsing_helper.internal_error "If a variable access refers to a replication index, all the rest of the indices must be the indices at creation"
		    ) args l
	| _ -> 
	    check_indices all_args rargs rl
      end
  | _ -> Parsing_helper.internal_error "Variable indices have length different from args_at_creation"

let rec invt_fc in_find_cond defined_refs t =
  match t.t_desc with
  | Var(b,l) ->
      if not (Terms.mem_binderref (b,l) defined_refs) then
	begin
	  print_string "Variable access "; 
	  Display.display_var b l; 
	  print_newline();
	  Parsing_helper.internal_error "Variable accessed but definition not guaranteed"
	end;
      check_indices b.args_at_creation b.args_at_creation l;
      List.iter2 (fun arg p ->
	if arg.ri_type != p.t_type then
	  begin
	    print_string "Variable access "; 
	    Display.display_var b l; 
	    print_newline();
	    print_string ("Excepted index type: " ^ arg.ri_type.tname ^ "\n");
	    print_string ("Actual index type: " ^ p.t_type.tname ^ "\n");
	    Parsing_helper.internal_error "Type error"
	  end) b.args_at_creation l;
      if t.t_type != b.btype then
	begin
	  print_string "Variable access "; 
	  Display.display_var b l; 
	  print_newline();
	  print_string ("Variable type: " ^ b.btype.tname ^ "\n");
	  print_string ("Term type: " ^ t.t_type.tname ^ "\n");
	  Parsing_helper.internal_error "Type error"
	end;
      List.iter (invt_fc in_find_cond defined_refs) l
  | ReplIndex(b) ->
      if t.t_type != b.ri_type then
	begin
	  print_string "Replication index "; 
	  Display.display_term t; 
	  print_newline();
	  print_string ("Replication index type: " ^ b.ri_type.tname ^ "\n");
	  print_string ("Term type: " ^ t.t_type.tname ^ "\n");
	  Parsing_helper.internal_error "Type error"
	end
  | FunApp(f,l) ->
      List.iter2 (fun ty p ->
	if ty != p.t_type then
	  begin
	    print_string "Function application "; 
	    Display.display_term t; 
	    print_newline();
	    print_string ("Expected argument type: " ^ ty.tname ^ "\n");
	    print_string ("Actual argument type: " ^ p.t_type.tname ^ "\n");
	    Parsing_helper.internal_error "Type error"
	  end) (fst f.f_type) l;
      if t.t_type != snd f.f_type then
	begin
	  print_string "Function application "; 
	  Display.display_term t; 
	  print_newline();
	  print_string ("Function result type: " ^ (snd f.f_type).tname ^ "\n");
	  print_string ("Term type: " ^ t.t_type.tname ^ "\n");
	  Parsing_helper.internal_error "Type error"
	end;
      List.iter (invt_fc in_find_cond defined_refs) l
  | ResE(b,t) ->
      if in_find_cond then
	Parsing_helper.internal_error "new should not appear in a condition of find";
      let ty = b.btype in
      if ty.toptions land Settings.tyopt_CHOOSABLE == 0 then
	Parsing_helper.internal_error ("Cannot choose randomly a bitstring from " ^ ty.tname ^ "\n");
      no_array_ref in_find_cond b;
      invt_fc in_find_cond ((Terms.binderref_from_binder b)::defined_refs) t
  | EventAbortE _ ->
      if in_find_cond then
	Parsing_helper.internal_error "event_abort should not appear in a condition of find"
  | EventE(t,p) ->
      if in_find_cond then
	Parsing_helper.internal_error "event should not appear in a condition of find";	
      invt_fc in_find_cond defined_refs t;
      invt_fc in_find_cond defined_refs p
  | GetE _ | InsertE _  ->
      Parsing_helper.internal_error "get, insert should not appear as terms"
  | TestE(t1,t2,t3) ->
      invt_fc in_find_cond defined_refs t1;
      invt_fc in_find_cond defined_refs t2;
      invt_fc in_find_cond defined_refs t3;
      if t2.t_type != t3.t_type then 
	Parsing_helper.internal_error "Type error: branches of if with different types";
      if t1.t_type != Settings.t_bool then
	Parsing_helper.internal_error "Type error: condition should have type bool"
  | LetE(pat, t, t2, topt) ->
      let ty = invpat in_find_cond defined_refs pat in
      let bpat = Terms.vars_from_pat [] pat in
      List.iter (no_array_ref in_find_cond) bpat;
      let defs = List.map Terms.binderref_from_binder bpat in
      invt_fc in_find_cond defined_refs t;
      invt_fc in_find_cond (defs @ defined_refs) t2;
      if ty != t.t_type then
	Parsing_helper.internal_error "Type error: assigned pattern has different type than its value";
      begin
	match topt with
	  Some t3 -> 
	    invt_fc in_find_cond defined_refs t3;
	    if t3.t_type != t2.t_type then
	      Parsing_helper.internal_error "Type error: branches of let with different types"
	| None -> 
	    match pat with
	      PatVar _ -> ()
	    | _ -> Parsing_helper.internal_error "The else branch of let can be omitted only when the pattern is a variable"
      end
  | FindE(l0,t3,_) ->
      invt_fc in_find_cond defined_refs t3;
      List.iter (fun (bl, def_list, t, t2) ->
	List.iter (fun (b,b') ->
	  if b.btype != b'.ri_type then
	    Parsing_helper.internal_error "Type error: different types for variable and replication index in find") bl;
	if t3.t_type != t2.t_type then
	  Parsing_helper.internal_error "Type error: branches of find with different types";
	if t.t_type != Settings.t_bool then
	  Parsing_helper.internal_error "Type error: condition of find should have type bool";
	List.iter (no_array_ref in_find_cond) (List.map fst bl);
	let (defined_refs_t, defined_refs_t2) = Terms.defined_refs_find bl def_list defined_refs in
	(* Check def_list and t *)
	List.iter (fun br -> invt_fc in_find_cond defined_refs_t (Terms.term_from_binderref br)) def_list;
	invt_fc true defined_refs_t t;
	(* Check t2 *)
	invt_fc in_find_cond defined_refs_t2 t2
	) l0

and invpat in_find_cond defined_refs = function
    PatVar b -> b.btype
  | PatTuple(f,l) ->
      let tl = List.map (invpat in_find_cond defined_refs) l in
      List.iter2 (fun t t' ->
	if t != t' then
	  Parsing_helper.internal_error "Type error: function argument in pattern") (fst f.f_type) tl;
      snd f.f_type
  | PatEqual t ->
      invt_fc in_find_cond defined_refs t;
      t.t_type
      
let invfc defined_refs t =
  invt_fc true defined_refs t

let invt defined_refs t =
  invt_fc false defined_refs t
    
let rec inv defined_refs p =
  match p.i_desc with
    Nil -> ()
  | Par(p1,p2) -> 
      inv defined_refs p1;
      inv defined_refs p2
  | Repl(b,p) ->
      inv defined_refs p
  | Input((c,tl),pat,p) ->
      List.iter (invt defined_refs) tl;
      let _ = invpat false defined_refs pat in
      let bpat = Terms.vars_from_pat [] pat in
      let defs = List.map Terms.binderref_from_binder bpat in
      invo (defs @ defined_refs) p

and invo defined_refs p =
  match p.p_desc with
    Yield -> ()
  | EventAbort f -> 
      begin
	match f.f_type with
	  [t], t' when t == Settings.t_bitstring && t' == Settings.t_bool -> ()
	| _ ->
	    Parsing_helper.internal_error "Type error: badly typed event in event_abort"
      end
  | Restr(b,p) ->
      let ty = b.btype in
      if ty.toptions land Settings.tyopt_CHOOSABLE == 0 then
	Parsing_helper.internal_error ("Cannot choose randomly a bitstring from " ^ ty.tname ^ "\n");
      invo ((Terms.binderref_from_binder b)::defined_refs) p
  | Test(t,p1,p2) ->
      invt defined_refs t;
      invo defined_refs p1;
      invo defined_refs p2;
      if t.t_type != Settings.t_bool then
	Parsing_helper.internal_error "Type error: condition should have type bool"
  | Let(pat, t, p1, p2) ->
      let ty = invpat false defined_refs pat in
      let bpat = Terms.vars_from_pat [] pat in
      let defs = List.map Terms.binderref_from_binder bpat in
      invt defined_refs t;
      invo (defs @ defined_refs) p1;
      if ty != t.t_type then
	Parsing_helper.internal_error "Type error: assigned pattern has different type than its value";
      invo defined_refs p2
  | Find(l0,p2,_) ->
      invo defined_refs p2;
      List.iter (fun (bl, def_list, t, p1) ->
	List.iter (fun (b,b') ->
	  if b.btype != b'.ri_type then
	    Parsing_helper.internal_error "Type error: different types for variable and replication index in find") bl;
	if t.t_type != Settings.t_bool then
	  Parsing_helper.internal_error "Type error: condition of find should have type bool";
	let (defined_refs_t, defined_refs_p1) = Terms.defined_refs_find bl def_list defined_refs in
	(* Check def_list and t *)
	List.iter (fun br -> invt defined_refs_t (Terms.term_from_binderref br)) def_list;
	invfc defined_refs_t t;
	(* Check t2 *)
	invo defined_refs_p1 p1
	) l0
  | Output((c,tl),t,p) ->
      List.iter (invt defined_refs) tl;
      invt defined_refs t;
      inv defined_refs p
  | EventP(t,p) ->
      invt defined_refs t;
      invo defined_refs p
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

let global_inv g =
  let p = Terms.get_process g in
  whole_game := g;
  let _ = inv1 [] p in
  Terms.array_ref_process p;
  Terms.build_def_process None p;
  inv [] p;
  Terms.cleanup_array_ref();
  whole_game := Terms.empty_game;
  Terms.empty_def_process p
