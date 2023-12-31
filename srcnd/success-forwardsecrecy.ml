open Types

let whole_game = ref { proc = Terms.nil_proc; game_number = -1 }


let rec check_usage_term seen_accu b t =
  match t.t_desc with
    Var(b',l) ->
      if b' == b then raise Not_found;
      List.iter (check_usage_term seen_accu b) l
  | FunApp(f,l) ->
      List.iter (check_usage_term seen_accu b) l
  | TestE(t1,t2,t3) ->
      check_usage_term seen_accu b t1;
      check_usage_term seen_accu b t2;
      check_usage_term seen_accu b t3
  | FindE(l0,t3,_) ->
      List.iter (fun (bl,def_list,t1,t2) ->
	List.iter (fun (_,l) -> List.iter (check_usage_term seen_accu b) l) def_list;
	check_usage_term seen_accu b t1;
	check_usage_term seen_accu b t2) l0;
      check_usage_term seen_accu b t3
  | LetE(PatVar b', { t_desc = Var(b'',l) }, t2, _) when b'' == b ->
      if not (List.memq b' (!seen_accu)) then
	begin
	  seen_accu := b' :: (!seen_accu);
	  try
	    check_usage_process seen_accu b' (!whole_game).proc
	  with Not_found ->
	    if List.length b'.def > 1 then
	      Transform.advise := Terms.add_eq (SArenaming b') (!Transform.advise);
	    raise Not_found
	end;
      List.iter (check_usage_term seen_accu b) l;
      check_usage_term seen_accu b t2
  | LetE(pat, t1, t2, topt) ->
      begin
	check_usage_pat seen_accu b pat;
	check_usage_term seen_accu b t1;
	check_usage_term seen_accu b t2;
	match topt with
	  None -> ()
	| Some t3 -> check_usage_term seen_accu b t3
      end
  | ResE(b,t) ->
      check_usage_term seen_accu b t
  | EventE _ ->
      Parsing_helper.internal_error "Event should have been expanded"
      
and check_usage_pat seen_accu b = function
    PatVar _ -> ()
  | PatTuple (f,l) -> List.iter (check_usage_pat seen_accu b) l
  | PatEqual t -> check_usage_term seen_accu b t

and check_usage_process seen_accu b p =
  match p.i_desc with
    Nil -> ()
  | Par(p1,p2) -> 
      check_usage_process seen_accu b p1;
      check_usage_process seen_accu b p2
  | Repl(_,p) ->
      check_usage_process seen_accu b p
  | Input((c, tl), pat, p) ->
      List.iter (check_usage_term seen_accu b) tl;
      check_usage_pat seen_accu b pat;
      check_usage_oprocess seen_accu b p

and check_usage_oprocess seen_accu b p =
  match p.p_desc with
    Yield -> ()
  | Restr(_,p) ->
      check_usage_oprocess seen_accu b p
  | Test(t,p1,p2) ->
      check_usage_term seen_accu b t;
      check_usage_oprocess seen_accu b p1;
      check_usage_oprocess seen_accu b p2
  | Find(l0,p2,_) ->
      List.iter (fun (bl,def_list, t, p1) ->
	List.iter (fun (_,l) -> List.iter (check_usage_term seen_accu b) l) def_list;
	check_usage_term seen_accu b t;
	check_usage_oprocess seen_accu b p1) l0;
      check_usage_oprocess seen_accu b p2
  | Let(PatVar b', { t_desc = Var(b'',l) }, p1, _) when b'' == b ->
      if not (List.memq b' (!seen_accu)) then
	begin
	  seen_accu := b' :: (!seen_accu);
	  try
	    check_usage_process seen_accu b' (!whole_game).proc
	  with Not_found ->
	    if List.length b'.def > 1 then
	      Transform.advise := Terms.add_eq (SArenaming b') (!Transform.advise);
	    raise Not_found
	end;
      List.iter (check_usage_term seen_accu b) l;
      check_usage_oprocess seen_accu b p1
  | Let(pat,t,p1,p2) ->
      check_usage_pat seen_accu b pat;
      check_usage_term seen_accu b t;
      check_usage_oprocess seen_accu b p1;
      check_usage_oprocess seen_accu b p2
  | Output((c, tl),t2,p) ->
      List.iter (check_usage_term seen_accu b) tl;
      check_usage_term seen_accu b t2;
      check_usage_process seen_accu b p
  | EventP(t,p) ->
      (* Events are ignored when checking secrecy
	 This assumes that LetE/FindE have been expanded, so that
	 they do not occur in t *)
      check_usage_oprocess seen_accu b p
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

let has_assign b =
  List.exists (fun def ->
    match def.definition with
      DProcess { p_desc = Let _ } | DTerm { t_desc = LetE _} -> true
    | _ -> false) b.def

let check_secrecy b =
  let ty = ref None in
  let r = 
    List.for_all (fun d -> 
      match d.definition with
	DProcess { p_desc = Let(PatVar _,{ t_desc = Var(b',_) },_,_) }
      |	DTerm { t_desc = LetE(PatVar _, { t_desc = Var(b',_) },_,_) } ->
	  if has_assign b' then
	    begin
	      Transform.advise := Terms.add_eq (RemoveAssign (OneBinder b')) (!Transform.advise);
	      false
	    end
	  else if Terms.is_restr b' then
	    begin
	      (match !ty with
		None -> ty := Some b'.btype; true
	      |	Some ty' -> ty' == b'.btype) && (
	      try
		check_usage_process (ref [b']) b' (!whole_game).proc;
		true
	      with Not_found ->
		if List.length b'.def > 1 then
		  Transform.advise := Terms.add_eq (SArenaming b') (!Transform.advise);
		false)
	    end
	  else
	    false
      |	DProcess { p_desc = Restr _ } ->
	  (match !ty with
	    None -> ty := Some b.btype; true
	  | Some ty' -> ty' == b.btype) && 
	  begin
	    try
	      check_usage_process (ref [b]) b (!whole_game).proc;
	      true
	    with Not_found ->
	      false
	  end
      |	_ ->
	  false) b.def
  in
  if r then
    begin
      print_string "Proved one-session secrecy of ";
      Display.display_binder b;
      print_newline()
    end;
  r


(* TO DO For secrecy of part of an array; useful for forward secrecy 
Commented out for now because it is work in progress.
 take into account probabilities 

(* [check_usage seen_accu b lidx facts X] checks that [X] cannot leak
   [ b[lidx] ] when [facts] holds. [seen_accu] contains the values of
   [b] already seen, to avoid loops. *)

let rec check_usage_term seen_accu b lidx facts t =
  match t.t_desc with
    Var(b',l) ->
      if b' == b then 
	begin
	  (* Dependency on b[l] 
	     rename replaces b'.args_at_creation with fresh indices
	     facts union (rename Facts.get_facts_at t.t_facts) union (lidx = rename l) implies a contradiction
	     TO DO *)
	  try
	    let lidx' = Facts.make_indexes b' in
	    let rename = Terms.subst (List.map Terms.binder_from_term b'.args_at_creation) lidx' in
	    let new_facts = List.map rename (Facts.get_facts_at t.t_facts) in
	    let eq_index = List.map2 Terms.make_equal lidx (List.map rename l) in 
	    let facts' = new_facts @ eq_index @ facts in
	    ignore (Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) facts');
	    print_string "At "; print_int t.t_occ; print_string ", bad usage of the secret\n";
	    List.iter (fun f -> Display.display_term [] f; print_newline()) facts';
	    raise Not_found
	  with Contradiction -> ()
	end;
      List.iter (check_usage_term seen_accu b lidx facts) l
  | FunApp(f,l) ->
      List.iter (check_usage_term seen_accu b lidx facts) l
  | TestE(t1,t2,t3) ->
      check_usage_term seen_accu b lidx facts t1;
      check_usage_term seen_accu b lidx facts t2;
      check_usage_term seen_accu b lidx facts t3
  | FindE(l0,t3,_) ->
      List.iter (fun (bl,def_list,t1,t2) ->
	List.iter (fun (_,l) -> List.iter (check_usage_term seen_accu b lidx facts) l) def_list;
	check_usage_term seen_accu b lidx facts t1;
	check_usage_term seen_accu b lidx facts t2) l0;
      check_usage_term seen_accu b lidx facts t3
  | LetE(PatVar b', ({ t_desc = Var(b'',l) } as t1), t2, _) when b'' == b ->
      if List.memq b' seen_accu then
	raise Not_found;
      begin
	  try
	    (* rename replaces b'.args_at_creation with fresh indices
	       facts' = facts union (rename Facts.get_facts_at t.t_facts) union (lidx = rename l) union (rename b'[b'.args_at_creation] = b''[l]) 
	       lidx' = rename b'.args_at_creation *)
	    let lidx' = Facts.make_indexes b' in
	    let rename = Terms.subst (List.map Terms.binder_from_term b'.args_at_creation) lidx' in
	    let new_facts = List.map rename (Facts.get_facts_at t.t_facts) in
	    let eq_index = List.map2 Terms.make_equal lidx (List.map rename l) in 
	    let fact1 = rename (Terms.make_equal (Terms.term_from_binder b') t1) in
	    let facts' = new_facts @ eq_index @ (fact1 :: facts) in
	    check_usage_process (b'::seen_accu) b' lidx' facts' (!whole_game).proc
	  with Not_found ->
	    if List.length b'.def > 1 then
	      Transform.advise := Terms.add_eq (SArenaming b') (!Transform.advise);
	    raise Not_found
	  | Contradiction -> 
	      (* current program point unreachable *)
	      ()
      end;
      List.iter (check_usage_term seen_accu b lidx facts) l;
      check_usage_term seen_accu b lidx facts t2
  | LetE(pat, t1, t2, topt) ->
      begin
	check_usage_pat seen_accu b lidx facts pat;
	check_usage_term seen_accu b lidx facts t1;
	check_usage_term seen_accu b lidx facts t2;
	match topt with
	  None -> ()
	| Some t3 -> check_usage_term seen_accu b lidx facts t3
      end
  | ResE(b,t) ->
      check_usage_term seen_accu b lidx facts t
  | EventE _ ->
      Parsing_helper.internal_error "Event should have been expanded"
      
and check_usage_pat seen_accu b lidx facts = function
    PatVar _ -> ()
  | PatTuple (f,l) -> List.iter (check_usage_pat seen_accu b lidx facts) l
  | PatEqual t -> check_usage_term seen_accu b lidx facts t

and check_usage_process seen_accu b lidx facts p =
  match p.i_desc with
    Nil -> ()
  | Par(p1,p2) -> 
      check_usage_process seen_accu b lidx facts p1;
      check_usage_process seen_accu b lidx facts p2
  | Repl(_,p) ->
      check_usage_process seen_accu b lidx facts p
  | Input((c, tl), pat, p) ->
      List.iter (check_usage_term seen_accu b lidx facts) tl;
      check_usage_pat seen_accu b lidx facts pat;
      check_usage_oprocess seen_accu b lidx facts p

and check_usage_oprocess seen_accu b lidx facts p =
  match p.p_desc with
    Yield -> ()
  | Restr(_,p) ->
      check_usage_oprocess seen_accu b lidx facts p
  | Test(t,p1,p2) ->
      check_usage_term seen_accu b lidx facts t;
      check_usage_oprocess seen_accu b lidx facts p1;
      check_usage_oprocess seen_accu b lidx facts p2
  | Find(l0,p2,_) ->
      List.iter (fun (bl,def_list, t, p1) ->
	List.iter (fun (_,l) -> List.iter (check_usage_term seen_accu b lidx facts) l) def_list;
	check_usage_term seen_accu b lidx facts t;
	check_usage_oprocess seen_accu b lidx facts p1) l0;
      check_usage_oprocess seen_accu b lidx facts p2
  | Let(PatVar b', ({ t_desc = Var(b'',l) } as t1), p1, _) when b'' == b ->
      if List.memq b' seen_accu then
	raise Not_found;
      begin
	  try
	    (* rename replaces b'.args_at_creation with fresh indices
	       facts' = facts union (rename Facts.get_facts_at p.p_facts) union (lidx = rename l) union (rename b'[b'.args_at_creation] = b''[l]) 
	       lidx' = rename b'.args_at_creation *)
	    let lidx' = Facts.make_indexes b' in
	    let rename = Terms.subst (List.map Terms.binder_from_term b'.args_at_creation) lidx' in
	    let new_facts = List.map rename (Facts.get_facts_at p.p_facts) in
	    let eq_index = List.map2 Terms.make_equal lidx (List.map rename l) in 
	    let fact1 = rename (Terms.make_equal (Terms.term_from_binder b') t1) in
	    let facts' = new_facts @ eq_index @ (fact1 :: facts) in
	    check_usage_process (b'::seen_accu) b' lidx' facts' (!whole_game).proc
	  with Not_found ->
	    if List.length b'.def > 1 then
	      Transform.advise := Terms.add_eq (SArenaming b') (!Transform.advise);
	    raise Not_found
	  | Contradiction -> 
	      (* Current program point unreachable *)
	      ()
      end;
      List.iter (check_usage_term seen_accu b lidx facts) l;
      check_usage_oprocess seen_accu b lidx facts p1
  | Let(pat,t,p1,p2) ->
      check_usage_pat seen_accu b lidx facts pat;
      check_usage_term seen_accu b lidx facts t;
      check_usage_oprocess seen_accu b lidx facts p1;
      check_usage_oprocess seen_accu b lidx facts p2
  | Output((c, tl),t2,p) ->
      List.iter (check_usage_term seen_accu b lidx facts) tl;
      check_usage_term seen_accu b lidx facts t2;
      check_usage_process seen_accu b lidx facts p
  | EventP(t,p) ->
      (* Events are ignored when checking secrecy
	 This assumes that LetE/FindE have been expanded, so that
	 they do not occur in t *)
      check_usage_oprocess seen_accu b lidx facts p
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

let has_assign b =
  List.exists (fun def ->
    match def.definition with
      DProcess { p_desc = Let _ } | DTerm { t_desc = LetE _} -> true
    | _ -> false) b.def



let check_secrecy b =
  let ty = ref None in
  let r = 
    List.for_all (fun d -> 
      match d.definition with
	DProcess { p_desc = Let(PatVar _,({ t_desc = Var(b',l) } as t1),_,_); p_facts = facts }
      |	DTerm { t_desc = LetE(PatVar _, ({ t_desc = Var(b',l) } as t1),_,_); t_facts = facts } ->
	  if has_assign b' then
	    begin
	      Transform.advise := Terms.add_eq (RemoveAssign (OneBinder b')) (!Transform.advise);
	      false
	    end
	  else if Terms.is_restr b' then
	    begin
	      (match !ty with
		None -> ty := Some b'.btype; true
	      |	Some ty' -> ty' == b'.btype) && (
	      try
		let lidx = Facts.make_indexes b in
		let rename = Terms.subst (List.map Terms.binder_from_term b.args_at_creation) lidx in
		let new_facts = List.map rename (Facts.get_facts_at facts) in
		let fact1 = rename (Terms.make_equal (Terms.term_from_binder b) t1) in
		let facts = fact1 :: new_facts in
		check_usage_process [b'] b' (List.map rename l) facts (!whole_game).proc;
		true
	      with Not_found ->
		if List.length b'.def > 1 then
		  Transform.advise := Terms.add_eq (SArenaming b') (!Transform.advise);
		false
	      |	Contradiction ->
		  (* Current program point unreachable *)
		  true)
	    end
	  else
	    false
      |	DProcess { p_desc = Restr _; p_facts = facts } ->
	  (match !ty with
	    None -> ty := Some b.btype; true
	  | Some ty' -> ty' == b.btype) && 
	  begin
	    try
	      let lidx = Facts.make_indexes b in
	      let rename = Terms.subst (List.map Terms.binder_from_term b.args_at_creation) lidx in
	      let facts = List.map rename (Facts.get_facts_at facts) in
	      check_usage_process [b] b lidx facts (!whole_game).proc;
	      true
	    with Not_found ->
	      false
	  end
      |	_ ->
	  false) b.def
  in
  if r then
    begin
      print_string "Proved one-session secrecy of ";
      Display.display_binder b;
      print_newline()
    end;
  r
*)

let check_query = function
    (QSecret1 b,_) -> (check_secrecy b, [])
  | (QSecret b,_) -> 
      let r1 = check_secrecy b in
      if r1 then
	let (r2, proba) = Facts.check_distinct b (!whole_game) in
	if r2 then
	  begin
	    print_string "Proved secrecy of ";
	    Display.display_binder b;
	    if proba != [] then
	      begin
		print_string " Probability: ";
		Display.display_set proba
	      end;
	    print_newline();
	    (true, proba)
	  end
	else (false, [])
      else (false, [])
  | (QEventQ(t1,t2),gn) ->
      let (r, proba) = Facts.check_corresp (t1,t2) (!whole_game) in
      if r then
	begin
	  print_string "Proved query ";
	  Display.display_query (QEventQ(t1,t2),gn);
	  if proba != [] then
	    begin
	      print_string " Probability: ";
	      Display.display_set proba
	    end;
	  print_newline();
	  (true, proba)
	end
      else (false, [])
  | (AbsentQuery,_) -> (false, [])	

let rec check_query_list = function
    [] -> ([],[])
  | (a::l) ->
      let (l',l'') = check_query_list l in
      let (res, proba) = check_query a in
      if res then ((a,proba)::l', l'') else (l', a::l'')

let is_success g = 
  whole_game := g;
  let vcounter = !Terms.vcounter in
  Terms.build_def_process None g.proc;
  let (proved_queries, rem_queries) = check_query_list (!Transform.queries) in
  Transform.queries := rem_queries; (* Queries still to prove *)
  Terms.vcounter := vcounter; (* Forget created variables *)
  proved_queries, (rem_queries == [])


      

	  
