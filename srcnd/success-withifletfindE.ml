open Types

let whole_game = ref Nil

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
      List.iter (fun (bl,def_list,otheruses_list,t1,t2) ->
	List.iter (fun (b,l) -> List.iter (check_usage_term seen_accu b) l) def_list;
	List.iter (fun (b,l) -> List.iter (check_usage_term seen_accu b) l) otheruses_list;
	check_usage_term seen_accu b t1;
	check_usage_term seen_accu b t2) l0;
      check_usage_term seen_accu b t3
  | LetE(PatVar b', { t_desc = Var(b'',l) }, t2, _) when b'' == b ->
      if not (List.memq b' (!seen_accu)) then
	begin
	  seen_accu := b' :: (!seen_accu);
	  check_usage_process seen_accu b' (!whole_game)
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
      
and check_usage_pat seen_accu b = function
    PatVar _ -> ()
  | PatTuple (f,l) -> List.iter (check_usage_pat seen_accu b) l
  | PatEqual t -> check_usage_term seen_accu b t

and check_usage_process seen_accu b = function
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

and check_usage_oprocess seen_accu b = function
    Yield -> ()
  | Restr(_,p) ->
      check_usage_oprocess seen_accu b p
  | Test(t,p1,p2) ->
      check_usage_term seen_accu b t;
      check_usage_oprocess seen_accu b p1;
      check_usage_oprocess seen_accu b p2
  | Find(l0,p2,_) ->
      List.iter (fun (bl,def_list, otheruses_list, t, p1) ->
	List.iter (fun (b,l) -> List.iter (check_usage_term seen_accu b) l) def_list;
	List.iter (fun (b,l) -> List.iter (check_usage_term seen_accu b) l) otheruses_list;
	check_usage_term seen_accu b t;
	check_usage_oprocess seen_accu b p1) l0;
      check_usage_oprocess seen_accu b p2
  | Let(PatVar b', { t_desc = Var(b'',l) }, p1, _) when b'' == b ->
      if not (List.memq b' (!seen_accu)) then
	begin
	  seen_accu := b' :: (!seen_accu);
	  check_usage_process seen_accu b' (!whole_game)
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

let has_assign b =
  List.exists (fun def ->
    match def.definition with
      DProcess (Let _) | DTerm ({ t_desc = LetE _}) -> true
    | _ -> false) b.def



let check_secrecy b =
  let ty = ref None in
  let r = 
    List.for_all (fun d -> 
      match d.definition with
	DProcess (Let(PatVar _,{ t_desc = Var(b',_) },_,_))
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
		check_usage_process (ref [b']) b' (!whole_game);
		true
	      with Not_found ->
		if List.length b'.def > 1 then
		  Transform.advise := Terms.add_eq (SArenaming b') (Terms.add_eq Simplify (!Transform.advise));
		false)
	    end
	  else
	    false
      |	DProcess (Restr _) ->
	  (match !ty with
	    None -> ty := Some b.btype; true
	  | Some ty' -> ty' == b.btype) && 
	  begin
	    try
	      check_usage_process (ref [b]) b (!whole_game);
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

let check_query simplify_internal_info gn = function
    QSecret1 b -> (check_secrecy b, Zero)
  | QSecret b -> 
      let r1 = check_secrecy b in
      if r1 then
	let (r2, proba) = Simplify.check_distinct b simplify_internal_info gn (!whole_game) in
	if r2 then
	  begin
	    print_string "Proved secrecy of ";
	    Display.display_binder b;
	    if proba != Zero then
	      begin
		print_string " Probability: ";
		Display.display_proba 0 proba
	      end;
	    print_newline();
	    (true, proba)
	  end
	else (false, Zero)
      else (false, Zero)
  | QEventQ(t1,t2) ->
      let (r, proba) = Simplify.check_corresp (t1,t2) simplify_internal_info gn (!whole_game) in
      if r then
	begin
	  print_string "Proved query ";
	  Display.display_query (QEventQ(t1,t2));
	  if proba != Zero then
	    begin
	      print_string " Probability: ";
	      Display.display_proba 0 proba
	    end;
	  print_newline();
	  (true, proba)
	end
      else (false, Zero)
	

let rec check_query_list simplify_internal_info gn = function
    [] -> ([],[])
  | (a::l) ->
      let (l',l'') = check_query_list simplify_internal_info gn l in
      let (res, proba) = check_query simplify_internal_info gn a in
      if res then ((a,proba)::l', l'') else (l', a::l'')

let is_success simplify_internal_info gn process = 
  whole_game := process;
  Terms.build_def_process None process;
  let (proved_queries, rem_queries) =
    check_query_list simplify_internal_info gn (!Transform.queries)
  in
  Transform.queries := rem_queries; (* Queries still to prove *)
  proved_queries, (rem_queries == [])


      

	  
