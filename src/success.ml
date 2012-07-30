open Types

(* check_usage can return the following results:
- raise Not_found, when secrecy cannot be proved, even by applying
  advised transformations
- add transformations to "advise", when secrecy cannot be proved
  in the current game, but may be provable by applying the transformations
  in "advise"
- leave "advise" empty when secrecy is proved in the current game.
*)


let advise = ref []

let whole_game = ref { proc = Terms.nil_proc; game_number = -1 }

let rec check_usage_term seen_accu b t =
  match t.t_desc with
    Var(b',l) ->
      if b' == b then raise Not_found;
      List.iter (check_usage_term seen_accu b) l
  | ReplIndex _ -> ()
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
	      advise := Terms.add_eq (SArenaming b') (!advise)
	    else
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
    Yield | Abort -> ()
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
	      advise := Terms.add_eq (SArenaming b') (!advise)
	    else
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
  advise := [];
  try
    List.iter (fun d -> 
      match d.definition with
	DProcess { p_desc = Let(PatVar _,{ t_desc = Var(b',_) },_,_) }
      |	DTerm { t_desc = LetE(PatVar _, { t_desc = Var(b',_) },_,_) } ->
	  if has_assign b' then
	    advise := Terms.add_eq (RemoveAssign (OneBinder b')) (!advise)
	  else if Terms.is_restr b' then
	    begin
	      (match !ty with
		None -> ty := Some b'.btype
	      |	Some ty' -> if ty' != b'.btype then 
		  Parsing_helper.internal_error ("Variable " ^ (Display.binder_to_string b) ^ " has definitions of different types"));
	      try
		check_usage_process (ref [b']) b' (!whole_game).proc
	      with Not_found ->
		if List.length b'.def > 1 then
		  advise := Terms.add_eq (SArenaming b') (!advise)
		else
		  raise Not_found
	    end
	  else
	    raise Not_found
      |	DProcess { p_desc = Restr _ } ->
	  (match !ty with
	    None -> ty := Some b.btype
	  | Some ty' -> if ty' != b.btype then 
	      Parsing_helper.internal_error ("Variable " ^ (Display.binder_to_string b) ^ " has definitions of different types"));
	  check_usage_process (ref [b]) b (!whole_game).proc
      |	_ ->
	  raise Not_found) b.def;
    if (!advise) == [] then
      begin
	print_string "Proved one-session secrecy of ";
	Display.display_binder b;
	print_newline();
	true
      end
    else
      begin
	List.iter (fun i -> 
	  Transform.advise := Terms.add_eq i (!Transform.advise)) (!advise);
	advise := [];
	false
      end
  with Not_found -> 
    advise := [];
    false

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


      

	  
