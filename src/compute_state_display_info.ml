open Types

let rec has_assume = function
  | ProbaAssume -> true
  | proba -> Terms.exists_sub_probaf has_assume proba
	
let rec map_remove_empty f = function
  | [] -> []
  | a::l ->
      let l' = map_remove_empty f l in
      let a' = f a in
      if snd a' == [] then l' else a' :: l'

let rec map_opt f = function
  | [] -> []
  | a::l ->
      let l' = map_opt f l in
      match f a with
      | Some a' -> a' :: l'
      | None -> l' 
	
let is_non_unique (q,_) =
  match Terms.get_event_query q with
  | Some f -> f.f_cat == NonUniqueEvent
  | _ -> false
	
let is_secrecy = function
  | (QSecret _), _ -> true
  | _ -> false

let has_secrecy ql = List.exists is_secrecy ql

let double_if_needed ql p =
  if has_secrecy ql then Mul(Cst 2.0, p) else p

let equal_q_g (q,g) (q',g') =
  g == g' && Terms.equal_query q' q
	
let get_poptref g q =
  try 
    let (_,popt_ref) = List.find (fun (q_g',_) -> equal_q_g (q,g) q_g') g.current_queries in
    popt_ref
  with Not_found ->
    Display.display_query3 q;
    print_string (" not found in game "^ (Display.get_game_id g)^"\n");
    assert false
	
let rec is_full_poptref q poptref =
  match !poptref with
  | Inactive | ToProve -> false
  | Proved(ql,probaf, _) ->
      is_full_probaf q probaf

and is_full_probaf q probaf = not (is_not_full_probaf q probaf)

and is_not_full_probaf q = function
  | Advt(g,cur_q,ql) ->
      (List.exists (fun (q,popt_ref) -> not (is_full_poptref q popt_ref)) ql) ||
      (if cur_q then
	let popt_ref = get_poptref g q in
	not (is_full_poptref q popt_ref)
      else false)
  | probaf -> Terms.exists_sub_probaf (is_not_full_probaf q) probaf
      
and is_full_proba = function
  | SetProba _ (* Must not contain Advt *) -> true
  | SetEvent(f,g,pub_vars, poptref) ->
      let f_query = Terms.build_event_query f pub_vars in
      is_full_poptref f_query poptref

let get_proved poptref =
  match !poptref with
  | Inactive | ToProve -> Parsing_helper.internal_error "Probability not fully computed"
  | Proved(ql, proba_info, s) -> (ql, proba_info, s)

let contains_event_q f s =
  List.exists (Terms.is_event_query f) s.game.current_queries 

type maybe_other_side_ty =
  | ThisSide of query list * probaf * state
  | OtherSide of state
    
let get_proved_maybe_other_side other_side_info poptref =
  match !poptref with
  | Inactive | ToProve ->
      begin
	match other_side_info with
	| Some middle_s, Some s_other_side ->
	    (* We accept unproved queries event(..) => false when we prove
	       an equivalence between 2 games and we are not in the sequence
	       of games in which the query was proved *)
	    OtherSide(middle_s)
	| _ -> Parsing_helper.internal_error "Probability not fully computed"
      end
  | Proved(ql, proba, s) -> ThisSide(ql, proba, s)

let rec get_non_unique_q = function
  | [] -> []
  | q::l ->
      let l' = get_non_unique_q l in
      match Terms.get_nonunique_event_query q with
      | None -> l'
      | Some _ -> q::l'

(* A proof tree is a tree in which
   - nodes are games (field pt_game of pt_node below) 
   - edges correspond to game transformations. These edges are labelled with
       * pt_proba: pt_proba_info, the probability difference
       * pt_sons: pt_node list, the obtained sons (there can be several sons for a single edge in case of the guess_branch transformation)
       * pt_queries: (query_specif * game) list, the list of properties proved by going through the
         considered edge.
   We have a tree and not just a list of games, because events may be introduced by Shoup's lemma,
   and proved later to have negligible probability, so we may need to prove several properties
   at once. Moreover, these properties may be proved using different sequences of games, thus
   leading to a tree.
   The last edge (the one that proves a property) already deals with a single property.
   Other edges may be shared between the proofs of several properties. *)

type pt_proba_info =
  | Default of probaf * (funsymb * binder list(*public vars*)) list
      (* [Default(p,ql')] means [2 p + Adv_G0(Q0::ql')] for (one-session) secrecy
                                [p + Adv_G0(Q0::ql')] otherwise
	 [p] must not use Advt  
	 [pt_sons] must be [proof tree for G0] *)
  | Case of query list * probaf
      (* [Case(ql, p)] means that the proof applies only to queries in [ql],
	 use another edge for other queries.
	 [p] is a probability formula that can contain Adv_Gi(Q0::ql')
	 [pt_sons] must be the list of proof trees for Gi.
	 [pt_queries] must contain a sublist of queries in [ql].
	 There can be several edges connecting the same father to the same
	 sons for disjoint [ql]. *)
  | OtherSide of query
      (* [OtherSide q] means that [q] has been proved on the other side of
	 an equivalence query *)
	
type pt_node =
    { pt_game : game;
      mutable pt_edges : pt_edge list }

and pt_edge =
    { pt_proba: pt_proba_info;
      pt_sons: pt_node list;
      mutable pt_queries: (query * game) list }

let equal_pt_proba_case p1 p2 =
  match (p1,p2) with
  | Case(ql1,proba1), Case(ql2,proba2) ->
      (Terms.equal_lists_sets Terms.equal_query ql1 ql2) &&
      (Terms.equal_probaf proba1 proba2)
  | _ -> false
      
let query_from_q_g (q,_) =
  (q, ref ToProve(*not needed for display*))
    
let build_advt g ql = 
  Advt(g, false, List.map query_from_q_g ql)

(* For debugging *)

let display_short_query q =
  match Terms.get_event_query q with
  | Some f -> print_string f.f_name
  | None -> Display.display_query3 q

let display_q_g (q,g) =
  display_short_query q;
  print_string " in game "; print_string (Display.get_game_id g)
	
let rec display_proof_tree indent pt =
  print_string (indent ^ "Game " ^ (Display.get_game_id pt.pt_game) ^"\n");
  let display_edge indent_next edge =
    print_string (indent ^ "- Probability: ");
    begin
      match edge.pt_proba with
      | Default(p,ql') ->
	  Display.display_proba 0 p;
	  if ql' != [] then
	    begin
	      print_string " Additional events: ";
	      Display.display_list (fun (f,pub_vars) -> print_string f.f_name) ql'
	    end
      | Case(ql,p) ->
	  Display.display_proba 0 p;
	  print_string " valid for queries ";
	  Display.display_list display_short_query ql
      | OtherSide q ->
	  print_string "query "; display_short_query q; print_string " proved on the other side"
    end;
    print_newline();
    print_string (indent ^ "- Properties to prove: ");
    Display.display_list display_q_g edge.pt_queries;
    print_newline();
    match edge.pt_sons with
    | [] -> print_string (indent ^ "No son\n")
    | [s] ->
	print_string (indent ^ "Son:\n");
	display_proof_tree indent_next s
    | _ ->
	print_string (indent ^ "Sons:\n");
	List.iter (display_proof_tree (indent ^ "  ")) edge.pt_sons
  in
  match pt.pt_edges with
    [] -> print_string (indent ^ "No outgoing edge\n") 
  | [e] -> 
      print_string (indent ^ "Outgoing edge:\n"); 
      display_edge indent e
  | _ ->
      print_string (indent ^ "Outgoing edges:\n");
      List.iter (display_edge (indent ^ "  ")) pt.pt_edges

(* Build the proof tree *)

(* [other_side_info] is used only for indistinguishability proofs between
   2 games G0 and G1. ProVerif generates two sequences of games
   G0 ---> G2 and G1 ---> G2' in which G2 and G2' are trivially 
   indistinguishable (just by eliminating collisions).
   Indistinguishability between G2 and G2' is proved when we are either 
   working on G2 or on G2'; let's say G2. Then the proof continues from
   G2, showing that the probability of events remaining in G2 is bounded.
   In this case, [other_side_info] is a pair 
   [(Some middle_state, other_side_state_option)]
   where [middle_state] is the final state of the sequence we are currently
   looking at and [other_side_state_option] is 
   [None] when we are looking at the sequence in which the proof succeeded
   (G0 ---> G2; all queries are necessarily proved in this sequence)
   [Some other_side_middle_state] when we are looking at the other sequence
   (G1 ---> G2'; some queries may not be explicitly proved in this sequence:
   - events that appear in the middle game and whose probability is bounded
   in the sequence in which the proof succeeded;
   - events that do not appear in the middle game, but whose absence was
   not necessarily proved; we know that they are absent because the proof
   succeeded in the other sequence and the middle games are the same.)
   In this case, [other_side_middle_state] is the final state of the sequence 
   G0 ---> G2 in which the proof succeeded.

   In other cases, [other_side_info = (None, None)].
   *)

let rec collect_advt accu = function
  | Advt(g,cur_q,ql) -> (g,cur_q,ql)::accu
  | AttTime | Cst _ | Count _ | Zero | Card _ | TypeMaxlength _
  | EpsFind | EpsRand _ | PColl1Rand _ | PColl2Rand _ | OCount _
  | Maxlength _ | ProbaAssume -> accu
  | Time(_,_,p) | Power(p,_) -> collect_advt accu p
  | Proba(_,l) | Max(l) | Min(l) | ActTime(_,l) | Length(_,l) ->
      List.fold_left collect_advt accu l
  | Add(p1,p2) | Mul(p1,p2) | Sub(p1,p2) | Div(p1,p2) ->
      collect_advt (collect_advt accu p1) p2
  | OptimIf(cond,x,y) -> collect_advt (collect_advt (collect_advt_optim_cond accu cond) x) y
	
and collect_advt_optim_cond accu = function
  | OCProbaFun(_,l) -> List.fold_left collect_advt accu l
  | OCBoolFun(_,l) -> List.fold_left collect_advt_optim_cond accu l
    

	
let rec build_proof_tree other_side_info g0 queries =
  let pt_init = { pt_game = g0;
		  pt_edges = [] }
  in
  let proof_tree_table = ref [(g0, pt_init)] in
  let get_node_for_game g =
    try
      let pt_cur = List.assq g (!proof_tree_table) in
      (* print_string ("Found " ^ (string_of_int g.game_number)); *)
      (pt_cur, true)
    with Not_found ->
      let pt_cur = { pt_game = g;
		     pt_edges = [] }
      in
      (* print_string ("Added game " ^ (string_of_int s.game.game_number)); *)
      proof_tree_table := (g, pt_cur) :: (!proof_tree_table);
      (pt_cur, false)
  in
  (* We need to ignore "Proof" steps because they do not change the game at all
     (the game is physically the same), which causes bugs if we don't ignore 
     this step *)
  let rec father_ignore_proof s =
    match s.prev_state with
      None -> None
    | Some(Proof _,p,_,s') ->
	if p != [] then Parsing_helper.internal_error "Proof steps should have 0 probability";
	father_ignore_proof s'
    | x -> x
  in
  (* Add a new query [q] in the list of proved properties, in a part of the 
     proof tree that is already built *)
  let rec add_query ((q,g) as q_g) pt_cur s =
    if s.game == g then () else 
    match father_ignore_proof s with
      None -> ()
    | Some (i,p,_,s') ->
	let pt_father =
	  try
	    List.assq s'.game (!proof_tree_table)
	  with Not_found ->
	    print_string ("Game "^(Display.get_game_id s'.game)^" not found\n");
	    Parsing_helper.internal_error "This game should always be found"
	in
	let e =
	  try 
	    List.find (fun e ->
	      (List.memq pt_cur e.pt_sons) &&
	      (match e.pt_proba with
	      | Default _ -> true
	      | Case(ql,_) -> List.exists (Terms.equal_query q) ql
	      | OtherSide q0  -> Terms.equal_query q q0)
		) pt_father.pt_edges
	  with Not_found ->
	    print_string "edge for query "; display_short_query q; print_string " not found\n";
	    Parsing_helper.internal_error "This edge should always be found"
	in
	if not (List.exists (fun (q',_) -> Terms.equal_query q q') e.pt_queries) then
	  e.pt_queries <- q_g :: e.pt_queries;
	add_query q_g pt_father s'
  in
  (* Build the proof tree for state [s], proving property [q]. [edge_to_add] is 
     an edge to add to the proof corresponding to state [s]. *)
  let rec build_pt_rec edge_to_add ((q,g) as q_g) s =
    let (pt_cur,known_game) = get_node_for_game s.game in
    (* print_string " adding sons ";
      display_list (fun s -> print_int s.pt_game.game_number) edge_to_add.pt_sons;
       print_newline(); *)
    begin
      try
	let edge_old =
	  List.find (fun edge_old ->
	    match edge_old.pt_proba with
	    | Case(ql_old, _) -> List.exists (Terms.equal_query q) ql_old
	    | _ -> false) pt_cur.pt_edges
	in
	(* There is already an edge for query [q] *)
	assert (equal_pt_proba_case edge_old.pt_proba edge_to_add.pt_proba);
	assert (Terms.equal_lists_sets_q edge_old.pt_sons edge_to_add.pt_sons);
	edge_old.pt_queries <- Terms.union equal_q_g edge_to_add.pt_queries edge_old.pt_queries
      with Not_found -> 
	pt_cur.pt_edges <- edge_to_add :: pt_cur.pt_edges
    end;
    if known_game then
      add_query q_g pt_cur s
    else
      match father_ignore_proof s with
	None -> Parsing_helper.internal_error "Initial game should already have been entered in the proof tree"
      |	Some(i,p,_,s) ->
	  let probaf = 
	    Polynom.p_sum (map_opt (function
	      | SetProba p -> Some p
	      | SetEvent _ -> None) p)
	  in
	  let add_events =
	    map_opt (function
	      | SetProba _ -> None
	      | SetEvent(f,g, pub_vars, popt') -> Some (f,pub_vars)) p
	  in
	  let edge =
	    { pt_proba = Default(probaf, add_events);
	      pt_sons = [pt_cur];
	      pt_queries = [q_g] }
	  in
	  build_pt_rec edge q_g s;
	  List.iter (function 
	      SetProba _ -> ()
	    | SetEvent(f,g, pub_vars, popt') ->
		(* Build the query that tests for event f in game g *)
                let f_query = Terms.build_event_query f pub_vars in
		handle_query ((f_query, g),popt')
		  ) p
  and handle_query ((query,g) as q_g,popt') =
    (* Get the proof of the property "query,g" *)
    match get_proved_maybe_other_side other_side_info popt' with
    | OtherSide s' -> 
	let edge =
	  { pt_proba = OtherSide query;
	    pt_sons = [];
	    pt_queries = [q_g] }
	in
	build_pt_rec edge q_g s'
    | ThisSide(ql,probaf,s') -> 
	let sons =
	  let collected_advt = collect_advt [] probaf in
	  List.map (fun (g_new, cur_q, ql) ->
	    let (pt_cur,_) = get_node_for_game g_new in
	    if cur_q then
	      begin
		let popt_new = get_poptref g_new query in
		handle_query ((query,g_new),popt_new)
	      end;
	    List.iter (fun (q,popt) ->
	      handle_query ((q,g_new),popt)
		) ql;
	    pt_cur
	      ) collected_advt
	in
	let edge =
	  { pt_proba = Case(ql, probaf);
	    pt_sons = sons;
	    pt_queries = [q_g] }
	in
	build_pt_rec edge q_g s'
  in
  List.iter handle_query queries;
  pt_init

let rec evaluate_proba other_side_info bounds start_adv start_game above_proba ql pt =
  (* Sanity check: all elements of ql must occur in some edge in pt *)
  List.iter (fun q_g -> 
    if not ((List.exists (fun e -> 
      List.exists (equal_q_g q_g) e.pt_queries
	) pt.pt_edges) )
    then
      begin
	print_string "Game "; print_string (Display.get_game_id pt.pt_game);
	print_string ": missing ";
	display_q_g q_g;
	print_newline();
	Parsing_helper.internal_error "Missing property in evaluate_proba"
      end
	) ql;
  (* Sanity check: the ql_ref are disjoint *)
  let check_disjoint e1 e2 =
    if List.exists (fun qg1 -> List.exists (equal_q_g qg1) e2.pt_queries) e1.pt_queries then
      Parsing_helper.internal_error "ql_ref not disjoint"
  in
  let rec check_disjoint_l pt1 = function
      [] -> ()
    | (pt2::r) -> check_disjoint pt1 pt2; check_disjoint_l pt1 r
  in
  let rec check_disjoint_ll = function
      [] -> ()
    | (pt1::ptl) -> check_disjoint_l pt1 ptl; check_disjoint_ll ptl
  in
  check_disjoint_ll pt.pt_edges;
  (* Take into account tree branching (several sons): split [ql] according to what
     each son proves *)
  match pt.pt_edges with
    [ { pt_proba = Default(p,[]); pt_sons = [pt_son] } ] ->
	 evaluate_proba other_side_info bounds start_adv start_game (Polynom.p_add(double_if_needed ql p, above_proba)) ql pt_son
  | _ ->
      let above_proba = Polynom.simplify_proba above_proba in
      (* When [pt] has several sons, split the queries in [ql] according to which 
         son proves them.
	 If we do not prove secrecy, Adv_Q(C,||_i D_i) <= sum_i Adv_Q(C,D_i)
	 If we prove secrecy, Adv_Q(C, ||_i D_i) <= sum_i Adv_Q(C,D_i) + sum_{i \neq i_0} \Adv_Q(C, D_{NUi}) 
	 where D_{i_0} is the element that contains the secrecy query and D{NUi} contains only the queries for non-unique events in D_i. *)
      let ql_list =
	(* Compute the list of D_i with the associated [edge_info] in the proof tree. *)
	map_remove_empty (fun edge ->
	  edge, List.filter (fun q_g -> List.exists (equal_q_g q_g) ql) edge.pt_queries) pt.pt_edges
      in
      let ql_list_with_nu =
	(* Add the list of D_{NUi} with the associated [edge] in the proof tree. *)
	if has_secrecy ql then
	  List.concat (List.map (fun (edge, ql') ->
	      if has_secrecy ql' then
	        (* We do not compute D_{NUi} for i=i_0 *)
		[ (1.0, edge, ql') ]
	      else if List.for_all is_non_unique ql' then
		[ (2.0, edge, ql') ]
	      else
		let nu_ql' = List.filter is_non_unique ql' in
		if nu_ql' = [] then
		  [ (1.0, edge, ql') ]
		else
		  [ (1.0, edge, nu_ql'); (1.0, edge, ql') ]
		    ) ql_list)
	else
	  (* When we do not prove secrecy, there is nothing to add *)
	  List.map (fun (edge, ql') -> (1.0, edge, ql')) ql_list
      in
      begin
	match other_side_info with
	| (Some middle_s, _) when middle_s.game == pt.pt_game ->
	    (* We omit the bound when it concerns only the middle game;
	       it would yield an inaccurate display with potentially missing
	       event probabilities in the sequence of games in which the 
	       property is not proved, and in the other sequence, events 
	       proved but presented only for that sequence while we need 
	       them for both sequences *)
	    if middle_s.game != start_game then
	      bounds := (BLeq(start_adv, Polynom.p_add (above_proba, build_advt pt.pt_game ql))) :: (!bounds) 
	| _ ->
	    bounds := (BLeq(start_adv, Polynom.p_sum (above_proba :: List.map (fun (factor, edge, ql) -> Polynom.p_mul (Cst factor, build_advt pt.pt_game ql)) ql_list_with_nu))) :: (!bounds) 
      end;
      Polynom.p_sum (above_proba :: (List.map (fun (factor, edge, ql') ->
	let start_adv = build_advt pt.pt_game ql' in
	let proba = 
	  (* We consider the whole set of queries ql' at once, 
	     and avoid counting several times the same events. *)
	  match edge.pt_proba with
	  | Default(p, ql) ->
	      begin
		match edge.pt_sons with
		| [pt_son] ->
		    let ql'' = (List.map (fun (f,pub_vars) -> (Terms.build_event_query f pub_vars, pt_son.pt_game)) ql) @ ql' in
		    let p = Polynom.simplify_proba (double_if_needed ql' p) in
		    if ql == [] then
	              (* No event introduced *)
		      evaluate_proba other_side_info bounds start_adv pt.pt_game p ql'' pt_son
		    else
		      begin
	                (* An event has been introduced, display its probability separately *)
			let adv' = build_advt pt_son.pt_game ql'' in
			bounds := (BLeq(start_adv, Polynom.p_add(p, adv'))) :: (!bounds); 
			Polynom.p_add (p, evaluate_proba other_side_info bounds adv' pt_son.pt_game Zero ql'' pt_son)
		      end
		| _ -> assert false
	      end
	  | Case(ql,p) ->
	      (* Sanity check: [ql'] included in [ql] *)
	      List.iter (fun (q',g) ->
		if not (List.exists (Terms.equal_query q') ql) then
		  Parsing_helper.internal_error "Query not in the right case in evaluate_proba"
		    ) ql';
	      (* Display bound *)
	      let rec map_proba_formula = function
		| Advt(g, cur_q, ql) ->
		    let updated_ql =
		      if cur_q then
			(List.map query_from_q_g ql') @ ql
		      else ql
		    in
		    Advt(g, false, updated_ql) 
		| proba -> Terms.map_sub_probaf map_proba_formula proba
	      in
	      let p_img = map_proba_formula p in
	      begin
		match other_side_info with
		| (Some middle_s, _)
		    when middle_s.game == pt.pt_game 
	            && List.exists (fun (q,_) -> Terms.get_event_query q == None) ql' ->
	            (* Do not display the proof of the initial equivalence query 
		       in the middle game (the middle game may contain events
		       and in this case, the probability of these events 
		       must be taken into account in the final result, which
		       would not be done here) *)
		      ()
		| _ -> 
		    bounds := (BLeq(start_adv, p_img)) :: (!bounds)	      
	      end;

	      (* Compute the actual proba *)
	      let rec evaluate_proba_formula = function
		| Advt(g, cur_q, ql) as adv ->
		    assert (cur_q == false);
		    let pt_son = List.find (fun pt -> pt.pt_game == g) edge.pt_sons in
		    let ql_g = List.map (fun (q,_) -> (q,g)) ql in
		    evaluate_proba other_side_info bounds adv g Zero ql_g pt_son
		| proba -> Terms.map_sub_probaf evaluate_proba_formula proba
	      in
	      evaluate_proba_formula p_img
	  | OtherSide q -> 
	      (* Sanity check: [ql'] included in [q] *)
	      List.iter (fun (q',_) ->
		if not (Terms.equal_query q' q) then
		  Parsing_helper.internal_error "Query not in the right case in evaluate_proba (other side)"
		    ) ql';
	      (* Compute the proba *)
	      Zero
	in
	Polynom.p_mul (Cst factor, proba)
	  ) ql_list_with_nu))

and compute_proba_internal other_side_info bounds g queries =
  let pt = build_proof_tree other_side_info g queries in
  (* display_proof_tree "" pt; *)
  let start_queries = List.map fst queries in
  evaluate_proba other_side_info bounds (build_advt g start_queries) g Zero start_queries pt 
    
let compute_proba (((q0,g),poptref) as full_q) =
  let g_non_unique_q = get_non_unique_q g.current_queries in
  let bounds = ref [] in
  let fullp = 
    match q0 with
    | QEquivalence(state,pub_vars,_) ->
	let (_,p,s) = get_proved poptref in
	bounds := (BSameGame(s.game, state.game, p)) :: (!bounds);
	let g' = Display.get_initial_game state in
	let g'_non_unique_q = get_non_unique_q g'.current_queries in
	let q1 = QEquivalenceFinal(s.game, pub_vars) in
	let q2 = QEquivalenceFinal(state.game, pub_vars) in
	Polynom.p_add(compute_proba_internal (Some s, None) bounds g
			(((q1,g), ref (Proved([q1],Zero,s)))::g_non_unique_q),
		      Polynom.p_add (p, compute_proba_internal (Some state, Some s) bounds g'
				       (((q2,g'), ref(Proved([q2],Zero,state)))::g'_non_unique_q)))
    | AbsentQuery ->
	let (_,p,s) = get_proved poptref in
	let q0 = QEquivalenceFinal(s.game, []) in
	compute_proba_internal (None, None) bounds g (((q0,g),ref (Proved([q0],p,s)))::g_non_unique_q)
    | _ -> 
	compute_proba_internal (None, None) bounds g (full_q::g_non_unique_q) 
  in
  (List.rev (!bounds)), fullp

let get_initial_queries s =
  (Display.get_initial_game s).current_queries

let rec reachable s s' =
  (s == s') ||
  (match s'.prev_state with
    None -> false
  | Some (_,_,_,s'') -> reachable s s'')
    
let rec get_all_states_from_sequence accu s =
  match s.prev_state with
    None -> accu
  | Some(_, proba, _, s') ->
      get_all_states_from_sequence (get_all_states_from_proba accu proba) s'

and add_sequence accu s' =
  if List.exists (reachable s') accu then accu else
  get_all_states_from_sequence (s' :: accu) s'
	
and get_all_states_from_proba accu = function
    [] -> accu
  | (SetProba _)::r -> get_all_states_from_proba accu r
  | (SetEvent(f,g,pub_vars,poptref)) :: r  ->
      let accu' = get_all_states_from_proba accu r in
      let f_query = Terms.build_event_query f pub_vars in
      add_sequence_poptref accu' f_query poptref

and add_sequence_poptref accu q poptref = 
  match !poptref with
  | ToProve | Inactive -> accu
  | Proved(ql,probaf,s') ->
      add_sequence_probaf (add_sequence accu s') q probaf

and add_sequence_probaf accu q probaf =
  let adv_list = collect_advt [] probaf in
  List.fold_left (fun accu (g,cur_q,ql) ->
    let accu' =
      List.fold_left (fun accu (q,poptref) ->
	add_sequence_poptref accu q poptref) accu ql
    in
    if cur_q then
      let popt_ref = get_poptref g q in
      add_sequence_poptref accu' q popt_ref
    else
      accu') accu adv_list
    
let rec get_all_states_from_queries = function
    [] -> []
  | ((q,g), poptref)::r ->
      let accu = get_all_states_from_queries r in
      let accu' =
	match q with
	| QEquivalence(s',_,_) ->
	    add_sequence accu s'
	| _ -> accu
      in
      add_sequence_poptref accu' q poptref

let rec remove_dup seen_list r s =
  let seen_list' = List.filter (fun s' -> s' != s) seen_list in
  let r' = List.filter (fun s' -> s' != s) r in
  match s.prev_state with
    None -> (seen_list', r')
  | Some(_,_,_,s') ->
      remove_dup seen_list' r' s'

let rec remove_duplicate_states seen_list = function
    [] -> seen_list
  | (s::r) ->
      let (seen_list', r') = remove_dup seen_list r s in
      remove_duplicate_states (s::seen_list') r'

(* [update_full_proof state] updates [poptref]
   with the proof of query [q] when [q] is fully proved inside [state].
   Indeed, when we introduce events during the proof of a query [q],
   it is not enough to prove [q] on the final game, we must also 
   bound the probability that the events introduced during the proof happen. 
   [popt = Some(proba, state)] records the proof that the query [q] 
   is proved in the final game of [state], so that it holds up to 
   probability [proba] in the initial game. 
   However, [proba] may refer to the probabilities of events introduced
   during the proof. 
   [update_full_proof] sets [poptref] to [proba] when the probability
   of these events has also been bounded. *)

let rec update_full_proof state =
  match state.prev_state with
    None -> ()
  | Some(_, proba, _, s') ->
      if List.for_all is_full_proba proba then
	begin
	  (* Transfer proved queries from [state] to the previous state [s'] *)
	  List.iter (fun (q, poptref) ->
	    if !poptref = ToProve then
	      let poptref' = List.assq q state.game.current_queries in
	      match !poptref' with
	      | Proved(ql, proba_info, state') ->
		  if is_full_probaf (fst q) proba_info then
		    poptref := !poptref'
	      | _ -> ()
		  ) s'.game.current_queries;
	  update_full_proof s'
	end

(* [undo_absent_query state] undoes the proof of [AbsentQuery] *)
	  
let rec undo_absent_query state =
  List.iter (function 
      (AbsentQuery, g), poptref -> poptref := ToProve
    | _ -> ()) state.game.current_queries;
  match state.prev_state with
      None -> ()
    | Some(_, _, _, s') -> undo_absent_query s'
	    
let compute_state_display_info state = 
  (* AbsentQuery is proved in the current state, if present *)
  let s = 
    let eq_queries = List.filter (function (AbsentQuery, _),_ -> true | _ -> false) state.game.current_queries in
    if eq_queries == [] then
      state
    else
      begin
	List.iter (function 
	  | (AbsentQuery, g), poptref -> 
	      poptref := Proved([AbsentQuery], Zero, state)
	  | q -> ()) eq_queries;
	update_full_proof state;
	{ game = state.game;
	  prev_state = Some (Proof (List.map (fun (q, _) -> (q, Zero)) eq_queries), [], [], state);
	  tag = None }
      end
  in

  let initial_queries = get_initial_queries s in
  let states_needed_in_queries = get_all_states_from_queries initial_queries in
  let states_to_display = remove_duplicate_states [] (s::states_needed_in_queries) in

  (* List the unproved queries *)
  let unproved_queries = ref (List.map fst (List.filter (function (q, poptref) -> (!poptref) == ToProve || (!poptref) == Inactive) initial_queries)) in

  (* List the proved queries *)
  let proved_queries = ref [] in
  let (non_unique_initial_queries, other_initial_queries) =
    List.partition Terms.is_nonunique_event_query initial_queries
  in
  if List.for_all (fun ((q,_),poptref) -> is_full_poptref q poptref) non_unique_initial_queries then
    List.iter (fun (((q,_) as q_g,poptref) as full_q) ->
      if is_full_poptref q poptref then
	begin
          let (bounds, p'') = compute_proba full_q in
	  let assume = has_assume p'' in
	  if assume then
	    unproved_queries := q_g :: (!unproved_queries);
	  proved_queries := (q_g, bounds, assume, Polynom.simplify_proba p'') :: (!proved_queries)
	end
	  ) other_initial_queries;
  
  (* Undo the proof of AbsentQuery *)
  undo_absent_query state;

  { states_to_display = states_to_display;
    proved_queries = List.rev (!proved_queries);
    unproved_queries = !unproved_queries }
