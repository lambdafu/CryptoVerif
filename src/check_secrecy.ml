open Types

(* check_usage can return the following results:
- raise Not_found, when secrecy cannot be proved, even by applying
  advised transformations
- add transformations to "advise", when secrecy cannot be proved
  in the current game, but may be provable by applying the transformations
  in "advise"
- leave "advise" empty when secrecy is proved in the current game.
*)

(* [advise] stores advised transformations to try to make the proof
   of secrecy succeed. *)

let advise = ref []

(* [whole_game] contains the game on which we want to prove security properties *)

let whole_game = ref Terms.empty_game

(* [detected_leaks] and [current_restr] store information 
   useful for explaining why the proof of secrecy fails.

   [detected_leaks] stores all the detected reasons why the
   proof of secrecy fails. 

   [current_restr] stores the current restriction that defines the secret:
   typically, we want to prove the secrecy of a variable [b]. 
   [b] may itself be defined by a restriction, in which case [current_restr]
   will be set to [Some b]. 
   [b] may also be defined by assignment from [b'], where [b'] is defined 
   by a restriction. In this case, [!current_restr = Some b'].

   [public_vars] stores the list of public variables. *)

type leak_t =
  | Leak of binder * int list (* [Leak(b, occs)] means that variable [b] is 
				 leaked at the occurrences [occs] in the game *)
  | PublicVar of binder (* [PublicVar b] means that variable [b] is public *)

type group_leak_t =
    LeaksOf of binder * leak_t list
  | NotOnlyRestr of binder
  | NotRestrOrAssign

let detected_leaks = ref ([] : group_leak_t list)

let current_restr = ref None

let public_vars = ref []

(* [add_leak_for_current_restr l1] adds the leak [l1],
   which may be [Leak(b',occs)] or [PublicVar b'],
   where [b'] depends on the current restriction [current_restr = Some b]. 
   This leak is added inside the group [LeaksOf(b, ...)]
   in [detected_leaks]. If this group is not already present,
   it is created. *)

let add_leak_for_current_restr l1 =
  let rec add_leak_rec = function
      [] -> [l1]
    | (l2::rest) as l ->
	match l1, l2 with
	| Leak(b,n), Leak(b',n') when b == b' -> 
	    Leak(b, Terms.unionq n n') :: rest
	| PublicVar b, PublicVar b' when b == b' ->
	    l
	| _ -> 
	    l2 :: (add_leak_rec rest)
  in
  let current_restr = 
    match !current_restr with
      None -> Parsing_helper.internal_error "current_restr should be set"
    | Some b -> b
  in
  let rec add_leak_rec2 = function
      [] -> [LeaksOf(current_restr, [l1])]
    | l2::rest ->
	match l2 with
	  LeaksOf(b,l) when b == current_restr ->
	    (LeaksOf(b, add_leak_rec l))::rest
	| _ -> 
	    l2::add_leak_rec2 rest
  in
  detected_leaks := add_leak_rec2 (!detected_leaks)

(* [add_leak l1] adds the leak [l1] to [detected_leaks]
   if it is not already present. [l1] may be
   [NotOnlyRestr b] or [NotRestrOrAssign]. *)

let add_leak l1 =
  let rec add_leak_rec = function
      [] -> [l1]
    | (l2::rest) as l ->
	match l1,l2 with
	  NotRestrOrAssign, NotRestrOrAssign ->
	    l
	| NotOnlyRestr b, NotOnlyRestr b' ->
	    if b == b' then l else l2::(add_leak_rec rest)
	| _ ->
	    l2::(add_leak_rec rest)
  in
  detected_leaks := add_leak_rec (!detected_leaks)


(* [display_leaks b0] displays the explanation of the failure
   of the proof of one-session secrecy of [b0], as recorded
   in [detected_leaks]. *)

let rec display_list_sc f = function
    [] -> ()
  | [a] -> f a
  | (a::l) -> f a; print_string "; ";
      display_list_sc f l

let display_leaks_of b l =
  let display_leak = function
    | Leak(b',occs) ->
	print_string "at ";
	Display.display_list print_int occs;
	print_string (", bad usage(s) of " ^ (Display.binder_to_string b'));
	if b' != b then
	  print_string (", which may depend on " ^ (Display.binder_to_string b))
    | PublicVar b' ->
	print_string ((Display.binder_to_string b') ^ " is a public variable");
	if b' != b then
	  print_string (", which may depend on " ^ (Display.binder_to_string b))
  in
  display_list_sc display_leak l;
  print_string ".";
  print_newline()

let display_leaks b0 =
  print_string ("Proof of (one-session) secrecy of " ^ 
		(Display.binder_to_string b0) ^ " failed:\n");
  List.iter (function
      LeaksOf(b,l) -> 
	print_string "  ";
	if b != b0 then 
	  print_string ((Display.binder_to_string b0) ^ " is defined from " ^ 
			(Display.binder_to_string b) ^ "; ");
	display_leaks_of b l
    | NotOnlyRestr b' ->
	print_string ("  " ^ (Display.binder_to_string b0) ^ " is defined from " ^ 
		      (Display.binder_to_string b') ^
		        ", which is not defined only by restrictions.");
        print_newline()
    | NotRestrOrAssign ->
	print_string ("  " ^ (Display.binder_to_string b0) ^ 
		        " is not defined only by restrictions or assignments.");
        print_newline()
      ) (!detected_leaks)


(* We can prove secrecy of part of an array; this is useful for forward secrecy  *)

(* [add_facts_at (all_indices, simp_facts0, defined_refs0, pp_list) 
   cur_array new_facts pp] updates the quadruple 
   [(all_indices, simp_facts0, defined_refs0, pp_list)] where
   - [cur_array] contains the current replication indices
   - [pp] is the current program point
   - [new_facts] contains other facts that should also be added.
   It renames the current_replication indices of [cur_array] to 
   fresh indices [lidx'].
   Inside the quadruple, 
   - [all_indices] contains all indices seen so far. (It is extended with the
   fresh indices [lidx'].)
   - [simp_facts0] contains facts that are known to hold. (It is extended with
   facts from [fact_info] and from [new_facts], after renaming
   of replication indices, as well as from facts inferred by [Terms.both_pp_add_fact]
   from the list of visited program points.)
   - [defined_refs] contains variables that are known to be defined. (It is extended
   with the variables known to be defined from [fact_info], after renaming
   of replication indices.)
   - [pp_list] contains the program points that are known to have been
   visited with their corresponding indices. (It is extended with [(lidx', pp)].)
   [add_facts_at] returns [lidx'] as well as the updated quadruple.
*)

let rec find_and_remove idx eq_list =
  let rec aux seen_eq = function
    | [] -> None
    | ((i1,i2) as eq)::rest ->
	if Terms.is_repl_index idx i1 then
	  begin
	    eq_list := List.rev_append seen_eq rest;
	    Some i2
	  end
	else
	  aux (eq::seen_eq) rest
  in
  aux [] (!eq_list)
    
let add_facts_at known_facts cur_array new_eqs pp =
  let new_eqs = ref new_eqs in
  let new_indices = ref [] in
  (* Avoid creating a fresh replication index when its value is known by equalities *)
  let lidx' = List.map (fun idx ->
    match find_and_remove idx new_eqs with
    | Some i2 -> i2
    | None -> 
	let idx' = Terms.new_repl_index idx in
	new_indices := idx' :: (!new_indices);
	Terms.term_from_repl_index idx'
		       ) cur_array
  in
  let new_indices = !new_indices in
  let new_eqs = List.map (fun (i1, i2) -> (Terms.subst cur_array lidx' i1, i2)) (!new_eqs) in
  (* When an equality in [new_eqs] is i1 = i2 and i2 is a replication index, 
     rather instantiate [known_facts] with its value i1. *)
  let (subst, new_eqs) = List.partition (fun (i1,i2) ->
    match i2.t_desc with
    | ReplIndex _ -> true
    | _ -> false) new_eqs in
  let (all_indices0, pp_list0, simp_facts0, defined_refs0) =
    if subst = [] then known_facts else
    let subst_orig = List.map (fun (_, i2) -> Terms.repl_index_from_term i2) subst in
    let subst_target = List.map fst subst in
    let (all_indices0, pp_list0, simp_facts0, defined_refs0) = known_facts in
    (List.filter (fun ix -> not (List.memq ix subst_orig)) all_indices0,
     Terms.subst_pps subst_orig subst_target pp_list0,
     Terms.subst_simp_facts subst_orig subst_target simp_facts0,
     Terms.subst_def_list subst_orig subst_target defined_refs0)
  in
  (* Reusing indices as we do above makes the incompatibility between 
     program points more precise *)
  let new_facts1 = List.map (fun (i1, i2) -> Terms.make_equal i1 i2) new_eqs in
  let (new_facts2, pp_list1, defined_refs1) = Facts.get_facts_at_args pp_list0 defined_refs0 (pp, lidx') in
  let simp_facts1 = Terms.auto_cleanup (fun () -> 
    Facts.simplif_add_list Facts.no_dependency_anal simp_facts0 (new_facts1 @ new_facts2)) 
  in
  (lidx', (new_indices @ all_indices0, pp_list1, simp_facts1, defined_refs1))

(* [collect_bargs args_accu b t] collects in [args_accu] the arguments
   of the variables [b] inside the term [t]. 
   It raises [TooComplex] when it does not support the term [t]
   (let/find/new). *)

exception TooComplex

let rec collect_bargs args_accu b t =
  match t.t_desc with
    Var(b',l) -> 
      if b' == b then
	begin
	  if not (List.exists (Terms.equal_term_lists l) (!args_accu)) then
	    args_accu := l :: (!args_accu)
	end
      else
	List.iter (collect_bargs args_accu b) l
  | FunApp(_,l) ->
      List.iter (collect_bargs args_accu b) l
  | ReplIndex _ -> ()
  | TestE(t1,t2,t3) ->
      collect_bargs args_accu b t1;
      collect_bargs args_accu b t2;
      collect_bargs args_accu b t3
  | _ -> 
      raise TooComplex

(* [check_usage seen_accu b lidx facts X] checks that [X] cannot leak
   [ b[lidx] ] when [facts] holds. [seen_accu] contains the values of
   [b] already seen, to avoid loops. *)

type state =
    { cur_array : repl_index list;
      seen_accu : binder list;
      b : binder;
      lidx : term list;
      facts : repl_index list * program_points_args list * simp_facts * binderref list }
	
(* [used] is true when the result of the term [t] is really used.
   [used] is false for arguments of events. *)
let rec check_usage_term state used t =
  match t.t_desc with
    Var(b',l) ->
      if used && (b' == state.b) then 
	begin
	  (* Dependency on b[l] 
	     let 'rename' replace cur_array with fresh indices
	     facts union (rename Facts.get_facts_at t.t_facts) union (lidx = rename l) implies a contradiction *)
	  try
	    let eq_index = List.combine l state.lidx in 
	    let (lidx', (all_indices, _, simp_facts, defined_refs)) = add_facts_at state.facts state.cur_array eq_index (DTerm t) in
	    let facts2 = 
	      if !Settings.elsefind_facts_in_success then
		Facts_of_elsefind.get_facts_of_elsefind_facts (!whole_game) all_indices simp_facts defined_refs 
	      else
		[]
	    in
	    ignore (Terms.auto_cleanup (fun () -> Facts.simplif_add_list Facts.no_dependency_anal simp_facts facts2));
	    (* For debugging*)
	    add_leak_for_current_restr (Leak(state.b, [t.t_occ]));
	    (* print_string "Known facts:\n";
	    Display.display_facts simp_facts; 
	    print_string "Defined variables:\n";
	    Display.display_def_list_lines defined_refs;	    
	    print_string "Added using elsefind:\n";
	    List.iter (fun t -> Display.display_term t; print_newline()) facts2; *)
	    raise Not_found
	  with Contradiction -> ()
	end;
      List.iter (check_usage_term state used) l
  | ReplIndex _ -> ()	
  | FunApp(f,l) ->
      List.iter (check_usage_term state used) l
  | TestE(t1,t2,t3) ->
      check_usage_term state true t1;
      check_usage_term state used t2;
      check_usage_term state used t3
  | FindE(l0,t3,_) ->
      List.iter (fun (bl,def_list,t1,t2) ->
	let state' = { state with cur_array = (List.map snd bl) @ state.cur_array } in
	List.iter (fun (_,l) -> List.iter (check_usage_term state' true) l) def_list;
	check_usage_term state' true t1;
	check_usage_term state used t2) l0;
      check_usage_term state used t3
  | LetE(PatVar b', t1, t2, _) ->
      check_assign state b' t1 (DTerm t2);
      check_usage_term state used t2
  | LetE(pat, t1, t2, topt) ->
      begin
	check_usage_pat state pat;
	check_usage_term state true t1;
	check_usage_term state used t2;
	match topt with
	  None -> ()
	| Some t3 -> check_usage_term state used t3
      end
  | ResE(b,t) ->
      check_usage_term state used t
  | EventAbortE _ ->
      ()
  | EventE(t,p) ->
      check_usage_term state false t;
      check_usage_term state used p
  | GetE _ | InsertE _ ->
      Parsing_helper.internal_error "Event, event_abort, get, insert should have been expanded"
	
and check_usage_pat state = function
    PatVar _ -> ()
  | PatTuple (f,l) -> List.iter (check_usage_pat state) l
  | PatEqual t -> check_usage_term state true t

(* Check the assignment [let b' = t in] where program_point pp occurs just after this assignment *) 
and check_assign state b' t pp =
  try 
    let args_accu = ref [] in
    collect_bargs args_accu state.b t;
    if (!args_accu) != [] then
      begin
	if List.memq b' state.seen_accu then
	  raise TooComplex;
	List.iter (fun l ->
	  (* b[l] occurs in t1, so the cells b'[lidx'] with lidx = l may
	     depend on b[lidx]. We check that they do not leak information *)
	  begin
	    try
	      (* let 'rename' replace b'.args_at_creation with fresh indices
		 facts' = facts union (rename (get_facts_at pp)) union (lidx = rename l)
		 lidx' = rename b'.args_at_creation *)
	      let eq_index = List.combine l state.lidx in 
	      let (lidx', facts') = add_facts_at state.facts state.cur_array eq_index pp in
	      check_usage_full_process { cur_array = []; seen_accu = b'::state.seen_accu; b = b'; lidx = lidx'; facts = facts' } 
	    with Contradiction -> 
	      (* Current program point unreachable *)
	      ()
	  end;
	  List.iter (check_usage_term state true) l
	    ) (!args_accu)
      end
  with TooComplex ->
    (* Either [t] does not depend on [b], or it may depend on [b]
       in a too complex way. Check directly that [t] does not depend on [b]. *)
    check_usage_term state true t

	
and check_usage_process state p =
  match p.i_desc with
    Nil -> ()
  | Par(p1,p2) -> 
      check_usage_process state p1;
      check_usage_process state p2
  | Repl(ri,p) ->
      check_usage_process { state with cur_array = ri:: state.cur_array } p
  | Input((c, tl), pat, p) ->
      List.iter (check_usage_term state true) tl;
      check_usage_pat state pat;
      check_usage_oprocess state p

and check_usage_oprocess state p =
  match p.p_desc with
    Yield | EventAbort _ -> ()
  | Restr(_,p) ->
      check_usage_oprocess state p
  | Test(t,p1,p2) ->
      check_usage_term state true t;
      check_usage_oprocess state p1;
      check_usage_oprocess state p2
  | Find(l0,p2,_) ->
      List.iter (fun (bl,def_list, t, p1) ->
	let state' = { state with cur_array = (List.map snd bl) @ state.cur_array } in
	List.iter (fun (_,l) -> 
	  List.iter (check_usage_term state' true) l) def_list;
	check_usage_term state' true t;
	check_usage_oprocess state p1) l0;
      check_usage_oprocess state p2
  | Let(PatVar b', t, p1, _) ->
      check_assign state b' t (DProcess p1);
      check_usage_oprocess state p1
  | Let(pat,t,p1,p2) ->
      check_usage_pat state pat;
      check_usage_term state true t;
      check_usage_oprocess state p1;
      check_usage_oprocess state p2
  | Output((c, tl),t2,p) ->
      List.iter (check_usage_term state true) tl;
      check_usage_term state true t2;
      check_usage_process state p
  | EventP(t,p) ->
      check_usage_term state false t;
      check_usage_oprocess state p
  | Get _ | Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

and check_usage_full_process state =
  if List.memq state.b (!public_vars) then
    begin
      add_leak_for_current_restr (PublicVar state.b);
      raise Not_found
    end
  else
    check_usage_process state (Terms.get_process (!whole_game))


let has_assign b =
  List.exists (fun def ->
    match def.definition with
      DProcess { p_desc = Let _ } | DTerm { t_desc = LetE _} -> true
    | _ -> false) b.def

(* [check_secrecy b pub_vars] proves one-session secrecy of [b]
   with public variables [pub_vars].
   It returns [(true, proba)] when one-session secrecy of [b]
   holds up to probability [proba].
   It returns [(false, _)] when the proof of one-session secrecy
   of [b] failed. *)

let check_one_session_secrecy collector b pub_vars =
  let not_found_flag = ref false in (* Flag set to true instead of raising Not_found 
				       when we want to examine all cases to fill the collector *)
  let set_not_found() =
    if Terms.collector_useless collector then
      raise Not_found
    else
      not_found_flag := true
  in
  let ty = ref None in
  advise := [];
  detected_leaks := [];
  try
    List.iter (fun d -> 
      match Terms.def_kind d.definition with
      | AssignDef(b',l) ->
	  if has_assign b' then
	    begin
	      add_leak (NotOnlyRestr b');
	      Terms.collector_set_no_info collector;
	      advise := Terms.add_eq (RemoveAssign (false, Binders [b'])) (!advise)
	    end
	  else if Terms.is_restr b' then
	    begin
	      current_restr := Some b';
	      public_vars := pub_vars;
	      (match !ty with
		None -> ty := Some b'.btype
	      |	Some ty' -> if ty' != b'.btype then 
		  Parsing_helper.internal_error ("Variable " ^ (Display.binder_to_string b) ^ " has definitions of different types"));
	      try
		let (lidx, ((all_indices, pp_list, simp_facts, defined_refs) as facts)) = add_facts_at ([],[],([],[],[]),[]) b.args_at_creation [] d.definition_success in
		let rename = Terms.subst b.args_at_creation lidx in
		try
		  check_usage_full_process { cur_array = []; seen_accu = [b']; b = b'; lidx = List.map rename l; facts = facts }
		with Not_found ->
		  Terms.add_to_collector collector (CollectorFacts(all_indices, pp_list, simp_facts, defined_refs));
		  if List.length b'.def > 1 then
		    advise := Terms.add_eq (SArenaming b') (!advise)
		  else
		    set_not_found()
	      with Contradiction ->
		(* Current program point unreachable *)
		()
	    end
	  else
	    begin
	      add_leak (NotOnlyRestr b');
	      Terms.collector_set_no_info collector;
	      raise Not_found
	    end
      |	RestrDef ->
	  (match !ty with
	    None -> ty := Some b.btype
	  | Some ty' -> if ty' != b.btype then 
	      Parsing_helper.internal_error ("Variable " ^ (Display.binder_to_string b) ^ " has definitions of different types"));
	  begin
	    try
	      current_restr := Some b;
	      public_vars := pub_vars;
	      let (lidx, ((all_indices, pp_list, simp_facts, defined_refs) as facts)) = add_facts_at ([],[],([],[],[]),[]) b.args_at_creation [] d.definition_success in
	      try 
		check_usage_full_process { cur_array = []; seen_accu = [b]; b = b; lidx = lidx; facts = facts }
	      with Not_found ->
		Terms.add_to_collector collector (CollectorFacts(all_indices, pp_list, simp_facts, defined_refs));
		set_not_found()
	    with Contradiction ->
	      (* Current program point unreachable *)
	      ()
	  end
      |	OtherDef ->
	  add_leak NotRestrOrAssign;
	  Terms.collector_set_no_info collector;
	  raise Not_found) b.def;
    if !not_found_flag then raise Not_found;
    if (!advise) == [] then
      begin
	let proba = Polynom.proba_from_set (Depanal.get_proba()) in
	print_string "Proved one-session secrecy of ";
	Display.display_binder b;
	Display.display_up_to_proba proba;
	print_newline();
	detected_leaks := [];
	current_restr := None;
	public_vars := [];
	(true, proba)
      end
    else
      begin
	display_leaks b;
	List.iter (fun i -> 
	  Settings.advise := Terms.add_eq i (!Settings.advise)) (!advise);
	advise := [];
	detected_leaks := [];
	current_restr := None;
	public_vars := [];
	(false, Zero)
      end
  with Not_found ->
    display_leaks b;
    advise := [];
    detected_leaks := [];
    current_restr := None;
    public_vars := [];
    (false, Zero)

(*****
   [check_distinct b g] shows that elements of the array [b] 
   at different indices are always different (up to negligible probability).
   [g] is the full game.
   This is useful for showing secrecy of a key.
 *****)


let make_indexes cur_array =
  List.map Terms.new_repl_index cur_array

let rename_facts bindex index (facts, pps, def_vars (*, elsefind_facts*)) =
  (* Rename session identifiers in facts, variables, and elsefind facts *)
  List.iter2 (fun b t -> b.ri_link <- (TLink t)) bindex index;
  let new_facts = List.map (Terms.copy_term Terms.Links_RI) facts in
  let new_pps = List.map (fun (ppl, args) -> (ppl, List.map (Terms.copy_term Terms.Links_RI) args)) pps in
  let new_def_vars = Terms.copy_def_list Terms.Links_RI def_vars in
  (* let new_elsefind_facts = List.map Terms.copy_elsefind elsefind_facts in *)
  List.iter (fun b -> b.ri_link <- NoLink) bindex;
  (new_facts, new_pps, new_def_vars(*, new_elsefind_facts*))
    
let collect_facts def index1 =
  Facts.get_facts_at_args [] [] (def.definition_success, index1) 
  (* + Facts.get_elsefind_facts_at def.definition_success *)
  
let collect_facts_list r_index1 index1 index2 defs =
  List.fold_left (fun accu d ->
    try
      let facts = collect_facts d index1 in
      (d, facts, rename_facts r_index1 index2 facts)::accu
    with Contradiction ->
      accu) [] defs

let check_distinct collector b =
  (* Do not reset: we continue with the state from [check_onesession_secrecy]
     Depanal.reset [] g; *)
  (* Already done in success.ml
     Improved_def.improved_def_game None false g; *)
  let r_index1 = make_indexes b.args_at_creation in
  let r_index2 = make_indexes b.args_at_creation in
  let index1 = List.map Terms.term_from_repl_index r_index1 in
  let index2 = List.map Terms.term_from_repl_index r_index2 in
  let diff_index = Terms.make_or_list (List.map2 Terms.make_diff index1 index2) in
  let bindex = b.args_at_creation in
  let dwithfacts = collect_facts_list r_index1 index1 index2 b.def in
  let distinct_def
      (d1,(d1facts,d1pps,d1def_vars(*,d1elsefind_facts*)),_)
      (d2,_,(d2facts,d2pps,d2def_vars(*,d2elsefind_facts*))) =
    let distinct_def_aux (b1',l1) (b2',l2) =
      (b1' != b2') || 
      (
      try
	let indices12 = r_index1 @ r_index2 in
	let pp12 = d1pps @ d2pps in
	let def_vars12 = d1def_vars @ d2def_vars in
	let eq_b = Terms.make_and_list 
	    (List.map2 Terms.make_equal 
	       (List.map (Terms.subst bindex index1) l1) 
	       (List.map (Terms.subst bindex index2) l2))
	in
	let facts1 = diff_index :: eq_b :: d2facts @ d1facts in
	let facts2 = Incompatible.both_ppl_ppl_add_facts facts1 d1pps d2pps in
	let simp_facts12 = Terms.auto_cleanup (fun () -> 
	  Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) facts2) 
	in
	let facts_ef = 
	  if !Settings.elsefind_facts_in_success then
	    Facts_of_elsefind.get_facts_of_elsefind_facts (!whole_game) indices12 simp_facts12
	      def_vars12
	  else
	    []
	in
	let simp_facts12 = Facts.simplif_add_list Facts.no_dependency_anal simp_facts12 facts_ef in
	(* The following part is commented out because it is too costly. 
	   
	   We assume that the 2nd Let is executed after the 1st one.
	   WARNING: if I use this code, I must scan the whole lists dwithfacts 
	   for both definitions, so that the other case is checked symmetrically.
	   Hence the elsefind facts at the 2nd let hold. 
	let (subst, facts, _) = simp_facts2 in
	let simp_facts3 = (subst, facts, d2elsefind_facts) in
	let simp_facts4 = Facts.convert_elsefind Facts.no_dependency_anal def_vars simp_facts3 in *)
	Terms.add_to_collector collector (CollectorFacts(indices12, pp12, simp_facts12, def_vars12));
	false
      with Contradiction -> true
	  )
    in
    match Terms.def_kind d1.definition, Terms.def_kind d2.definition with
    | RestrDef, RestrDef -> true
    | RestrDef, AssignDef(b',l) | AssignDef(b',l), RestrDef ->
	if not (Terms.is_restr b') then
	  Parsing_helper.internal_error "restriction should be checked when testing secrecy";
	distinct_def_aux (Terms.binderref_from_binder b) (b',l)
    | AssignDef(b1',l1), AssignDef(b2',l2) ->
	if not ((Terms.is_restr b1') && (Terms.is_restr b2')) then
	  Parsing_helper.internal_error "restriction should be checked when testing secrecy";
	distinct_def_aux (b1',l1) (b2',l2)
    | _ -> 
	Parsing_helper.internal_error "definition cases should be checked when testing secrecy"
  in
  let rec all_distinct = function
    | [] -> true
    | a::l ->
	let av = Terms.for_all_collector collector (distinct_def a) (a::l) in
	if av = false && Terms.collector_useless collector then false else
	let lv = all_distinct l in
	av && lv
  in
  all_distinct dwithfacts 
  (* Must not empty, because may be used by other queries;
     Will be emptied in success.ml
     Simplify1.empty_improved_def_process false g.proc; *)

let check_secrecy g collector b pub_vars one_session =
  Depanal.reset [] g;
  whole_game := g;
  let (r1, _) as one_session_result = check_one_session_secrecy collector b pub_vars in
  if one_session then
    begin
      if r1 then
	Depanal.final_empty_state()
      else
	Terms.add_to_collector collector (CollectorProba (Depanal.get_and_final_empty_state()));
      (one_session_result, None)
    end
  else
    if r1 = false && Terms.collector_useless collector then
      begin
	Depanal.final_empty_state();
	(one_session_result, Some (false, Zero)) 
      end
    else
      let r2 = check_distinct collector b in
      if r1 && r2 then
	begin
          (* Add probability for eliminated collisions *)
	  let proba = Polynom.proba_from_set (Depanal.final_add_proba()) in 
	  print_string "Proved secrecy of ";
	  Display.display_binder b;
	  Display.display_up_to_proba proba;
	  print_newline();
	  (one_session_result, Some(true, proba))
	end
      else
	begin
	  Terms.add_to_collector collector (CollectorProba (Depanal.get_and_final_empty_state()));
	  if r1 then
	    begin
	      print_string ("Proof of secrecy of " ^ 
			    (Display.binder_to_string b) ^ " failed:\n");
	      print_string "  Proved one-session secrecy but not secrecy.\n";
	    end;
	  (one_session_result, Some(false, Zero))
	end
