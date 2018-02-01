open Types

(***** Check correspondence assertions 
       [check_corresp (t1,t2) g] checks that the correspondence
       [(t1,t2)] holds in the game [g] *****)

let whole_game = ref Terms.empty_game

(* [get_var_link] function associated to [guess_by_matching].
   See the interface of [Terms.match_funapp] for the 
   specification of [get_var_link]. *)

let get_var_link_g t () = 
  match t.t_desc with
    FunApp _ -> None
  | Var(v,[]) -> Some (v.link, true)
  | Var _ | ReplIndex _ | TestE _ | FindE _ | LetE _ | ResE _ | EventAbortE _ ->
      Parsing_helper.internal_error "Var with arguments, replication indices, if, find, let, new, event should not occur in guess_by_matching"      

let rec guess_by_matching simp_facts next_f t t' () = 
  match t.t_desc with
    Var (v,[]) -> 
    (* Check that types match *)
      if t'.t_type != v.btype then
	raise NoMatch;
      begin
	match v.link with
	  NoLink -> Terms.link v (TLink t')
	| TLink t -> ()
      end;
      next_f()
  | FunApp _ ->
      Terms.match_funapp (guess_by_matching simp_facts) get_var_link_g next_f simp_facts next_f t t' ()
  | Var _ | ReplIndex _ | TestE _ | FindE _ | LetE _ | ResE _ | EventAbortE _ ->
      Parsing_helper.internal_error "Var with arguments, replication indices, if, find, let, and new should not occur in guess_by_matching"

let guess_by_matching_same_root next_f simp_facts t t' = 
  match t.t_desc with
    Var (v,[]) -> 
      guess_by_matching simp_facts next_f t t' ()
  | FunApp(f,l) ->
      begin
	let t'' = Terms.try_no_var simp_facts t' in 
	match t''.t_desc with
	  FunApp(f',l') when f == f' ->
	    guess_by_matching simp_facts next_f t t'' ()
	| _ -> raise NoMatch
      end
  | Var _ | ReplIndex _ | TestE _ | FindE _ | LetE _ | ResE _ | EventAbortE _ ->
      Parsing_helper.internal_error "Var with arguments, replication indices, if, find, let, and new should not occur in guess_by_matching"

let rec collect_vars accu t =
  match t.t_desc with
    Var(b,[]) -> accu := b :: (!accu)
  | FunApp(f,l) -> List.iter (collect_vars accu) l
  | _ -> Parsing_helper.internal_error "expecting variable or function in collect_vars"

let show_fact facts fact =
  Terms.auto_cleanup (fun () ->
      try
	let r = Facts.simplif_add Facts.no_dependency_anal facts (Terms.make_not fact) in
	if !Settings.debug_corresp then
	  begin
	    print_string "Failed to prove "; 
	    Display.display_term fact;
	    print_newline();
	    print_string "Simplified facts: ";
	    Facts.display_facts r;
          end;
	false
      with Contradiction ->
        if !Settings.debug_corresp then
	  begin
	    print_string "Proved "; 
	    Display.display_term fact;
	    print_newline()
	  end;
	true)


(* Try to prove injectivity for injective correspondences 
   simp_facts = facts derivable 
   injrepidxs = list of sequences of replication indexes at the injective end events
   begin_sid = sequence of replication indexes at an injective begin event

   facts', injrepidxs', begin_sid' = same thing for another way of proving
   the concerned injective begin event, with renamed variables.

   (Variables in t1/t2 do not occur in the facts. 
   Only variables in t1/t2 have links.)

   *)

let check_inj_compat (simp_facts, def_vars, elsefind_facts, injrepidxs, repl_indices, _, begin_sid) 
    facts' def_vars' elsefind_facts' injrepidxs' repl_indices' begin_sid' =
  Terms.auto_cleanup (fun () ->
    try
      let facts_with_inj1 = Facts.simplif_add_list Facts.no_dependency_anal simp_facts facts' in
      (* injrepidxs \neq injrepidxs' *)
      let diff_fact = Terms.make_or_list (List.concat (List.map2 
	(List.map2 Terms.make_diff) injrepidxs injrepidxs')) in
      let facts_with_inj2 = Facts.simplif_add Facts.no_dependency_anal facts_with_inj1 diff_fact in
      (* begin_sid = begin_sid' *)
      let eq_facts = List.map2 Terms.make_equal begin_sid begin_sid' in
      let facts_with_inj3 = Facts.simplif_add_list Facts.no_dependency_anal facts_with_inj2 eq_facts in
      (* If we could not prove the injectivity so far,
         try to use elsefind facts to prove it.
	 We distinguish cases depending on which event is executed last:
	 only the elsefind facts true at that event hold. 
	 So we consider each set of elsefind_facts in turn, and try to
	 derive a contradiction by combining it with the other known
	 facts and defined variables. *)
      let def_vars_all = def_vars @ def_vars' in
      let repl_indices_all = repl_indices @ repl_indices' in
      let facts2 = 
	if !Settings.elsefind_facts_in_success then
	  Simplify1.get_facts_of_elsefind_facts (!whole_game) repl_indices_all facts_with_inj3 def_vars_all 
	else
	  []
      in
      ignore (Facts.simplif_add_list Facts.no_dependency_anal facts_with_inj3 facts2);
      raise NoMatch
    with Contradiction ->
      ())

let add_inj simp_facts def_vars elsefind_facts injrepidxs (repl_indices, vars) fact' fact injinfo =
  match fact'.t_desc with
    FunApp(_, { t_desc = FunApp(_, begin_sid) }::_) ->
      begin
	let (subst, facts, _) = simp_facts in
	let nsimpfacts = subst @ facts in 
	let new_repl_indices =
	  List.map (fun b ->
	    let b' = Terms.new_repl_index b in
	    b.ri_link <- TLink (Terms.term_from_repl_index b');
	    b') repl_indices
	in
	List.iter (fun b -> b.link <- TLink (Terms.term_from_binder (Terms.new_binder b))) vars;
	let new_facts = List.map (Terms.copy_term Terms.Links_RI_Vars) nsimpfacts in
	(* The variables that we rename are variables that occur in the correspondence to prove.
           They do not occur in def_vars, so we need to rename only replication indices.
	   Same comment for elsefind_facts. *)
	let new_def_vars = Terms.copy_def_list Terms.Links_RI def_vars in
	let new_elsefind_facts =  List.map (List.map Terms.copy_elsefind) elsefind_facts in
	let new_injrepidxs = List.map (List.map (Terms.copy_term Terms.Links_RI_Vars)) injrepidxs in
	let new_begin_sid = List.map (Terms.copy_term Terms.Links_RI_Vars) begin_sid in
	List.iter (fun b -> b.ri_link <- NoLink) repl_indices;
	List.iter (fun b -> b.link <- NoLink) vars;

        if !Settings.debug_corresp then
          begin
	    print_string "Checking inj compatiblity\n";
	    Facts.display_facts simp_facts;
	    print_string "New facts\n";
	    List.iter (fun f -> Display.display_term f; print_newline()) new_facts;
	    print_string "Inj rep idxs:";
	    Display.display_list (Display.display_list Display.display_term) injrepidxs;
	    print_string "\nNew inj rep idxs:";
	    Display.display_list (Display.display_list Display.display_term) new_injrepidxs;
	    print_string "\nBegin sid:";
	    Display.display_list Display.display_term begin_sid;
	    print_string "\nNew begin sid:";
	    Display.display_list Display.display_term new_begin_sid;
	    print_string "\n\n";
	  end;

	check_inj_compat (simp_facts, def_vars, elsefind_facts, injrepidxs, repl_indices, vars, begin_sid) new_facts new_def_vars new_elsefind_facts new_injrepidxs new_repl_indices new_begin_sid;
	try
	  let l = List.assq fact injinfo in
	  List.iter (fun lelem -> check_inj_compat lelem new_facts new_def_vars new_elsefind_facts new_injrepidxs new_repl_indices new_begin_sid) l;
	  (fact, (simp_facts, def_vars, elsefind_facts, injrepidxs, repl_indices, vars, begin_sid) :: l) :: (List.filter (fun (f, _) -> f != fact) injinfo)
	with Not_found ->
	  (fact, [(simp_facts, def_vars, elsefind_facts, injrepidxs, repl_indices, vars, begin_sid)]) ::injinfo 
      end
  | _ -> Parsing_helper.internal_error "event should have session id"

(* try to find a instance of fact in the list of facts given as
last argument *)
let rec prove_by_matching next_check simp_facts def_vars elsefind_facts injrepidxs vars injinfo is_inj fact = function
    [] -> raise NoMatch
  | (fact'::l) ->
      let tmp_proba_state = Proba.get_current_state() in
      try
	Terms.auto_cleanup (fun () ->
          (* When I am trying to prove an event, the root symbol is
             the event symbol, and it must really be the same for
             fact and fact'. When I am trying to prove another fact,
             it is a good heuristic, since a variable can be bound
             only when at least the root symbol is the same *)
	  guess_by_matching_same_root (fun () ->
	    if !Settings.debug_corresp then
	      begin
		print_string "Found ";
		Display.display_term fact';
		print_string " as instance of ";
		Display.display_term fact;
		print_newline();
	      end;
	    (* Check that all variables of fact are instantiated *)
	    let vars_fact = ref [] in
	    collect_vars vars_fact fact;
	    if not ((List.for_all (fun b -> (b.link != NoLink)) (!vars_fact)) &&
                    (* ... and that fact' is equal to fact *)
	            show_fact simp_facts (Terms.make_equal fact' (Terms.copy_term Terms.Links_Vars fact)))
	    then raise NoMatch;
	    if is_inj then 
	      next_check (add_inj simp_facts def_vars elsefind_facts injrepidxs vars fact' fact injinfo)
	    else
	      next_check injinfo
	    ) simp_facts fact fact');
      with NoMatch -> 
	Proba.restore_state tmp_proba_state;
	prove_by_matching next_check simp_facts def_vars elsefind_facts injrepidxs vars injinfo is_inj fact l

let rec check_term next_check ((_,facts2,_) as facts) def_vars elsefind_facts injrepidxs vars injinfo = function
    QAnd(t,t') ->
      check_term (fun injinfo' -> check_term next_check facts def_vars elsefind_facts injrepidxs vars injinfo' t')
	facts def_vars elsefind_facts injrepidxs vars injinfo t
  | QOr(t,t') ->
      begin
	let tmp_proba_state = Proba.get_current_state() in
	try
	  Terms.auto_cleanup (fun () ->
	    check_term next_check facts def_vars elsefind_facts injrepidxs vars injinfo t)
	with NoMatch ->
	  Proba.restore_state tmp_proba_state;
	  check_term next_check facts def_vars elsefind_facts injrepidxs vars injinfo t'
      end
  | QTerm t2 ->
      begin
	(* Try to find an instance of t2 in simp_facts *)
	let tmp_proba_state = Proba.get_current_state() in
	try
	  prove_by_matching next_check facts def_vars elsefind_facts injrepidxs vars injinfo false t2 facts2
	with NoMatch -> 
	  Proba.restore_state tmp_proba_state;
	  (* If failed, try to prove t2 by contradiction,
	     when t2 is fully instantiated *)
	  let vars_t2 = ref [] in
	  collect_vars vars_t2 t2;
	  if (List.for_all (fun b -> (b.link != NoLink)) (!vars_t2)) &&
	    (show_fact facts (Terms.copy_term Terms.Links_Vars t2))
	      then next_check injinfo else raise NoMatch
      end
  | QEvent(is_inj,t2) ->
      begin
	(* Try to find an instance of t2 in simp_facts *)
	let tmp_proba_state = Proba.get_current_state() in
	try
	  prove_by_matching next_check facts def_vars elsefind_facts injrepidxs vars injinfo is_inj t2 facts2
	with NoMatch -> 
	  Proba.restore_state tmp_proba_state;
	  raise NoMatch
      end

(* [includes l1 l2] returns true when [l1] is included in [l2] *)

let includes l1 l2 =
  List.for_all (fun f1 ->
    List.exists (Terms.equal_terms f1) l2) l1

(* [implies fll1 fll2] returns true when [fll1] implies [fll2],
   where [fll1], [fll2] are lists of lists of facts, 
   [ffl1 = [l1; ...; ln]] means that [fll1 = l1 || ... || ln]
   (logical disjunction) where each list [li] represents a conjunction
   of facts.
     fll1 = l1 || ... || ln
     fll2 = l'1 || ... || l'n' 
     When for all i, there exists j such that l'j is included in li then
     li implies l'j so li implies fll2 = l'1 || ... || l'n', and since this is
     true for all i, fll1 = l1 || ... || ln implies fll2 = l'1 || ... || l'n'. *)

let implies fll1 fll2 =
  List.for_all (fun fl1 ->
    List.exists (fun fl2 ->
      includes fl2 fl1) fll2) fll1

(* [simplify_cases fact_accu fact_accu_cases] returns a simplified
   version of [fact_accu_cases].
   [fact_accu] is a list of facts that are known to hold.
   [fact_accu_cases] is a list of list of list of facts (3 levels of lists),
   interpreted as a conjunction of a disjunction of a conjunction of facts. *)

let simplify_cases fact_accu fact_accu_cases =
  (* remove facts from fact_accu *)
  let fact_accu_cases = 
    List.map (List.map (List.filter (fun f -> not (List.exists (Terms.equal_terms f) fact_accu)))) 
      fact_accu_cases
  in
  (* remove disjunctions that contain an empty conjunction, that is, true *)
  let fact_accu_cases =
    List.filter (fun fll ->
      not (List.exists (fun fl -> fl == []) fll)) fact_accu_cases
  in
  (* inside a disjunction, if a disjunct is included in another disjunct,
     remove the larger disjunct *)
  (* TO DO not done for now because it seems not to reduce much the number
     of cases to consider *)
  (* in the big conjunction, if a conjunct C1 implies an other conjunct C2,
     remove the weaker conjunct C2 *)
  let rec remove_implied seen = function
      [] -> seen
    | fll2::rest -> 
	if (List.exists (fun fll1 -> implies fll1 fll2) seen) ||
	   (List.exists (fun fll1 -> implies fll1 fll2) rest) then
	  remove_implied seen rest
	else
	  remove_implied (fll2::seen) rest
  in
  remove_implied [] fact_accu_cases

let get_facts_at_cases fact_info =
  if !Settings.corresp_cases then
    Facts.get_facts_at_cases fact_info
  else
    (Facts.get_facts_at fact_info, [])
    
let check_corresp event_accu (t1,t2) g =
  Terms.auto_cleanup (fun () ->
(* Dependency collision must be deactivated, because otherwise
   it may consider the equality between t1 and t1' below as an unlikely
   collision, because t1 does not depend on variables in the process.
   That's why I use "no_dependency_anal" *)

  if !Settings.debug_corresp then
    begin
      print_string "Trying to prove ";
      Display.display_query (QEventQ(t1,t2), g)
    end;
  whole_game := g;
  Simplify1.reset [] g;
  let vars_t1 = ref [] in
  List.iter (fun (_, t) -> collect_vars vars_t1 t) t1;
  let vars_t1' = List.map (fun b ->
    let rec def_node = { above_node = def_node; binders = [];
			 true_facts_at_def = []; def_vars_at_def = []; 
			 elsefind_facts_at_def = [];
			 future_binders = []; future_true_facts = []; 
			 definition = DNone; definition_success = DNone }
    in
    b.def <- [def_node];
    let b' = Terms.new_binder b in
    Terms.link b (TLink (Terms.term_from_binder b'));
    b') (!vars_t1)
  in
  let collect_facts1 next_f facts def_vars elsefind_facts injrepidxs vars (is_inj,t) =
    List.for_all (fun (t1',fact_info) ->
      match t.t_desc,t1'.t_desc with
	FunApp(f,idx::l),FunApp(f',idx'::l') ->
	  if f == f' then
	    try
	      let end_sid = 
		match idx'.t_desc with
		  FunApp(_,lsid) -> lsid
		| _ -> Parsing_helper.internal_error "Session ids should occur first in the arguments of events"
	      in
	      let bend_sid = List.map Terms.repl_index_from_term end_sid in
	      let new_bend_sid = List.map Terms.new_repl_index bend_sid in
	      let new_end_sid = List.map Terms.term_from_repl_index new_bend_sid in
	      let eq_facts = List.map2 Terms.make_equal (List.map (Terms.copy_term Terms.Links_Vars) l) (List.map (Terms.subst bend_sid new_end_sid) l') in
	      
	      let (facts_common, facts_cases) = get_facts_at_cases fact_info in
	      let elsefind_facts_common = Facts.get_elsefind_facts_at fact_info in
	      let def_vars_common = Facts.get_def_vars_at fact_info in

	      (* Rename session identifiers in facts, variables, and elsefind facts *)
	      List.iter2 (fun b t -> b.ri_link <- (TLink t)) bend_sid new_end_sid;
	      let new_facts = List.map (Terms.copy_term Terms.Links_RI) facts_common in
	      let new_elsefind_facts = List.map Terms.copy_elsefind elsefind_facts_common in
	      let new_def_vars = Terms.copy_def_list Terms.Links_RI def_vars_common in
	      List.iter (fun b -> b.ri_link <- NoLink) bend_sid;

	      if !Settings.debug_corresp then
		begin
		  print_string "\nFound ";
                  Display.display_term t1';
                  print_string " with facts\n";
                  List.iter (fun t -> Display.display_term t; print_newline()) (eq_facts @ new_facts); 
	          print_string "Cases:";
	          List.iter (fun fll ->
		    print_string "BLOCK CASE\n";
		    List.iter (fun fl ->
		      print_string "OR "; Display.display_list Display.display_term fl; print_newline()) fll;
		  ) facts_cases;
	          print_newline();
		end;
	      let new_facts = Terms.both_def_list_facts new_facts def_vars new_def_vars in
	      
	      let facts1 = Terms.auto_cleanup (fun () -> Facts.simplif_add_list Facts.no_dependency_anal facts new_facts) in
	      if !Settings.debug_corresp then
		begin
		  print_string "First step without contradiction";
		  print_newline();
		end;
	      let facts' = Terms.auto_cleanup (fun () -> Facts.simplif_add_list Facts.no_dependency_anal facts1 eq_facts) in
	      if !Settings.debug_corresp then
		begin
		  print_string "After simplification ";
		  Facts.display_facts facts';
		end;

	      let new_facts_cases = List.map (List.map (List.map (Terms.subst bend_sid new_end_sid)))
		  (simplify_cases facts_common facts_cases)
	      in
	      let def_vars' = new_def_vars @ def_vars in
	      (* The elsefind facts are not all guaranteed to be true
                 at the same time. We perform the proof at the last event of t1 executed
                 (so that the facts and defined variables collected at all events
                 are indeed true). Thus, only the elsefind facts at that event 
		 are known to be true. If we use elsefind facts, we will need to 
		 distinguish depending on which event is the last one.
		 We store the set of elsefind facts at each event in a different
		 element of the list, to be able to distinguish such cases. *)
	      let elsefind_facts' = new_elsefind_facts :: elsefind_facts in

	      if !Settings.debug_corresp then
		begin
		  print_string "Simplified cases:";
		  List.iter (fun fll ->
		    print_string "BLOCK CASE\n";
		    List.iter (fun fl ->
		      print_string "OR "; Display.display_list Display.display_term fl; print_newline()) fll;
		    ) new_facts_cases;
		  print_newline()
		end;
	      
	      let rec collect_facts_cases facts = function
		  [] -> 
		    if not is_inj then
		      next_f facts def_vars' elsefind_facts' injrepidxs (new_bend_sid @ vars)
		    else
		      next_f facts def_vars' elsefind_facts' (new_end_sid :: injrepidxs) (new_bend_sid @ vars)
		| f_disjunct::rest ->
		    (* consider all possible cases in the disjunction *)
		    List.for_all (fun fl ->
		      try 
			let facts' = Terms.auto_cleanup (fun () -> Facts.simplif_add_list Facts.no_dependency_anal facts fl) in
			collect_facts_cases facts' rest
		      with Contradiction -> 
			true
			) f_disjunct
	      in
	      collect_facts_cases facts' new_facts_cases
	    with Contradiction -> 
	      if !Settings.debug_corresp then
		begin
		  print_string "Contradiction. Proof succeeded.";
		  print_newline();
		end;
	      true
	  else 
	    true
      | _ -> Parsing_helper.internal_error "event expected in check_corresp"
	    ) event_accu
  in
  let rec collect_facts_list next_f facts def_vars elsefind_facts injrepidxs vars = function
      [] -> next_f facts def_vars elsefind_facts injrepidxs vars
    | (a::l) -> collect_facts1 (fun facts' def_vars' elsefind_facts' injrepidxs' vars' -> collect_facts_list next_f facts' def_vars' elsefind_facts' injrepidxs' vars' l) facts def_vars elsefind_facts injrepidxs vars a
  in  
  let injinfo = ref [] in
  let r =
    collect_facts_list (fun facts' def_vars' elsefind_facts' injrepidxs' vars' ->
      try 
	Terms.auto_cleanup (fun () -> 
	  let facts2 = 
	    if !Settings.elsefind_facts_in_success then
	      Simplify1.get_facts_of_elsefind_facts g vars' facts' def_vars' 
	    else
	      []
	  in
	  let facts' = Facts.simplif_add_list Facts.no_dependency_anal facts' facts2 in
	  check_term (fun injinfo' -> injinfo := injinfo'; true) facts' def_vars' elsefind_facts' injrepidxs' (vars', vars_t1') (!injinfo) t2)
      with NoMatch -> 
	  false
      |	Contradiction -> 
	  true
	  ) ([],[],[]) [] [] [] [] t1
  in
  whole_game := Terms.empty_game;
  if r then
    (* Add probability for eliminated collisions *)
    (true, Simplify1.final_add_proba())
  else
    begin
      (false, [])
    end)

