open Types

(* Exception [NoMatchExplain] is used to provide an explanation
   of why the proof of the correspondence fails *)
  
type explanation =
    FactFailed of qterm
  | OrExp of explanation * explanation

let rec display_explanation = function
    FactFailed qt ->
      Display.display_query2 qt
  | OrExp(e1,e2) ->
      display_explanation e1;
      print_string " nor ";
      display_explanation e2
	
exception NoMatchExplain of explanation
  
(***** Check correspondence assertions 
       [check_corresp (t1,t2) g] checks that the correspondence
       [(t1,t2)] holds in the game [g] *****)

(* [get_var_link] function associated to [guess_by_matching].
   See the interface of [Terms.match_funapp] for the 
   specification of [get_var_link]. *)

let get_var_link_g t () = 
  match t.t_desc with
    FunApp _ -> None
  | Var(v,[]) -> Some (v.link, true)
  | Var _ | ReplIndex _ | TestE _ | FindE _ | LetE _ | ResE _ | EventAbortE _ | EventE _ | GetE _ | InsertE _ ->
      Parsing_helper.internal_error "Var with arguments, replication indices, if, find, let, new, event, event_abort, get, insert should not occur in guess_by_matching"      

(* [guess_by_matching_same_root next_f known_facts t t']
   tries to match [t'] with [t], in order to determine
   the values of variables in [t]. 
   Matches only variables or terms with the same root function symbol.
   The values of variables are stored as links inside [t].
   Raises [NoMatch] when the matching fails.

   [known_facts] is a quintuple [(simp_facts, elsefind_facts_list, injrepidx_pps, repl_indices, vars_t1)]
   where 
   - [simp_facts] is the set of facts that are known to hold, in simplified form, that is,
   [(substitutions, facts, elsefind facts)]
   - [elsefind_facts_list] is the set of elsefind facts that are known to hold at each event
   [e_i] before the arrow in the correspondence to prove, with additional information:
   [elsefind_facts_list] is a list of [(elsefind_facts, fact_info, def_vars, new_end_sid)] where
   [elsefind_facts] is the list of elsefind facts that hold at [e_i]
   [fact_info] is the program point at [e_i]
   [def_vars] is the list of variables known to be defined at [e_i]
   [new_end_sid] is the list of replication indices at [e_i] as renamed in the proof of the correspondence.
   [fact_info] and [new_end_sid] are used to compute the variables defined after [e_i]
   in the same input...output block as [e_i].
   - [injrepidx_pps] is the list of sequences of replication indices and program points 
   of injective events before the arrow in the correspondence.
   - [repl_indices] is the list of replication indices of all events before the arrow 
   in the correspondence.
   - [vars_t1] is the list of variables that occur before the arrow in the correspondence
   (after renaming).

   [guess_by_matching_same_root] uses only the component [simp_facts] of [known_facts].
   *)
	
let rec guess_by_matching simp_facts next_f t t' () = 
  match t.t_desc with
    Var (v,[]) -> 
    (* Check that types match *)
      if t'.t_type != v.btype then
	raise NoMatch;
      begin
	match v.link with
	  NoLink -> Terms.link v (TLink t')
	| TLink _ -> ()
      end;
      next_f()
  | FunApp _ ->
      Match_eq.match_funapp (guess_by_matching simp_facts) get_var_link_g next_f simp_facts next_f t t' ()
  | Var _ | ReplIndex _ | TestE _ | FindE _ | LetE _ | ResE _ | EventAbortE _ | EventE _ | GetE _ | InsertE _ ->
      Parsing_helper.internal_error "Var with arguments, replication indices, if, find, let, new, event, event_abort, get, insert should not occur in guess_by_matching"

let guess_by_matching_same_root next_f (simp_facts,_,_,_,_) t t' = 
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
  | Var _ | ReplIndex _ | TestE _ | FindE _ | LetE _ | ResE _ | EventAbortE _ | EventE _ | GetE _ | InsertE _ ->
      Parsing_helper.internal_error "Var with arguments, replication indices, if, find, let, new, event, event_abort, get, insert should not occur in guess_by_matching"

(* [is_instantiated t] returns true when all variables that occur in [t]
   are linked. *)

let rec is_instantiated t =
  match t.t_desc with
    Var(b,[]) -> b.link != NoLink
  | FunApp(f,l) -> List.for_all is_instantiated l
  | _ -> Parsing_helper.internal_error "expecting variable or function in is_instantiated"

(* [show_fact known_facts fact] tries to prove [fact] from [known_facts],
   by adding the negation of [fact] and obtaining a contradiction.
   It returns true when it succeeds and false when it fails.

   See the definition of [known_facts] above. 
   [show_fact] uses only the component [simp_facts] of [known_facts]. *)
	
let show_fact (facts,_,_,_,_) fact =
  Terms.auto_cleanup (fun () ->
      try
	let r = Facts.simplif_add Facts.no_dependency_anal facts (Terms.make_not fact) in
	if !Settings.debug_corresp then
	  begin
	    print_string "Failed to prove "; 
	    Display.display_term fact;
	    print_newline();
	    print_string "Simplified facts: ";
	    Display.display_facts r;
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


(* [get_contradiction simp_facts def_vars elsefind_facts] tries to derive
   a contradiction from the fact that [simp_facts] holds and at some event [e],
   the [elsefind_facts] hold and the variables in [def_vars] are defined. 
   It returns true when it succeeds and false when it fails.

   The facts in [simp_facts] may not hold yet at the event [e],
   they may involve variables defined after [e] in the trace.
   They are used:
   - when converting [elsefind_facts] to standard facts, 
   but only derive equalities between indices. If these equalities hold
   later in the trace, they also hold at the event [e].
   - when deriving the final contradiction, by combining
   the derived standard facts with [simp_facts]. 
*)
    
let get_contradiction simp_facts def_vars elsefind_facts =
  try
    let (subst, facts, _) = simp_facts in
    let simp_facts' = (subst, facts, elsefind_facts) in
    if !Settings.debug_corresp then
      begin
	print_string "Proving injectivity using elsefind facts.\n";
	print_string "Available facts:\n";
	Display.display_facts simp_facts';
	print_string "Defined variables:\n";
	Display.display_def_list_lines def_vars
      end;
    ignore (Facts.convert_elsefind Facts.no_dependency_anal def_vars simp_facts');
    if !Settings.debug_corresp then
      print_string "Could not prove a contradiction\n";
    false
  with Contradiction ->
    if !Settings.debug_corresp then
      print_string "Proved a contradiction\n";
    true

(* [get_future_defvars end_pp new_end_sid] returns the list of variables
   defined after the program point [end_pp] in the same input...output block,
   with indices [new_end_sid]. *)

let get_future_defvars end_pp new_end_sid =
  match Incompatible.get_facts end_pp with
    Some (_,_,_,_,_,fut_binders,_) ->
      List.map (fun b -> (b, new_end_sid)) fut_binders
  | None -> []
  
(* [add_inj known_facts fact' fact injinfo] performs the proof of injectivity.

   See above the definition of [known_facts].

   [fact'] is an injective event that occurs after the arrow in the correspondence ("begin event"),
   as it is proved.
   [fact] is an injective "begin" event, as it is in the correspondence.
   ([fact'] is an instance of [fact].)

   [injinfo] is a list of pieces of injective information containing,
   for each way to prove the correspondence [t1 ==> t2], 
   a list of pairs [(fact, inj_list)] where
   - [fact] is an injective "begin" event, as it is in the correspondence.
   - [inj_list] is information on the context in which [fact] was proved.
   It is a list of quadruples [(simp_facts, elsefind_facts_list, injrepidx_pps, begin_sid_occ)]:
     * [simp_facts] is a set of facts that hold, in simplified form.
     * [elsefind_facts_list] is information on elsefind facts that hold,
       as in [known_facts]
     * [injrepidx_pps] is the list of sequences of replication indices and program points 
       of injective events before the arrow in the correspondence.
     * [begin_sid_occ] is the list of replication indices and occurrence 
       at which the "begin" event [fact] was proved.

   To prove injectivity, we need to show that, if the injective events in [t1] are executed
   with different indices, then each injective event in [t2] is also executed with different
   indices. 
   Therefore, for each [(fact, inj_list)] in [injinfo], we consider two
   elements of [inj_list], 
   [inj_elem = (simp_facts, elsefind_facts_list, injrepidx_pps, begin_sid_occ)]
   [inj_elem' = (simp_facts', elsefind_facts_list', injrepidx_pps', begin_sid_occ')]
   and show that [injrepidx_pps <> injrepidx_pps' && begin_sid_occ = begin_sid_occ' &&
   simp_facts && simp_facts' && elsefind_facts_list && elsefind_facts_list']
   leads to a contradiction.
   [check_inj_compat inj_elem inj_elem'] performs this check, with a minor
   difference: the facts in the first component of [inj_elem'] are a list of facts; 
   they are not in simplified form.

   Note: when the two elements of [inj_list] are in fact the same element,
   the variables are renamed in one of the copies.

   [add_inj] creates a new element [inj_elem] and adds it to the appropriate
   [inj_list] after performing the needed checks, that is, 
   calling [check_inj_compat] with any element already in [inj_list] and [inj_elem] and 
   calling [check_inj_compat] with [inj_elem] and [inj_elem] renamed.

   (Variables in t1/t2 do not occur in the facts. 
   Only variables in t1/t2 have links.)

   *)
	
(* [case_check facts else_info else_info'] returns true when
   [facts && else_info && else_info'] leads to a contradiction,
   under the assumption that the events corresponding to 
   [else_info] and [else_info'] are executed with different replication indices.

   This is done by distinguishing which of the two events
   corresponding to [else_info] and [else_info'] is executed last,
   and calling [get_contradiction]. *)
let case_check facts 
    (elsefind, end_pp, def_vars, new_end_sid)
    (elsefind', end_pp', def_vars', new_end_sid') =
  (* By the case distinction made before [case_check],
     we know that the events corresponding to these elsefind
     pieces of information are executed with different indices.
     We distinguish cases depending which one is executed first.
     (Note: by symmetry, it may be enough to consider one case
     when we test [check_inj_compat] with the same element [injelem].
     However, when we test [check_inj_compat] with two different
     elements, we already use the symmetry to perform the test of
     [check_inj_compat] in only one direction, so we must test both
     cases here.) *)
  let future_def_vars =
    (* When [end_pp'] is after [end_pp] in the same input..output
       block and we assume that the event at [end_pp'] is executed 
       after the one at [end_pp], we are not sure that the full
       input..output block of [end_pp] has been executed,
       so we are not sure that the future_defvars are really defined. *)
    if (Terms.occ_from_pp end_pp != Terms.occ_from_pp end_pp') &&
      (Facts.is_before_same_block end_pp end_pp') then
      []
    else
      get_future_defvars end_pp new_end_sid
  in
  let future_def_vars' =
    if (Terms.occ_from_pp end_pp != Terms.occ_from_pp end_pp') &&
      (Facts.is_before_same_block end_pp' end_pp) then
      []
    else
      get_future_defvars end_pp' new_end_sid'
  in
  (* The event corresponding to (elsefind, end_pp, def_vars, new_end_sid)
     is executed before the one corresponding to 
     (elsefind', end_pp', def_vars', new_end_sid').
     At the last of these two events, the variables in
     [future_def_vars @ def_vars @ def_vars'] are all defined,
     and [elsefind'] holds. *)
  (get_contradiction facts (future_def_vars @ def_vars @ def_vars') elsefind') &&
  (* Symmetrically, when the event corresponding to 
     (elsefind', end_pp', def_vars', new_end_sid') 
     is executed before the one corresponding to 
     (elsefind, end_pp, def_vars, new_end_sid). *)
  (get_contradiction facts (future_def_vars' @ def_vars' @ def_vars) elsefind)

let check_inj_compat
    (simp_facts, elsefind_facts_list, injrepidx_pps, (begin_occ, begin_sid)) 
    (facts', elsefind_facts_list', injrepidx_pps', (begin_occ', begin_sid')) =
  Terms.auto_cleanup (fun () ->
    try
      (* different end events: injrepidx_pps \neq injrepidx_pps' *)
      let facts'' =
	if List.for_all2 (fun (end_pp, end_sid) (end_pp', end_sid') ->
	  Terms.occ_from_pp end_pp == Terms.occ_from_pp end_pp') injrepidx_pps injrepidx_pps' then
	  (* The program points of end events are the same, we require some indices to be different *)
	  (Terms.make_or_list (List.concat (List.map2 (fun (end_pp, end_sid) (end_pp', end_sid') ->
	    (List.map2 Terms.make_diff end_sid end_sid')) injrepidx_pps injrepidx_pps'))) ::facts'
	else
	  (* When one end_occ is different from end_occ', we know that injrepidx_pps \neq injrepidx_pps'.
	     However, we can still get information from the incompatibility of the program points end_pp/end_pp' *)
	  List.fold_left2 Incompatible.both_pp_add_fact facts' injrepidx_pps injrepidx_pps'
      in
      (* same begin events: (begin_occ, begin_sid) = (begin_occ', begin_sid') *)
      if begin_occ != begin_occ' then raise Contradiction;
      let eq_facts = List.map2 Terms.make_equal begin_sid begin_sid' in
      (* Add all facts *)
      let facts_with_inj1 = Facts.simplif_add_list Facts.no_dependency_anal simp_facts facts'' in
      let facts_with_inj2 = Facts.simplif_add_list Facts.no_dependency_anal facts_with_inj1 eq_facts in
      (* If we could not prove the injectivity so far,
         try to use elsefind facts to prove it.
	 We distinguish cases depending on which event is executed
	 with indices different in the two sequences of events
	 before the arrow considered in the proof of injectivity. *)
      if not (List.for_all2 (case_check facts_with_inj2) elsefind_facts_list elsefind_facts_list') then
	raise NoMatch
    with Contradiction ->
      ())


let add_inj (simp_facts, elsefind_facts_list, injrepidx_pps, repl_indices, vars) fact' fact injinfo =
  match fact'.t_desc with
    FunApp(_, { t_desc = FunApp(_, begin_sid) }::_) ->
      begin
	let begin_occ = fact'.t_occ in
	if begin_occ == -1 then
	  Parsing_helper.internal_error "Occurrence of begin fact not correctly set";
	let nsimpfacts = Facts.true_facts_from_simp_facts simp_facts in 
	List.iter (fun b -> b.ri_link <- TLink (Terms.term_from_repl_index (Terms.new_repl_index b))) repl_indices;
	List.iter (fun b -> b.link <- TLink (Terms.term_from_binder (Terms.new_binder b))) vars;
	let new_facts = List.map (Terms.copy_term Terms.Links_RI_Vars) nsimpfacts in
	(* The variables that we rename are variables that occur in the correspondence to prove.
           They do not occur in def_vars, so we need to rename only replication indices.
	   Same comment for elsefind_facts. *)
	let new_elsefind_facts_list =  List.map (function (elsefind, end_pp, def_vars, new_end_sid) ->
	  (List.map Terms.copy_elsefind elsefind,
	   end_pp,
	   Terms.copy_def_list Terms.Links_RI def_vars,
	   List.map (Terms.copy_term Terms.Links_RI_Vars) new_end_sid)
	    ) elsefind_facts_list in
	let new_injrepidx_pps =
	  List.map
	    (function (end_pp, end_sid) ->
	      (end_pp, List.map (Terms.copy_term Terms.Links_RI_Vars) end_sid))
	    injrepidx_pps
	in
	let new_begin_sid = List.map (Terms.copy_term Terms.Links_RI_Vars) begin_sid in
	List.iter (fun b -> b.ri_link <- NoLink) repl_indices;
	List.iter (fun b -> b.link <- NoLink) vars;

        if !Settings.debug_corresp then
          begin
	    print_string "Checking inj compatiblity\n";
	    Display.display_facts simp_facts;
	    print_string "New facts\n";
	    List.iter (fun f -> Display.display_term f; print_newline()) new_facts;
	    print_string "Inj rep idxs:";
	    let display_end_sid_occ (end_pp, end_sid) =
	      print_int (Terms.occ_from_pp end_pp); print_string ", ";
	      Display.display_list Display.display_term end_sid
	    in
	    Display.display_list display_end_sid_occ injrepidx_pps;
	    print_string "\nNew inj rep idxs:";
	    Display.display_list display_end_sid_occ new_injrepidx_pps;
	    print_string "\nBegin occ, sid:";
	    print_int begin_occ; print_string ", "; Display.display_list Display.display_term begin_sid;
	    print_string "\nNew begin occ, sid:";
	    print_int begin_occ; print_string ", "; Display.display_list Display.display_term new_begin_sid;
	    print_string "\n\n";
	  end;
        (* The new element [inj_elem] to be added to [inj_info] *)
	let add_inj_info = (simp_facts, elsefind_facts_list, injrepidx_pps, (begin_occ, begin_sid)) in
        (* The new element [inj_elem] with variables renamed *)
	let new_inj_info = (new_facts, new_elsefind_facts_list, new_injrepidx_pps, (begin_occ, new_begin_sid)) in
	
	check_inj_compat add_inj_info new_inj_info;
	try
	  let l = List.assq fact injinfo in
	  List.iter (fun lelem -> check_inj_compat lelem new_inj_info) l;
	  (fact, add_inj_info :: l) :: (List.filter (fun (f, _) -> f != fact) injinfo)
	with Not_found ->
	  (fact, [add_inj_info]) ::injinfo 
      end
  | _ -> Parsing_helper.internal_error "event should have session id"

(* [prove_by_matching next_check known_facts injinfo is_inj fact] tries to prove
   [fact], or [inj:fact] when [is_inj] is true, from 
   the known facts [known_facts] and the information of injective events [injinfo].
   It tries to find an instance of [fact] in the list of facts contained in [known_facts].
   When it succeeds, it calls [next_check] with the updated [injinfo].
   When it fails, it raises 
   - [NoMatch] when the proof of [fact] fails
   - [NoMatchExplain e] when [next_check] fails.
   ([next_check] should only raise exception [NoMatchExplain])

   see the definition of [known_facts] and [injinfo] above.
*)
let prove_by_matching next_check (((_,facts,_),_,_,_,_) as known_facts) injinfo is_inj fact =
  let rec prove_by_matching_aux = function
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
	    (* Check that all variables of [fact] are instantiated *)
	    if not ((is_instantiated fact) &&
                    (* ... and that [fact'] is equal to [fact] *)
	            show_fact known_facts (Terms.make_equal fact' (Terms.copy_term Terms.Links_Vars fact)))
	    then raise NoMatch;
	    if is_inj then 
	      next_check (add_inj known_facts fact' fact injinfo)
	    else
	      next_check injinfo
	    ) known_facts fact fact');
      with
	NoMatch -> 
	  Proba.restore_state tmp_proba_state;
	  prove_by_matching_aux l
      | NoMatchExplain e ->
	  (* In case the current fact was proved, but [next_check] failed *)
	  try
	    Proba.restore_state tmp_proba_state;
	    prove_by_matching_aux l
	  with NoMatch ->
	    raise (NoMatchExplain e)
  in
  prove_by_matching_aux facts

(* [check_term next_check known_facts injinfo t] tries to prove the term [t]
   using the known facts [known_facts] and the information of injective events [injinfo].
   When it succeeds, calls [next_check] with the updated [injinfo].
   When it fails, raises [NoMatchExplain] with an explanation of why it failed. 

   See the definition of [known_facts] and [injinfo] above. *)
    
let rec check_term next_check known_facts injinfo = function
    QAnd(t,t') ->
      check_term (fun injinfo' -> check_term next_check known_facts injinfo' t')
	known_facts injinfo t
  | QOr(t,t') ->
      begin
	let tmp_proba_state = Proba.get_current_state() in
	try
	  Terms.auto_cleanup (fun () ->
	    check_term next_check known_facts injinfo t)
	with NoMatchExplain e1 ->
	  Proba.restore_state tmp_proba_state;
	  try
	    check_term next_check known_facts injinfo t'
	  with NoMatchExplain e2 ->
	    raise (NoMatchExplain(OrExp(e1,e2)))
      end
  | QTerm t2 ->
      begin
	(* Try to find an instance of t2 in simp_facts *)
	let tmp_proba_state = Proba.get_current_state() in
	try
	  prove_by_matching next_check known_facts injinfo false t2
	with
	  NoMatch -> 
	    Proba.restore_state tmp_proba_state;
	     (* If failed, try to prove t2 by contradiction,
	        when t2 is fully instantiated *)
	    if (is_instantiated t2) &&
	      (show_fact known_facts (Terms.copy_term Terms.Links_Vars t2))
	    then
	      next_check injinfo
	    else
	      raise (NoMatchExplain(FactFailed(QTerm t2)))
	| NoMatchExplain e ->
	    (* In case the current fact was proved, but [next_check] failed *)
	    Proba.restore_state tmp_proba_state;
	    (* No need to retry proving t2: if t2 was fully
	       instantiated, we already tried [next_check] and failed. *)
	    raise (NoMatchExplain e)
      end
  | QEvent(is_inj,t2) ->
      begin
	(* Try to find an instance of t2 in simp_facts *)
	let tmp_proba_state = Proba.get_current_state() in
	try
	  prove_by_matching next_check known_facts injinfo is_inj t2
	with
	  NoMatch -> 
	    Proba.restore_state tmp_proba_state;
	    raise (NoMatchExplain(FactFailed(QEvent(is_inj,t2))))
	| NoMatchExplain e ->
	    (* In case the current fact was proved, but [next_check] failed *)
	    Proba.restore_state tmp_proba_state;
	    raise (NoMatchExplain e)
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

(* [is_event_abort_pp pp] is true when the program point [pp]
   is an [event_abort] instruction. *)

let is_event_abort_pp = function
  | DProcess ({ p_desc = EventAbort _ })
  | DTerm ({ t_desc = EventAbortE _ }) -> true
  | _ -> false

(* [is_event_false q] is true when the query [q] is of the
   form [event(e(...)) ==> false] *)

let is_event_false = function
  | [inj, { t_desc = FunApp(f,l) }], QTerm tfalse, _ ->
      Terms.is_false tfalse &&
      (not inj) &&
      ((f.f_cat == Event) || (f.f_cat == NonUniqueEvent))
  | _ -> false

(* [get_event_false q] returns [Some f] when the query [q] is of the
   form [event(f) ==> false]. Otherwise, it returns [None]. *)

let get_event_false = function
  | [inj, { t_desc = FunApp(f,[idx]) }], QTerm tfalse, _ ->
      if Terms.is_false tfalse &&
	(not inj) &&
	((f.f_cat == Event) || (f.f_cat == NonUniqueEvent)) then Some f else None
  | _ -> None

(* In [add_to_collector_f_false collector q end_pp t1']
   the query [q] must be [event(f(M1...Mn)) ==> false]
   and [t1',end_pp] be an entry of [event_accu]:
   [t1'] is an executed event and [end_pp] is its program point. 
   This function adds to [collector] the information known
   when event [f(M1...Mn)] is executed: 
   - f(M1...Mn) = t1' 
   - facts known at [end_pp], including elsefind facts and defined variables
   It does not use the future facts at [end_pp]. 
   This is needed for 2 reasons:
   - using elsefind facts is a bit more precise than what we do for general queries,
   and allowed for queries [event(f(M1...Mn)) ==> false] since continuing the execution
   after the event [f] will not help make the query true, so we can consider that
   we stop the trace at event [f] and use the elsefind facts at that event.
   - for non-unique events, future facts must not be used because the
   future facts at the find will not be true when the non-unique event is
   executed. *)

let add_to_collector_f_false collector q end_pp t1' =
  match q, t1'.t_desc with
  | ([_, { t_desc = FunApp(f,idx::l) }], QTerm _, _), FunApp(f',idx'::l') ->
      if f == f' then
	let end_sid = 
	  match idx'.t_desc with
	  | FunApp(_,lsid) -> lsid
	  | _ -> Parsing_helper.internal_error "Session ids should occur first in the arguments of events"
	in
	let bend_sid = List.map Terms.repl_index_from_term end_sid in
	let new_bend_sid = List.map Terms.new_repl_index bend_sid in
	let new_end_sid = List.map Terms.term_from_repl_index new_bend_sid in
	let (new_facts, new_pps, def_vars') = Facts.get_facts_at_args [] [] (end_pp, new_end_sid) in
	let elsefind_facts_common = Facts.get_elsefind_facts_at end_pp in
        (* Rename session identifiers in facts, variables, and elsefind facts *)
	List.iter2 (fun b t -> b.ri_link <- (TLink t)) bend_sid new_end_sid;
	let eq_facts = List.map2 Terms.make_equal
	    (List.map (Terms.copy_term Terms.Links_Vars) l)
	    (List.map (Terms.copy_term Terms.Links_RI) l')
	in
	let collector_elsefind_facts' = List.map Terms.copy_elsefind elsefind_facts_common in
	List.iter (fun b -> b.ri_link <- NoLink) bend_sid;
	let (subst, facts, else_find) =
	  Terms.auto_cleanup (fun () -> Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) (eq_facts @ new_facts)) in
	Terms.add_to_collector collector
	  (CollectorFacts(new_bend_sid, new_pps, (subst, facts, collector_elsefind_facts' @ else_find), def_vars'))
      else
	() (* [t1',end_pp] does not correspond to the event in [q], do nothing *)
  | _ -> assert false

(* [optim_non_unique q] tries to quickly prove or fail to prove
   a query [event(f) ==> false], in particular when [f] is a
   non-unique event. It returns [Some r] when the quick evaluation worked,
   and [None] when the detailed proof should be performed. *)
	
let optim_non_unique collector event_accu ((t1,t2,pub_vars) as q) =
  match get_event_false q with
  | Some f ->
      begin
	try 
	  let (one_t1', one_end_pp) =
	    List.find (fun (t1',end_pp) ->
	      match t1'.t_desc with
	      | FunApp(f',_) -> f' == f
	      | _ -> Parsing_helper.internal_error "event expected in check_corresp") event_accu
	  in
	  (* Event [f] occurs in the game *)
	  if f.f_cat == NonUniqueEvent then
	    begin
	      (* Event [f] is a non-unique event, we stop the proof here,
		 considering that it fails.
                 The detailed proof is done in module [Unique]. *)
	      print_string "Proof of ";
	      Display.display_query3 (QEventQ(t1,t2,pub_vars));
	      print_string (" failed:\n  Found event "^f.f_name^" at ");
	      print_int one_t1'.t_occ;
	      print_newline();
	      if collector != None then
		List.iter (fun (t1',end_pp) ->
		  add_to_collector_f_false collector q end_pp t1'
		    ) event_accu;
	      Some (false, Zero)
	    end
	  else
	    (* Do the detailed proof *)
	    None
	with Not_found ->
	  (* Event [f] does not occur in the game, the query is proved *)
	  Some (true, Zero)
      end
  | None ->
      (* Do the detailed proof *)
      None
	
	
(* [collect_facts_list collector event_accu next_f tl] collects 
   the facts that hold when [tl] is true and calls [next_f] on 
   the collected facts *)
	
let collect_facts_list collector event_accu next_f tl =
  let collect_facts1 next_f (end_pps, events_found, facts, def_vars, elsefind_facts_list, injrepidx_pps, vars, collector_pp, collector_elsefind_facts) (is_inj,t) =
    Terms.for_all_collector collector (fun (t1',end_pp) ->
      match t.t_desc,t1'.t_desc with
	FunApp(f,idx::l),FunApp(f',idx'::l') ->
	  if f == f' then
	    if not (List.for_all Terms.check_simple_term l') then
	      begin
	      (* Cannot make the proof when the arguments of the event in the process
                 are not simple terms *)
		Terms.collector_set_no_info collector;
		false
	      end
	    else
	    try
	      let events_found' = t1' :: events_found in
	      let end_sid =
		match idx'.t_desc with
		  FunApp(_,lsid) -> lsid
		| _ -> Parsing_helper.internal_error "Session ids should occur first in the arguments of events"
	      in
	      let bend_sid = List.map Terms.repl_index_from_term end_sid in
	      let new_bend_sid = List.map Terms.new_repl_index bend_sid in
	      let new_end_sid = List.map Terms.term_from_repl_index new_bend_sid in
	      let eq_facts = List.map2 Terms.make_equal (List.map (Terms.copy_term Terms.Links_Vars) l) (List.map (Terms.subst bend_sid new_end_sid) l') in
	      (* The adversary cannot prevent the end of the input...output block 
		 from being executed, so we can collect true facts until the end 
		 of the block. *)
	      let (facts_common, facts_cases, pps_common, def_vars_common) = Facts.get_facts_full_block_args [] [] (end_pp, new_end_sid) in
	      let new_def_vars = (get_future_defvars end_pp new_end_sid) @ def_vars_common in

	      let elsefind_facts_common = Facts.get_elsefind_facts_at end_pp in

	      (* Rename session identifiers in facts, variables, and elsefind facts *)
	      List.iter2 (fun b t -> b.ri_link <- (TLink t)) bend_sid new_end_sid;
	      let new_elsefind_facts = List.map Terms.copy_elsefind elsefind_facts_common in
	      (* The adversary cannot prevent the end of the input...output block 
		 from being executed, so we can collect the defined variables 
		 until the end of the block.
		 However, we must still be careful when we apply elsefind facts,
		 to use defined variables at the point of the elsefind facts. *)
	      List.iter (fun b -> b.ri_link <- NoLink) bend_sid;

	      if !Settings.debug_corresp then
		begin
		  print_string "\nAt ";
		  print_int t1'.t_occ;
		  print_string ", found ";
                  Display.display_term t1';
                  print_string " with facts\n";
                  List.iter (fun t -> Display.display_term t; print_newline()) (eq_facts @ facts_common); 
	          print_string "Cases:";
	          List.iter (fun fll ->
		    print_string "BLOCK CASE\n";
		    List.iter (fun fl ->
		      print_string "OR "; Display.display_list Display.display_term fl; print_newline()) fll;
		  ) facts_cases;
	          print_newline();
		end;
	      let new_facts = Incompatible.both_ppl_ppl_add_facts facts_common collector_pp pps_common in
	      
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
		  Display.display_facts facts';
		end;

	      let new_facts_cases = simplify_cases new_facts facts_cases in
	      let def_vars' = new_def_vars @ def_vars in
	      (* The elsefind facts are not all guaranteed to be true
                 at the same time. We perform the proof at the last event of t1 executed
                 (so that the facts and defined variables collected at all events
                 are indeed true). Thus, only the elsefind facts at that event 
		 are known to be true. If we use elsefind facts, we will need to 
		 distinguish depending on which event is the last one.
		 We store the set of elsefind facts at each event in a different
		 element of the list, to be able to distinguish such cases.

		 In addition to the elsefind facts, we store the end_pp,
                 def_vars_common and new_end_sid corresponding to this event. *)
	      let elsefind_facts_list' = (new_elsefind_facts, end_pp, def_vars_common, new_end_sid) :: elsefind_facts_list in

	      let collector_pp' = pps_common @ collector_pp in
	      let collector_elsefind_facts' =
		(* When [end_pp] is [event_abort], nothing is executed after it,
		   so the elsefind facts found at that point remain true. *)
		if is_event_abort_pp end_pp then
		  new_elsefind_facts @ collector_elsefind_facts
		else
		  collector_elsefind_facts
	      in
	      
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
		      next_f (end_pp :: end_pps, events_found', facts, def_vars', elsefind_facts_list, injrepidx_pps, (new_bend_sid @ vars), collector_pp', collector_elsefind_facts')
		    else
		      next_f (end_pp :: end_pps, events_found', facts, def_vars', elsefind_facts_list', ((end_pp, new_end_sid) :: injrepidx_pps), (new_bend_sid @ vars), collector_pp', collector_elsefind_facts')
		| f_disjunct::rest ->
		    (* consider all possible cases in the disjunction *)
		    Terms.for_all_collector collector (fun fl ->
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

  let rec collect_facts_list next_f accu = function
      [] -> next_f accu
    | (a::l) -> 
        collect_facts1 (fun accu' -> collect_facts_list next_f accu' l) accu a
  in

  collect_facts_list next_f ([], [], ([],[],[]), [], [], [], [], [], []) tl



(* [check_corresp event_accu corresp g] is the main function to prove
   correspondences. It proves the correspondence [corresp = t1 ==> t2] in the game [g],
   using the information on events collected in [event_accu].
   ([event_accu] is a list of events and program points at which they are 
   executed. From the program point, we can recover the facts that hold,
   the variables that are defined, etc.) *)
      
let check_corresp collector event_accu ((t1,t2,pub_vars) as q) g =
  Terms.auto_cleanup (fun () ->
(* Dependency collision must be deactivated, because otherwise
   it may consider the equality between t1 and t1' below as an unlikely
   collision, because t1 does not depend on variables in the process.
   That's why I use "no_dependency_anal" *)

  if !Settings.debug_corresp then
    begin
      print_string "Trying to prove ";
      Display.display_query (QEventQ(t1,t2,pub_vars), g)
    end;

  match optim_non_unique collector event_accu q with
  | Some r -> r
  | None -> 
	
  Depanal.reset [] g;
  let vars_t1 = Terms.collect_vars_hyp t1 in
  let vars_t1' = List.map (fun b ->
    b.def <- [];
    ignore (Terms.set_def [b] DNone DNone None);
    let b' = Terms.new_binder b in
    Terms.link b (TLink (Terms.term_from_binder b'));
    b') vars_t1
  in
  let injinfo = ref [] in
  let r =
    (* The proof of the correspondence [t1 ==> t2] works in two steps:
       first, collect all facts that hold because [t1] is true *)
    collect_facts_list collector event_accu (fun (end_pps, events_found', facts', def_vars', elsefind_facts_list', injrepidx_pps', vars', collector_pp', collector_elsefind_facts') ->
      try 
	Terms.auto_cleanup (fun () -> 
	  let facts2 = 
	    if !Settings.elsefind_facts_in_success then
	      Facts_of_elsefind.get_facts_of_elsefind_facts g vars' facts' collector_pp' None def_vars' 
	    else
	      []
	  in
          let facts' = Facts.simplif_add_list Facts.no_dependency_anal facts' facts2 in
          (* second, prove [t2] from these facts *)
	  try
	    check_term (fun injinfo' -> injinfo := injinfo'; true) (facts', elsefind_facts_list', injrepidx_pps', vars', vars_t1') (!injinfo) t2
	  with NoMatchExplain e ->
	    (* The proof failed. Explain why in a short message. *)
	    print_string "Proof of ";
	    Display.display_query3 (QEventQ(t1,t2,pub_vars));
	    print_string " failed:\n";
	    print_string "  Found ";
	    Display.display_list (fun t ->
	      Display.display_term t;
	      print_string " at ";
	      print_int t.t_occ
		) events_found';
	    print_newline();
	    print_string "  but could not prove ";
	    display_explanation e;
	    print_newline();
	    if collector != None then
	      begin
		let default() = 
		  let (subst, facts, else_find) = facts' in
		  Terms.add_to_collector collector
		    (CollectorFacts(vars', collector_pp', (subst, facts, collector_elsefind_facts' @ else_find), def_vars'))
		in
		  (* For the query event e ==> false, we try to be a bit more precise.
                     We collect the facts that are true at the event e (not at the end of the block),
                     and use the elsefind facts at the event e.
                     We already used the elsefind facts in case of event_abort e, 
		     so we do not redo it in this case. *)
		if is_event_false q then
		  match end_pps, events_found' with
		  | [end_pp], [t1'] ->
		      if is_event_abort_pp end_pp then
                        (* No change when event_abort, because we already used the elsefind facts *)
			default()
		      else
			add_to_collector_f_false collector q end_pp t1'
		  | _ -> Parsing_helper.internal_error "for query event e ==> false, collector_pp' should contain a single element"
		else
		  default()
	      end;
	    false)
      with Contradiction -> 
	true
	  ) t1
  in
  if r then
    (* Add probability for eliminated collisions *)
    (true, Polynom.proba_from_set (Depanal.final_add_proba()))
  else
    begin
      Terms.add_to_collector collector (CollectorProba (Depanal.get_and_final_empty_state()));
      (false, Zero)
    end
      )

(**** Prove that a non-injective correspondence implies the injective
      correspondence and replace the injective one with the non-injective one. 
      *)

let rec remove_inj_qt = function
  | QEvent(inj,t) -> QEvent(false,t)
  | QTerm t -> QTerm t
  | QAnd(t1,t2) ->
      QAnd(remove_inj_qt t1, remove_inj_qt t2)
  | QOr(t1,t2) ->
      QOr(remove_inj_qt t1, remove_inj_qt t2)

let remove_inj_q = function
  | QEventQ(hyp,concl,pub_vars) ->
      QEventQ(List.map (fun (inj,t) -> (false,t)) hyp,
	      remove_inj_qt concl, pub_vars)
  | x -> x

(* [add_inj] works similarly to when we want to prove injectivity,
   except that it uses the [begin_fact] we want to prove instead
   of the [begin_sid_occ] *)

let check_inj_compat
    (simp_facts, elsefind_facts_list, injrepidx_pps, begin_fact) 
    (facts', elsefind_facts_list', injrepidx_pps', begin_fact') =
  Terms.auto_cleanup (fun () ->
    try
      (* different end events: injrepidx_pps \neq injrepidx_pps' *)
      let facts'' =
	if List.for_all2 (fun (end_pp, end_sid) (end_pp', end_sid') ->
	  Terms.occ_from_pp end_pp == Terms.occ_from_pp end_pp') injrepidx_pps injrepidx_pps' then
	  (* The program points of end events are the same, we require some indices to be different *)
	  (Terms.make_or_list (List.concat (List.map2 (fun (end_pp, end_sid) (end_pp', end_sid') ->
	    (List.map2 Terms.make_diff end_sid end_sid')) injrepidx_pps injrepidx_pps'))) ::facts'
	else
	  (* When one end_occ is different from end_occ', we know that injrepidx_pps \neq injrepidx_pps'.
	     However, we can still get information from the incompatibility of the program points end_pp/end_pp' *)
	  List.fold_left2 Incompatible.both_pp_add_fact facts' injrepidx_pps injrepidx_pps'
      in
      (* same begin events *)
      let eq_facts =
	match begin_fact.t_desc, begin_fact'.t_desc with
	| FunApp(f,l), FunApp(f',l') when f == f' -> 
	    List.map2 Terms.make_equal l l'
	| _ -> assert false
      in
      (* Add all facts *)
      let facts_with_inj1 = Facts.simplif_add_list Facts.no_dependency_anal simp_facts facts'' in
      let facts_with_inj2 = Facts.simplif_add_list Facts.no_dependency_anal facts_with_inj1 eq_facts in
      (* If we could not prove the injectivity so far,
         try to use elsefind facts to prove it.
	 We distinguish cases depending on which event is executed
	 with indices different in the two sequences of events
	 before the arrow considered in the proof of injectivity. *)
      if not (List.for_all2 (case_check facts_with_inj2) elsefind_facts_list elsefind_facts_list') then
	raise NoMatch
    with Contradiction ->
      ())

let add_inj (simp_facts, elsefind_facts_list, injrepidx_pps, repl_indices, vars) fact' fact injinfo =
	let nsimpfacts = Facts.true_facts_from_simp_facts simp_facts in 
	List.iter (fun b -> b.ri_link <- TLink (Terms.term_from_repl_index (Terms.new_repl_index b))) repl_indices;
	List.iter (fun b -> b.link <- TLink (Terms.term_from_binder (Terms.new_binder b))) vars;
	let new_facts = List.map (Terms.copy_term Terms.Links_RI_Vars) nsimpfacts in
	(* The variables that we rename are variables that occur in the correspondence to prove.
           They do not occur in def_vars, so we need to rename only replication indices.
	   Same comment for elsefind_facts. *)
	let new_elsefind_facts_list =  List.map (function (elsefind, end_pp, def_vars, new_end_sid) ->
	  (List.map Terms.copy_elsefind elsefind,
	   end_pp,
	   Terms.copy_def_list Terms.Links_RI def_vars,
	   List.map (Terms.copy_term Terms.Links_RI_Vars) new_end_sid)
	    ) elsefind_facts_list in
	let new_injrepidx_pps =
	  List.map
	    (function (end_pp, end_sid) ->
	      (end_pp, List.map (Terms.copy_term Terms.Links_RI_Vars) end_sid))
	    injrepidx_pps
	in
	let new_fact = Terms.copy_term Terms.Links_RI_Vars fact' in
	List.iter (fun b -> b.ri_link <- NoLink) repl_indices;
	List.iter (fun b -> b.link <- NoLink) vars;

        if !Settings.debug_corresp then
          begin
	    print_string "Checking inj compatiblity\n";
	    Display.display_facts simp_facts;
	    print_string "New facts\n";
	    List.iter (fun f -> Display.display_term f; print_newline()) new_facts;
	    print_string "Inj rep idxs:";
	    let display_end_sid_occ (end_pp, end_sid) =
	      print_int (Terms.occ_from_pp end_pp); print_string ", ";
	      Display.display_list Display.display_term end_sid
	    in
	    Display.display_list display_end_sid_occ injrepidx_pps;
	    print_string "\nNew inj rep idxs:";
	    Display.display_list display_end_sid_occ new_injrepidx_pps;
	    print_string "\nBegin fact:";
	    Display.display_term fact';
	    print_string "\nNew begin fact:";
	    Display.display_term new_fact;
	    print_string "\n\n";
	  end;
        (* The new element [inj_elem] to be added to [inj_info] *)
	let add_inj_info = (simp_facts, elsefind_facts_list, injrepidx_pps, fact') in
        (* The new element [inj_elem] with variables renamed *)
	let new_inj_info = (new_facts, new_elsefind_facts_list, new_injrepidx_pps, new_fact) in
	
	check_inj_compat add_inj_info new_inj_info;
	try
	  let l = List.assq fact injinfo in
	  List.iter (fun lelem -> check_inj_compat lelem new_inj_info) l;
	  (fact, add_inj_info :: l) :: (List.filter (fun (f, _) -> f != fact) injinfo)
	with Not_found ->
	  (fact, [add_inj_info]) ::injinfo 


let rec check_term_inj next_check known_facts injinfo = function
  | QAnd(t,t') | QOr(t,t') ->
      check_term_inj (fun injinfo' -> check_term_inj next_check known_facts injinfo' t')
	known_facts injinfo t
  | QTerm t2 ->
      next_check injinfo
  | QEvent(is_inj,t2) as qt ->
      if is_inj then
	next_check
	  (try
	    let fact' = Terms.copy_term Terms.Links_Vars t2 in
	    add_inj known_facts fact' t2 injinfo
	  with NoMatch ->
	    raise (NoMatchExplain (FactFailed qt)))
      else
	next_check injinfo

let proved_inj event_accu (t1,t2,pub_vars) g = 
  Terms.auto_cleanup (fun () ->
(* Dependency collision must be deactivated, because otherwise
   it may consider the equality between t1 and t1' below as an unlikely
   collision, because t1 does not depend on variables in the process.
   That's why I use "no_dependency_anal" *)
  if !Settings.debug_corresp then
    begin
      print_string "Trying to prove injectivity for ";
      Display.display_query (QEventQ(t1,t2,pub_vars), g)
    end;
  Depanal.reset [] g;
  let vars_t1 = Terms.collect_vars_hyp t1 in
  let vars_t1' = List.map (fun b ->
    b.def <- [];
    ignore (Terms.set_def [b] DNone DNone None);
    let b' = Terms.new_binder b in
    Terms.link b (TLink (Terms.term_from_binder b'));
    b') vars_t1
  in
  let injinfo = ref [] in
  let r =
    (* The proof of the correspondence [t1 ==> t2] works in two steps:
       first, collect all facts that hold because [t1] is true *)
    collect_facts_list None event_accu (fun (end_pps, events_found', facts', def_vars', elsefind_facts_list', injrepidx_pps', vars', collector_pp', collector_elsefind_facts') ->
      try 
	Terms.auto_cleanup (fun () -> 
	  let facts2 = 
	    if !Settings.elsefind_facts_in_success then
	      Facts_of_elsefind.get_facts_of_elsefind_facts g vars' facts' collector_pp' None def_vars' 
	    else
	      []
	  in
          let facts' = Facts.simplif_add_list Facts.no_dependency_anal facts' facts2 in
          (* second, prove [t2] from these facts *)
	  try
	    check_term_inj (fun injinfo' -> injinfo := injinfo'; true) (facts', elsefind_facts_list', injrepidx_pps', vars', vars_t1') (!injinfo) t2
	  with NoMatchExplain e ->
	    (* The proof failed. Explain why in a short message. *)
	    print_string "Proof of injectivity for ";
	    Display.display_query3 (QEventQ(t1,t2,pub_vars));
	    print_string " failed:\n";
	    print_string "  Found ";
	    Display.display_list (fun t ->
	      Display.display_term t;
	      print_string " at ";
	      print_int t.t_occ
		) events_found';
	    print_newline();
	    print_string "  but could not prove injectivity of ";
	    display_explanation e;
	    print_newline();
	    false)
      with Contradiction -> 
	true
	  ) t1
  in
  if r then
    (* Add probability for eliminated collisions *)
    Some (Depanal.final_add_proba())
  else
    begin
      Depanal.reset [] g;
      None
    end
      )


let proved_inj event_accu g = function
  | QEventQ(hyp,concl,pub_vars) ->
      if List.exists (fun (inj,_) -> inj) hyp then
	proved_inj event_accu (hyp,concl,pub_vars) g
      else
	(* The query is not injective *)
	None
  | x -> 
      None

	
let remove_inj event_accu g q =
  match proved_inj event_accu g q with
  | Some proba -> 
      Some (remove_inj_q q, proba)
  | None -> 
      None


(**** Check well-formedness *)

let well_formed = function
  | QSecret _ | QEquivalence _ | QEquivalenceFinal _ | AbsentQuery -> ()
  | QEventQ(psi,phi,_pub_vars) ->
      let vars_psi = Terms.collect_vars_hyp psi in
      let subst = List.map (fun b ->
	b.def <- [];
	ignore (Terms.set_def [b] DNone DNone None);
	let b' = Terms.new_binder b in
	ignore (Terms.set_def [b'] DNone DNone None);
	(b, Terms.term_from_binder b')
	  ) vars_psi
      in
      let eq_facts = List.concat (List.map (fun (_,t) ->
	match t.t_desc with
	| FunApp(f,l) ->
	    List.map (fun t -> Terms.make_equal t (Terms.subst3 subst t)) l
	| _ -> assert false
	      ) psi)
      in
      let simp_facts = Facts.simplif_add_list Facts.no_dependency_anal Terms.simp_facts_id eq_facts in
      let check_eq_term t =
	let diff_fact = Terms.make_diff t (Terms.subst3 subst t) in
	try
	  ignore(Facts.simplif_add Facts.no_dependency_anal simp_facts diff_fact);
	  let t_string = Display.string_out (fun () -> Display.display_term t) in
	  Parsing_helper.input_warning ("could not prove that the term "^t_string^" in the conclusion of a correspondence is determined by the hypothesis of the correspondence: it might take several different values for the same events in the hypothesis") t.t_loc
	with Contradiction ->
	  ()
      in
      let rec check_eq = function
	| QEvent(_,t) ->
	    begin
	      match t.t_desc with
	      | FunApp(f,l) ->
		  List.iter check_eq_term l
	      | _ -> assert false
	    end
	| QTerm t ->
	    check_eq_term t
	| QAnd(t1,t2) | QOr(t1,t2) ->
	    check_eq t1;
	    check_eq t2
      in
      check_eq phi
