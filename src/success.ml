open Types

(* [whole_game] contains the game on which we want to prove security properties *)

let whole_game = ref Terms.empty_game

(* [proved_one_session_secrets] contains a list of triples [(b,l,res)]
   which mean that [check_secrecy b l] returned [res].
   The goal is avoid redoing the proof of one-session secrecy when we
   want to prove both secrecy and one-session secrecy for the same
   variable with the same public variables. *)

let proved_one_session_secrets = ref []

(* [check_secrecy_memo b l] does the same as [check_secrecy b l] 
   but uses [proved_one_session_secrets] to avoid redoing work 
   when it is called several times with the same variable [b]
   and list [l]. *)

let has_full_secrecy_query b pub_vars =
  let q = QSecret (b,pub_vars,RealOrRandom false) in
  List.exists (fun ((q',_),popt_ref) -> (!popt_ref = ToProve) && (Terms.equal_query q q'))
    (!whole_game).current_queries
      
let check_secrecy_memo collector b l =
  try
    let (_,_,res) = List.find (fun (b',l',res) -> (b == b') && (Terms.equal_lists_sets_q l l')) 
	(!proved_one_session_secrets) 
    in 
    res
  with Not_found ->
    (* [one_session] is true when only one-session secrecy is needed. *)
    let one_session = not (has_full_secrecy_query b l) in
    let res = Check_secrecy.check_secrecy (!whole_game) collector b l one_session in
    proved_one_session_secrets := (b, l, res) :: (!proved_one_session_secrets);
    res

(* [check_equivalence state game] checks indistinguishability *)

let check_active mess g =
  List.for_all (fun ((q,g),poptref) ->
    if !poptref = Inactive then
      begin
	print_string "Query "; Display.display_query3 q;
	print_string " is inactive"; print_string mess;
	print_string ". You should prove it.";
	print_newline();
	false
      end
    else true
	) g.current_queries

let check_included mess1 g1 mess2 g2 =
  List.for_all (function
    | (QEquivalence _,_),_ ->
	(* The equivalence query is present only on one side, and that's normal *)
	true
    | ((q,g),poptref) ->
	if (!poptref = ToProve) && not (List.exists (fun ((q',g'), poptref') ->
	  !poptref' = ToProve && Terms.equal_query q q'
	    ) g2.current_queries) then
	  begin
	    print_string "Query "; Display.display_query3 q;
	    print_string " is still to prove"; print_string mess1;
	    print_string ", but not"; print_string mess2; print_string ".";
	    print_newline();
	    false
	  end
	else true
	    ) g1.current_queries
    
let check_equivalence collector state game =
  (* The adversary may always win *)
  Terms.collector_set_no_info collector;
  let (r, proba) = Transf_merge.equal_games game state.game in
  if r &&
    (check_active "" game) &&
    (check_active " on the other side" state.game) &&
    (check_included " on this side" game " on the other side" state.game) &&
    (check_included " on the other side" state.game " on this side" game)
  then (true, Polynom.proba_from_set proba)
  else (false, Zero)
      
(* [check_query q] proves the query [q]. 
   It returns [(true, proba)] when [q] holds up to probability [proba].
   It returns [(false, _)] when the proof of [q] failed.*)

let check_query collector event_accu = function
  | (QSecret (b,pub_vars,options),_) ->
      (* Deal with one-session and multi-session queries in one step *) 
      let (one_session_res, multi_session_opt) = check_secrecy_memo collector b pub_vars in
      begin
	match options with
	| Bit | RealOrRandom true -> 
	    one_session_res
	| RealOrRandom false -> 
	    begin
	      match multi_session_opt with
	      | None -> assert false
	      | Some multi_session_res -> multi_session_res
	    end
	| Reachability _ ->
	    Parsing_helper.internal_error "reachability secrecy not implemented"
      end
  | (AbsentQuery,_) ->
      (* The adversary may always win *)
      Terms.collector_set_no_info collector;
      (false, Zero)
  | (query, _) ->
      let (r, proba) =
	match query with
	| QEventQ(t1,t2,pub_vars) ->
	    Check_corresp.check_corresp collector event_accu (t1,t2,pub_vars) (!whole_game)
	| QEquivalence(state,pub_vars,_) ->
	    check_equivalence collector state (!whole_game)
	| QEquivalenceFinal _ | AbsentQuery | QSecret _ ->
	    (* AbsentQuery | QSecret _ handled above;
	       QEquivalenceFinal should never happen *)
	    assert false
      in
      if r then
	begin
	  print_string "Proved query ";
	  Display.display_query3 query;
	  Display.display_up_to_proba proba;
	  print_newline();
	  (true, proba)
	end
      else (false, Zero)

(* [check_query_list collector event_accu state qlist] takes a list of queries [qlist], tries to prove
   those that are not proved yet, and returns
    - the list of queries it proved with the associated probability of success of an attack.
    - the updated list of all queries with their proofs
    - a boolean which is true when all queries have been proved *)

let rec check_query_list collector event_accu state = function
    [] -> ([],true)
  | (((a, poptref) as q)::l) ->
      let (l',b) = check_query_list collector event_accu state l in
      match Settings.get_query_status q with
      | Proved _ | Inactive -> (* The query was already proved before, 
				  or is inactive *)
	  (l',b)
      |	ToProve -> (* We need to prove the query *)
	  let (res, proba) = check_query collector event_accu a in
	  if res then
	    begin
	      (* The query is proved *)
              poptref := Proved([fst a], proba, state);
	      ((a,proba)::l', b)
	    end
	  else 
	    (* The query is not proved *)
	    (l', false)
    
(* [is_success collector state] tries to prove queries that still need to be
   proved in [state]. It updates the proofs of the queries inside
   [state] and returns the list of newly proved queries (with the
   associated probability of success of an attack) as well as boolean
   which is true when all queries are proved. *)

let is_success collector state =
  let g = state.game in
  whole_game := g;
  proved_one_session_secrets := [];
  let vcounter = Terms.get_var_num_state() in
  let event_accu = ref [] in
  Improved_def.improved_def_game (Some event_accu) true g;
  (* Check equivalence queries last, so that, if another query (unreachability 
     of some event) can be proved, it is already proved when we check the 
     equivalence query. For that, we put the equivalence queries first,
     because [check_query_list] checks queries in the reverse order
     of the list *)
  let (equiv_queries, other_queries) = List.partition (function
    | (QEquivalence _,_),_ -> true
    | _ -> false) g.current_queries in
  let queries = equiv_queries @ other_queries in
  let res = check_query_list collector (!event_accu) state queries in
  Compute_state_display_info.update_full_proof state;
  Terms.set_var_num_state vcounter; (* Forget created variables *)
  proved_one_session_secrets := [];
  Improved_def.empty_improved_def_game true g;
  whole_game := Terms.empty_game;
  res
