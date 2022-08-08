open Types
open Parsing_helper

type state_ty =
    { whole_game : game;
      occ : int;
      ext_o : Parsing_helper.extent;
      mutable to_do : bool;
      branch_num : int;
      has_secrecy : bool;
      mutable guess_br_var : binder option }

exception Finished
      
let may_be_inside state min_occ max_occ =
  if state.to_do then
    (min_occ <= state.occ) && (state.occ <= max_occ)
  else
    begin
      if (min_occ <= state.occ) && (state.occ <= max_occ) then
	Parsing_helper.internal_error "Ambiguous occurrence. That should never happen";
      false
    end

let check_unique_exec state pp cur_array =
  if state.branch_num = 0 && cur_array != [] then
    begin
      (* Check that the branching instruction at [pp] is executed once.
	 For speed, do it only for the first branch *)
      Depanal.reset [] state.whole_game;      
      let old_proba_zero = !Settings.proba_zero in
      Settings.proba_zero := true;
      Improved_def.improved_def_game None false state.whole_game;
      let cleanup() = 
        Improved_def.empty_improved_def_game false state.whole_game;
        assert (Depanal.final_add_proba() == []);
        Settings.proba_zero := old_proba_zero
      in
      try
	(* We create a new copy [cur_array'] of [cur_array] 
	   (when computing [diff_fact] below)
	   and show that: 
	     facts when executing [pp] with indices [cur_array] (this is [facts]/[simp_facts]/[nsimpfacts])
           + facts when executing [pp] with indices [cur_array'] (this is [facts_other_indices])
           + [cur_array <> cur_array'] (this is [diff_fact])
           implies a contradiction.
	   *)
	let facts = Facts.get_facts_at pp in
	let simp_facts = Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) facts in
	let nsimpfacts = Facts.true_facts_from_simp_facts simp_facts in 
	let diff_fact = Terms.make_or_list (List.map (fun b ->
	  let b_term = Terms.term_from_repl_index b in
	  let b_term' = Terms.term_from_repl_index (Terms.new_repl_index b) in
	  b.ri_link <- TLink b_term';
	  Terms.make_diff b_term b_term'
	    ) cur_array)
	in
	let facts_other_indices = List.map (Terms.copy_term Terms.Links_RI) nsimpfacts in
	List.iter (fun b -> b.ri_link <- NoLink) cur_array;
	let _ = Facts.simplif_add_list Facts.no_dependency_anal simp_facts (diff_fact::facts_other_indices) in
        cleanup();
        raise (Error("The guessed branching instruction must be executed at most once. I did not manage to prove that at occurrence "^(string_of_int state.occ), state.ext_o)) 
      with Contradiction -> 
        (* OK *)
        cleanup()
    end
  
      
let bad_guess_t() =
  Terms.build_term_type Settings.t_any (EventAbortE (Terms.e_bad_guess()))

let rec guess_t state cur_array t =
  if state.occ == t.t_occ then
    if state.to_do then
      let t' = 
	match t.t_desc with
	| TestE(t0,p1,p2) ->
	    begin
	      match state.branch_num with
	      | 0 -> Terms.build_term t (TestE(t0,bad_guess_t(),p2))
	      | 1 -> Terms.build_term t (TestE(t0,p1,bad_guess_t()))
	      | _ -> raise Finished
	    end
	| LetE(pat,t0,p1,popt) ->
	    begin
	      match pat with
	      | PatVar _ -> raise (Error("At occurrence "^(string_of_int state.occ)^", cannot guess branch for let <var> = ...", state.ext_o))
	      | _ -> ()
	    end;
	    begin
	      match state.branch_num with
	      | 0 -> Terms.build_term t (LetE(pat,t0,bad_guess_t(),popt))
	      | 1 -> Terms.build_term t (LetE(pat,t0,p1,Some (bad_guess_t())))
	      | _ -> raise Finished
	    end
	| FindE(l0,p2,find_info) ->
	    begin
	      if l0 == [] then
		raise (Error("At occurrence "^(string_of_int state.occ)^", cannot guess branch for an empty find", state.ext_o));
	      if state.branch_num = 0 then
		Terms.build_term t (FindE(List.map (fun (bl,def_list,t0,p1) ->
		  (bl,def_list,t0,bad_guess_t())
		    ) l0, p2, find_info))
	      else if state.branch_num <= List.length l0 then
		let l0' =
		  List.mapi (fun n (bl,def_list,t0,p1) ->
		    (bl,def_list,t0,
		     if n = state.branch_num-1 then
		       p1
		     else
		       bad_guess_t())
		      ) l0
		in
		Terms.build_term t (FindE(l0', bad_guess_t(),find_info))
	      else
		raise Finished
	    end
	| _ ->
	    raise (Error("At occurrence "^(string_of_int state.occ)^", can guess a branch only for if, let, and find", state.ext_o))
      in
      state.to_do <- false;
      check_unique_exec state (DTerm t) cur_array;
      if state.has_secrecy then
	let b = Terms.create_binder "guess_br_defined" Settings.t_bool cur_array in
	state.guess_br_var <- Some b;
	Terms.build_term_type t.t_type (LetE(PatVar b, Terms.make_true(), t', None))
      else
	t'
    else
      Parsing_helper.internal_error "Ambiguous occurrence. That should never happen"
  else if not (may_be_inside state t.t_occ t.t_max_occ) then
    t
  else
    Terms.build_term t 
	(match t.t_desc with
	  Var(b,l) ->
	    Var(b, List.map (guess_t state cur_array) l)
	| (ReplIndex _ | EventAbortE _) as x -> x
	| FunApp(f,l) ->
	    FunApp(f, List.map (guess_t state cur_array) l)
	| ResE(b,p) ->
	    ResE(b, guess_t state cur_array p)
	| EventE(t1,p) ->
	    EventE(guess_t state cur_array t1,
		   guess_t state cur_array p)
	| GetE _ | InsertE _ ->
	    Parsing_helper.internal_error "get, insert should not occur as term"
	| TestE(t1,t2,t3) ->
	    let t2' = guess_t state cur_array t2 in
	    let t3' = guess_t state cur_array t3 in
	    let t1' = guess_t state cur_array t1 in
	    TestE(t1',t2',t3')
	| LetE(pat,t1,t2,topt) ->
	    let t2' = guess_t state cur_array t2 in
	    let topt' = 
	      match topt with
		None -> None
	      | Some t3 -> Some (guess_t state cur_array t3)
	    in
	    let pat' = guess_pat state cur_array pat  in
	    let t1' = guess_t state cur_array t1 in
	    LetE(pat',t1',t2',topt')
	| FindE(l0,t3, find_info) ->
	    let t3' = guess_t state cur_array t3 in
	    let l0' = List.map (fun (bl, def_list, tc, p) ->
	      let p' = guess_t state cur_array p in
	      let tc' = guess_t state cur_array tc in
	      (bl, def_list, tc', p')
		  ) l0
	    in
	    FindE(l0',t3',find_info))

and guess_pat state cur_array = function
  | PatVar b -> PatVar b
  | PatTuple(f,l) -> PatTuple(f, List.map (guess_pat state cur_array) l)
  | PatEqual t -> PatEqual(guess_t state cur_array t)


let bad_guess_p() = Terms.oproc_from_desc (EventAbort (Terms.e_bad_guess()))
	
let rec guess_i state cur_array p =
  if not (may_be_inside state p.i_occ p.i_max_occ) then
    p
  else
  let p_desc' =
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) ->
      Par(guess_i state cur_array p1,
	  guess_i state cur_array p2)
  | Repl(b,p) ->
      Repl(b, guess_i state (b::cur_array) p)
  | Input((c,tl),pat, p) ->
      let p' = guess_o state cur_array p in
      let pat' = guess_pat state cur_array pat in
      let tl' = List.map (guess_t state cur_array) tl in
      Input((c,tl'),pat',p')
  in
  Terms.iproc_from_desc_loc p p_desc'

and guess_o state cur_array p =
  if state.occ == p.p_occ then
    if state.to_do then
      let p' = 
	match p.p_desc with
	| Test(t,p1,p2) ->
	    begin
	      match state.branch_num with
	      | 0 -> Terms.oproc_from_desc (Test(t,bad_guess_p(),p2))
	      | 1 -> Terms.oproc_from_desc (Test(t,p1,bad_guess_p()))
	      | _ -> raise Finished
	    end
	| Let(pat,t,p1,p2) ->
	    begin
	      match pat with
	      | PatVar _ -> raise (Error("At occurrence "^(string_of_int state.occ)^", cannot guess branch for let <var> = ...", state.ext_o))
	      | _ -> ()
	    end;
	    begin
	      match state.branch_num with
	      | 0 -> Terms.oproc_from_desc (Let(pat,t,bad_guess_p(),p2))
	      | 1 -> Terms.oproc_from_desc (Let(pat,t,p1,bad_guess_p()))
	      | _ -> raise Finished
	    end
	| Find(l0,p2,find_info) ->
	    begin
	      if l0 == [] then
		raise (Error("At occurrence "^(string_of_int state.occ)^", cannot guess branch for an empty find", state.ext_o));
	      if state.branch_num = 0 then
		Terms.oproc_from_desc (Find(List.map (fun (bl,def_list,t,p1) ->
		  (bl,def_list,t,bad_guess_p())
		    ) l0, p2, find_info))
	      else if state.branch_num <= List.length l0 then
		let l0' =
		  List.mapi (fun n (bl,def_list,t,p1) ->
		    (bl,def_list,t,
		     if n = state.branch_num-1 then
		       p1
		     else
		       bad_guess_p())
		      ) l0
		in
		Terms.oproc_from_desc (Find(l0', bad_guess_p(),find_info))
	      else
		raise Finished
	    end
	| _ ->
	    raise (Error("At occurrence "^(string_of_int state.occ)^", can guess a branch only for if, let, and find", state.ext_o))
      in
      state.to_do <- false;
      check_unique_exec state (DProcess p) cur_array;
      if state.has_secrecy then
	let b = Terms.create_binder "guess_br_defined" Settings.t_bool cur_array in
	state.guess_br_var <- Some b;
	Terms.oproc_from_desc (Let(PatVar b, Terms.make_true(), p',
				   Terms.oproc_from_desc Yield))
      else
	p'
    else
      Parsing_helper.internal_error "Ambiguous occurrence. That should never happen"
  else if not (may_be_inside state p.p_occ p.p_max_occ) then
    p
  else
  let p_desc' =
    match p.p_desc with
      Yield -> Yield
    | EventAbort f -> EventAbort f
    | Restr(b,p) ->
	Restr(b, guess_o state cur_array p)
    | Test(t,p1,p2) ->
	let p1' = guess_o state cur_array p1 in
	let p2' = guess_o state cur_array p2 in
	let t' = guess_t state cur_array t in
	Test(t',p1',p2')
    | EventP(t,p) ->
	let p' = guess_o state cur_array p in
	let t' = guess_t state cur_array t in
	EventP(t',p')
    | Let(pat,t,p1,p2) ->
	let p1' = guess_o state cur_array p1 in
	let p2' = guess_o state cur_array p2 in
	let pat' = guess_pat state cur_array pat  in
	let t' = guess_t state cur_array t in
	Let(pat',t',p1',p2')
    | Find(l0,p3,find_info) ->
	let p3' = guess_o state cur_array p3 in
	let l0' = List.map (fun (bl, def_list, t, p1) ->
	  let p1' = guess_o state cur_array p1 in
	  let t' = guess_t state cur_array t in
	  (bl, def_list, t', p1')
	  ) l0
	in
	Find(l0',p3',find_info)
    | Output((c,tl),t,p) ->
	let p' = guess_i state cur_array p in
	let t' = guess_t state cur_array t in
	let tl' = List.map (guess_t state cur_array) tl in
	Output((c,tl'),t',p')
    | Get _ | Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"
  in
  Terms.oproc_from_desc_loc p p_desc'

let update_query v q =
  match q with
  | QSecret(b,pub_vars,one_session) ->
      begin
	match v with
	| None ->
		    (* v must be defined when there is a secrecy query *)
            assert false
	| Some b' ->
	    QSecret(b,b'::pub_vars,one_session)
      end
  | QEventQ _ ->
      q
  | _ ->
      Parsing_helper.internal_error "equivalence queries/absent query should have been eliminated earlier"


let guess_branch occ ext_o state g =
  let p = Terms.get_process g in
  let has_secrecy = ref false in
  List.iter (function ((q,_),_) as q_proof ->
    match q with
    | _ when Settings.get_query_status q_proof != ToProve -> () (* I ignore already proved and inactive queries *)
    | QSecret _ ->
	has_secrecy := true;
    | QEventQ _ -> ()
    | _ ->
	raise (Error("Cannot guess a branch when there is an equivalence query to prove, or no query", ext_o))
	  ) g.current_queries;
  let rec gen_case br_num =
    let loc_state =
      { whole_game = g;
        occ = occ;
	ext_o = ext_o;
	to_do = true;
	branch_num = br_num;
	has_secrecy = !has_secrecy;
	guess_br_var = None }
    in
    let p' = guess_i loc_state [] p in
    if loc_state.to_do then
      raise (Error("Could not find the designated program point (occurrence "^(string_of_int loc_state.occ)^")", ext_o));
    let g' = Terms.build_transformed_game p' g in
    let rest =
      try
	gen_case (br_num + 1)
      with Finished ->
	[]
    in
    (g', loc_state.guess_br_var)::rest
  in
  let g_var_list = gen_case 0 in
  let (g',_) = List.hd g_var_list in
  (* Compute the new queries *)
  (*   Create a new physical place for the proof indication, 
       so that the proof is carried to the father game only when
       it is a full proof *)
  let current_queries' = List.map (fun (q, poptref) -> (q, ref (!poptref))) g.current_queries in
  let new_queries = ref [] in
  List.iter (function ((q, g), proof_opt) as q_proof ->
    if Settings.get_query_status q_proof == ToProve then
          (* I ignore already proved and inactive queries *)
      let add_queries =
	List.map (fun (g_new, v) ->
	  let q' = update_query v q in
	  let proof_opt' = ref (if g_new == g' then ToProve else Inactive) in
	  ((q', g_new), proof_opt')
	    ) g_var_list
      in
      proof_opt := Proved(List.map (fun (qg', proof_opt') ->
	MulQueryProba(Cst 1.0, qg', proof_opt')
	  ) add_queries, state);
      new_queries := add_queries @ (!new_queries)
				     ) current_queries';
  g'.current_queries <- (!new_queries) @ current_queries';
  Settings.changed := true;
  (g', [], [DGuessBranch occ])

(* [next_case state] returns 
   - [Some state'] where [state'] is the state to prove the queries in the next case
   (next branch). 
   - [None] in case all branches have already been proved *)

let next_case state =
  let prev_state = 
    match state.prev_state with
    | Some(GuessBranch _,_,_,prev_state) -> prev_state
    | _ -> assert false
  in
  let is_in_prev_state g =
    List.exists (fun ((q, g'), proof_opt) -> 
      g' == g
        ) prev_state.game.current_queries
  in
  try
    let (_,next_g), _ = 
      List.find (fun ((_,g), proof_opt) ->
        !proof_opt = Inactive && not (is_in_prev_state g)
          ) state.game.current_queries
    in
    List.iter (fun ((_,g),proof_opt) ->
      if g == next_g then
        begin
          assert (!proof_opt = Inactive);
          proof_opt := ToProve
        end
          ) state.game.current_queries;
    next_g.current_queries <- state.game.current_queries;
    Some (next_g)
  with Not_found ->
    (* When [next_g] is not found, all cases of the GuessBranch instruction
       have been proved *)
    None
