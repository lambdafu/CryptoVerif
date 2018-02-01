open Types
open Terms

(* TO DO integrate this in the terms.ml module; pass is_var_inst and explicit_value as arguments
 *)

let no_advice_mode = ref false (* TO DO comes from transf_crypto *)

(* [is_var_inst]: [is_var_inst t] returns true when [t] is a variable
   that may be replaced by a product after applying advice. *)

let is_var_inst t =
  match t.t_desc with
    Var(b,_) ->
      if (!no_advice_mode) || (not (List.exists (function 
        { definition = DProcess { p_desc = Let _ }} -> true
      | { definition = DTerm { t_desc = LetE _ }} -> true
      | _ -> false) b.def)) then
        false
      else
        true
  | _ -> false

let explicit_value b = (* TO DO comes from transf_crypto *)
    match b.def with
      [] | [_] -> RemoveAssign (OneBinder b)
    | _ -> SArenaming b

type state_t = (* TO DO comes from transf_crypto *)
    { advised_ins : instruct list;
      sthg_discharged : bool;
      names_to_discharge : name_to_discharge_t;
      priority : int;
      lhs_array_ref_map : ((binder * term list) * term) list;
      name_indexes : ((binder * term list) * term list) list }

let explicit_value t state =
  match t.t_desc with
    Var(b,_) -> 
      { state with advised_ins = Terms.add_eq (explicit_value b) state.advised_ins }
  | _ -> Parsing_helper.internal_error "Var expected (should have been checked by is_var_inst)"

(*********** Matching modulo equational theory, with advice *************)
(*********** for use in transf_crypto.ml                    *************)

(* Common arguments for the matching functions:

   [match_term]: [match_term next_f t1 t2 state] matches [t1] with [t2];
   calls [next_f state'] when the match succeeds; raises NoMatch when it
   fails. It must clean up the links it has put at least when it fails.
   (When it succeeds, the cleanup is optional.)

   [explicit_value]: [explicit_value t state] returns a state in which 
   the advice needed to instantiate the variable [t] has been recorded.
   Causes an internal error when [t] is not a variable.

   [get_var_link]: [get_var_link t state] returns [Some (link, allow_neut)]
   when [t] is variable that can be bound by a product of terms,
   [link] is the current contents of the link of that variable,
   [allow_neut] is true if and only if the variable may be bound to
   the neutral element (provided there is a neutral element for the
   product); it returns [None] otherwise.

   [is_var_inst]: [is_var_inst t] returns [true] when [t] is a variable
   that can be instantiated by applying advice.

   [prod] is the product function symbol, which is associative or AC.
   *)

(* [prod_has_neut prod] returns true if and only if the product
   [prod] has a neutral element. *)

let prod_has_neut prod =
  (* Look for the neutral element of the product *)
  match prod.f_eq_theories with
    Group(_,_,n) | CommutGroup(_,_,n) | AssocN(_,n) 
  | AssocCommutN(_,n) | ACUN(_,n) -> true
  | _ -> false

(* Matching modulo associativity, plus perhaps neutral element *)


(* [match_assoc_advice match_term explicit_value get_var_link is_var_inst next_f prod l1 l2 state]
   matches the lists [l1] and [l2] modulo associativity. 
   It calls [next_f state'] after linking variables in [l1]
   so that [\sigma l1 = l2] modulo associativity.

   [fresh_vars_init] contains fresh variables created for the matching.

   [match_assoc_advice] is programmed like unification modulo associativity, 
   because in the second term, variables may be instantiated by advice. 

   For this to work, either the function match_term must also be programmed as
   unification (i.e. be invariant by swapping l1 and l2). This would imply modifying
   check_instance_of_rec, match_funapp, match_AC. 
   Or we need a reliable way to attribute each element to its source (the pattern
   or the instance), to call match_term in the right direction. When both
   elements come from the instance, we can just test equality. Both elements
   cannot come from the pattern, because we do not put explicit links in the
   advice variables. We have chosen this second implementation. *)

type var_type =
    Fresh | Advice | Pat

let match_assoc_advice match_term explicit_value get_var_link is_var_inst fresh_vars_init next_f prod l1 l2 state =
  (* [has_neut] is true iff there is a neutral element for the product [prod]. *)
  let has_neut = prod_has_neut prod in

  let fresh_vars = ref fresh_vars_init in

  let put_side s l =
    List.map (fun t ->
      match t.t_desc with
	Var(b,_) when List.memq b (!fresh_vars) -> (Fresh, t)
      |	_ -> (s, t)) l
  in

  (*
   [get_var_link_unif]: [get_var_link_unif t state] returns 
   [Some(link, allow_neut, var_advice, shortest)] when [t] is a variable
   can that be bound to a product using [prod]. 
   [link] is the current link of that variable.
   [allow_neut] is true if and only if that variable may be bound to 
   the neutral element of the product [prod] (when it has a neutral element).
   [var_advice] is true if and only if the variable is to be 
   instantiated using advice. 
   [shortest] is true if and only if we should try first to 
   instantiate the variable with a product containing as few terms
   as possible.
   Otherwise, [get_var_link_unif] returns None.
   The function [get_var_link_unif] is programmed using
   the functions [get_var_link] and [is_var_inst].
  *)

  let get_var_link_unif (side, t) state =
    (* fresh variables created during the matching *)
    match side with
      Fresh ->
	begin
	  match t.t_desc with
	    Var(b,_) -> Some(b.link, false, Fresh, true)
	  | _ -> Parsing_helper.internal_error "get_var_link_unif: Fresh variables should be variables!"
	end
    | Advice ->
      (* variables are advice variables *)
	if is_var_inst t then
	  Some(NoLink, true, Advice, true)
	else
	  None
    | Pat ->
      (* variables are variables from the pattern *)
	match get_var_link t state with
	  None -> None
	| Some(l, allow_neut) -> 
	    Some(l, allow_neut, Pat, false)
  in

  let assign_var next_f (side, tvar) l state =
    match tvar.t_desc with
      Var(b,_) -> 
	begin
          (* check that tvar does not occur in l! *)
	  if List.exists (fun (_,t) -> refers_to b t) l then
	    raise NoMatch;
	  match side with
	    Advice -> next_f (explicit_value tvar state)
	  | Fresh ->
	      if List.exists (fun (side,_) -> side == Pat) l then
		(* Ignore the link when it points to a Pat term, so
                   that, when we will expend the link, we can give it
		   side Advice (or Fresh when it is a fresh variable).
		   TO DO I'm not entirely sure if this can happen for variables
		   other than the two variables b_left and b_right that come
		   from match_assoc_advice_pat_subterm.
		   Perhaps I could raise an internal error for the other variables... *)
		next_f state
	      else
		let tval = make_prod prod (List.map snd l) in
		auto_cleanup (fun () ->
		  link b (TLink tval);
		  next_f state
		    )
	  | Pat ->
	      if List.exists (fun (side,_) -> side == Pat) l then
		Parsing_helper.internal_error "Pat variables should be linked to non-Pat terms";
	      let tval = make_prod prod (List.map snd l) in	      
	      match_term next_f tvar tval state
	end
    | _ -> Parsing_helper.internal_error "assign_var: Variable expected"
  in

  let match_term_orient next_f (side1,t1) (side2,t2) state =
    match side1, side2 with
      Fresh, _ | _, Fresh -> Parsing_helper.internal_error "match_term_orient: Fresh variables should have been treated before"
    | Advice, Advice ->
	if not (equal_terms t1 t2) then raise NoMatch;
	next_f state
    | Advice, Pat -> match_term next_f t2 t1 state
    | Pat, Advice -> match_term next_f t1 t2 state
    | Pat, Pat -> Parsing_helper.internal_error "match_term_orient: terms should not come both from the pattern"
  in

  (* Invariant: one of the two lists [l1] (with [tvar] in [try_prefix]) or 
     [l2] (with [seen] in [try_prefix]) entirely comes from the game
     (all its elements have side Advice or Fresh). The other list may 
     contain a mix of sides Pat, Advice, and Fresh, since links
     from Pat to Advice may be replaced with their content. *)

  (* try to match [tvar . l1 = seen . l2] where [tvar] is a variable *)

  let rec try_prefix tvar l1 seen l2 state =
    match get_var_link_unif tvar state with
      None | Some(TLink _,_,_,_) -> Parsing_helper.internal_error "try_prefix: Should be a variable"
    | Some(NoLink, allow_neut, var_type, shortest) ->
	try 
	  if shortest then
	    try
            (* tvar = seen *)
	      if seen = [] && not (has_neut && allow_neut) then raise NoMatch;
	      assign_var (match_assoc_rec l1 l2) tvar seen state
	    with NoMatch ->
              (* If it does not work, try with one more element *)
	      match l2 with
		[] -> raise NoMatch
	      | a::r -> try_prefix tvar l1 (seen @ [a]) r state
	  else
	    (* For variables of the pattern (shortest = false),
	       I try the prefixes by first trying l2 entirely, then removing the
	       last element of l2, etc. until I try the empty list. 
	       The reason for this order is that, in case we match a subterm of the
	       product, we want to take the largest possible subterm that works. *)
	    try 
	      match l2 with
		[] -> raise NoMatch
	      | a::r -> try_prefix tvar l1 (seen @ [a]) r state
	    with NoMatch ->
              (* tvar = seen *)
	      if seen = [] && not (has_neut && allow_neut) then raise NoMatch;
	      assign_var (match_assoc_rec l1 l2) tvar seen state
	with NoMatch ->
	  match l2 with
	    [] -> raise NoMatch
	  | a::r -> 
	      match get_var_link_unif a state with
		None -> raise NoMatch
	      | Some(TLink t, _, _, _) -> 
		  let l2' = simp_prod try_no_var_id (ref false) equal_terms prod t in
		  try_prefix tvar l1 seen ((put_side Advice l2') @ r) state
	      | Some(NoLink, _, _, _) ->
		  let x = create_binder "@$match_var" (new_vname()) (snd prod.f_type) [] in
		  fresh_vars := x :: (!fresh_vars);
		  let x_term = term_from_binder x in
	          (* tvar = seen . x ; a = x . (some prefix of l1 to be defined) *)
		  assign_var (try_prefix a r [Fresh,x_term] l1) 
		    tvar (seen @ [Fresh,x_term]) state
		    
  and match_var status1 l1 l2 state =
    match l1 with
      [] -> Parsing_helper.internal_error "match_var: l1 should not be empty"
    | t1::r1 ->
    match status1 with
      None | Some (TLink _, _, _, _) -> Parsing_helper.internal_error "match_var: get_var_link_unif should be Some(NoLink, ...)"
    | Some (NoLink, allow_neut, var_type, shortest) ->
	match l2 with
	  t2::r2 when equal_terms (snd t1) (snd t2) -> 
	    match_assoc_rec r1 r2 state
	| _ ->
	    if (r1 == []) then
	      begin
	        (* If variable t1 is alone, that's easy: t1 should be linked to l2 *)
		if (not (has_neut && allow_neut)) && (l2 == []) then raise NoMatch;
		assign_var next_f t1 l2 state
	      end
	    else
	      begin
	        (* try to see if the end of the list contains something that is not an unbound variable *)
		let l1rev = List.rev l1 in
		let l2rev = List.rev l2 in
		if (match get_var_link_unif (List.hd l1rev) state with
		     Some (NoLink, _, _, _) -> true
		   | _ -> false) ||
		     ((l2 != []) && 
		      (match get_var_link_unif (List.hd l2rev) state with
			Some (NoLink, _, _, _) -> true
		      | _ -> false))
		then
		  (* l1 starts and ends with a variable, I really need to try all prefixes
		     of l2 as values for variable v. That can be costly. *)
		  try_prefix t1 r1 [] l2 state
		else
		  match_assoc_rec l1rev l2rev state
	      end

  and match_assoc_rec l1 l2 state =
    let status1 =
      match l1 with
	[] -> None
      |	t1::_ -> get_var_link_unif t1 state
    in
    let status2 =
      match l2 with
	[] -> None
      |	t2::_ -> get_var_link_unif t2 state
    in
    match l1, status1, l2, status2 with
    | [], _, [], _ -> next_f state 
    | t1::r1, Some(TLink t,_,_,_), _, _ ->
	let l1' = simp_prod try_no_var_id (ref false) equal_terms prod t in
	match_assoc_rec ((put_side Advice l1') @ r1) l2 state
    | _, _, t2::r2, Some(TLink t,_,_,_) ->
	let l2' = simp_prod try_no_var_id (ref false) equal_terms prod t in
	match_assoc_rec l1 ((put_side Advice l2') @ r2) state
    | t1::r1, Some(NoLink,_,(Pat|Fresh),_), _, _ ->
	match_var status1 l1 l2 state
    | _, _, t2::r2, Some(NoLink,_,(Pat|Fresh),_) ->
	match_var status2 l2 l1 state
    | t1::r1, Some(NoLink,_,Advice,_), _, _ ->
	match_var status1 l1 l2 state
    | _, _, t2::r2, Some(NoLink,_,Advice,_) ->
	match_var status2 l2 l1 state
    | [], _, _, _ -> raise NoMatch
    | _, _, [], _ -> raise NoMatch
    | t1::r1, _, t2::r2, _ -> 
	match_term_orient (match_assoc_rec r1 r2) t1 t2 state

  in
  match_assoc_rec (put_side Pat l1) (put_side Advice l2) state
		    
(* [match_assoc_advice_subterm match_term explicit_value get_var_link is_var_inst next_f prod l1 l2 state]
   matches the lists [l1] and [l2] modulo associativity. 
   More precisely, it calls [next_f left_rest right_rest state']  after linking variables in [l1]
   so that [left_rest. \sigma l1 . right_rest = l2] modulo associativity. *)

let match_assoc_advice_subterm match_term explicit_value get_var_link is_var_inst next_f prod l1 l2 state =
  let b_right = create_binder "@$special_var_allow_rest" (new_vname()) (snd prod.f_type) [] in
  let b_left = create_binder "@$special_var_allow_rest" (new_vname()) (snd prod.f_type) [] in
  let l1' = term_from_binder b_left :: l1 @ [term_from_binder b_right] in
  let next_f_unif state = 
    let right_rest = 
      match b_right.link with
	NoLink -> []
      | TLink t -> simp_prod try_no_var_id (ref false) equal_terms prod t
    in
    let left_rest = 
      match b_left.link with
	NoLink -> []
      | TLink t -> simp_prod try_no_var_id (ref false) equal_terms prod t
    in
    next_f left_rest right_rest state
  in
  match_assoc_advice match_term explicit_value get_var_link is_var_inst [b_left; b_right] next_f_unif prod l1' l2 state 

(* [match_assoc_advice_pat_subterm match_term explicit_value get_var_link is_var_inst next_f prod l1 l2 state]
   matches the lists [l1] and [l2] modulo associativity. 
   More precisely, it calls [next_f state']  after linking variables in [l1]
   so that [\sigma l1 = left_rest . l2 . right_rest] modulo associativity.
   [left_rest] and [right_rest] are just ignored, they are not passed to [next_f]. *)

let match_assoc_advice_pat_subterm match_term explicit_value get_var_link is_var_inst next_f prod l1 l2 state =
  let b_right = create_binder "@$special_var_allow_rest" (new_vname()) (snd prod.f_type) [] in
  let b_left = create_binder "@$special_var_allow_rest" (new_vname()) (snd prod.f_type) [] in
  let l2' = term_from_binder b_left :: l2 @ [term_from_binder b_right] in
  match_assoc_advice match_term explicit_value get_var_link is_var_inst [b_left; b_right] next_f prod l1 l2' state 

(* Matching modulo associativity and commutativity, plus perhaps neutral element *)

(* [match_AC_advice match_term explicit_value get_var_link is_var_inst next_f prod allow_rest_pat allow_rest l1 l2 state]
   matches the lists [l1] and [l2] modulo AC. 
   When [allow_rest] is false, it calls [next_f [] state'] after linking variables in [l1]
   so that [\sigma l1 = l2] modulo AC. 
   When [allow_rest] is true, it calls [next_f lrest state']  after linking variables in [l1]
   so that [\sigma l1 . lrest = l2] modulo AC. 

   [allow_rest_pat] is true when a subterm of the pattern in [l1] should match
   [l2], so that some elements of [l1] are allowed to remain unmatched.

   [allow_rest] is true when the pattern in [l1] should match a subterm of 
   the term in [l2], so that some elements of [l2] are allowed to remain unmatched.
*)

let match_AC_advice match_term explicit_value get_var_link is_var_inst next_f prod allow_rest_pat allow_rest l1 l2 state =
  let has_neut = prod_has_neut prod in
  if (not has_neut) && (List.length l1 > List.length l2) then raise NoMatch else 

  let final_step next_f l2 state =
    if (l2 == []) then next_f [] l2 state else raise NoMatch
  in

  let rec all_possible_explicit_value l state =
    match l with
      [] -> state
    | t::r ->
	if is_var_inst t then
	  all_possible_explicit_value r (explicit_value t state)
	else
	  all_possible_explicit_value r state
  in

  let rec split_among_vars_with_possible_rest next_f vl l state =
    match vl with
      [] -> next_f l state
    | v :: rest_vl ->
      (* Split [l] into two disjoint subsets, one that matches [v], the other that
	 matches [rest_vl]. We start with [l] matching [v] and the empty list matching
	 [rest_vl], and continue with fewer and fewer elements matching [v]. *)
	let len_l = List.length l in
	let allow_neut = 
	  match get_var_link v state with
	    None -> Parsing_helper.internal_error "get_var_link should return a link"
	  | Some(_, allow_neut) -> allow_neut
	in
	let rec partition_n n =
	  (* Considers a partition in which a sublist of [l] of [n] elements matches
	     [rest_vl] and the rest of [l], of [len_l - n] elements matches [v]. *) 
	  if n > len_l then raise NoMatch else
	  if (n = len_l) && (not (has_neut && allow_neut)) then raise NoMatch else
	  try 
	    split_n default_match_error (fun n_elem rest ->
	      match_term (split_among_vars_with_possible_rest next_f rest_vl n_elem) v (make_prod prod rest) state
		) [] [] n l
	  with NoMatch ->
	    partition_n (n+1)
	in
	partition_n 0
  in

  let rec match_variable_groups next_f g l2 state =
    match g with
      [] -> final_step next_f l2 state
    | (c, vl) :: rest ->
        (* Separate l2 into the elements that are present at least
	   [c] times and the others *)
	if c > 1 then
	  let (at_least_c, not_at_least_c) = sep_at_least_occ try_no_var_id c l2 in
	  split_among_vars_with_possible_rest (fun rest_l2 state' ->
	    let real_rest_l2 = append_n_times not_at_least_c c rest_l2 in
	    match_variable_groups next_f g real_rest_l2 state'
	      )  vl at_least_c state
	else
	  begin
	    assert(rest == []);
	    split_among_vars_with_possible_rest (final_step next_f) vl l2 state
	  end
  in
  
  let rec match_remaining_vars next_f remaining_vars l2 state =
    match remaining_vars with
      [] -> 
	final_step next_f l2 state
    | [t] when not allow_rest ->
	let allow_neut = 
	  match get_var_link t state with
	    None -> Parsing_helper.internal_error "get_var_link should return a link"
	  | Some(_, allow_neut) -> allow_neut
	in
	if (not (has_neut && allow_neut)) && (l2 == []) then raise NoMatch else
	match_term (next_f [] []) t (make_prod prod l2) state
    | _ -> 
        (* Count the number of occurrences of variables in [remaining_vars] *)
	let var_occs = count_occ [] remaining_vars in
        (* Sort the variables in decreasing number of occurrences *)
	let var_occs_sorted = List.sort (fun (v1, c1) (v2, c2) -> (!c2) - (!c1)) var_occs in
	match var_occs_sorted with
          (vmax, cmax) :: rest ->
	    let g = group_same_occ (!cmax, [vmax]) rest in
	    match_variable_groups next_f g l2 state
	| _ -> Parsing_helper.internal_error "Should have at least one variable"	
  in

  let rec match_AC_rec next_f advice_delayed remaining_vars l1 l2 state =
    match l1 with
      [] -> 
	if List.exists (fun t -> 
	  match get_var_link t state with 
	    Some (TLink _, _) -> true
	  | _ -> false) remaining_vars then
	  match_AC_rec next_f advice_delayed [] remaining_vars l2 state
	else
	  begin
	    try
	      if advice_delayed != [] then raise NoMatch;
	      match_remaining_vars next_f remaining_vars l2 state
	    with NoMatch ->
	      let (with_advice, without_advice) = List.partition is_var_inst l2 in
	      if (with_advice = []) && not allow_rest_pat then 
		(* there remains unmatched elements in l1, the elements of [advice_delayed] and [remaining_vars],
		   except in case they are both empty. In this case, [allow_rest = false] and [l2 != []], otherwise
		   [match_remaining_vars] would have succeeded; since [with_advice = []], [without_advice != []],
		   so in this case, there remains unmatched elements in l2, the elements of [without_advice]. *)
		raise NoMatch;
	      if without_advice != [] && (not allow_rest) && remaining_vars = [] then 
		(* there remains unmatched elements in l2, the elements of [without_advice] *)
		raise NoMatch;
	      if allow_rest && (remaining_vars = []) then
		(* Since there are no remaining variables, at least the terms
		   in [without_advice] cannot be matched by the expression,
		   so they end up in the rest part passed to next_f. *)
		next_f [] without_advice (all_possible_explicit_value with_advice state)
	      else if with_advice = [] then
		(* allow_rest_pat must be true *)
		next_f advice_delayed [] state
	      else
		next_f [] [] (all_possible_explicit_value with_advice state)
	  end
    | t1::r1 ->
	match get_var_link t1 state with
	  None ->
	    (* Try to match t1 with an element of l2, and 
	       r1 with the rest of l2. *)
	    let rec try_list seen = function
		[] -> 
		  (* In case an element of l2 may be instantiated by
		     advice, delay the treatment of t1 *)
		  if allow_rest_pat || (List.exists is_var_inst l2) then
		    match_AC_rec next_f (t1::advice_delayed) remaining_vars r1 l2 state
		  else
		    raise NoMatch
	      | t2::r2 ->
		  let l2' = List.rev_append seen r2 in
		  try
		    match_term (match_AC_rec next_f advice_delayed remaining_vars r1 l2') t1 t2 state
		  with NoMatch ->
		    try_list (t2::seen) r2
	    in
	    try_list [] l2
	| Some (TLink t, _) ->
	    let l1' = simp_prod try_no_var_id (ref false) equal_terms prod t in
	    begin
	      try 
		let r2 = multiset_minus try_no_var_id l2 l1' in
		match_AC_rec next_f advice_delayed remaining_vars r1 r2 state
	      with Not_found -> 
		(* In case an element of l2 may be instantiated by
		   advice, delay the treatment of t1 *)
		if allow_rest_pat || (List.exists is_var_inst l2) then
		  match_AC_rec next_f (t1::advice_delayed) remaining_vars r1 l2 state
		else
		  raise NoMatch
	    end
	| Some (NoLink, _) ->
	    match_AC_rec next_f advice_delayed (t1::remaining_vars) r1 l2 state
  in

  match_AC_rec next_f [] [] l1 l2 state

(* Match function application *)

let match_funapp_advice match_term explicit_value get_var_link is_var_inst next_f t t' state =
  if t.t_type != t'.t_type then raise NoMatch else
  match t.t_desc, t'.t_desc with
  | FunApp(f, [t1;t2]), FunApp(f', [t1';t2']) when 
    f == f' && (f.f_cat == Equal || f.f_cat == Diff) ->
	(* It is important to test this case before the commutative
	   function symbols: = and <> are also commutative function
	   symbols. *)
      begin
	match (match get_prod_list try_no_var_id [t1;t2] with
	         NoEq -> get_prod_list try_no_var_id [t1';t2']
	       | x -> x)
	with
	  ACUN(xor,_) ->
	    match_term next_f (app xor [t1;t2]) (app xor [t1';t2']) state
	| CommutGroup(prod,inv,_) ->
	    begin
	      try
		match_term next_f (app prod [t1; app inv [t2]])
		  (app prod [t1'; app inv [t2']]) state
	      with NoMatch ->
		match_term next_f (app prod [t1; app inv [t2]])
		  (app prod [t2'; app inv [t1']]) state
	    end
        | Group(prod,inv,neut) -> 
            begin
	      let l1 = simp_prod try_no_var_id (ref false) equal_terms prod (app prod [t1; app inv [t2]]) in
	      let l2 = remove_inverse_ends try_no_var_id (ref false) (prod, inv, neut) (simp_equal_terms try_no_var_id) l1 in
	      let l1' = simp_prod try_no_var_id (ref false) equal_terms prod (app prod [t1'; app inv [t2']]) in
	      let l2' = remove_inverse_ends try_no_var_id (ref false) (prod, inv, neut) equal_terms l1' in
	      let rec match_assoc_up_to_roll seen' rest' =
		try
		  match_assoc_advice match_term explicit_value get_var_link is_var_inst [] next_f prod l2 (rest' @ (List.rev seen')) state
		with NoMatch ->
		  match rest' with
		    [] -> raise NoMatch
		  | a::rest'' ->
		      match_assoc_up_to_roll (a::seen') rest''
	      in
	      try
		match_assoc_up_to_roll [] l2'
	      with NoMatch ->
		let l3' = List.rev (List.map (compute_inv try_no_var_id (ref false) (prod, inv, neut)) l2') in
		match_assoc_up_to_roll [] l3'
	    end
	| _ -> 
	    (* Fall back to the basic commutativity case when there is
	       no product. *)
            try
	      match_term (match_term next_f t2 t2') t1 t1' state
            with NoMatch ->
              match_term (match_term next_f t2 t1') t1 t2' state
      end
  | FunApp(f, [t1; t2]), FunApp(f', [t1';t2']) when (f == f') && (f.f_eq_theories = Commut) ->
      begin
        try
	  match_term (match_term next_f t2 t2') t1 t1' state
        with NoMatch ->
          match_term (match_term next_f t2 t1') t1 t2' state
      end
  | FunApp({f_eq_theories = (Group(f,inv',n) | CommutGroup(f,inv',n)) } as inv, [t]), _ when inv' == inv ->
      let t''inv = compute_inv try_no_var_id (ref false) (f,inv,n) t' in
      match_term next_f t t''inv state
  | FunApp(f,[_;_]),_ when f.f_eq_theories != NoEq && f.f_eq_theories != Commut ->
      (* f is a binary function with an equational theory that is
	 not commutativity -> it is a product-like function *)
      begin
	let l = simp_prod try_no_var_id (ref false) equal_terms f t in
	let l' = simp_prod try_no_var_id (ref false) equal_terms f t' in
	match f.f_eq_theories with
	  NoEq | Commut -> Parsing_helper.internal_error "Terms.match_funapp_advice: cases NoEq, Commut should have been eliminated"
	| AssocCommut | AssocCommutN _ | CommutGroup _ | ACUN _ ->
	    (* Commutative equational theories: use matching modulo AC *)
	    match_AC_advice match_term explicit_value get_var_link is_var_inst (fun _ _ state -> next_f state) f false false l l' state
	| Assoc | AssocN _ | Group _ -> 
	    (* Non-commutative equational theories: use matching modulo associativity *)
	    match_assoc_advice match_term explicit_value get_var_link is_var_inst [] next_f f l l' state
	      (* Above, I ignore on purpose group and XOR properties,
		 they would yield too general and counter-intuitive matchings. *)
      end
  | FunApp(f,l), FunApp(f',l') when f == f' ->
      match_term_list match_term next_f l l' state
  | _ -> raise NoMatch
