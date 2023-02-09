open Types

(*********** Matching modulo equational theory *************)

(* Common arguments for the matching functions:

   [match_term]: [match_term next_f t1 t2 state] matches [t1] with [t2];
   calls [next_f state'] when the match succeeds; raises NoMatch when it
   fails. It must clean up the links it has put at least when it fails.
   (When it succeeds, the cleanup is optional.)

   [get_var_link]: [get_var_link t state] returns [Some (link, allow_neut)]
   when [t] is variable that can be bound by a product of terms,
   [link] is the current contents of the link of that variable,
   [allow_neut] is true if and only if the variable may be bound to
   the neutral element (provided there is a neutral element for the
   product); it returns [None] otherwise.

   [match_error]: [match_error()] is called in case of matching error.
   (In most cases, [match_error] should be [default_match_error]
   which raises the [NoMatch] exception.)

   [simp_facts] collects the rewrite rules corresponding to known equalities
   and other known facts, which we use in order to replace variables with their values and
   to test equality between terms.

   [prod] is the product function symbol, which is associative or AC.

   [allow_rest] is true when we match inside a subterm, so that some
   elements of the products are allowed to remain unmatched.
   *)


let default_match_error() = raise NoMatch

(* [prod_has_neut prod] returns true if and only if the product
   [prod] has a neutral element. *)

let prod_has_neut prod =
  (* Look for the neutral element of the product *)
  match prod.f_eq_theories with
    Group(_,_,n) | CommutGroup(_,_,n) | AssocN(_,n) 
  | AssocCommutN(_,n) | ACUN(_,n) -> true
  | _ -> false

(* Matching modulo associativity, plus perhaps neutral element *)

(* [remove_list_prefix simp_facts l1 l2] checks that [l1] is equal to a prefix of [l2],
   and returns the remaining suffix of [l2] after removing [l1]. *)

let rec remove_list_prefix simp_facts l1 l2 =
  match (l1,l2) with
    [], _ -> l2
  | _::_, [] -> raise Not_found
  | t1::r1, t2::r2 ->  
      if not (Terms.simp_equal_terms simp_facts true t1 t2) then raise Not_found;
      remove_list_prefix simp_facts r1 r2

let final_step match_error next_f allow_rest l2 state =
  if (l2 == []) || allow_rest then next_f l2 state else match_error()


(* [match_assoc match_term get_var_link match_error next_f simp_facts prod allow_rest l1 l2 state]
   matches the lists [l1] and [l2] modulo associativity. 
   When [allow_rest] is false, it calls [next_f [] state'] after linking variables in [l1]
   so that [\sigma l1 = l2] modulo associativity. 
   When [allow_rest] is true, it calls [next_f lrest state']  after linking variables in [l1]
   so that [\sigma l1 . lrest = l2] modulo associativity. *)

let match_assoc match_term get_var_link match_error next_f simp_facts prod allow_rest l1 l2 state =
  (* [has_neut] is true iff there is a neutral element for the product [prod]. *)
  let has_neut = prod_has_neut prod in
  if (not has_neut) && (List.length l1 > List.length l2) then match_error() else

  (* is_rev is true when the lists l1 and l2 have been reversed.
     In this case, when a variable is assigned or read, its content
     must also be reversed. *)
  let rec match_assoc_rec is_rev l1 l2 state =
    match l1 with
    | [] -> final_step match_error next_f allow_rest l2 state
    | t1::r1 ->
	match get_var_link t1 state, l2 with
	  None, [] -> match_error()
	| None, t2::r2 -> 
	    match_term (match_assoc_rec is_rev r1 r2) t1 t2 state
	| Some (TLink t, _), _ ->
            let l1' = Terms.simp_prod simp_facts (ref false) prod t in
	    let l1' = if is_rev then List.rev l1' else l1' in
	    begin
	      try 
		let r2 = remove_list_prefix simp_facts l1' l2 in
		match_assoc_rec is_rev r1 r2 state
	      with Not_found -> match_error()
	    end
	| Some (NoLink, allow_neut), _ ->
	    if (not allow_rest) && (r1 == []) then
	      begin
	        (* If variable v is alone, that's easy: v should be linked to l2 *)
		if (not (has_neut && allow_neut)) && (l2 == []) then match_error() else
		let t' = Terms.make_prod prod (if is_rev then List.rev l2 else l2) in
		match_term (next_f []) t1 t' state
	      end
	    else
	      begin
	        (* try to see if the end of the list contains something that is not an unbound variable *)
		let l1rev = List.rev l1 in
		if allow_rest || (match get_var_link (List.hd l1rev) state with
		                    Some (NoLink, _) -> true
		                  | _ -> false) then
		  (* l1 starts and ends with a variable, I really need to try all prefixes
		     of l2 as values for variable v. That can be costly.
		     I try the prefixes by first trying l2 entirely, then removing the
		     last element of l2, etc. until I try the empty list. 
		     The reason for this order is that, in case we match a subterm of the
		     product, we want to take the largest possible subterm that works. *)
		  let rec try_prefixes seen r2 =
		    try 
		      (* Try with at least one more element as seen if possible *)
		      match r2 with
			[] -> match_error()
		      | a::l -> 
			  if (not has_neut) && (List.length r1 > List.length l) then match_error() else
			  try_prefixes (seen @ [a]) l
		    with NoMatch ->
		      (* Try the list "seen" *)
		      if (seen == []) && (not (has_neut && allow_neut)) then match_error() else
		      match_term (match_assoc_rec is_rev r1 r2) t1 
			(Terms.make_prod prod (if is_rev then List.rev seen else seen)) state;
		  in
		  try_prefixes [] l2
		else
		  let l2rev = List.rev l2 in
		  match_assoc_rec (not is_rev) l1rev l2rev state
	      end
  in
  match_assoc_rec false l1 l2 state

(* [match_assoc_subterm match_term get_var_link next_f simp_facts prod l1 l2 state]
   matches the lists [l1] and [l2] modulo associativity. 
   More precisely, it calls [next_f left_rest right_rest]  after linking variables in [l1]
   so that [left_rest. \sigma l1 . right_rest = l2] modulo associativity. *)

let match_assoc_subterm match_term get_var_link next_f simp_facts prod l1 l2 state =
  let rec try_prefix seen l =
    try
      (* Try to match [l1] with [l], assuming [seen] will be the left rest of the subterm *)
      match_assoc match_term get_var_link default_match_error (fun right_rest -> next_f seen right_rest) simp_facts prod true l1 l state
    with NoMatch ->
      (* If it does not work, try with one more element in the left rest *)
      match l with
	[] -> raise NoMatch
      |	a::r -> 
	  try_prefix (seen @ [a]) r
  in
  try_prefix [] l2

(* Matching modulo associativity and commutativity, plus perhaps neutral element *)

(* [remove_elem simp_facts a l] returns list [l] after removing element [a] *)

let rec remove_elem simp_facts a = function
    [] -> raise Not_found
  | a'::l ->
      if Terms.simp_equal_terms simp_facts true a a' then l else
      a'::(remove_elem simp_facts a l)
	  
(* [multiset_minus simp_facts l lrem] returns list [l] after removing
   the elements in [lrem] *)

let rec multiset_minus simp_facts l = function
    [] -> l
  | a::r ->
      multiset_minus simp_facts (remove_elem simp_facts a l) r

let rec count_occ list_occ = function
    [] -> list_occ
  | (v::l) ->
      try
	let count = List.assq v list_occ in
	incr count;
	count_occ list_occ l
      with Not_found ->
	count_occ ((v, ref 1)::list_occ) l

let rec group_same_occ ((n, vl) as current_group) = function
    [] -> [current_group]
  | (v, c)::r ->
      if !c = n then
	group_same_occ (n, v::vl) r
      else
	(n, vl) :: (group_same_occ (!c, [v]) r)
	

let rec remove_n_times simp_facts n a l = 
  if n = 0 then l else
  match l with
    [] -> raise Not_found
  | a'::l' ->
      if Terms.simp_equal_terms simp_facts true a a' then
	remove_n_times simp_facts (n-1) a l'
      else
	a' :: (remove_n_times simp_facts n a l')

(* [sep_at_least_occ simp_facts n l] returns a pair [(l1,l2)] where
   [l] contains at least [n] times the elements in [l1], and [l2]
   consists of the remaining elements of [l]: the elements of [l] are
   [n] times the elements of [l1] plus the elements of [l2]; [l2]
   never contains [n] times the same element. *)

let rec sep_at_least_occ simp_facts n = function
    [] -> [], []
  | a::l ->
      try 
	let l' = remove_n_times simp_facts (n-1) a l in
	let (at_least_n, not_at_least_n) = sep_at_least_occ simp_facts n l' in
	(a::at_least_n, not_at_least_n)
      with Not_found ->
	let (at_least_n, not_at_least_n) = sep_at_least_occ simp_facts n l in
	(at_least_n, a::not_at_least_n)

(* [append_n_times accu n l] returns the concatenation
   of [n] copies of [l] and [accu]. (Assumes n >= 0.) *)

let rec append_n_times accu n l =
  if n = 0 then
    accu 
  else
    append_n_times (l @ accu) (n-1) l

(* [split_n next_f [] [] n l] splits the list [l] into a list of [n]
   elements and the rest, and calls [next_f] with the two lists. When
   [next_f] raises [NoMatch], try another partition of [l] (with the
   same numbers of elements).  Raises [NoMatch] when no partition
   works.

   Inside the induction, [split_n next_f n_part rest n l] splits the
   list [l] into a list [l1] of [n] elements and the rest [l2], and
   calls [next_f] with [l1 @ n_part] and [l2 @ rest] (reversed).
 *)

let rec split_n match_error next_f n_part rest n l =
  if n = 0 then
    next_f n_part (List.rev_append rest l)
  else
    match l with
      [] -> match_error()
    | a::r ->
	try 
	  split_n match_error next_f (a::n_part) rest (n-1) r
	with NoMatch ->
	  if List.length r < n then match_error() else
	  split_n match_error next_f n_part (a::rest) n r 


(* [match_AC match_term get_var_link match_error next_f simp_facts prod allow_rest l1 l2 state]
   matches the lists [l1] and [l2] modulo AC. 
   When [allow_rest] is false, it calls [next_f [] state'] after linking variables in [l1]
   so that [\sigma l1 = l2] modulo AC. 
   When [allow_rest] is true, it calls [next_f lrest state']  after linking variables in [l1]
   so that [\sigma l1 . lrest = l2] modulo AC. *)

let match_AC match_term get_var_link match_error next_f simp_facts prod allow_rest l1 l2 state =
  let has_neut = prod_has_neut prod in
  if (not has_neut) && (List.length l1 > List.length l2) then match_error() else 

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
	  if n > len_l then match_error() else
	  if (n = len_l) && (not (has_neut && allow_neut)) then match_error() else
	  try 
	    split_n match_error (fun n_elem rest ->
	      match_term (split_among_vars_with_possible_rest next_f rest_vl n_elem) v (Terms.make_prod prod rest) state
		) [] [] n l
	  with NoMatch ->
	    partition_n (n+1)
	in
	partition_n 0
  in

  let rec match_variable_groups next_f g l2 state =
    match g with
      [] -> final_step match_error next_f allow_rest l2 state
    | (c, vl) :: rest ->
        (* Separate l2 into the elements that are present at least
	   [c] times and the others *)
	if c > 1 then
	  let (at_least_c, not_at_least_c) = sep_at_least_occ simp_facts c l2 in
	  split_among_vars_with_possible_rest (fun rest_l2 state' ->
	    let real_rest_l2 = append_n_times not_at_least_c c rest_l2 in
	    match_variable_groups next_f g real_rest_l2 state'
	      )  vl at_least_c state
	else
	  begin
	    assert(rest == []);
	    split_among_vars_with_possible_rest (final_step match_error next_f allow_rest) vl l2 state
	  end
  in
  
  let rec match_remaining_vars next_f remaining_vars l2 state =
    match remaining_vars with
      [] -> 
	final_step match_error next_f allow_rest l2 state
    | [t] when not allow_rest ->
	let allow_neut = 
	  match get_var_link t state with
	    None -> Parsing_helper.internal_error "get_var_link should return a link"
	  | Some(_, allow_neut) -> allow_neut
	in
	if (not (has_neut && allow_neut)) && (l2 == []) then match_error() else
	match_term (next_f []) t (Terms.make_prod prod l2) state
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

  let rec match_AC_rec next_f remaining_vars l1 l2 state =
    match l1 with
      [] -> 
	if List.exists (fun t -> 
	  match get_var_link t state with 
	    Some (TLink _, _) -> true
	  | _ -> false) remaining_vars then
	  match_AC_rec next_f [] remaining_vars l2 state
	else
	  match_remaining_vars next_f remaining_vars l2 state
    | t1::r1 ->
	match get_var_link t1 state with
	  None ->
	    (* Try to match t1 with an element of l2, and 
	       r1 with the rest of l2. *)
	    let rec try_list seen = function
		[] -> match_error()
	      | t2::r2 ->
		  let l2' = List.rev_append seen r2 in
		  try
		    match_term (match_AC_rec next_f remaining_vars r1 l2') t1 t2 state
		  with NoMatch ->
		    try_list (t2::seen) r2
	    in
	    try_list [] l2
	| Some (TLink t, _) ->
	    let l1' = Terms.simp_prod simp_facts (ref false) prod t in
	    begin
	      try 
		let r2 = multiset_minus simp_facts l2 l1' in
		match_AC_rec next_f remaining_vars r1 r2 state
	      with Not_found -> match_error()
	    end
	| Some (NoLink, _) ->
	    match_AC_rec next_f (t1::remaining_vars) r1 l2 state
  in

  match_AC_rec next_f [] l1 l2 state

(* Match term list *)

let rec match_term_list match_term next_f l l' state = 
  match l,l' with
    [],[] -> next_f state
  | a::l,a'::l' ->
      match_term (match_term_list match_term next_f l l') a a' state
  | _ -> Parsing_helper.internal_error "Different lengths in match_term_list"

(* [normalize_opt simp_facts t] normalizes [t] either 
   by calling [try_no_var] (just normalizes variables)
   or by calling [normalize] (normalizes variables and function 
   applications), depending on the current settings.
   The former is faster, but the latter is useful in
   some cases, when applying a known equality on functions
   is needed. *)

let normalize_opt simp_facts t =
  if !Settings.normalize_in_match_funapp then
    Terms.normalize simp_facts t
  else
    Terms.try_no_var simp_facts t
                                       
(* Match function application *)

let match_funapp match_term get_var_link match_error simp_facts next_f t t' state =
  if t.t_type != t'.t_type then match_error() else
  let t'' = normalize_opt simp_facts t' in
  match t.t_desc, t''.t_desc with
  | FunApp(f, [t1;t2]), FunApp(f', [t1';t2']) when 
    f == f' && (f.f_cat == Equal || f.f_cat == Diff) ->
	(* It is important to test this case before the commutative
	   function symbols: = and <> are also commutative function
	   symbols. *)
      begin
	match (match Terms.get_prod_list Terms.try_no_var_id [t1;t2] with
	         NoEq -> Terms.get_prod_list (normalize_opt simp_facts) [t1';t2']
	       | x -> x)
	with
	  ACUN(xor,_) ->
	    match_term next_f (Terms.app xor [t1;t2]) (Terms.app xor [t1';t2']) state
	| CommutGroup(prod,inv,_) ->
	    begin
	      try
		match_term next_f (Terms.app prod [t1; Terms.app inv [t2]])
		  (Terms.app prod [t1'; Terms.app inv [t2']]) state
	      with NoMatch ->
		match_term next_f (Terms.app prod [t1; Terms.app inv [t2]])
		  (Terms.app prod [t2'; Terms.app inv [t1']]) state
	    end
        | Group(prod,inv,neut) -> 
            begin
	      let l1 = Terms.simp_prod Terms.simp_facts_id (ref false) prod (Terms.app prod [t1; Terms.app inv [t2]]) in
	      let l2 = Terms.remove_inverse_ends Terms.simp_facts_id (ref false) (prod, inv, neut) l1 in
	      let l1' = Terms.simp_prod simp_facts (ref false) prod (Terms.app prod [t1'; Terms.app inv [t2']]) in
	      let l2' = Terms.remove_inverse_ends simp_facts (ref false) (prod, inv, neut) l1' in
	      let rec match_assoc_up_to_roll seen' rest' =
		try
		  match_assoc match_term get_var_link match_error (fun _ state -> next_f state) simp_facts prod false l2 (rest' @ (List.rev seen')) state
		with NoMatch ->
		  match rest' with
		    [] -> match_error()
		  | a::rest'' ->
		      match_assoc_up_to_roll (a::seen') rest''
	      in
	      try
		match_assoc_up_to_roll [] l2'
	      with NoMatch ->
		let l3' = List.rev (List.map (Terms.compute_inv (normalize_opt simp_facts) (ref false) (prod, inv, neut)) l2') in
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
      let t''inv = Terms.compute_inv (normalize_opt simp_facts) (ref false) (f,inv,n) t'' in
      match_term next_f t t''inv state
  | FunApp(f,[_;_]),_ when f.f_eq_theories != NoEq && f.f_eq_theories != Commut ->
      (* f is a binary function with an equational theory that is
	 not commutativity -> it is a product-like function *)
      begin
	let l = Terms.simp_prod Terms.simp_facts_id (ref false) f t in
	let l' = Terms.simp_prod simp_facts (ref false) f t'' in
	match f.f_eq_theories with
	  NoEq | Commut -> Parsing_helper.internal_error "Terms.match_funapp: cases NoEq, Commut should have been eliminated"
	| AssocCommut | AssocCommutN _ | CommutGroup _ | ACUN _ ->
	    (* Commutative equational theories: use matching modulo AC *)
	    match_AC match_term get_var_link match_error (fun _ state -> next_f state) simp_facts f false l l' state
	| Assoc | AssocN _ | Group _ -> 
	    (* Non-commutative equational theories: use matching modulo associativity *)
	    match_assoc match_term get_var_link match_error (fun _ state -> next_f state) simp_facts f false l l' state
	      (* Above, I ignore on purpose group and XOR properties,
		 they would yield too general and counter-intuitive matchings. *)
      end
  | FunApp(f,l), FunApp(f',l') when f == f' ->
      match_term_list match_term next_f l l' state
  | _ -> match_error()


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

   [simp_facts] collects the rewrite rules corresponding to known equalities
   and other known facts, which we use in order to replace variables with their values and
   to test equality between terms.

   [prod] is the product function symbol, which is associative or AC.
   *)

(* Matching modulo associativity, plus perhaps neutral element *)


(* [match_assoc_advice match_term explicit_value get_var_link is_var_inst fresh_vars_init next_f simp_facts prod l1 l2 state]
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

let special_neut_symb = 
  Settings.create_fun "$@special_neut" ([], Settings.t_any) Std

let special_neut_term = 
  Terms.app special_neut_symb []

let match_assoc_advice match_term explicit_value get_var_link is_var_inst fresh_vars_init next_f simp_facts prod l1 l2 state =
  (* [has_neut] is true iff there is a neutral element for the product [prod]. *)
  let has_neut = prod_has_neut prod in

  let fresh_vars = ref (List.map fst fresh_vars_init) in

  (* is_rev is true when the lists l1 and l2 have been reversed.
     In this case, when a variable is assigned or read, its content
     must also be reversed. *)
  let put_side is_rev s l =
    List.map (fun t ->
      match t.t_desc with
	Var(b,_) when List.memq b (!fresh_vars) -> (Fresh, t)
      |	_ -> (s, t)) (if is_rev then List.rev l else l)
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
	    Var(b,_) -> Some(b.link, 
			     (try
			       List.assq b fresh_vars_init
			     with Not_found -> false), 
			     Fresh, true)
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

  let assign_var is_rev next_f allow_neut (side, tvar) l state =
    match tvar.t_desc with
      Var(b,_) -> 
	begin
          (* check that tvar does not occur in l! *)
	  if List.exists (fun (_,t) -> Terms.refers_to b t) l then
	    raise NoMatch;
	  match side with
	    Advice -> 
	      if (not (has_neut && allow_neut)) && (l == []) then raise NoMatch;
	      next_f (explicit_value tvar state)
	  | Fresh ->
	      (* For fresh variables created in match_assoc_advice_subterm, 
		 we may create a special neutral element
		 when there is no neutral element *)
	      if (not allow_neut) && (l == []) then raise NoMatch;
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
		let tval = 
                  if (not has_neut) && (l == []) then special_neut_term else
                  Terms.make_prod prod (List.map snd (if is_rev then List.rev l else l)) 
                in
		Terms.auto_cleanup (fun () ->
		  Terms.link b (TLink tval);
		  next_f state
		    )
	  | Pat ->
	      if (not (has_neut && allow_neut)) && (l == []) then raise NoMatch;
	      if List.exists (fun (side,_) -> side == Pat) l then
		Parsing_helper.internal_error "Pat variables should be linked to non-Pat terms";
	      let tval = Terms.make_prod prod (List.map snd (if is_rev then List.rev l else l)) in	      
	      match_term next_f tvar tval state
	end
    | _ -> Parsing_helper.internal_error "assign_var: Variable expected"
  in

  let match_term_orient next_f (side1,t1) (side2,t2) state =
    match side1, side2 with
      Fresh, _ | _, Fresh -> Parsing_helper.internal_error "match_term_orient: Fresh variables should have been treated before"
    | Advice, Advice ->
	if not (Terms.simp_equal_terms simp_facts true t1 t2) then raise NoMatch;
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

  let rec try_prefix is_rev tvar l1 seen l2 state =
    match get_var_link_unif tvar state with
      None | Some(TLink _,_,_,_) -> Parsing_helper.internal_error "try_prefix: Should be a variable"
    | Some(NoLink, allow_neut, var_type, shortest) ->
	try 
	  if shortest then
	    try
            (* tvar = seen *)
	      assign_var is_rev (match_assoc_rec is_rev l1 l2) allow_neut tvar seen state
	    with NoMatch ->
              (* If it does not work, try with one more element *)
	      match l2 with
		[] -> raise NoMatch
	      | a::r -> try_prefix is_rev tvar l1 (seen @ [a]) r state
	  else
	    (* For variables of the pattern (shortest = false),
	       I try the prefixes by first trying l2 entirely, then removing the
	       last element of l2, etc. until I try the empty list. 
	       The reason for this order is that, in case we match a subterm of the
	       product, we want to take the largest possible subterm that works. *)
	    try 
	      match l2 with
		[] -> raise NoMatch
	      | a::r -> try_prefix is_rev tvar l1 (seen @ [a]) r state
	    with NoMatch ->
              (* tvar = seen *)
	      assign_var is_rev (match_assoc_rec is_rev l1 l2) allow_neut tvar seen state
	with NoMatch ->
	  match l2 with
	    [] -> raise NoMatch
	  | a::r -> 
	      match get_var_link_unif a state with
		None -> raise NoMatch
	      | Some(TLink t, _, _, _) -> 
		  let l2' = Terms.simp_prod simp_facts (ref false) prod t in
		  try_prefix is_rev tvar l1 seen ((put_side is_rev Advice l2') @ r) state
	      | Some(NoLink, allow_neut, _, _) ->
		  let x = Terms.create_binder "@$match_var" (snd prod.f_type) [] in
		  fresh_vars := x :: (!fresh_vars);
		  let x_term = Terms.term_from_binder x in
	          (* tvar = seen . x ; a = x . (some prefix of l1 to be defined) *)
		  assign_var is_rev (try_prefix is_rev a r [Fresh,x_term] l1) 
		    allow_neut tvar (seen @ [Fresh,x_term]) state
		    
  and match_var is_rev status1 l1 l2 state =
    match l1 with
      [] -> Parsing_helper.internal_error "match_var: l1 should not be empty"
    | t1::r1 ->
    match status1 with
      None | Some (TLink _, _, _, _) -> Parsing_helper.internal_error "match_var: get_var_link_unif should be Some(NoLink, ...)"
    | Some (NoLink, allow_neut, var_type, shortest) ->
	match l2 with
	  t2::r2 when Terms.simp_equal_terms simp_facts true (snd t1) (snd t2) -> 
	    match_assoc_rec is_rev r1 r2 state
	| _ ->
	    if (r1 == []) then
	      begin
	        (* If variable t1 is alone, that's easy: t1 should be linked to l2 *)
		assign_var is_rev next_f allow_neut t1 l2 state
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
		  try_prefix is_rev t1 r1 [] l2 state
		else
		  match_assoc_rec (not is_rev) l1rev l2rev state
	      end

  and match_assoc_rec is_rev l1 l2 state =
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
	let l1' = Terms.simp_prod simp_facts (ref false) prod t in
	match_assoc_rec is_rev ((put_side is_rev Advice l1') @ r1) l2 state
    | _, _, t2::r2, Some(TLink t,_,_,_) ->
	let l2' = Terms.simp_prod simp_facts (ref false) prod t in
	match_assoc_rec is_rev l1 ((put_side is_rev Advice l2') @ r2) state
    | t1::r1, Some(NoLink,_,(Pat|Fresh),_), _, _ ->
	match_var is_rev status1 l1 l2 state
    | _, _, t2::r2, Some(NoLink,_,(Pat|Fresh),_) ->
	match_var is_rev status2 l2 l1 state
    | t1::r1, Some(NoLink,_,Advice,_), _, _ ->
	match_var is_rev status1 l1 l2 state
    | _, _, t2::r2, Some(NoLink,_,Advice,_) ->
	match_var is_rev status2 l2 l1 state
    | [], _, _, _ -> raise NoMatch
    | _, _, [], _ -> raise NoMatch
    | t1::r1, _, t2::r2, _ -> 
	match_term_orient (match_assoc_rec is_rev r1 r2) t1 t2 state

  in
  match_assoc_rec false (put_side false Pat l1) (put_side false Advice l2) state
		    
(* [match_assoc_advice_subterm match_term explicit_value get_var_link is_var_inst next_f simp_facts prod l1 l2 state]
   matches the lists [l1] and [l2] modulo associativity. 
   More precisely, it calls [next_f left_rest right_rest state']  after linking variables in [l1]
   so that [left_rest. \sigma l1 . right_rest = l2] modulo associativity. *)

let match_assoc_advice_subterm match_term explicit_value get_var_link is_var_inst next_f simp_facts prod l1 l2 state =
  let b_right = Terms.create_binder "@$special_var_allow_rest" (snd prod.f_type) [] in
  let b_left = Terms.create_binder "@$special_var_allow_rest" (snd prod.f_type) [] in
  let l1' = Terms.term_from_binder b_left :: l1 @ [Terms.term_from_binder b_right] in
  let next_f_unif state = 
    let right_rest = 
      match b_right.link with
	NoLink -> []
      | TLink t -> 
	  if t == special_neut_term then [] else
	  Terms.simp_prod simp_facts (ref false) prod t
    in
    let left_rest = 
      match b_left.link with
	NoLink -> []
      | TLink t -> 
	  if t == special_neut_term then [] else
	  Terms.simp_prod simp_facts (ref false) prod t
    in
    next_f left_rest right_rest state
  in
  (* the variables b_right and b_left can ALWAYS be bound to the neutral element
     (even if there is in fact no neutral element! In this case, we use the special
     term special_neut_term instead) because I want to be able to match the full term *)
  match_assoc_advice match_term explicit_value get_var_link is_var_inst [(b_left, true); (b_right, true)] next_f_unif simp_facts prod l1' l2 state 

(* [match_assoc_advice_pat_subterm match_term explicit_value get_var_link is_var_inst next_f prod allow_full l1 l2 state]
   matches the lists [l1] and [l2] modulo associativity. 
   More precisely, it calls [next_f state']  after linking variables in [l1]
   so that [\sigma l1 = left_rest . l2 . right_rest] modulo associativity.
   [left_rest] and [right_rest] are just ignored, they are not passed to [next_f].
   [allow_full] is true when [l2] may match the full list [l1], that is,
   [left_rest] and [right_rest] may both be empty. *)

let match_assoc_advice_pat_subterm match_term explicit_value get_var_link is_var_inst next_f simp_facts prod allow_full l1 l2 state =
  let b_right = Terms.create_binder "@$special_var_allow_rest" (snd prod.f_type) [] in
  let b_left = Terms.create_binder "@$special_var_allow_rest" (snd prod.f_type) [] in
  let l2' = Terms.term_from_binder b_left :: l2 @ [Terms.term_from_binder b_right] in
  (* the variables b_right and b_left must not be both bound to the 
     neutral element because I want to match a strict subterm *)
  let is_neut t =
    (t == special_neut_term) ||
    (match prod.f_eq_theories, t.t_desc with
       (Group(_,_,n) | CommutGroup(_,_,n) | AssocN(_,n) 
        | AssocCommutN(_,n) | ACUN(_,n)), FunApp(n',[]) -> n == n'
    | _ -> false)
  in
  let next_f_unif state =
    if not allow_full then
      begin
	match b_left.link, b_right.link with
	  TLink t_left, TLink t_right ->
	    if (is_neut t_left) && (is_neut t_right) then raise NoMatch
	| _ -> ()
      end;
    next_f state
  in
  match_assoc_advice match_term explicit_value get_var_link is_var_inst [(b_left, true); (b_right, true)] next_f_unif simp_facts prod l1 l2' state 

(* Matching modulo associativity and commutativity, plus perhaps neutral element *)

(* [match_AC_advice match_term explicit_value get_var_link is_var_inst next_f simp_facts prod allow_rest_pat allow_full allow_rest l1 l2 state]
   matches the lists [l1] and [l2] modulo AC. 
   When [allow_rest] and [allow_rest_pat] are false, it calls [next_f [] state'] after linking variables in [l1]
   so that [\sigma l1 = l2] modulo AC. 
   When [allow_rest] is true and [allow_rest_pat] is false, it calls [next_f lrest state']  after linking variables in [l1]
   so that [\sigma l1 . lrest = l2] modulo AC. 
   When [allow_rest] is false and [allow_rest_pat] is true, it calls [next_f [] state']  after linking variables in [l1]
   so that [\sigma l1 = l2 . lrest] modulo AC. [lrest] must not be empty; it is ignored, it is not passed to [next_f].

   [allow_rest_pat] is true when a subterm of the pattern in [l1] should match
   [l2], so that some elements of [l1] are allowed to remain unmatched.

   In case [allow_rest_pat] is true, [allow_full] is true when [l2] may match the 
   full list [l1], that is, [lrest] may be empty.

   [allow_rest] is true when the pattern in [l1] should match a subterm of 
   the term in [l2], so that some elements of [l2] are allowed to remain unmatched.
*)

let match_AC_advice match_term explicit_value get_var_link is_var_inst next_f simp_facts prod allow_rest_pat allow_full allow_rest l1 l2 state =
  let has_neut = prod_has_neut prod in

  let final_step next_f l2 state =
    if (l2 == []) || allow_rest then next_f l2 state else raise NoMatch
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
	      match_term (split_among_vars_with_possible_rest next_f rest_vl n_elem) v (Terms.make_prod prod rest) state
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
	  let (at_least_c, not_at_least_c) = sep_at_least_occ simp_facts c l2 in
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
	match_term (next_f []) t (Terms.make_prod prod l2) state
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
	      if allow_rest_pat then raise NoMatch; (* This case is handled below *)
	      match_remaining_vars next_f remaining_vars l2 state
	    with NoMatch ->
	      (* advice_delayed and remaining_vars must match the elements of l2 *)
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
	      if advice_delayed == [] && remaining_vars == [] && (allow_rest_pat && not allow_full) then 
		(* the rest of the pattern would be empty, this is not allowed *)
		raise NoMatch;
	      if allow_rest && (remaining_vars = []) then
		(* Since there are no remaining variables, at least the terms
		   in [without_advice] cannot be matched by the expression,
		   so they end up in the rest part passed to next_f. *)
		next_f without_advice (all_possible_explicit_value with_advice state)
	      else 
		next_f [] (all_possible_explicit_value with_advice state)
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
	    let l1' = Terms.simp_prod simp_facts (ref false) prod t in
	    begin
	      try 
		let r2 = multiset_minus simp_facts l2 l1' in
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

let match_funapp_advice match_term explicit_value get_var_link is_var_inst next_f simp_facts t t' state =
  if t.t_type != t'.t_type then raise NoMatch else
  match t.t_desc, t'.t_desc with
  | FunApp(f, [t1;t2]), FunApp(f', [t1';t2']) when 
    f == f' && (f.f_cat == Equal || f.f_cat == Diff) ->
	(* It is important to test this case before the commutative
	   function symbols: = and <> are also commutative function
	   symbols. *)
      begin
	match (match Terms.get_prod_list (normalize_opt simp_facts) [t1;t2] with
	         NoEq -> Terms.get_prod_list (normalize_opt simp_facts) [t1';t2']
	       | x -> x)
	with
	  ACUN(xor,_) ->
	    match_term next_f (Terms.app xor [t1;t2]) (Terms.app xor [t1';t2']) state
	| CommutGroup(prod,inv,_) ->
	    begin
	      try
		match_term next_f (Terms.app prod [t1; Terms.app inv [t2]])
		  (Terms.app prod [t1'; Terms.app inv [t2']]) state
	      with NoMatch ->
		match_term next_f (Terms.app prod [t1; Terms.app inv [t2]])
		  (Terms.app prod [t2'; Terms.app inv [t1']]) state
	    end
        | Group(prod,inv,neut) -> 
            begin
	      let l1 = Terms.simp_prod simp_facts (ref false) prod (Terms.app prod [t1; Terms.app inv [t2]]) in
	      let l2 = Terms.remove_inverse_ends simp_facts (ref false) (prod, inv, neut) l1 in
	      let l1' = Terms.simp_prod simp_facts (ref false) prod (Terms.app prod [t1'; Terms.app inv [t2']]) in
	      let l2' = Terms.remove_inverse_ends simp_facts (ref false) (prod, inv, neut) l1' in
	      let rec match_assoc_up_to_roll seen' rest' =
		try
		  match_assoc_advice match_term explicit_value get_var_link is_var_inst [] next_f simp_facts prod l2 (rest' @ (List.rev seen')) state
		with NoMatch ->
		  match rest' with
		    [] -> raise NoMatch
		  | a::rest'' ->
		      match_assoc_up_to_roll (a::seen') rest''
	      in
	      try
		match_assoc_up_to_roll [] l2'
	      with NoMatch ->
		let l3' = List.rev (List.map (Terms.compute_inv (normalize_opt simp_facts) (ref false) (prod, inv, neut)) l2') in
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
      let t''inv = Terms.compute_inv (normalize_opt simp_facts) (ref false) (f,inv,n) t' in
      match_term next_f t t''inv state
  | FunApp(f,[_;_]),_ when f.f_eq_theories != NoEq && f.f_eq_theories != Commut ->
      (* f is a binary function with an equational theory that is
	 not commutativity -> it is a product-like function *)
      begin
	let l = Terms.simp_prod simp_facts (ref false) f t in
	let l' = Terms.simp_prod simp_facts (ref false) f t' in
	match f.f_eq_theories with
	  NoEq | Commut -> Parsing_helper.internal_error "Terms.match_funapp_advice: cases NoEq, Commut should have been eliminated"
	| AssocCommut | AssocCommutN _ | CommutGroup _ | ACUN _ ->
	    (* Commutative equational theories: use matching modulo AC *)
	    match_AC_advice match_term explicit_value get_var_link is_var_inst (fun _ state -> next_f state) simp_facts f false false false l l' state
	| Assoc | AssocN _ | Group _ -> 
	    (* Non-commutative equational theories: use matching modulo associativity *)
	    match_assoc_advice match_term explicit_value get_var_link is_var_inst [] next_f simp_facts f l l' state
	      (* Above, I ignore on purpose group and XOR properties,
		 they would yield too general and counter-intuitive matchings. *)
      end
  | FunApp(f,l), FunApp(f',l') when f == f' ->
      match_term_list match_term next_f l l' state
  | _ -> raise NoMatch
