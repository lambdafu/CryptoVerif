(* Transform the game using an equivalence coming from a cryptographic
   primitive. This is the key operation. *)

open Types

(*

TO DO update to the new, more general equivalences.
For now, I commented everything to be able to test the new parsing.

let debug = false

(* Check if a variable in var_list occurs in t
   If yes, raise Found l, where l is the list of array indexes of this 
   variable in t *)

exception Found of term list
    (* This exception is local to occurs_var/check_occurs_var.
       It is raise when the variable is found;
       the argument is the list of array indexes of the variable. *)

let rec occurs_var var_list t =
  match t.t_desc with
    Var(b,l) ->
      if List.memq b var_list then
	raise (Found l)
  | FunApp(f,l) ->
      List.iter (occurs_var var_list) l
  | TestE _ | LetE _ | FindE _ -> 
      Parsing_helper.internal_error "If, find, and let should have been expanded (Cryptotransf.occurs_var)"
      
(* Check that all occurrences of variables in var_list are used in the same
   term "term" up to substitution of array indexes in cur_array.
   Also check that variables in var_list are only defined by Restr *)

let rec check_occurs_var var_list term cur_array t =
  try 
    occurs_var var_list t;
      (* The variables in var_list do not occur in t => OK *)
    true
  with (Found l) ->
    (Terms.equal_terms (Terms.subst cur_array l term) t) || 
  (* maybe TO DO In case of failure, I should perhaps suggest ways of making 
     it work: assignment expansion, if/find expansion, ... *)
    (match t.t_desc with
      Var(b,l) ->
	if List.memq b var_list then
	  false
	else
	  List.for_all (check_occurs_var var_list term cur_array) l
    | FunApp(f,l) ->
	List.for_all (check_occurs_var var_list term cur_array) l
    | TestE _ | LetE _ | FindE _ -> 
	Parsing_helper.internal_error "If, find, and let should have been expanded (Cryptotransf.check_occurs_var)")

      
let rec check_occurs_vars_pat var_list term cur_array = function
    PatVar b -> not (List.memq b var_list)
  | PatTuple l -> List.for_all (check_occurs_vars_pat var_list term cur_array) l
  | PatEqual t -> check_occurs_var var_list term cur_array t


(* NOTE: check_occurs_vars_cterm is simply check_occurs_var when 
   TestE/FindE/LetE are forbidden *)
let rec check_occurs_vars_cterm var_list term cur_array t =
  match t.t_desc with
    TestE(t1,t2,t3) ->
      (check_occurs_var var_list term cur_array t1) &&
      (check_occurs_vars_cterm var_list term cur_array t2) &&
      (check_occurs_vars_cterm var_list term cur_array t3)
  | FindE(l0,t3) ->
      (List.for_all (fun (bl,def_list,t1,t2) ->
	(not (List.exists (fun b -> List.memq b var_list) bl)) &&
	(List.for_all (fun (b,l) ->
	  List.for_all (check_occurs_var var_list term cur_array) l) def_list) &&
	(check_occurs_vars_cterm var_list term cur_array t1) &&
	(check_occurs_vars_cterm var_list term cur_array t2)) l0) &&
      (check_occurs_vars_cterm var_list term cur_array t3)
  | LetE(pat, t1, t2, topt) ->
      (check_occurs_vars_pat var_list term cur_array pat) &&
      (check_occurs_var var_list term cur_array t1) &&
      (check_occurs_vars_cterm var_list term cur_array t2) &&
      (match topt with
	None -> true
      |	Some t3 -> check_occurs_vars_cterm var_list term cur_array t3)
  | _ -> check_occurs_var var_list term cur_array t

let rec check_occurs_vars_process var_list term cur_array = function
    Nil -> true
  | Par(p1,p2) -> 
      (check_occurs_vars_process var_list term cur_array p1) &&
      (check_occurs_vars_process var_list term cur_array p2)
  | Repl(b,p) ->
      (not (List.memq b var_list)) &&
      (check_occurs_vars_process var_list term cur_array p)
  | Restr(b,p) ->
      check_occurs_vars_process var_list term cur_array p
  | Test(t,p1,p2) ->
      (check_occurs_var var_list term cur_array t) &&
      (check_occurs_vars_process var_list term cur_array p1) &&
      (check_occurs_vars_process var_list term cur_array p2)
  | Find(l0,p2) ->
      (List.for_all (fun (bl,def_list,t,p1) ->
	(not (List.exists (fun b -> List.memq b var_list) bl)) &&
	(List.for_all (fun (b,l) ->
	  List.for_all (check_occurs_var var_list term cur_array) l) def_list) &&
	(check_occurs_vars_cterm var_list term cur_array t) &&
	(check_occurs_vars_process var_list term cur_array p1)) l0) &&
      (check_occurs_vars_process var_list term cur_array p2)
  | Input(t,pat,p) ->
      (check_occurs_var var_list term cur_array t) &&
      (check_occurs_vars_pat var_list term cur_array pat) &&
      (check_occurs_vars_process var_list term cur_array p)
  | Output(t1,t2,p) ->
      (check_occurs_var var_list term cur_array t1) &&
      (check_occurs_var var_list term cur_array t2) &&
      (check_occurs_vars_process var_list term cur_array p)
  | Let(pat, t, p1, p2) ->
      (check_occurs_vars_pat var_list term cur_array pat) &&
      (check_occurs_var var_list term cur_array t) &&
      (check_occurs_vars_process var_list term cur_array p1) &&
      (check_occurs_vars_process var_list term cur_array p2)
      
let check_occurs_vars_process var_list term cur_array p =
  (not (List.exists Transform.occurs_in_queries var_list)) &&
  (check_occurs_vars_process var_list term cur_array p)

(* Check if t is an instance of term.
   Variables of term may be substituted by any term, except 
   - variables in name_list_g which must be kept, but may be indexed 
   (always the same indexes for all elements of name_list_g) 
   - variables in name_list_i which may be renamed to variables
   created by "new" of the same type, and indexed (always the same
   indexes for all elements of name_list_i, and the indexes of variables of 
   name_list_g must be a suffix of the indexes of variables in name_list_i)

   If it is impossible, raise SurelyNot
   If it may be possible after some syntactic game transformations,
   return the list of these transformations.
   When the returned list is empty, t is an instance of term in the
   sense above.
 *)

exception SurelyNot

let name_list_g = ref ([] : binder list)
let name_list_g_target_set = ref true
let name_list_g_target = ref ([] : binder list)
let name_list_g_assoc = ref ([] : (binder * binder) list)

let name_list_g' = ref ([] : binder list)
let name_list_g_target' = ref ([] : binder list)
let name_list_g_assoc' = ref ([] : (binder * binder) list)

let name_list_g_indexes = ref None (* not set yet *)
let name_list_i_indexes = ref None (* not set yet *)


let check_distinct_links bl =
  let seen_binders = ref [] in
  List.iter (fun b ->
    match b.link with
      TLink { t_desc = Var(b',l) } -> 
	if (List.memq b' (!seen_binders)) || (List.memq b' (!name_list_g_target)) then
	  raise SurelyNot;
	seen_binders := b' :: (!seen_binders)
    | TLink t -> Parsing_helper.internal_error "unexpected link in check_distinct_links"
    | _ -> (* binder not linked; should not happen when no useless
	      new is present in the equivalence *) ()) bl

let rec check_instance_of_rec name_list_i term t =
  match (term.t_desc, t.t_desc) with
    FunApp(f,l), FunApp(f',l') when f == f' ->
      check_instance_of_rec_list name_list_i l l'
  | FunApp(f,l), FunApp(_,_) -> 
      raise SurelyNot
	(* Might work after rewriting with an equation *)
  | FunApp(f,l), Var(b,_) ->
      (* suggest assignment expansion on b *)
      [RemoveAssign (OneBinder b)]
  | FunApp(f,l), (TestE _ | FindE _ | LetE _) ->
      Parsing_helper.internal_error "If, let, find should have been expanded (Cryptotransf.check_instance_of_rec)"
  | Var(b,l), _ ->
      begin
        match b.link with
          TLink t' -> 
	    if not (Terms.equal_terms t t') then
	      raise SurelyNot
	    else
	      []
        | NoLink ->
            begin
              if List.memq b (!name_list_g) then
		try 
                  match t.t_desc with
                    Var(b',l') when b' == List.assq b (!name_list_g_assoc) ->
                      begin
			match !name_list_g_indexes with
			  None -> name_list_g_indexes := Some l'
			| Some l'' -> 
			    if not (List.for_all2 Terms.equal_terms l'' l') then
			      raise SurelyNot
                      end;
		      []
                  | _ -> raise SurelyNot
		with Not_found ->
		  (* b has no associated name in name_list_g_assoc *)
		  if !name_list_g_target_set then
		    Parsing_helper.internal_error "name_list_g_assoc should give images for all elements of name_list_g";
                  match t.t_desc with
                    Var(b',l') ->
                      begin
			if List.memq b' (!name_list_g_target) then raise SurelyNot;
                        (* check that b' is defined by a restriction *)
			if not (Terms.is_restr b') then raise SurelyNot;
                        (* check that b' is of the right type *)
			if b'.btype != b.btype then raise SurelyNot;
			match !name_list_g_indexes with
			  None -> name_list_g_indexes := Some l'
			| Some l'' -> 
			    if not (List.for_all2 Terms.equal_terms l'' l') then
			      raise SurelyNot
                      end;
		      (* Note: when I catch SurelyNot, I backtrack on the values of name_list_g_assoc and name_list_g_target *)
		      name_list_g_assoc := (b,b') :: (!name_list_g_assoc);
		      name_list_g_target := b' :: (!name_list_g_target);
		      []
                  | _ -> raise SurelyNot
		  
              else if List.memq b name_list_i then
                match t.t_desc with
                  Var(b',l') ->
                    begin
                      (* check that b' is defined by a restriction *)
		      if not (Terms.is_restr b') then raise SurelyNot;
                      (* check that b' is of the right type *)
                      if b'.btype != b.btype then raise SurelyNot; 
                      Terms.link b (TLink t);
                      match !name_list_i_indexes with
			None -> name_list_i_indexes := Some l'; []
                      | Some l'' -> 
			  if not (List.for_all2 Terms.equal_terms l'' l') then
			    raise SurelyNot
			  else
			    []
                    end
                | _ -> raise SurelyNot
              else
                begin
                  (* check that t is of the right type *)
                  if not (Terms.is_subtype t.t_type b.btype) then
                    raise SurelyNot; 
                  Terms.link b (TLink t);
		  []
                end
            end
        | _ -> Parsing_helper.internal_error "unexpected link in check_instance_of"
      end
  | _ -> Parsing_helper.internal_error "if, find, defined should have been excluded from left member of equivalences"

and check_instance_of_rec_list name_list_i l l' =
  match l,l' with
    [],[] -> []
  | a::l, a'::l' ->
	Terms.union_eq (check_instance_of_rec name_list_i a a')
                       (check_instance_of_rec_list name_list_i l l')
  | _ -> Parsing_helper.internal_error "different length in check_instance_of_rec_list"

let clean_up_instance_of () =
  Terms.cleanup();
  name_list_i_indexes := None;
  name_list_g_indexes := None

let check_instance_of name_list_i term t =
  if !Terms.current_bound_vars != [] then
    Parsing_helper.internal_error "Bound vars should be cleaned up (check_instance_of)";
  try 
    (* print_string "Check instance of ";
    Display.display_term [] term;
    print_string " ";
    Display.display_term [] t;
    print_newline(); *)
    let il = check_instance_of_rec name_list_i term t in
    if !name_list_g_indexes == None then raise SurelyNot; (* This transformation could not discharge any element of name_list_g -> useless *)
    if il == [] then check_distinct_links name_list_i; (* Check that elements of name_list_i are linked to distinct binders *)
    if debug then
      begin
	print_string "check_instance_of ";
	Display.display_term [] term;
	print_string " ";
	Display.display_term [] t;
	print_string " succeeded with advise ";
	Display.display_list Display.display_instruct il;
	print_string "\n"
      end;
    il
  with SurelyNot ->
    clean_up_instance_of(); (* Clean up bindings when fails *)
    raise SurelyNot

(* Check whether t is an instance of a subterm of term
   Useful when t is just a test (if/find) or an assignment,
   so that by syntactic transformations of the game, we may
   arrange so that a superterm of t is an instance of term *)

let rec check_instance_of_subterms name_list_i term t =
  match term.t_desc with
    Var(b,l) -> raise SurelyNot
  | FunApp(f,l) ->
      check_instance_of_list name_list_i l t
  | TestE _ | LetE _ | FindE _ ->
      Parsing_helper.internal_error "if, let, find should have been excluded from left member of equivalences"

and check_instance_of_list name_list_i l t = 
  match l with
    [] -> raise SurelyNot
  | (term::l) -> 
      let old_name_list_g_target = !name_list_g_target in
      let old_name_list_g_assoc = !name_list_g_assoc in
      try
	check_instance_of name_list_i term t	
      with SurelyNot ->
	name_list_g_target := old_name_list_g_target;
	name_list_g_assoc := old_name_list_g_assoc;
	try 
	  check_instance_of_subterms name_list_i term t
	with SurelyNot ->
	  name_list_g_target := old_name_list_g_target;
	  name_list_g_assoc := old_name_list_g_assoc;
	  check_instance_of_list name_list_i l t

(* Reverse substitution: all array references must be suffixes of 
   name_list_i_indexes, and these values are replaced with variables 
   of cur_array *)

exception Failure

let reverse_subst forbidden_cur_array name_list_i_indexes cur_array t =
  let rec rev_subst_index l =
     let len = List.length l in
     let len' = List.length name_list_i_indexes in
     if (len' >= len) &&
        (List.for_all2 Terms.equal_terms l (Terms.skip (len'-len) name_list_i_indexes))
     then Terms.skip (len'-len) cur_array
     else List.map reverse_subst_rec l
  and reverse_subst_rec t =
  { t_desc = 
    begin
    match t.t_desc with
      Var(b,l) -> 
        if List.memq b forbidden_cur_array then
          raise Failure;
        Var(b, rev_subst_index l)
    | FunApp(f,l) -> 
        FunApp(f, List.map reverse_subst_rec l)
    | TestE _ | LetE _ | FindE _ -> 
	Parsing_helper.internal_error "If, find, and let should have been expanded (Cryptotransf.reverse_subst_rec)"
    end;
    t_type = t.t_type;
    t_occ = t.t_occ }
  in
  reverse_subst_rec t

(* First pass: check and collect mappings of variables and expressions *)

type one_exp =
   { source_exp_instance : term; (* The expression to replace -- physical occurrence *)
     after_transfo_let_vars : (binder * binder) list; 
        (* List of (b,b') where b is a binder created by a let in
           the right member of the equivalence and b' is its image in 
           the transformed process. The indexes at creation of b' are cur_array_exp *)
     cur_array_exp : term list; 
        (* Value of cur_array at this expression in the process. *)
     name_list_g_indexes_exp : term list; 
        (* Values of indexes of names in name_list_g in this expression *)
     name_list_i_indexes_exp : term list; 
        (* Values of indexes of names in name_list_i in this expression *)
     after_transfo_input_vars_exp : (binder * term) list 
        (* List of (b,t) where b is a binder defined by an input in the 
           right member of the equivalence and the term t is its image in the process *)
   }

type mapping =
   { mutable expressions : one_exp list; (* List of uses of this expression, described above *)
     before_transfo_restr : (binder * binder) list;
     source_exp : term; (* Left-member expression in the equivalence *)
     after_transfo_restr : (binder * binder) list; 
        (* List of (b, b') where b is a binder created by a restriction in the
           right member of the equivalence, and b' is its image in the transformed process.
           The indexes at creation of b' are name_list_i_indexes *)
     name_list_i_indexes : term list; 
        (* List of binders at creation of names in name_list_i in the process *)
     target_repl : binder; (* Replication binder in the equivalence *)
     target_exp : term; (* Right-member expression in the equivalence *)
     count : probaf (* Number of times this expression is evaluated
                       for each different sequence of names in name_list_g in the process *)
   }

(* expression to insert for replacing source_exp_instance 
     = (name_list_g_assoc'[name_list_g_indexes_exp], 
        after_transfo_input_vars_exp, 
        after_transfo_restr[name_list_i_indexes_exp], 
        after_transfo_let_vars[cur_array_exp]) ( target_exp )
*)

let map = ref ([] : mapping list)

let equiv = ref ((([],[]),([],[]),Zero) : equiv)

let whole_game = ref Nil

let rec find_rm lm lm_list rm_list =
  match (lm_list,rm_list) with
    [],_ | _,[] -> Parsing_helper.internal_error "Could not find left member"
  | (a::l,b::l') -> 
      if lm == a then b else find_rm lm l l'

let rec letvars_from_term accu t =
  match t.t_desc with
    Var(_,l) | FunApp(_,l) -> 
      List.iter (letvars_from_term accu) l
  | TestE(t1,t2,t3) ->
      letvars_from_term accu t1;
      letvars_from_term accu t2;
      letvars_from_term accu t3
  | LetE(pat,t1, t2, topt) -> 
      vars_from_pat accu pat; letvars_from_term accu t1;
      letvars_from_term accu t2; 
      begin
	match topt with
	  None -> ()
	| Some t3 -> letvars_from_term accu t3
      end
  | FindE(l0,t3) ->
      List.iter (fun (bl,def_list,t1,t2) ->
	List.iter (fun (_,l) -> List.iter (letvars_from_term accu) l) def_list;
	letvars_from_term accu t1;
	letvars_from_term accu t2) l0;
      letvars_from_term accu t3      

and vars_from_pat accu = function
    PatVar b -> accu := b :: (!accu)
  | PatTuple l -> List.iter (vars_from_pat accu) l
  | PatEqual t -> letvars_from_term accu t

let new_binder2 b args_at_creation = 
  { sname = b.sname;
    vname = Terms.new_vname();
    btype = b.btype;
    args_at_creation = args_at_creation;
    def = [];
    link = NoLink }

let rec make_prod = function
    [] -> Cst 1
  | [a] -> Count (Terms.param_from_type a.t_type)
  | (a::l) -> Mul (Count (Terms.param_from_type a.t_type), make_prod l)

let make_prod_suffix name_list_g_indexes name_list_i_indexes =
  let len = List.length name_list_g_indexes in
  let len' = List.length name_list_i_indexes in
  if (len > len') || 
    (not (List.for_all2 Terms.equal_terms name_list_g_indexes (Terms.skip (len'-len) name_list_i_indexes))) then
	(* name_list_g_indexes is not a suffix of name_list_i_indexes.
	   We must make the whole product of name_list_i_indexes *)
    make_prod name_list_i_indexes
  else
	(* name_list_g_indexes is a suffix of name_list_i_indexes.
	   We make the product of the part of name_list_i_indexes not in name_list_g_indexes *)
    let (l1,_) = Terms.split (len'-len) name_list_i_indexes in
    make_prod l1

let check_same_args_at_creation = function
    [] -> ()
  | (a::l) -> 
      if not (List.for_all (fun b -> List.for_all2 Terms.equal_terms b.args_at_creation a.args_at_creation) l)
	  then raise SurelyNot

(* ta_above: when there is a test (if/find) or an assignment
   just above t, contains the instruction to expand this test or assignment;
   otherwise empty list 

   Return the list of transformations to apply before so that the desired
   transformation may work. When this list is empty, the desired transformation
   is ok. Raises SurelyNot when the desired transformation is impossible,
   even after preliminary changes.
*)

let rec check_term ta_above cur_array t =
   try
     occurs_var (!name_list_g_target) t;
     (* The variables in name_list_g_target do not occur in t => OK *)
     []
   with (Found l) ->
     (* First try to find a matching source expression in the equivalence to apply *)
     let ((blm, lm), (brm, rm), probaf) = !equiv in

     let transform_to_do = ref None in
     let r = List.exists (fun ({ b_inputs = b_inputs; b_restr = name_list_i; res = res_term } as lm1) -> 
       try 
	 let to_do = 
	   let old_name_list_g_target = !name_list_g_target in
	   let old_name_list_g_assoc = !name_list_g_assoc in
	   try 
	     check_instance_of name_list_i res_term t 
	   with SurelyNot ->
	     name_list_g_target := old_name_list_g_target;
	     name_list_g_assoc := old_name_list_g_assoc;
	   (* When t is just under a test (if/find) or an assignment,
	      try subterms of res_term *)
	     if ta_above != [] then
	       Terms.union_eq ta_above (check_instance_of_subterms name_list_i res_term t)
	     else
	       raise SurelyNot
	 in
	 let env = List.map (fun b ->
	   match b.link with
	     TLink t -> (b, t)
	   | _ -> Parsing_helper.internal_error "unexpected link in check_term"
		 ) (!Terms.current_bound_vars) 
	 in
	 let name_list_i_indexes =
	   match !name_list_i_indexes with
	     None -> []
	   | Some l -> l
	 in
	 let name_list_g_indexes = 
	   match !name_list_g_indexes with
	     None -> Parsing_helper.internal_error "name_list_g_indexes should be set"
	   | Some l -> l
	 in
	 clean_up_instance_of();
	 let to_do' = 
	   (Terms.map_concat  (fun (b,t) ->
	     if (List.memq b (!name_list_g)) || (List.memq b name_list_i) then [] else
	     check_term [] cur_array t
	       ) env) @ to_do
	 in
	 if to_do' == [] then
	   begin
	     if name_list_i != [] then
	       begin
		 (* Check that names in name_list_i are always used in the same expression *)
	 	 (* TO DO this test could be made more permissive to succeed in all cases when the names in name_list_i occur in a single expression.
		    More generally, it would be nice to allow different session identifiers when they are related by an equality. For instance, if name_list_i_indexes is iX, and jX[iX[i]] = i, then i should also be allowed, and the result of the reverse subtitution applied to i is jX. *)
		 let cur_array' = List.map (fun e -> { sname = "tmpcur";
						       vname = Terms.new_vname();
						       btype = e.t_type;
						       args_at_creation = [];
						       def = [];
						       link = NoLink }) name_list_i_indexes in
		 let cur_array_terms' = List.map Terms.term_from_binder cur_array' in
		 let t' = reverse_subst cur_array name_list_i_indexes cur_array_terms' t in
		 if not (check_occurs_vars_process name_list_i t' cur_array' (!whole_game)) then raise Failure;
	         (* SUCCESS store the mapping in the mapping list *)
		 let { b_inputs = b_inputs'; b_repl = b_repl'; b_restr = name_list_i'; res = res_fun' } as rm1 = find_rm lm1 lm rm in
		 let let_vars' = ref [] in
		 letvars_from_term let_vars' res_fun';
		 let name_list_i_assoc = List.map (fun b ->
		   match List.assq b env with
		     { t_desc = Var(b',_) } -> (b,b')
		   | _ -> Parsing_helper.internal_error "unexpected image of name_list_i in check_term"
			 ) name_list_i
		 in
		 let input_env = List.filter (fun (b,_) -> 
		   not (List.memq b (!name_list_g) || 
		   List.memq b name_list_i)) env 
		 in
		 check_same_args_at_creation (List.map snd name_list_i_assoc);
		 let one_name = snd (List.hd name_list_i_assoc) in
		 let rec find_old_mapping = function
		     [] -> (* No old mapping found, create a new one *)
		       let cur_array_terms = List.map  Terms.term_from_binder cur_array in
		       let new_mapping =
			 { expressions = [ { source_exp_instance = t;
					     name_list_i_indexes_exp = name_list_i_indexes;
					     after_transfo_let_vars = 
					       List.map (fun b -> (b, new_binder2 b cur_array_terms)) (!let_vars');
					     cur_array_exp = cur_array_terms;
					     name_list_g_indexes_exp = name_list_g_indexes;
					     after_transfo_input_vars_exp = 
					       List.map (fun (b,t) ->
						 (find_rm b b_inputs b_inputs', t)) input_env
					   } ];
			   before_transfo_restr = name_list_i_assoc;
			   source_exp = res_term;
			   after_transfo_restr = 
			       List.map (fun b -> (b, new_binder2 b one_name.args_at_creation)) name_list_i';
			   name_list_i_indexes = one_name.args_at_creation;
			   target_repl = b_repl';
			   target_exp = res_fun';
			   count = make_prod_suffix name_list_g_indexes name_list_i_indexes
		         } 
		       in
		       map := new_mapping :: (!map)
		   | (mapping::rest) -> 
		       if List.exists (fun (b,b') -> b' == one_name) mapping.before_transfo_restr then
			 (* Old mapping found, just add the current expression in the 
			    list of expressions of this mapping *)
			 let cur_array_terms = List.map  Terms.term_from_binder cur_array in
			 mapping.expressions <-
			    { source_exp_instance = t;
			      name_list_i_indexes_exp = name_list_i_indexes;
			      after_transfo_let_vars = 
			        List.map (fun b -> (b, new_binder2 b cur_array_terms)) (!let_vars');
			      cur_array_exp = cur_array_terms;
			      name_list_g_indexes_exp = name_list_g_indexes;
			      after_transfo_input_vars_exp = 
			        List.map (fun (b,t) ->
				  (find_rm b b_inputs b_inputs', t)) input_env
			    } :: mapping.expressions
                       else 
			 find_old_mapping rest
		 in
		 find_old_mapping (!map)
	       end
	     else
	       begin
	         (* SUCCESS store the mapping in the mapping list *)
		 let { b_inputs = b_inputs'; b_repl = b_repl'; b_restr = name_list_i'; res = res_fun' } as rm1 = find_rm lm1 lm rm in
		 let let_vars' = ref [] in
		 letvars_from_term let_vars' res_fun';
		 let input_env = List.filter (fun (b,_) -> not (List.memq b (!name_list_g))) env in
		 let cur_array_terms = List.map Terms.term_from_binder cur_array in
		 let new_mapping = 
		   { expressions = [ { source_exp_instance = t;
				       name_list_i_indexes_exp = cur_array_terms;
				       after_transfo_let_vars = 
				         List.map (fun b -> (b, new_binder2 b cur_array_terms)) (!let_vars');
				       cur_array_exp = cur_array_terms;
				       name_list_g_indexes_exp = name_list_g_indexes;
				       after_transfo_input_vars_exp = 
			                 List.map (fun (b,t) ->
					   (find_rm b b_inputs b_inputs', t)) input_env
				     } ];
		     before_transfo_restr = [];
		     source_exp = res_term;
		     after_transfo_restr = 
		       List.map (fun b -> (b, new_binder2 b cur_array_terms)) name_list_i';
		     name_list_i_indexes = cur_array_terms;
		     target_repl = b_repl';
		     target_exp = res_fun';
		     count = make_prod_suffix name_list_g_indexes cur_array_terms
		       (* TO DO (to reduce probability difference)
			  I should make some effort so that name_list_g_indexes is a suffix of 
			  the indexes of the expression.
			  Also, when not all indexes in cur_array_terms appear in the
			  expression, I could make only the product of the longest
			  prefix of cur_array_terms that appears.
			  *)
		   } 
		 in 
		 map := new_mapping :: (!map)
	       end;
	     true
	   end
	 else
	   begin
	     transform_to_do := Some to_do;
	     false
	   end
       with Failure | SurelyNot -> 
	 if debug then
	   begin
	     print_string "failed to discharge ";
	     Display.display_term [] t;
	     print_string "\n"
	   end;
	 clean_up_instance_of();
	 false
	 ) lm
     in

     if r then
       []
     else
       let old_name_list_g_target = !name_list_g_target in
       let old_name_list_g_assoc = !name_list_g_assoc in
       try 
         check_term_try_subterms cur_array t
       with SurelyNot ->
	 name_list_g_target := old_name_list_g_target;
	 name_list_g_assoc := old_name_list_g_assoc;
         match !transform_to_do with
           None -> raise SurelyNot
         | Some l -> l

and check_term_try_subterms cur_array t =
     (* If fails, try a subterm; if t is just a variable in name_list_g_target,
        the transformation is not possible *)
     match t.t_desc with
       Var(b,l) ->
         if List.memq b (!name_list_g_target) then
           raise SurelyNot
         else
           Terms.map_concat (check_term [] cur_array) l
     | FunApp(f,l) ->
	Terms.map_concat (check_term [] cur_array) l
     | TestE _ | LetE _ | FindE _ -> 
	 Parsing_helper.internal_error "If, find, and let should have been expanded (Cryptotransf.check_term_try_subterms)"

let rec check_pat cur_array = function
    PatVar b -> []
  | PatTuple l -> Terms.map_concat (check_pat cur_array) l
  | PatEqual t -> check_term [] cur_array t

let rec get_binders = function
    PatVar b -> [RemoveAssign (OneBinder b)]
  | PatTuple l -> Terms.map_concat get_binders l
  | PatEqual t -> []

(* NOTE: check_cterm is simply check_term [] when 
   TestE/FindE/LetE are forbidden *)
let rec check_cterm cur_array t =
  match t.t_desc with
    TestE(t1,t2,t3) ->
      Terms.union_eq (check_term [] cur_array t1)
     (Terms.union_eq (check_cterm cur_array t2)
     (check_cterm cur_array t3))
  | FindE(l0, t3) ->
      let accu = ref (check_cterm cur_array t3) in
      List.iter (fun (bl, def_list, t1, t2) ->
	accu :=
	   Terms.union_eq (Terms.map_concat (fun (b,l) ->
	     Terms.map_concat (check_term [] cur_array) l) def_list)
	     (Terms.union_eq (check_cterm cur_array t1)
		(Terms.union_eq (check_cterm cur_array t2) (!accu)))) l0;
      !accu
  | LetE(pat,t1,t2,topt) ->
     Terms.union_eq (check_pat cur_array pat)
     (Terms.union_eq (check_term (get_binders pat) cur_array t1)
     (Terms.union_eq (check_cterm cur_array t2)
     (match topt with
       None -> []
     | Some t3 -> check_cterm cur_array t3)))
  | _ -> check_term [] cur_array t

let rec check_process cur_array = function
    Nil -> []
  | Par(p1,p2) ->
      Terms.union_eq (check_process cur_array p1)
	(check_process cur_array p2)
  | Repl(b,p) ->
      check_process (b::cur_array) p
  | Restr(b,p) ->
      check_process cur_array p
  | Test(t,p1,p2) ->
      Terms.union_eq (check_term [] cur_array t)
     (Terms.union_eq (check_process cur_array p1)
     (check_process cur_array p2))
  | Find(l0, p2) ->
      let accu = ref (check_process cur_array p2) in
      List.iter (fun (bl, def_list, t, p1) ->
	accu := 
	Terms.union_eq (Terms.map_concat (fun (b,l) ->
	  Terms.map_concat (check_term [] cur_array) l) def_list)
	  (Terms.union_eq (check_cterm cur_array t)
	     (Terms.union_eq (check_process cur_array p1) (!accu)))) l0;
      !accu
  | Let(pat,t,p1,p2) ->
     Terms.union_eq (check_pat cur_array pat)
     (Terms.union_eq (check_term (get_binders pat) cur_array t)
     (Terms.union_eq (check_process cur_array p1)
     (check_process cur_array p2)))
  | Input(t,pat,p) ->
     Terms.union_eq (check_term [] cur_array t)
     (Terms.union_eq (check_pat cur_array pat)
     (check_process cur_array p))
  | Output(t1,t2,p) ->
     Terms.union_eq (check_term [] cur_array t1)
     (Terms.union_eq (check_term [] cur_array t2)
     (check_process cur_array p))

let check_process() =
  if List.exists Transform.occurs_in_queries (!name_list_g) then
    raise SurelyNot;
  check_same_args_at_creation (!name_list_g_target);
  check_process [] (!whole_game)

(* Second pass: perform the game transformation itself *)

(* Constraint eq_left = eq_right { cur_array_im / cur_array } *)

let rec make_constra cur_array cur_array_im eq_left eq_right =
  match (eq_left, eq_right) with
    [],[] -> None
  | (a::l),(b::l') -> 
      begin
      let t = Terms.make_equal (Terms.term_from_binder a) (Terms.subst cur_array cur_array_im b) in
      match make_constra cur_array cur_array_im l l' with
	None -> Some t
      |	Some t' -> Some (Terms.make_and t t')
      end
  | _ -> Parsing_helper.internal_error "Not same length in make_constra"
  

let rename_def_list loc_rename def_list = 
  List.map (fun (b,l) ->
      let rec find_loc_rename = function
	  [] -> Parsing_helper.internal_error "variable not found in rename_def_list"
	| ((b',l'),(b'',l''))::rest_rename ->
	    if (b == b') && (List.for_all2 Terms.equal_terms l l') then
	      (b'',l'')
	    else
	      find_loc_rename rest_rename
      in
      find_loc_rename loc_rename
    ) def_list

let rec transform_term t =
  let rec find_map = function
      [] -> (* Mapping not found, the term is unchanged. Visit subterms *)
	{ t_desc = 
	  begin
	    match t.t_desc with
	      Var(b,l) -> Var(b, List.map transform_term l)
	    | FunApp(f,l) -> FunApp(f, List.map transform_term l)
	    | TestE _ | LetE _ | FindE _ -> 
		Parsing_helper.internal_error "If, find, and let should have been expanded (Cryptotransf.transform_term)"
	  end;
	  t_type = t.t_type;
	  t_occ = t.t_occ }
    | (mapping::l) ->
	let rec find_exp = function
	    [] -> find_map l
	  | (one_exp::l') ->
	      if t == one_exp.source_exp_instance then
	        (* Mapping found; transform the term *)
		begin
		  (*print_string "Instantiating term ";
		  Display.display_term [] t;
		  print_string " into ";
		  Display.display_term [] mapping.target_exp;
		  print_newline();*)
		  instantiate_term [] mapping one_exp mapping.target_exp
		end
	      else
		find_exp l'
	in
	find_exp mapping.expressions
  in
  find_map (!map)

and instantiate_term loc_rename mapping one_exp t =
  match t.t_desc with
    Var(b,l) ->
      let rec find_loc_rename = function
	  [] ->
	    begin
	      match l with
		[] -> (* Reference to name_list_g *)
		  begin
		    try
		      { t_desc = Var(List.assq b (!name_list_g_assoc'),
				     one_exp.name_list_g_indexes_exp);
			t_type = t.t_type;
			t_occ = Terms.new_occ() }
		    with Not_found -> 
		      Parsing_helper.internal_error "Variable not found in instantiate_term (1)"
		  end
	      | [{ t_desc = Var(b',[])}] when b' == mapping.target_repl ->
	          (* Reference to another variable of the function *)
		  begin
		    try
		      transform_term (List.assq b one_exp.after_transfo_input_vars_exp)
		    with Not_found ->
		      try
			{ t_desc = Var(List.assq b mapping.after_transfo_restr,
				       one_exp.name_list_i_indexes_exp);
			  t_type = t.t_type;
			  t_occ = Terms.new_occ() }
		      with Not_found ->
			try
			  let b'' = List.assq b one_exp.after_transfo_let_vars in
			  { t_desc = Var(b'', b''.args_at_creation);
			    t_type = t.t_type;
			    t_occ = Terms.new_occ() }
			with Not_found ->
			  Parsing_helper.internal_error "Variable not found in instantiate_term"
		  end
	      | _ -> Parsing_helper.internal_error "Unexpected variable reference in instantiate_term"
	    end
	| ((b',l'),(b'',l''))::rest_rename ->
	    if (b == b') && (List.for_all2 Terms.equal_terms l l') then
	      { t_desc = Var(b'',l'');
		t_type = t.t_type;
		t_occ = Terms.new_occ() }
	    else
	      find_loc_rename rest_rename
      in
      find_loc_rename loc_rename
  | FunApp(f,l) ->
      { t_desc = FunApp(f, List.map (instantiate_term loc_rename mapping one_exp) l);
	t_type = t.t_type;
	t_occ = Terms.new_occ() }
  | TestE(t1,t2,t3) ->
      { t_desc = TestE(instantiate_term loc_rename mapping one_exp t1,
		       instantiate_term loc_rename mapping one_exp t2,
		       instantiate_term loc_rename mapping one_exp t3);
	t_type = t.t_type;
	t_occ = Terms.new_occ() }
  | FindE(l0, t3) ->
      let find_exp = ref [] in
      List.iter (function 
	  ([b],def_list,t1,t2) ->
	    let add_find (indexes, constra, var_map) =
	      let loc_rename' = var_map @ loc_rename in
	      find_exp :=
		 (indexes, rename_def_list var_map def_list,
		  begin
		    match constra with
		      None -> instantiate_term loc_rename' mapping one_exp t1
		    | Some t -> Terms.make_and t (instantiate_term loc_rename' mapping one_exp t1)
		  end,
		  instantiate_term loc_rename' mapping one_exp t2) :: (!find_exp)
	    in
	    List.iter (fun mapping' ->
	      let cur_var_map = ref [] in
	      let var_not_found = ref [] in
	      let map_indexes = List.map (fun t -> new_binder2 (Terms.binder_from_term t) one_exp.cur_array_exp) mapping'.name_list_i_indexes in
	      List.iter (fun (b,l) ->
		try
		  let b' = List.assq b mapping'.after_transfo_restr in
		  cur_var_map := ((b,l),(b',List.map Terms.term_from_binder map_indexes))::(!cur_var_map)
		with Not_found ->
		  var_not_found := (b,l) :: (!var_not_found)
					      ) def_list;
	      if (!var_not_found) == [] then
		add_find (map_indexes, None, !cur_var_map)
	      else
	  (* Some variable was not found in after_transfo_restr;
	     Try to find it in after_transfo_let_vars *)
		try 
		  List.iter (fun one_exp' ->
		    let exp_cur_var_map = ref (!cur_var_map) in
		    if (mapping'.name_list_i_indexes == one_exp'.name_list_i_indexes_exp) && 
		      (mapping'.name_list_i_indexes == one_exp'.cur_array_exp) then
		      begin
			List.iter (fun (b,l) ->
			  let b' = List.assq b one_exp'.after_transfo_let_vars in
			  exp_cur_var_map := ((b,l),(b',List.map Terms.term_from_binder map_indexes)) :: (!exp_cur_var_map)
													   ) (!var_not_found);
			add_find (map_indexes, None, !exp_cur_var_map)
		      end
		    else
		      begin
			let exp_map_indexes = List.map (fun t -> new_binder2 (Terms.binder_from_term t) one_exp.cur_array_exp) one_exp'.cur_array_exp in
			let constra = 
		    (* Constraint mapping'.name_list_i_indexes = one_exp'.name_list_i_indexes_exp after renaming
		         mapping'.name_list_i_indexes -> map_indexes 
		         one_exp'.cur_array_exp -> exp_map_indexes
		       that is
		         map_indexes = one_exp'.name_list_i_indexes_exp { exp_map_indexes / one_exp'.cur_array_exp } *)
			  make_constra 
			    (List.map Terms.binder_from_term one_exp'.cur_array_exp) 
			    (List.map Terms.term_from_binder exp_map_indexes)
			    map_indexes one_exp'.name_list_i_indexes_exp
			in
			List.iter (fun (b,l) ->
			  let b' = List.assq b one_exp'.after_transfo_let_vars in
			  exp_cur_var_map := ((b,l),(b',List.map Terms.term_from_binder exp_map_indexes)) :: (!exp_cur_var_map)
													       ) (!var_not_found);
			add_find (map_indexes @ exp_map_indexes, constra, !exp_cur_var_map)
		      end
			) mapping'.expressions
		with Not_found ->
	    (* Variable really not found; this mapping does not
	       correspond to the expected function *)
		  ()
		    ) (!map)
	| _ ->
	    Parsing_helper.internal_error "In right members of equivalences, find should bind one index") l0;
      { t_desc = FindE(!find_exp, instantiate_term loc_rename mapping one_exp t3);
	t_type = t.t_type;
	t_occ = Terms.new_occ() }	
  | LetE(pat,t1,t2,topt) ->
      { t_desc = LetE(instantiate_pattern loc_rename mapping one_exp pat,
		      instantiate_term loc_rename mapping one_exp t1,
		      instantiate_term loc_rename mapping one_exp t2,
		      match topt with
			None -> None
		      |	Some t3 -> Some (instantiate_term loc_rename mapping one_exp t3));
	t_type = t.t_type;
	t_occ = Terms.new_occ() }

and instantiate_pattern loc_rename mapping one_exp = function
    PatVar b ->
      PatVar(try
	List.assq b one_exp.after_transfo_let_vars
      with Not_found ->
	Parsing_helper.internal_error "Variable not found")
  | PatTuple l -> PatTuple (List.map (instantiate_pattern loc_rename mapping one_exp) l)
  | PatEqual t -> PatEqual (instantiate_term loc_rename mapping one_exp t)

let rec transform_pat = function
    PatVar b -> PatVar b
  | PatTuple l -> PatTuple (List.map transform_pat l)
  | PatEqual t -> PatEqual (transform_term t)

(* put_instruct = None -> put all restrictions with empty args_at_creation
   put_instruct = Some b -> put all restrictions whose args_at_creation begins with b *)

let rec put_restr put_instruct l p =
  match l with
    [] -> p
  | (b'::l) -> 
      match b'.args_at_creation, put_instruct  with
       	({ t_desc = Var(b'',_) }::_), Some b when b'' == b -> Restr(b', put_restr put_instruct l p)
      |	[], None -> Restr(b', put_restr put_instruct l p)
      |	_ -> put_restr put_instruct l p

let rec put_restr_map put_instruct p = function
    [] -> p
  | (mapping::l) -> put_restr put_instruct (List.map snd mapping.after_transfo_restr) (put_restr_map put_instruct p l)

let put_all_restr put_instruct p =
  put_restr put_instruct (!name_list_g_target') 
    (put_restr_map put_instruct p (!map))

(* NOTE: transform_cterm is simply transform_term when 
   TestE/FindE/LetE are forbidden *)
let rec transform_cterm t = 
  match t.t_desc with
    TestE(t1,t2,t3) ->
      { t_desc = TestE(transform_term t1, 
		       transform_cterm t2, 
		       transform_cterm t3);
	t_type = t.t_type;
	t_occ = t.t_occ }
  | FindE(l0, t3) ->
      { t_desc = FindE(List.map (fun (bl, def_list, t1, t2) ->
	                 (bl, List.map (fun (b',l') -> (b', List.map transform_term l')) def_list, 
			  transform_cterm t1, 
			  transform_cterm t2)) l0, 
		       transform_cterm t3);
	t_type = t.t_type;
	t_occ = t.t_occ }	
  | LetE(pat,t1,t2,topt) ->
      { t_desc = LetE(transform_pat pat, transform_term t1, 
		      transform_cterm t2, 
		      match topt with
			None -> None
		      |	Some t3 -> Some (transform_cterm t3));
	t_type = t.t_type;
	t_occ = t.t_occ }	
  | _ -> transform_term t

let rec transform_process array_ref_def = function
    Nil -> Nil
  | Par(p1,p2) ->
      Par(transform_process array_ref_def p1,
	  transform_process array_ref_def p2)
  | Repl(b,p) ->
      (* put new restrictions as soon as all replications above them have been seen
	 List.hd b'.args_at_creation == b -> insert b' *)
      Repl(b, put_all_restr (Some b) (transform_process array_ref_def p))
  | Restr(b,p) ->
      (* Remove restriction when it is now useless *)
      let p' = transform_process array_ref_def p in
      if (List.memq b (!name_list_g_target)) ||
	 (List.exists (fun mapping ->
	   List.exists (fun (b1,b2) -> b == b2) mapping.before_transfo_restr) (!map)) then
        begin	 
	  if List.memq b array_ref_def then
            Let(PatVar b, Terms.cst_for_type b.btype, p', Nil)
          else
            p'
        end
      else
        Restr(b,p')
  | Test(t,p1,p2) ->
      Test(transform_term t, 
	   transform_process array_ref_def p1, 
	   transform_process array_ref_def p2)
  | Find(l0, p2) ->
      Find(List.map (fun (bl, def_list, t, p1) ->
	     (bl, List.map (fun (b',l') -> (b', List.map transform_term l')) def_list, 
	      transform_cterm t, 
	      transform_process array_ref_def p1)) l0, 
	   transform_process array_ref_def p2)
  | Let(pat,t,p1,p2) ->
      Let(transform_pat pat, transform_term t, 
	  transform_process array_ref_def p1, 
	  transform_process array_ref_def p2)
  | Input(t,pat,p) ->
      Input(transform_term t, transform_pat pat, 
	    transform_process array_ref_def p)
  | Output(t1,t2,p) ->
      Output(transform_term t1, transform_term t2, 
	     transform_process array_ref_def p)

let do_crypto_transform p = 
  let (lmb,_),(rmb,_),_ = !equiv in
  name_list_g' := rmb;
  let name_list_g_args_at_creation =
    match !name_list_g_target with
      [] -> []
    | (a::l) -> a.args_at_creation
  in
  name_list_g_target' := List.map (fun b -> new_binder2 b name_list_g_args_at_creation) rmb;
  name_list_g_assoc' := List.combine (!name_list_g') (!name_list_g_target');
  let array_ref = ref [] in
  let array_ref_def = ref [] in
  Transform.array_ref_process [] array_ref_def array_ref p;
  put_all_restr None (transform_process (!array_ref_def) p)

(* Compute the difference of probability *)

let rec add_counts res_exp = function
    [] -> Polynom.zero
  | (mapping::rest_map) ->
      if mapping.source_exp == res_exp then 
	Polynom.sum (Polynom.probaf_to_polynom mapping.count) (add_counts res_exp rest_map)
      else
	add_counts res_exp rest_map
      
let rec map_probaf env = function
    (Proba _ | Cst _) as x -> Polynom.probaf_to_polynom x
  | Count p -> 
      begin
	try
	  !(List.assq p env)
	with Not_found ->
	  Polynom.zero
      end
  | Mul(x,y) -> Polynom.product (map_probaf env x) (map_probaf env y)
  | Add(x,y) -> Polynom.sum (map_probaf env x) (map_probaf env y)
  | Zero -> Polynom.zero
  | _ -> Parsing_helper.internal_error "Unexpected probability formula in Cryptotransf.map_probaf"

let compute_proba() = 
  let count_values = ref [] in
  let ((_,lm),_,probaf) = !equiv in
  List.iter (fun { b_repl = count; res = res_exp } ->
    let count_current_fun = add_counts res_exp (!map) in
    let count_param = Terms.param_from_type count.btype in
    try
      ignore (List.assq count_param (!count_values));
      Parsing_helper.internal_error "In an equivalence, different functions must have a different number\nof repetitions (1)"
    with Not_found ->
      count_values := (count_param, ref count_current_fun) :: (!count_values)
		    ) lm;
  let probaf' =  map_probaf (!count_values) probaf in
  let probaf'' =
    match !name_list_g_target with
      [] -> probaf'
    | (a::_) -> Polynom.product probaf' (Polynom.probaf_to_polynom (make_prod a.args_at_creation))
  in
  Polynom.polynom_to_probaf probaf''

(* Main transformation function 
   with automatic determination of name_list_g_assoc *)

let rec find_restr accu = function
    Nil -> ()
  | Par(p1,p2) | Let(_,_,p1,p2) | Test(_,p1,p2) -> 
      find_restr accu p1;
      find_restr accu p2
  | Find(l0,p2) ->
      List.iter (fun (_,_,_,p1) -> find_restr accu p1) l0;
      find_restr accu p2
  | Restr(b,p) ->
      if not (List.memq b (!accu)) then
	accu := b :: (!accu);
      find_restr accu p
  | Repl(_,p) | Input(_,_,p) | Output(_,_,p) -> 
      find_restr accu p

(* Returns either TSuccess (prob, p') -> game transformed into p' with difference of probability prob
   or TFailure l where l is a list of possible transformations:
   values for equiv, name_list_g_assoc, and preliminary transformations to do *)
let try_with_partial_assoc () =
  let rec update_name_list_g_target() =
    map := [];
    name_list_g_target_set := false;
    let old_name_list_g_target = !name_list_g_target in
    let to_do = check_process() in
    if !name_list_g_target != old_name_list_g_target then
      update_name_list_g_target()
    else 
      (!equiv, !name_list_g_assoc, to_do)
  in
  if List.length (!name_list_g) == List.length (!name_list_g_target) then
    begin
      (* In fact, the association is fully known *)
      name_list_g_target_set := true;
      map := [];
      (!equiv, !name_list_g_assoc, check_process())
    end
  else
    update_name_list_g_target()
           

let rec try_with_restr_list = function
    [] -> TFailure []
  | (b::l) ->
      if b.btype != (List.hd (!name_list_g)).btype then
	try_with_restr_list l
      else
        begin
          name_list_g_target := [b];
          name_list_g_assoc := [List.hd (!name_list_g), b];
          try 
            let (_,_,to_do) as res = try_with_partial_assoc() in
            if to_do == [] then
              TSuccess (compute_proba(), do_crypto_transform (!whole_game))
            else
            match try_with_restr_list l with
              TSuccess (prob,p') -> TSuccess (prob,p')
            | TFailure l' -> TFailure (res::l')
          with SurelyNot -> try_with_restr_list l
        end

let crypto_transform (((lmb,_),_,_) as apply_equiv) bl_assoc p = 
  whole_game := p;
  equiv := apply_equiv;
  name_list_g := lmb;
  if (bl_assoc == []) && (lmb != []) then
    begin
      (* I need to determine bl_assoc from scratch *)
      let restr = ref [] in
      find_restr restr p;
      Terms.build_def_process p;
      try_with_restr_list (!restr)
    end
  else
    begin
      (* bl_assoc is at least partly known *)
      name_list_g_target := List.map snd bl_assoc;
      name_list_g_assoc := bl_assoc;
      try 
        let (_,_,to_do) as res = try_with_partial_assoc() in
        if to_do == [] then
          TSuccess (compute_proba(), do_crypto_transform p)
        else
          TFailure [res]
      with SurelyNot -> TFailure []
    end
*)
    
let crypto_transform apply_equiv bl_assoc p = TFailure []
