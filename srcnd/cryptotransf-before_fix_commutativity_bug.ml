(* Transform the game using an equivalence coming from a cryptographic
   primitive. This is the key operation. *)

open Types

let equal_binder_pair_lists l1 l2 =
  (List.length l1 == List.length l2) && 
  (List.for_all2 (fun (b1,b1') (b2,b2') -> b1 == b2 && b1' == b2') l1 l2)

(* Finds terms that can certainly not be evaluated in the same
   session (because they are in different branches of if/find/let)
   *)

let incompatible_terms = ref []

let add_incompatible l1 l2 =
  List.iter (fun a ->
    List.iter (fun b ->
      if a == b then
	Parsing_helper.internal_error "An expression is compatible with itself!";
      incompatible_terms := (a,b):: (!incompatible_terms)) l2) l1

let rec incompatible_def_term t = 
  match t.t_desc with
    Var(b,l) -> t::(incompatible_def_term_list l)
  | FunApp(f,l) -> t::(incompatible_def_term_list l)
  | TestE(t1,t2,t3) -> 
      let def1 = incompatible_def_term t1 in
      let def2 = incompatible_def_term t2 in
      let def3 = incompatible_def_term t3 in
      add_incompatible def2 def3;
      t::(def1 @ (def2 @ def3))
  | FindE(l0, t3,_) ->
      let def3 = incompatible_def_term t3 in
      let accu = ref def3 in
      List.iter (fun (bl, def_list, otheruses_list, t1, t2) ->
	let def = (incompatible_def_list def_list) 
	    @ (incompatible_def_list otheruses_list) 
	    @ (incompatible_def_term t1) 
	    @ (incompatible_def_term t2) in
	add_incompatible (!accu) def;
	accu := def @ (!accu)) l0;
      t::(!accu)
  | LetE(pat, t1, t2, topt) ->
      let def1 = incompatible_def_term t1 in
      let def2 = incompatible_def_pat pat in
      let def3 = incompatible_def_term t2 in
      let def4 = match topt with
	None -> []
      |	Some t3 -> incompatible_def_term t3 
      in
      add_incompatible def3 def4;
      t::(def1 @ def2 @ def3 @ def4)
  | ResE(b,t) ->
      incompatible_def_term t

and incompatible_def_term_list = function
    [] -> []
  | (a::l) -> 
      (incompatible_def_term_list l) @ 
      (incompatible_def_term a)

and incompatible_def_list = function
    [] -> []
  | ((b,l)::l') ->
      (incompatible_def_term_list l) @
      (incompatible_def_list l')
      
and incompatible_def_pat = function
    PatVar b -> []
  | PatTuple (f,l) -> incompatible_def_pat_list l
  | PatEqual t -> incompatible_def_term t

and incompatible_def_pat_list = function
    [] -> []
  | (a::l) -> 
      (incompatible_def_pat_list l) @
      (incompatible_def_pat a)


let rec incompatible_def_process p = 
  match p.i_desc with
    Nil -> []
  | Par(p1,p2) ->
      (incompatible_def_process p1) @
      (incompatible_def_process p2)
  | Repl(b,p) ->
      incompatible_def_process p 
  | Input((c,tl),pat,p) ->
      (incompatible_def_term_list tl) @
      (incompatible_def_pat pat) @
      (incompatible_def_oprocess p)

and incompatible_def_oprocess p =
  match p.p_desc with
    Yield -> []
  | Restr(b, p) ->
      incompatible_def_oprocess p 
  | Test(t,p1,p2) ->
      let def1 = incompatible_def_term t in
      let def2 = incompatible_def_oprocess p1 in
      let def3 = incompatible_def_oprocess p2 in
      add_incompatible def2 def3;
      def1 @ (def2 @ def3)
  | Find(l0, p2,_) ->
      let def3 = incompatible_def_oprocess p2 in
      let accu = ref def3 in
      List.iter (fun (bl, def_list, otheruses_list, t, p1) ->
	let def = (incompatible_def_list def_list) @
	  (incompatible_def_list otheruses_list) @
	  (incompatible_def_term t) @
	  (incompatible_def_oprocess p1) in
	add_incompatible (!accu) def;
	accu := def @ (!accu)) l0;
      !accu
  | Output((c,tl),t2,p) ->
      (incompatible_def_term_list tl) @
      (incompatible_def_term t2) @
      (incompatible_def_process p)
  | Let(pat,t,p1,p2) ->
      let def1 = incompatible_def_term t in
      let def2 = incompatible_def_pat pat in
      let def3 = incompatible_def_oprocess p1 in
      let def4 = incompatible_def_oprocess p2 in
      add_incompatible def3 def4;
      def1 @ (def2 @ (def3 @ def4))
  | EventP(t,p) ->
      (incompatible_def_term t) @
      (incompatible_def_oprocess p)

let incompatible_defs p = 
  incompatible_terms := [];
  ignore (incompatible_def_process p);
  !incompatible_terms

(* Flags *)

let stop_mode = ref false
let no_advice_mode = ref false
let debug = false

(* Check if a variable in var_list occurs in t *)

let rec occurs_var var_list t =
  match t.t_desc with
    Var(b,l) ->
      (List.memq b var_list) || (List.exists (occurs_var var_list) l)
  | FunApp(f,l) ->
      List.exists (occurs_var var_list) l
  | TestE _ | LetE _ | FindE _ | ResE _ -> 
      Parsing_helper.internal_error "If, find, let, and new should have been expanded (Cryptotransf.occurs_var)"
      
(* Check if a function symbol in fun_list occurs in t *)

let rec occurs_symb fun_list t =
  match t.t_desc with
    Var(b,l) ->
      List.exists (occurs_symb fun_list) l
  | FunApp(f,l) ->
      (List.memq f fun_list) || (List.exists (occurs_symb fun_list) l)
  | TestE _ | LetE _ | FindE _ | ResE _ -> 
      Parsing_helper.internal_error "If, find, let, and new should have been expanded (Cryptotransf.occurs_symb)"
  


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

(* The flag global_sthg_discharged is useful to check that applying the
considered cryptographic transformation is useful; this is needed because
otherwise the advice "SArenaming b" could be given when b is positions
in which it will never be transformed *)
let global_sthg_discharged = ref false
let all_names_indexes = ref ([] : (binderref * term list) list)
let names_to_discharge = ref ([] : binder list)
let symbols_to_discharge = ref ([] : funsymb list)

let check_distinct_links bl =
  let seen_binders = ref [] in
  List.iter (List.iter (fun b ->
    match b.link with
      TLink { t_desc = Var(b',l) } -> 
	if (List.memq b' (!seen_binders)) then raise SurelyNot;
	seen_binders := b' :: (!seen_binders)
    | TLink t -> Parsing_helper.internal_error "unexpected link in check_distinct_links"
    | _ -> (* binder not linked; should not happen when no useless
	      new is present in the equivalence 
	      Now happens also for all names of the LHS that are not above the considered expression
	      because bl is the list of all name groups in the LHS, and not only above the considered expression *) ())) bl

(* Suggests a transformation to explicit the value of b
   If there are several of b, we start by SArenaming b,
   they RemoveAssign will probably be suggested at the next
   try (there will now be a single definition for each variable
   replacing b). Advantage: we avoid doing RemoveAssign for copies
   of b for which it is not necessary.
 *)
let explicit_value b =
  match b.def with
    [] | [_] -> RemoveAssign (OneBinder b)
  | _ -> SArenaming b

(*
ins_accu stores the advised instructions. 
The structure is the following:
   a list of pairs (list of advised instructions, priority)
The priority is an integer; the lower integer means the higher priority.
The elements of the list are always ordered by increasing values of priority. 
The transformation may succeed by applying one list of advised instructions.
They will be tried by priority.

*)

let success_no_advice = [([],0)]

let is_success_no_advice = function 
    ([],_)::_ -> true
  | [] -> Parsing_helper.internal_error "ins_accu should not be empty"
  | _ -> false

(* Adds an advised instruction to ins_accu *)

let add_ins ins ins_accu =
  List.map (fun (l,p) -> ((Terms.add_eq ins l), p)) ins_accu

(* Makes a "or" between two lists of advised instructions, by merging the lists;
   the list is cut after the empty advice *)

let eq_ins_set l1 l2 =
  (List.for_all (fun i1 -> List.exists (Terms.equal_instruct i1) l2) l1) &&
  (List.for_all (fun i2 -> List.exists (Terms.equal_instruct i2) l1) l2)

let rec merge_ins ins_accu1 ins_accu2 =
  match (ins_accu1, ins_accu2) with
    (l1,p1)::r1, (l2,p2)::r2 ->
      if p1 < p2 then 
	(* Put p1 first *)
	if l1 == [] then
	  [(l1,p1)]
	else
	  (l1,p1)::(merge_ins r1 ins_accu2)
      else if p1 > p2 then
	(* Put p2 first *)
	if l2 == [] then
	  [(l2,p2)]
	else
	  (l2,p2)::(merge_ins ins_accu1 r2)
      else
	(* Put the shortest list first when priorities are equal *)
	if l1 == [] then
	  [(l1,p1)]
	else if l2 == [] then
	  [(l2,p2)]
	else if List.length l1 <= List.length l2 then
	  (* Remove duplicates *)
	  if eq_ins_set l1 l2 then
	    (l1,p1)::(merge_ins r1 r2)
	  else
	    (l1,p1)::(merge_ins r1 ins_accu2)
	else
	  (l2,p2)::(merge_ins ins_accu1 r2)
  | [], ins_accu2 -> ins_accu2
  | ins_accu1, [] -> ins_accu1

(* Makes a "and" between two lists of advised instructions, by concatenating the sublists
   and adding priorities 

   First, "and" between one element and a list
*)

let and_ins1 (l,p) ins_accu =
  List.map (fun (l',p') -> ((Terms.union_eq l l'), p+p')) ins_accu

(* ... then "and" between two ins_accu *)

let rec and_ins ins_accu1 ins_accu2 =
  match ins_accu1 with
    [] -> []
  | lp1::r1 -> merge_ins (and_ins1 lp1 ins_accu2) (and_ins r1 ins_accu2)

(* Map the elements of a list, and make a "and" of the resulting
   advised instructions *)

let rec map_and_ins f = function
    [] -> success_no_advice
  | (a::l) -> and_ins (f a) (map_and_ins f l)


(* Richer structure for ins_accu:
        a list of tuples (list of advised instructions, sthg_discharged, names_to_discharge, priority)

NOTE: Should I also add all_names_indexes and the links between variables and names/terms to ins_accu?
They vary with the choices, but they are used only when the procedure succeeds with a first choice without
advice, and that's really the value stored in the references, so the change is not necessary.
By the way, I perhaps eliminate a bit quickly the choices with advice when I find a choice
without advice and with higher priority, because that choice may actually fail later. For now, it seems ok.
   *)

let success_no_advice2 = [([],false,[],0)]

let is_success_no_advice2 = function 
    ([],_,_,_)::_ -> true
  | [] -> Parsing_helper.internal_error "ins_accu should not be empty"
  | _ -> false

(* Adds an advised instruction to ins_accu *)

let add_ins2 ins ins_accu =
  List.map (fun (l,s,n,p) -> ((Terms.add_eq ins l), s,n,p)) ins_accu

let set_sthg_discharged2 ins_accu =
  List.map (fun (l,s,n,p) -> (l, true,n,p)) ins_accu

let add_name_to_discharge2 b ins_accu =
   List.map (fun (l,s,n,p) -> (l,s, (if List.memq b n then n else b::n),p)) ins_accu

(* Makes a "or" between two lists of advised instructions, by merging the lists;
   the list is cut after the empty advice *)

let eq_name_set l1 l2 =
  (List.for_all (fun i1 -> List.memq i1 l2) l1) &&
  (List.for_all (fun i2 -> List.memq i2 l1) l2)

let rec merge_ins2 ins_accu1 ins_accu2 =
  match (ins_accu1, ins_accu2) with
    (l1,s1,n1,p1)::r1, (l2,s2,n2,p2)::r2 ->
      if p1 < p2 then 
	(* Put p1 first *)
	if l1 == [] then
	  [(l1,s1,n1,p1)]
	else
	  (l1,s1,n1,p1)::(merge_ins2 r1 ins_accu2)
      else if p1 > p2 then
	(* Put p2 first *)
	if l2 == [] then
	  [(l2,s2,n2,p2)]
	else
	  (l2,s2,n2,p2)::(merge_ins2 ins_accu1 r2)
      else
	(* Put the shortest list first when priorities are equal *)
	if l1 == [] then
	  [(l1,s1,n1,p1)]
	else if l2 == [] then
	  [(l2,s2,n2,p2)]
	else if List.length l1 <= List.length l2 then
	  (* Remove duplicates *)
	  if (eq_ins_set l1 l2) && (s1 == s2) && (eq_name_set n1 n2) then
	    (l1,s1,n1,p1)::(merge_ins2 r1 r2)
	  else
	    (l1,s1,n1,p1)::(merge_ins2 r1 ins_accu2)
	else
	  (l2,s2,n2,p2)::(merge_ins2 ins_accu1 r2)
  | [], ins_accu2 -> ins_accu2
  | ins_accu1, [] -> ins_accu1

(* Intersection of sets of names to discharge, to get the names that must be discharged in all cases *)

let rec intersect l1 = function 
    [] -> []
  | (a::l) -> if List.memq a l1 then a::(intersect l1 l) else intersect l1 l

let rec get_inter_names = function
    [] -> []
  | [(_,_,n,_)] -> n
  | (_,_,n,_)::l -> intersect n (get_inter_names l)

(* Association lists (binderref, value) *)

let rec assq_binderref br = function
    [] -> raise Not_found
  | (br',v)::l ->
      if Terms.equal_binderref br br' then
	v
      else
	assq_binderref br l

(* In check_instance_of_rec, mode = AllEquiv for the root symbol of functions marked [all] 
   in the equivalence. Only in this case a function symbol can be discharged. *)

let rec check_instance_of_rec next_f all_names_exp mode term t lhs_array_ref_map ins_accu =
  match (term.t_desc, t.t_desc) with
    FunApp(f,[t1;t2]), FunApp(f',[t1';t2']) when f == f' && f.f_options land Settings.fopt_COMMUT != 0 ->
      (* Commutative function symbols *)
      begin
	let ins_accu' = 
	  if (mode == AllEquiv) && (List.memq f (!symbols_to_discharge)) then
	    set_sthg_discharged2 ins_accu
	  else
	    ins_accu
	in
	let old_bound_vars = !Terms.current_bound_vars in
	let old_name_indexes = !all_names_indexes in
	let rec cleanup_until l =
	  if l == old_bound_vars then () else
	  match l with
	    [] -> Parsing_helper.internal_error "Should not reach empty list"
	  | (v::l') ->
	      v.link <- NoLink;
	      cleanup_until l'
	in
	try
	  let (lhs_array_ref_map', r) = 
	    check_instance_of_rec (check_instance_of_rec next_f all_names_exp ExistEquiv t2 t2') all_names_exp ExistEquiv t1 t1' lhs_array_ref_map ins_accu'
	  in
	  match r with
	    ([],_,_,_)::_ -> (lhs_array_ref_map', r)
	  | [] -> Parsing_helper.internal_error "ins_accu should not be empty (2)"
	  | _ ->
	      cleanup_until (!Terms.current_bound_vars);
	      Terms.current_bound_vars := old_bound_vars;
              all_names_indexes := old_name_indexes;
	      let (lhs_array_ref_map', r') =
		check_instance_of_rec (check_instance_of_rec next_f all_names_exp ExistEquiv t1 t2') all_names_exp ExistEquiv t2 t1' lhs_array_ref_map ins_accu'
	      in
	      (lhs_array_ref_map', merge_ins2 r r')
	with SurelyNot ->
	  cleanup_until (!Terms.current_bound_vars);
	  Terms.current_bound_vars := old_bound_vars;
          all_names_indexes := old_name_indexes;
	  check_instance_of_rec (check_instance_of_rec next_f all_names_exp ExistEquiv t1 t2') all_names_exp ExistEquiv t2 t1' lhs_array_ref_map ins_accu'
      end
  | FunApp(f,l), FunApp(f',l') when f == f' ->
      let ins_accu' = 
	if (mode == AllEquiv) && (List.memq f (!symbols_to_discharge)) then
	  set_sthg_discharged2 ins_accu
	else
	  ins_accu
      in
      check_instance_of_rec_list next_f all_names_exp l l' lhs_array_ref_map ins_accu'
  | FunApp(f,l), FunApp(_,_) -> 
      raise SurelyNot
	(* Might work after rewriting with an equation *)
  | FunApp(f,l), Var(b,_) ->
      if (!no_advice_mode) || (not (List.exists (function 
	  { definition = DProcess { p_desc = Let _ }} -> true
	| { definition = DTerm { t_desc = LetE _ }} -> true
	| _ -> false) b.def)) then
	raise SurelyNot
      else
        (* suggest assignment expansion on b *)
	next_f lhs_array_ref_map (add_ins2 (explicit_value b) ins_accu)
  | FunApp(f,l), (TestE _ | FindE _ | LetE _ | ResE _) ->
      Parsing_helper.internal_error "If, let, find, and new should have been expanded (Cryptotransf.check_instance_of_rec)"
  | Var(b,l), _ when List.for_all2 Terms.equal_terms b.args_at_creation l ->
      begin
        match b.link with
          TLink t' -> 
	    if not (Terms.equal_terms t t') then
	      raise SurelyNot
	    else
	      next_f lhs_array_ref_map ins_accu
        | NoLink ->
            begin
              try
                let name_group = List.find (List.memq b) all_names_exp in
                match t.t_desc with
                  Var(b',l') ->
                    begin
                      (* check that b' is defined by a restriction *)
		      if not (Terms.is_restr b') then 
			begin
			  if (List.for_all (function
			      { definition = DProcess { p_desc = Restr _}} -> true
			    | { definition = DProcess { p_desc = Let _}} -> true
			    | _ -> false) b'.def) && (not (!no_advice_mode))
			  then
			    next_f lhs_array_ref_map (add_ins2 (explicit_value b') ins_accu)
			  else
			    raise SurelyNot
			end
		      else 
			begin
                          (* check that b' is of the right type *)
			  if b'.btype != b.btype then raise SurelyNot; 
		          (* check that b' is not used in a query *)
			  if Transform.occurs_in_queries b' then raise SurelyNot;

			  Terms.link b (TLink t);
                          (* Note: when I catch SurelyNot, backtrack on names_to_discharge *)
			  let ins_accu'' = 
			    if not (List.memq b' (!names_to_discharge)) then
			      begin
				if !stop_mode then 
				(* Do not add more names in stop_mode *)
				  raise SurelyNot
				else
				  add_name_to_discharge2 b' ins_accu
			      end
			    else
			      set_sthg_discharged2 ins_accu 
			  in
			  let group_head = List.hd name_group in
			  try
                            let indexes = assq_binderref (group_head, l) (!all_names_indexes) in
                            if not (Terms.equal_term_lists indexes l') then
			      raise SurelyNot
			    else
			      next_f lhs_array_ref_map ins_accu''
			  with Not_found -> 
                            (* Note: when I catch SurelyNot, backtrack on all_names_indexes *)
                            all_names_indexes := ((group_head,l), l') :: (!all_names_indexes);
                            next_f lhs_array_ref_map ins_accu''
			end
                    end
                | _ -> raise SurelyNot
              with Not_found -> 
                begin
                  (* check that t is of the right type *)
                  if t.t_type != b.btype then
                    raise SurelyNot; 
                  Terms.link b (TLink t);
		  next_f lhs_array_ref_map ins_accu
                end
            end
      end
  | Var(b,l), _ -> 
      (* variable used with indices given in argument *)
      begin
	(* Check if (b,l) is already mapped *)
	try 
	  let t' = assq_binderref (b,l) lhs_array_ref_map in
	  (* (b,l) is already mapped *)
	  if not (Terms.equal_terms t t') then
	    raise SurelyNot
	  else
	    next_f lhs_array_ref_map ins_accu
	with Not_found ->
	  (* (b,l) is not mapped yet *)
          match t.t_desc with
            Var(b',l') ->
                    begin
                      (* check that b' is defined by a restriction *)
		      if not (Terms.is_restr b') then 
			begin
			  if (List.for_all (function
			      { definition = DProcess { p_desc = Restr _} } -> true
			    | { definition = DProcess { p_desc = Let _} } -> true
			    | _ -> false) b'.def) && (not (!no_advice_mode))
			  then
			    next_f lhs_array_ref_map (add_ins2 (explicit_value b') ins_accu)
			  else
			    raise SurelyNot
			end
		      else 
			begin
                          (* check that b' is of the right type *)
			  if b'.btype != b.btype then raise SurelyNot; 
		          (* check that b' is not used in a query *)
			  if Transform.occurs_in_queries b' then raise SurelyNot;

			  let lhs_array_ref_map' = ((b,l), t)::lhs_array_ref_map in
                          (* Note: when I catch SurelyNot, backtrack on names_to_discharge *)
			  let ins_accu'' = 
			    if not (List.memq b' (!names_to_discharge)) then
			      begin
				if !stop_mode then 
				(* Do not add more names in stop_mode *)
				  raise SurelyNot
				else
				  add_name_to_discharge2 b' ins_accu
			      end
			    else
			      set_sthg_discharged2 ins_accu 
			  in
			  try
			    let name_group = List.find (List.memq b) all_names_exp in
			    let group_head = List.hd name_group in
			    try
                              let indexes = assq_binderref (group_head,l) (!all_names_indexes) in
                              if not (Terms.equal_term_lists indexes l') then
				raise SurelyNot
			      else
				next_f lhs_array_ref_map' ins_accu''
			    with Not_found -> 
                            (* Note: when I catch SurelyNot, backtrack on all_names_indexes *)
                              all_names_indexes := ((group_head,l), l') :: (!all_names_indexes);
                              next_f lhs_array_ref_map' ins_accu''
			  with Not_found ->
			    Display.display_binder b;
			    print_string " not in ";
			    Display.display_list (Display.display_list Display.display_binder) all_names_exp;
			    Parsing_helper.internal_error "Array reference in the left-hand side of an equivalence should always be a reference to a restriction"
			end
                    end
          | _ -> raise SurelyNot
      end
  | _ -> Parsing_helper.internal_error "if, find, defined should have been excluded from left member of equivalences"

and check_instance_of_rec_list next_f all_names_exp l l' lhs_array_ref_map ins_accu =
  match l,l' with
    [],[] -> next_f lhs_array_ref_map ins_accu
  | a::l, a'::l' ->
      check_instance_of_rec_list (check_instance_of_rec next_f all_names_exp ExistEquiv a a') all_names_exp l l' lhs_array_ref_map ins_accu
  | _ -> Parsing_helper.internal_error "different length in check_instance_of_rec_list"

let clean_up_instance_of () =
  Terms.cleanup();
  all_names_indexes := []

let check_instance_of all_names_exp mode term t =
  if !Terms.current_bound_vars != [] then
    Parsing_helper.internal_error "Bound vars should be cleaned up (check_instance_of)";
  try 
    if debug then
      begin
	print_string "Check instance of ";
	Display.display_term [] term;
	print_string " ";
	Display.display_term [] t;
	print_newline();
      end;
    let (lhs_array_ref_map, il) = check_instance_of_rec (fun lhs_array_ref_map ins_accu -> (lhs_array_ref_map, ins_accu)) all_names_exp mode term t [] success_no_advice2 in
    (* Remove the choices that discharge nothing *)
    let il = List.filter (fun (_,s,_,_) -> s) il in
    (* Add to names_to_discharge the names that must be discharged in all cases
       It has been verified when adding names in the elements of il that they are not
       already in names_to_discharge *)
    names_to_discharge := (get_inter_names il) @ (!names_to_discharge);
    begin
      match il with
	[] -> raise SurelyNot (* This transformation could not discharge any name -> useless *)
      |	[([],_,_,_)] -> 
	  check_distinct_links all_names_exp; (* Check that names are linked to distinct binders *)
      | ([],_,_,_)::_ -> 
	  Parsing_helper.internal_error "when the first element has no advice, the following elements should have been discarded from ins_accu"
      |	_ -> ()
    end;
    global_sthg_discharged := true;
    if debug then
      begin
	print_string "check_instance_of ";
	Display.display_term [] term;
	print_string " ";
	Display.display_term [] t;
	match il with
	  [([],_,_,_)] -> print_string " succeeded\n"
	| [] -> Parsing_helper.internal_error "ins_accu should not be empty (4)"
	| _ ->
	    print_string " succeeded with advice ";
	    List.iter (fun (l,s,n,p) -> Display.display_list Display.display_instruct l;
	      print_string " priority: ";
	      print_int p;
	      print_string "\n") il
      end;
    (* restore the simpler format for ins_accu, that contains pairs (list of advised instr, priority) *)
    (lhs_array_ref_map, List.map (fun (l,_,_,p) -> (l,p)) il)
  with SurelyNot ->
    clean_up_instance_of(); (* Clean up bindings when fails *)
    raise SurelyNot

(* Check whether t is an instance of a subterm of term
   Useful when t is just a test (if/find) or an assignment,
   so that by syntactic transformations of the game, we may
   arrange so that a superterm of t is an instance of term *)

let rec check_instance_of_subterms all_names_exp mode term t =
  match term.t_desc with
    Var(b,l) -> raise SurelyNot
  | FunApp(f,l) ->
      check_instance_of_list all_names_exp mode l t
  | TestE _ | LetE _ | FindE _ | ResE _ ->
      Parsing_helper.internal_error "if, let, find, and new should have been excluded from left member of equivalences"

and check_instance_of_list all_names_exp mode l t = 
  match l with
    [] -> raise SurelyNot
  | (term::l) -> 
      let old_name_indexes = !all_names_indexes in
      let old_names_to_discharge = !names_to_discharge in
      try
	(* We can forget the lhs_array_ref_map since the transformation
           will not be performed anyway; we are just collecting advice *)
	let (_, ins_accu) = check_instance_of all_names_exp mode term t	 in
	ins_accu
      with SurelyNot ->
        all_names_indexes := old_name_indexes;
        names_to_discharge := old_names_to_discharge;
	try 
	  check_instance_of_subterms all_names_exp mode term t
	with SurelyNot ->
          all_names_indexes := old_name_indexes;
          names_to_discharge := old_names_to_discharge;
	  check_instance_of_list all_names_exp mode l t

(* Reverse substitution: all array references must be suffixes of 
   indexes, and these values are replaced with variables 
   of cur_array *)

exception Failure

let rec reverse_subst forbidden_cur_array indexes cur_array t =
  Terms.build_term2 t 
   (match t.t_desc with
      Var(b,l) -> 
        if List.exists (fun b' -> b == b' && Terms.equal_term_lists l b'.args_at_creation) forbidden_cur_array then
          raise Failure;
        Var(b, reverse_subst_index forbidden_cur_array indexes cur_array l)
    | FunApp(f,l) -> 
        FunApp(f, List.map (reverse_subst forbidden_cur_array indexes cur_array) l)
    | TestE _ | LetE _ | FindE _ | ResE _ -> 
	Parsing_helper.internal_error "If, find, let, and new should have been expanded (Cryptotransf.reverse_subst)")

and reverse_subst_index forbidden_cur_array indexes cur_array l =
  let len_suffix = Terms.len_common_suffix l indexes in
  (List.map (reverse_subst forbidden_cur_array indexes cur_array) 
     (Terms.remove_suffix len_suffix l)) 
  @ (Terms.lsuffix len_suffix cur_array)

(* First pass: check and collect mappings of variables and expressions *)

type one_exp =
   { source_exp_instance : term; (* The expression to replace -- physical occurrence *)
     after_transfo_let_vars : (binder * binder) list; 
        (* List of (b,b') where b is a binder created by a let in
           the right member of the equivalence and b' is its image in 
           the transformed process. The indexes at creation of b' are cur_array_exp *)
     cur_array_exp : term list; 
        (* Value of cur_array at this expression in the process. *)
     name_indexes_exp : (binder list * term list) list; 
        (* Values of indexes of names in this expression *)
     before_transfo_array_ref_map : (binderref * binderref) list;
     mutable after_transfo_array_ref_map : (binderref * binderref) list;
     (* after_transfo_array_ref_map is declared mutable, because it will be computed
	only after the whole map is computed, so we first define it as [] and later
	assign its real value to it.
        ((b, l), (b', l'))
        b = binder in the LHS
	l = its indices in the LHS
        b' = the corresponding binder in the process
        l' = its indices in the process
     *)
     before_transfo_input_vars_exp : (binder * term) list;
        (* List of (b,t) where b is a binder defined by an input in the 
           left member of the equivalence and the term t is its image in the process *)        
     after_transfo_input_vars_exp : (binder * term) list 
        (* List of (b,t) where b is a binder defined by an input in the 
           right member of the equivalence and the term t is its image in the process *)
   }

type mapping =
   { mutable expressions : one_exp list; (* List of uses of this expression, described above *)
     before_transfo_name_table : (binder * binder) list list;
     after_transfo_name_table : (binder * binder) list list;
     before_transfo_restr : (binder * binder) list;
        (* List of (b, b') where b is a binder created by a restriction in the
           left member of the equivalence, and b' is its image in the initial process. *)
     source_exp : term; (* Left-member expression in the equivalence *)
     source_args : binder list; (* Input arguments in left-hand side of equivalence *)
     after_transfo_restr : (binder * binder) list; 
        (* List of (b, b') where b is a binder created by a restriction in the
           right member of the equivalence, and b' is its image in the transformed process.
           The indexes at creation of b' are name_list_i_indexes *)
     rev_subst_name_indexes : (binder list * term list) list; 
        (* List of binders at creation of names in name_list_i in the process *)
     target_exp : term; (* Right-member expression in the equivalence *)
     target_args : binder list; (* Input arguments in right-hand side of equivalence *)
     count : (binder * (binder * binder) list list option * probaf) list 
        (* Replication binders of the right member of the equivalence, 
	   and number of times each of them is repeated, with associated name
	   table: when several repl. binders have the same name table, they
           should be counted only once.*)
   }

(* expression to insert for replacing source_exp_instance 
     = (after_transfo_input_vars_exp, 
        after_transfo_restr[name_indexes_exp], 
        after_transfo_let_vars[cur_array_exp]) ( target_exp )
*)

let map = ref ([] : mapping list)

let equiv = ref ((([],[],[],StdEqopt),[]) : equiv_nm)

let whole_game = ref { proc = Terms.nil_proc; game_number = -1 }
let whole_game_next = ref { proc = Terms.nil_proc; game_number = -1 }

let incompatible_terms = ref []

let rebuild_map_mode = ref false

let is_incompatible t1 t2 =
  List.exists (fun (t1',t2')  -> ((t1 == t1') && (t2 == t2')) || 
  ((t1 == t2') && (t2 == t1'))) (!incompatible_terms)

let rec find_rm lm lm_list rm_list =
  match (lm_list,rm_list) with
    [],_ | _,[] -> Parsing_helper.internal_error "Could not find left member"
  | (a::l,b::l') -> 
      if lm == a then b else find_rm lm l l'


let rec insert l r m p = function
    [] -> [(l,r,m,p)]
  | (((_,_,_,p') as a)::rest) as accu ->
      if p < p' then (l,r,m,p)::accu else a::(insert l r m p rest)

let rec collect_expressions accu accu_names_lm accu_names_rm accu_repl_rm mode lm rm = 
  match lm, rm with
    ReplRestr(repl, restr, funlist), ReplRestr(repl', restr', funlist') ->
      List.iter2 (fun fg fg' ->
        collect_expressions accu (restr :: accu_names_lm) (restr' :: accu_names_rm) (repl' :: accu_repl_rm) mode fg fg') funlist funlist'
  | Fun(ch, args, res, (priority, _)), Fun(ch', args', res', _) ->
      accu := insert (accu_names_lm, args, res) (accu_names_rm, accu_repl_rm, args', res') mode priority (!accu)
  | _ -> Parsing_helper.internal_error "left and right members of equivalence do not match"

let rec collect_all_names accu = function
    ReplRestr(_, restr, funlist) ->
      accu := restr :: (!accu);
      List.iter (collect_all_names accu) funlist
  | Fun _ -> ()

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
  | FindE(l0,t3,_) ->
      List.iter (fun (bl,def_list,otheruses_list,t1,t2) ->
	List.iter (fun (_,l) -> List.iter (letvars_from_term accu) l) def_list;
	List.iter (fun (_,l) -> List.iter (letvars_from_term accu) l) otheruses_list;
	letvars_from_term accu t1;
	letvars_from_term accu t2) l0;
      letvars_from_term accu t3      
  | ResE(b,t) ->
      accu := b :: (!accu);
      letvars_from_term accu t

and vars_from_pat accu = function
    PatVar b -> accu := b :: (!accu)
  | PatTuple (f,l) -> List.iter (vars_from_pat accu) l
  | PatEqual t -> letvars_from_term accu t

let new_binder2 b args_at_creation = 
  Terms.create_binder b.sname (Terms.new_vname()) b.btype args_at_creation

let new_binder3 t args_at_creation = 
  Terms.create_binder "@i" (Terms.new_vname())  t.t_type args_at_creation

let rec make_prod = function
    [] -> Cst 1.0
  | [a] -> Count (Terms.param_from_type a.t_type)
  | (a::l) -> Mul (Count (Terms.param_from_type a.t_type), make_prod l)

let rec longest_common_suffix above_indexes current_indexes =
  match above_indexes with
    [] -> 0
  | (first_above_indexes :: rest_above_indexes) ->
      let l_rest = longest_common_suffix rest_above_indexes current_indexes in
      let l_cur = Terms.len_common_suffix first_above_indexes current_indexes in
      max l_rest l_cur

let rec make_count repl ordered_indexes before_transfo_name_table =
  match repl, ordered_indexes, before_transfo_name_table with
    [],[],[] -> []
  | (repl1::repll,index1::indexl,nt1::ntl) ->
      let len = longest_common_suffix indexl index1 in
      (repl1, 
       (if nt1 == [] then None else Some before_transfo_name_table), 
       make_prod (Terms.remove_suffix len index1)) :: (make_count repll indexl ntl)
  | _ -> Parsing_helper.internal_error "make_count" 

let check_same_args_at_creation = function
    [] -> ()
  | (a::l) -> 
      if not (List.for_all (fun b -> 
	(Terms.equal_term_lists b.args_at_creation a.args_at_creation)) l)
	  then raise SurelyNot

(* l1 and l2 are tables [[(binder in equiv, corresponding name);...];...]
   common_names return the number of name groups in common between l1 and l2 *)

let all_diff l1 l2 =
  if not (List.for_all (fun b -> not (List.memq b (List.map snd (List.concat l1))))
    (List.map snd (List.concat l2))) then raise SurelyNot

let rec common_names_rev l1 l2 =
  match l1,l2 with
    [],_ -> 0
  | _,[] -> 0
  | la1::lrest1, la2::lrest2 ->
      if (List.length la1 == List.length la2) && 
	(List.for_all2 (fun (b1, b1') (b2, b2') ->
	  (b1 == b2) && (b1' == b2')) la1 la2) then
	begin
	  let r = common_names_rev lrest1 lrest2 in
	  if (r == 0) && (la1 == []) then 
	    0
	  else
	    1+r
	end
      else
	begin
	  all_diff l1 l2;
	  0
	end

(* Compute the formula for upper indexes from current indexes *)

let rec rev_subst_indexes cur_array current_indexes name_table indexes =
  match name_table, indexes with
    [],[] -> []
  | name_table1::rest_name_table, ((names, index)::rest_indexes) ->
      begin
      if names == [] && index == [] then
	([],[])::(rev_subst_indexes cur_array current_indexes rest_name_table rest_indexes)
      else
	let args_at_creation = (snd (List.hd name_table1)).args_at_creation in
	match current_indexes with
	  None -> 
	    (names, index)::
	    (rev_subst_indexes cur_array (Some (args_at_creation, args_at_creation)) rest_name_table rest_indexes)
	| Some (cur_idx, cur_args_at_creation) -> 
	    (names, reverse_subst_index cur_array cur_idx cur_args_at_creation index)::
	    (rev_subst_indexes cur_array (Some (index, args_at_creation)) rest_name_table rest_indexes)
      end
  | _ -> Parsing_helper.internal_error "rev_subst_indexes"

(* Add missing names in the environment, if any *)

exception Next_empty
exception CouldNotComplete

let get_name b env =
  match List.assq b env with
    { t_desc = Var(b',_) } -> b'
  | _ -> Parsing_helper.internal_error "unexpected value for name in env"

let rec check_compatible name_indexes env rev_subst_name_indexes names_exp name_table =
  match (rev_subst_name_indexes, names_exp, name_table) with
    [],[],[] -> ()
  | (_::rev_subst_name_indexes_rest, names_exp_first::names_exp_rest, 
     name_table_first::name_table_rest) ->
       (* Complete the environment env if compatible *)
       List.iter2 (fun b1 (b,b') ->
	 if b != b1 then raise SurelyNot;
	 try 
	   if (get_name b1 (!env)) != b' then raise SurelyNot
	 with Not_found ->
	   env := (b,Terms.term_from_binder b') :: (!env)) names_exp_first name_table_first;
       (* Complete the indexes name_indexes if needed
	  The first indexes are always set, because there is at least one name in
	  the first sequence -- the one use to complete the sequence. We set the indexes
	  in the next sequence if there is one. *)
       begin
	 match (rev_subst_name_indexes_rest, names_exp_rest) with
	   [],[] -> ()
	 | (names, indexes)::_, (b0::_)::_ ->
	     begin
	     try 
	       ignore (assq_binderref (b0, b0.args_at_creation) (!name_indexes))
	       (* Found; will be checked for compatibility later *)
	     with Not_found ->
	       (* Add missing indexes *)
	       let b1 = List.hd names_exp_first in 
	       let indexes_above = assq_binderref (b1, b1.args_at_creation) (!name_indexes) in
	       let args_at_creation = (get_name b1 (!env)).args_at_creation in
	       name_indexes := ((b0, b0.args_at_creation), List.map (Terms.subst (List.map Terms.binder_from_term 
                  args_at_creation) indexes_above) indexes) :: (!name_indexes)
	     end
	 | _ -> Parsing_helper.internal_error "bad length in check_compatible (2)"
       end;   
       check_compatible name_indexes env rev_subst_name_indexes_rest names_exp_rest name_table_rest
  | _ -> Parsing_helper.internal_error "bad length in check_compatible"

let rec complete_with name_indexes env names_exp b0 = function
    [] -> raise CouldNotComplete (* Could not complete: the name is not found in the map *)
  | (mapping::rest_map) ->
      let b0' = get_name b0 (!env) in
      let rec find_b0' rev_subst_name_indexes name_table = 
	match (rev_subst_name_indexes, name_table) with
	  [],[] -> (* Not found, try other map element *)
	    complete_with name_indexes env names_exp b0 rest_map
	| (_::rev_subst_rest), (name_table_first::name_table_rest) ->
	    if List.exists (fun (b,b') -> b' == b0') name_table_first then
	      check_compatible name_indexes env rev_subst_name_indexes names_exp name_table
	    else
	      find_b0' rev_subst_rest name_table_rest
	| _ -> Parsing_helper.internal_error "bad length in complete_with"
      in
      find_b0' mapping.rev_subst_name_indexes mapping.before_transfo_name_table 

let rec complete_env name_indexes env = function
    [] -> ()
  | (bl::names_exp_rest) ->
      if bl = [] then
	complete_env name_indexes env names_exp_rest
      else 
	let name_present b = List.mem_assq b (!env) in
	if List.for_all name_present bl then
	  try
	    complete_env name_indexes env names_exp_rest
	  with Next_empty ->
	    complete_with name_indexes env (bl::names_exp_rest) (List.hd bl) (!map)
	else
	  try
	    let b0 = List.find name_present bl in
	    complete_with name_indexes env (bl::names_exp_rest) b0 (!map)
	  with Not_found ->
	    raise Next_empty


let complete_env_call name_indexes env all_names_exp =
  let env_ref = ref env in
  let name_indexes_ref = ref name_indexes in
  try
    complete_env name_indexes_ref env_ref all_names_exp;
    (!name_indexes_ref, !env_ref)
  with Next_empty -> (* Could not complete *)
    raise CouldNotComplete


(* Returns the list of variables defined in a term.
   Raises SurelyNot when it defines several times the same variable. *)

let rec get_def_vars accu t =
  match t.t_desc with
    Var(_,l) | FunApp(_,l) -> List.fold_left get_def_vars accu l
  | TestE(t1,t2,t3) ->
      get_def_vars (get_def_vars (get_def_vars accu t1) t2) t3
  | LetE(pat,t1,t2,topt) ->
      let accu' =
	match topt with
	  None -> accu
	| Some t3 -> get_def_vars accu t3
      in
      get_def_vars_pat (get_def_vars (get_def_vars accu' t1) t2) pat
  | ResE(b,t) ->
      if List.memq b accu then 
	raise SurelyNot;
      get_def_vars (b::accu) t
  | FindE(l0,t3,_) ->
      let accu' = get_def_vars accu t3 in
      List.fold_left (fun accu (bl,_,_,t1,t2) ->
	if List.exists (fun b -> List.memq b accu) bl then
	  raise SurelyNot;
	get_def_vars (get_def_vars (bl @ accu) t1) t2) accu' l0

and get_def_vars_pat accu = function
    PatVar b ->
      if List.memq b accu then 
	raise SurelyNot;
      b::accu
  | PatTuple(_,l) ->
      List.fold_left get_def_vars_pat accu l
  | PatEqual t -> get_def_vars accu t


(* Find the array indices that are really useful in the term t *)

let rec used_indices indices used t =
  try
    let index = List.find (Terms.equal_terms t) indices in
    if not (List.memq index (!used)) then
      used := index :: (!used)
  with Not_found ->
    match t.t_desc with
      Var(_,l) | FunApp(_,l) -> 
	List.iter (used_indices indices used) l
    | TestE _ | LetE _ |FindE _ | ResE _ ->
	Parsing_helper.internal_error "If, find, let, and new should have been expanded (Cryptotransf.used_indices)"

(* ta_above: when there is a test (if/find) or an assignment
   just above t, contains the instruction to expand this test or assignment;
   otherwise empty list 

   Return the list of transformations to apply before so that the desired
   transformation may work. When this list is empty, the desired transformation
   is ok. Raises SurelyNot when the desired transformation is impossible,
   even after preliminary changes.
*)

let rec check_term ((is_in_find_cond, find_indices) as find_info) ta_above cur_array defined_refs t =
  if not ((occurs_var (!names_to_discharge) t) || 
          (occurs_symb (!symbols_to_discharge) t)) then
     (* The variables in names_to_discharge do not occur in t => OK *)
     success_no_advice
  else
  try 
    let mapping = 
      List.find (fun mapping -> List.exists (fun exp ->
	exp.source_exp_instance == t
	  ) mapping.expressions) (!map)
    in
    let exp = 
      List.find (fun exp ->
	exp.source_exp_instance == t
	  ) mapping.expressions
    in
    (* The term t is already discharged in the map => OK
       The term t itself is ok, we just need to recheck the arguments
       of t; they may need to be further discharged when a new name
       has been added in names_to_discharge. *)
    map_and_ins  (fun (_,t') ->
      check_term find_info [] cur_array defined_refs t'
	) exp.before_transfo_input_vars_exp
  with Not_found ->
     (* First try to find a matching source expression in the equivalence to apply *)
     let ((lm, rm, _, _),name_mapping) = !equiv in 
     let transform_to_do = ref [] in
     (* Store in accu_exp all expressions in priority order *)
     let accu_exp = ref [] in
     List.iter2 (fun (lm1,mode) (rm1,_) -> collect_expressions accu_exp [] [] [] mode lm1 rm1) lm rm;
     let all_names_lhs = ref [] in
     List.iter (fun (lm1,_) -> collect_all_names all_names_lhs lm1) lm;
     (* Try all expressions in accu_exp, in order. When an expression succeeds without
        advice, we can stop, since all future expressions don't have higher priority *)
     let r = List.exists (fun ((restr, args, res_term), (restr', repl', args', res_term'), mode, priority) ->
       all_names_indexes := [];
       let old_names_to_discharge = !names_to_discharge in
       try 
	 let (lhs_array_ref_map, to_do) = 
	   try 
	     check_instance_of (!all_names_lhs) mode res_term t 
	   with SurelyNot ->
             all_names_indexes := [];
             names_to_discharge := old_names_to_discharge;
	   (* When t is just under a test (if/find) or an assignment,
	      try subterms of res_term *)
	     if ta_above != [] then
	       ([], and_ins1 (ta_above,0) (check_instance_of_subterms (!all_names_lhs) mode res_term t))
	     else
	       raise SurelyNot
	 in
	 if to_do == [] then Parsing_helper.internal_error "ins_accu should not be empty (6)";
	 let to_do = List.map (fun (l,p) -> (l,p+priority)) to_do in (* Take into account the priority *)
	 let env = List.map (fun b ->
	   match b.link with
	     TLink t -> (b, t)
	   | _ -> Parsing_helper.internal_error "unexpected link in check_term"
		 ) (!Terms.current_bound_vars) 
	 in
	 let name_indexes = !all_names_indexes in
	 clean_up_instance_of();
	 let to_do' = 
	   and_ins (map_and_ins  (fun (b,t) ->
	     if List.exists (List.memq b) restr then success_no_advice else
	     check_term find_info [] cur_array defined_refs t
	       ) env) to_do
	 in
	 match to_do' with
	   ([],_)::_ ->
	   begin
	     (* Adding missing names if necessary *)
	     let (name_indexes, env) = complete_env_call name_indexes env restr in

             let before_transfo_name_table = List.map (List.map (fun b ->
	       match List.assq b env with
		 { t_desc = Var(b',_) } -> (b, b')
	       | _ -> Parsing_helper.internal_error "unexpected link in check_term 2"
		     )) restr
             in

	     let before_transfo_array_ref_map = List.map (function 
		 (br, { t_desc = Var(b',l') }) -> (br, (b',l'))
	       | _ -> Parsing_helper.internal_error "Variable expected") lhs_array_ref_map
	     in

             let indexes_ordered = List.map (function 
		 (b::_ as lrestr) -> 
                   begin
                     try
                       (lrestr, assq_binderref (b, b.args_at_creation) name_indexes)
                     with Not_found ->
		       Parsing_helper.internal_error "indexes missing"
                   end
               | [] -> ([],[])) restr
             in

	     let cur_array_terms = List.map Terms.term_from_binder cur_array in
	     let indexes_ordered' = 
	       match indexes_ordered with
		 ([],[]) :: l -> ([],cur_array_terms)::l
	       | _ -> indexes_ordered
	     in

	     List.iter (fun name_group ->
	       check_same_args_at_creation (List.map snd name_group)) before_transfo_name_table;
	     List.iter (fun ((b1,l1), (b1',_)) ->
	       List.iter (fun ((b2,l2), (b2',_)) ->
		 if (Terms.equal_term_lists l1 l2) &&
		   not (Terms.equal_term_lists b1'.args_at_creation b2'.args_at_creation) then
		     raise SurelyNot
		   ) before_transfo_array_ref_map
		 ) before_transfo_array_ref_map;
		   
	     let before_transfo_restr = List.concat before_transfo_name_table in
	     (* Mapping from input variables to terms *)
	     let input_env = List.filter (fun (b,_) -> 
	       not (List.exists (List.memq b) restr)) env 
	     in
	     let after_transfo_input_vars_exp = 
	       List.map (fun (b,t) ->
		 (find_rm b args args', t)) input_env
	     in
	     (* Variables defined by let/new in the right member expression *)
	     let let_vars' = ref [] in
	     letvars_from_term let_vars' res_term';
	     let after_transfo_let_vars = 
	       if (!Settings.optimize_let_vars) && (not (is_in_find_cond)) then
		 (* Try to find an expression from which we could reuse the let variables.
		    We do not try to reuse let variables when we are in a "find" condition,
		    because variables in "find" conditions must have a single definition. *)
		 let rec find_incomp_same_exp = function
		     [] -> (* Not found; create new let variables *)
		       List.map (fun b -> (b, new_binder2 b cur_array_terms)) (!let_vars')
		   | (mapping::rest_map) ->
		       if mapping.target_exp == res_term' then
			 try
			   let exp = List.find (fun exp ->
			     (Terms.equal_terms exp.source_exp_instance t) &&
			     (is_incompatible exp.source_exp_instance t)
			     ) mapping.expressions in
			   (* Found, reuse exp.after_transfo_let_vars *)
			   exp.after_transfo_let_vars
			 with Not_found ->
			   find_incomp_same_exp rest_map
		       else
			 find_incomp_same_exp rest_map
		 in
		 find_incomp_same_exp (!map)
	       else
		 List.map (fun b -> (b, new_binder2 b cur_array_terms)) (!let_vars')
	     in

	     (* Compute rev_subst_indexes
		It must be possible to compute indexes of upper restrictions in 
		the equivalence from the indexes of lower restrictions.
		Otherwise, raise Failure *)
	     let rev_subst_name_indexes = rev_subst_indexes cur_array None before_transfo_name_table indexes_ordered in

	     (* Common names with other expressions
		When two expressions use a common name, 
                - the common names must occur at the same positions in the equivalence
                - if a name is common, all names above it must be common too, and the function that computes the 
                indexes of above names from the indexes of the lowest common name must be the same.
		*)
	     let longest_common_suffix = ref 0 in
	     let exp_for_longest_common_suffix = ref None in
	     List.iter (fun mapping ->
	       let name_table_rev = List.rev before_transfo_name_table in
	       let map_name_table_rev = List.rev mapping.before_transfo_name_table in
	       let new_common_suffix =
		 common_names_rev name_table_rev map_name_table_rev
	       in
	       if new_common_suffix > 0 then
		 begin
		   let common_rev_subst_name_indexes1 = Terms.lsuffix (new_common_suffix - 1) rev_subst_name_indexes in
		   let common_rev_subst_name_indexes2 = Terms.lsuffix (new_common_suffix - 1) mapping.rev_subst_name_indexes in
		   if not (List.for_all2 (fun (_,r1) (_,r2) -> Terms.equal_term_lists r1 r2) common_rev_subst_name_indexes1 common_rev_subst_name_indexes2) then
		     raise SurelyNot
		 end;
	       if new_common_suffix > (!longest_common_suffix) then
		 begin
		   longest_common_suffix := new_common_suffix;
		   exp_for_longest_common_suffix := Some mapping
		 end;

	       (* We check the compatibility of array references
		  - new array references in the current expression:
		  if ((b,_),(b',_)) in before_transfo_array_ref_map, then 
		  occurrences of b' in another expression must be mapped also to b
		  - if (b,b') in before_transfo_restr, then occurrences of b'
		  in array references in another expression must be mapped also to b
		  These two points are implied by the final checks performed in
		  check_lhs_array_ref, but performing them earlier allows to backtrack
		  and choose other expressions
		  *)
	       List.iter (fun ((b,_),(b',_)) ->
		 List.iter (fun (b1, b1') ->
		   if b1' == b' && b1 != b then raise SurelyNot
		       ) before_transfo_restr;
		 List.iter (fun exp ->
		   List.iter (fun ((b1,_),(b1',_)) ->
		     if b1' == b' && b1 != b then raise SurelyNot
			 ) exp.before_transfo_array_ref_map
		   ) mapping.expressions
		 ) before_transfo_array_ref_map;

	       List.iter (fun (b, b') ->
		 List.iter (fun exp ->
		   List.iter (fun ((b1,_),(b1',_)) ->
		     if b1' == b' && b1 != b then raise SurelyNot
			 ) exp.before_transfo_array_ref_map
		   ) mapping.expressions
		 ) before_transfo_restr

	       ) (!map);

	     let after_transfo_table_builder nt r = 
	       match nt with
		 [] -> List.map (fun b -> (b, new_binder2 b cur_array_terms)) r
	       | ((_,one_name)::_) ->
		   List.map (fun b -> 
		     try 
		       (* Try to reuse old binder when possible:
			  same string name, same number, and same type *)
		       (b, snd (List.find (fun (bf_name, _) -> 
			 (b.sname = bf_name.sname) &&
			 (b.vname == bf_name.vname) &&
			 (b.btype == bf_name.btype)) nt))
		     with Not_found ->
		       (b, new_binder2 b one_name.args_at_creation)) r
	     in
	     let after_transfo_name_table = 
	       match !exp_for_longest_common_suffix with
		 None -> 
		   List.map2 after_transfo_table_builder before_transfo_name_table restr'
	       | Some exp ->
		   let diff_name_table = Terms.remove_suffix (!longest_common_suffix) before_transfo_name_table in
		   let diff_restr' = Terms.remove_suffix (!longest_common_suffix) restr' in
		   let common_name_table = Terms.lsuffix (!longest_common_suffix) exp.after_transfo_name_table in
		   (List.map2 after_transfo_table_builder diff_name_table diff_restr') @ common_name_table
	     in
	     
	     let after_transfo_restr = List.concat after_transfo_name_table in

	     let count = 
	       match indexes_ordered' with
		 (_::_,_)::_ -> (* The down-most sequence of restrictions is not empty *)
		   make_count repl' (List.map snd indexes_ordered') before_transfo_name_table 
	       | ([], top_indices)::rest -> 
		   (* If we are in a find condition, the expression is
		      executed for value of the replication indices, but
		      also for each value of the find indices *)
		   let top_indices' = (List.map Terms.term_from_binder find_indices) @ top_indices in
		   (* Filter the indices that are really useful *)
		   let used = ref [] in
		   used_indices top_indices' used t;
		   (* I need to keep the indices in the same order as the initial
	              order (for cur_array), that's why I don't use (!used) directly.
	              I also need the property that if t refers to an element to cur_array,
		      it also refers to the following ones, so that a suffix of cur_array
		      is kept *)
		   let top_indices'' = List.filter (fun t -> List.memq t (!used)) top_indices' in
		   (*
                   print_string "Term: ";
		   Display.display_term [] t;
		   print_string "\nIndices before filtering: ";
		   Display.display_list (Display.display_term []) top_indices';
		   print_string "\nIndices used: ";
		   Display.display_list (Display.display_term []) top_indices'';
		   print_string "\n";
                   *)
		   make_count repl' (top_indices''::(List.map snd rest)) before_transfo_name_table 
	       | [] ->
		   (* There is no replication at all in the LHS => 
		      the expression must be evaluated once *)
		   if is_in_find_cond && (List.exists (fun b -> Terms.refers_to b t) find_indices) then 
		     raise SurelyNot;
		   if List.exists (fun b -> Terms.refers_to b t) cur_array then
		     raise SurelyNot;
		   if List.exists (fun mapping -> mapping.source_exp == res_term) (!map) then
		     raise SurelyNot;
		   make_count repl' [] before_transfo_name_table 
	     in

	     let exp =
	       { source_exp_instance = t;
		 name_indexes_exp = indexes_ordered';
		 before_transfo_array_ref_map = before_transfo_array_ref_map;
		 after_transfo_array_ref_map = [];
		 after_transfo_let_vars = after_transfo_let_vars;
		 cur_array_exp = cur_array_terms;
		 before_transfo_input_vars_exp = input_env;
		 after_transfo_input_vars_exp = after_transfo_input_vars_exp
	       }
	     in

	     (* verify that all restrictions will be correctly defined after the transformation *)

	     List.iter (fun (_,b,def_check) ->
	       List.iter (fun res_def_check ->
		 if res_term == res_def_check then
		   try
		     match List.assq b env with
		       { t_desc = Var(b_check,_) } -> 
			 let l_check = assq_binderref (b, b.args_at_creation) name_indexes in
			 (*print_string "Checking that ";
			 Display.display_term [] (Terms.term_from_binderref (b_check, l_check));
			 print_string " is defined... "; *)
			 if not (List.exists (Terms.equal_binderref (b_check, l_check)) defined_refs) then
			   raise SurelyNot;
			 (* print_string "Ok.\n" *)
		     | _ -> Parsing_helper.internal_error "unexpected link in check_term 3"
		   with Not_found ->
		     Parsing_helper.internal_error "binder not found when verifying that all restrictions will be defined after crypto transform"
		 ) def_check;
	       ) name_mapping;

	     (* If we are in a find condition, verify that we are not going to 
		create finds on variables defined in the condition of find,
		and that the variable definitions that we introduce are all 
		distinct. *)

	     if is_in_find_cond then
	       begin
		 Terms.array_ref_eqside rm;
		 let def_vars = get_def_vars [] res_term' in
		 if List.exists Terms.has_array_ref def_vars then
		   raise SurelyNot;
		 Terms.cleanup_array_ref()
	       end;

	     (* if the down-most (first in restr) sequence of
                restrictions is not empty, the result expression must
                be a function of the indexes of those names (checked
                using reverse substitutions) *)
	     begin
	     match indexes_ordered with
	       (_::_,down_indexes)::_ -> (* The down-most sequence of restrictions is not empty *)
     	       begin
		 (* Check that names in name_list_i are always used in
		    the same expression *)
	 	 (* TO DO this test could be made more permissive to
		    succeed in all cases when the names in name_list_i
		    occur in a single expression.
		    More generally, it would be nice to allow
		    different session identifiers when they are
		    related by an equality.
		    For instance, if name_list_i_indexes is iX, and
		    jX[iX[i]] = i, then i should also be allowed, and
		    the result of the reverse subtitution applied to i
		    is jX. *)
		 let cur_array' = List.map (fun e -> 
		   Terms.create_binder "tmpcur" (Terms.new_vname()) e.t_type []) down_indexes 
		 in
		 let cur_array_terms' = List.map Terms.term_from_binder cur_array' in
		 let t' = reverse_subst (find_indices @ cur_array) down_indexes cur_array_terms' t in
		 (* NOTE If we are in a find condition, we add the
		    find_indices to forbidden_cur_array, so that we
		    make sure that the term can be expressed as a
		    function of the down-most indices of the
		    replication without using the indices of
		    find. (Otherwise, a different expression may be
		    evaluated for each value of the indices of find,
		    so several evaluations for each value of the
		    down_most restriction *)
	         (* SUCCESS store the mapping in the mapping list *)
		 let one_name = snd (List.hd before_transfo_restr) in
		 let rec find_old_mapping = function
		     [] -> (* No old mapping found, create a new one *)
		       let new_mapping =
			 { expressions = [ exp ];
			   before_transfo_name_table = before_transfo_name_table;
			   after_transfo_name_table = after_transfo_name_table;
			   before_transfo_restr = before_transfo_restr;
			   source_exp = res_term;
			   source_args = args;
			   after_transfo_restr = after_transfo_restr;
			   rev_subst_name_indexes = rev_subst_name_indexes;
			   target_exp = res_term';
			   target_args = args';
			   count = count
		         } 
		       in
		       map := new_mapping :: (!map)
		   | (mapping::rest) -> 
		       if (List.exists (fun (b,b') -> b' == one_name) mapping.before_transfo_restr) && 
			 (mapping.source_exp == res_term) then
			 (* Old mapping found, just add the current expression in the 
			    list of expressions of this mapping, after a final check *)
			 begin
			   (* if a name in the down-most sequence of restrictions is common, the result expressions
                              must be equal up to change of indexes (checked using reverse substitutions) *)
			   let exp' = List.hd mapping.expressions in
			   if not (Terms.equal_terms exp'.source_exp_instance 
				     (Terms.subst cur_array' (snd (List.hd exp'.name_indexes_exp)) t')) then
			     raise SurelyNot;
			   mapping.expressions <- exp :: mapping.expressions
			 end
                       else 
			 find_old_mapping rest
		 in
		 find_old_mapping (!map)
	       end
	     | _ -> 
	       begin
	         (* SUCCESS store the mapping in the mapping list *)
		 (*Caused a bug, and anyway does not really reduce the number 
		   of branches of find, since we later avoid creating several 
		   branches when the names are common and no let variables
		   are used. Just allows to reuse the same index variables 
		   for the various branches. (This bug appears with 
		   examplesnd/testenc. It is caused by a mixing of current
		   array indexes for various occurrences of the same 
		   expression.)

		    Try to reuse an existing mapping to optimize
                    (reduces the number of find and the probability difference)
                 try 
		   let mapping' = List.find (fun mapping' -> 
		     List.exists (fun exp' -> Terms.equal_terms exp'.source_exp_instance t) mapping'.expressions) (!map)
		   in
		   mapping'.expressions <- exp :: mapping'.expressions
		 with Not_found -> *)
		   let new_mapping = 
		     { expressions = [ exp ];
		       before_transfo_name_table = before_transfo_name_table;
		       after_transfo_name_table = after_transfo_name_table;
		       before_transfo_restr = before_transfo_restr;
		       source_exp = res_term;
		       source_args = args;
		       after_transfo_restr = after_transfo_restr;
		       rev_subst_name_indexes = rev_subst_name_indexes;
		       target_exp = res_term';
		       target_args = args';
		       count = count
		       (* TO DO (to reduce probability difference)
			  When I have several times the same expression, possibly with different
			  indexes, I should count the probability difference only once.
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
	     end;
	     transform_to_do := merge_ins to_do' (!transform_to_do);
	     true
	   end
	 | [] -> Parsing_helper.internal_error "ins_accu should not be empty (5)"
	 | _ -> 
	   begin
	     transform_to_do := merge_ins to_do' (!transform_to_do);
	     false
	   end
       with 
	 CouldNotComplete ->
           names_to_discharge := old_names_to_discharge;
	   if debug then
	     begin
	       print_string "failed to discharge ";
	       Display.display_term [] t;
	       print_string " (could not complete missing names)\n"
	     end;
	   (* Accept not being able to complete missing names if I am in "rebuild map" mode *)
	   if (!rebuild_map_mode) then transform_to_do := merge_ins [([],priority)] (!transform_to_do);
	   !rebuild_map_mode
       | Failure | SurelyNot -> 
           names_to_discharge := old_names_to_discharge;
	   if debug then
	     begin
	       print_string "failed to discharge ";
	       Display.display_term [] t;
	       print_string "\n"
	     end;
	   clean_up_instance_of();
	   false
	 ) (!accu_exp)
     in

     if r then
       (* If r is true, the transformation can be done without advice
	  (even if that may not be the highest priority), then I don't consider
          transforming only subterms. Another way would be to always try to transform
          subterms but with a lower priority. *)
       !transform_to_do
     else
       let old_names_to_discharge = !names_to_discharge in
       try 
         merge_ins (!transform_to_do) (check_term_try_subterms find_info cur_array defined_refs t)
       with SurelyNot ->
	 names_to_discharge := old_names_to_discharge;
	 if (!transform_to_do) == [] then raise SurelyNot else (!transform_to_do)

and check_term_try_subterms find_info cur_array defined_refs t =
     (* If fails, try a subterm; if t is just a variable in names_to_discharge,
        the transformation is not possible *)
     match t.t_desc with
       Var(b,l) ->
         if List.memq b (!names_to_discharge) then
	   begin
	     if (not (!no_advice_mode)) && (List.length b.def > 1)
	     then
	       (* If b has several definitions, advise SArenaming, so that perhaps
		  the transformation becomes possible after distinguishing between
		  these definitions *)
	       [([SArenaming b],0)]
	     else
               raise SurelyNot
	   end
         else
           map_and_ins (check_term find_info [] cur_array defined_refs) l
     | FunApp(f,l) ->
	 if List.memq f (!symbols_to_discharge) then
	   raise SurelyNot
	 else
	   map_and_ins (check_term find_info [] cur_array defined_refs) l
     | TestE _ | LetE _ | FindE _ | ResE _ -> 
	 Parsing_helper.internal_error "If, find, let, and new should have been expanded (Cryptotransf.check_term_try_subterms)"

(* For debugging 

let check_term find_info l c defined_refs t =
  try
    let r = check_term find_info l c defined_refs t in
    print_string "check_term ";
    Display.display_term [] t;
    begin
    match r with
	  ([],_)::_ -> print_string " succeeded\n"
	| [] -> Parsing_helper.internal_error "ins_accu should not be empty (4)"
	| _ ->
	    print_string " succeeded with advice\n";
	    List.iter (fun (l,p) -> Display.display_list Display.display_instruct l;
	      print_string " priority: ";
	      print_int p;
	      print_string "\n") r
    end;
    r
  with x ->
    print_string "check_term ";
    Display.display_term [] t;
    print_string " raised exception";
    print_newline();
    raise x

*)

let not_in_find_cond = (false, [])

let rec check_pat cur_array accu defined_refs = function
    PatVar b -> accu := (b, b.args_at_creation)::(!accu); success_no_advice
  | PatTuple (f,l) -> map_and_ins (check_pat cur_array accu defined_refs) l
  | PatEqual t -> check_term not_in_find_cond [] cur_array defined_refs t

let rec get_binders = function
    PatVar b -> 
      if !no_advice_mode then
	[]
      else
	[explicit_value b]
  | PatTuple (f,l) -> Terms.map_concat get_binders l
  | PatEqual t -> []

let rec check_cterm t =
  match t.t_desc with
    Var(b,l) ->
      if List.memq b (!names_to_discharge) then
	raise SurelyNot;
      List.iter check_cterm l
  | FunApp(f,l) ->
      if List.memq f (!symbols_to_discharge) then
	raise SurelyNot;
      List.iter check_cterm l
  | TestE(t1,t2,t3) ->
      check_cterm t1;
      check_cterm t2;
      check_cterm t3
  | FindE(l0,t3,_) ->
      List.iter (fun (bl, def_list, otheruses_list, t1, t2) ->
	List.iter (fun b ->
	  if List.memq b (!names_to_discharge) then
	    raise SurelyNot) bl;
	List.iter (fun (b,l) -> List.iter check_cterm l) def_list;
	List.iter (fun (b,l) -> List.iter check_cterm l) otheruses_list;
	check_cterm t1;
	check_cterm t2) l0;
      check_cterm t3
  | LetE(pat,t1,t2,topt) ->
      check_cpat pat;
      check_cterm t1;
      check_cterm t2;
      begin
	match topt with
	  None -> ()
	| Some t3 -> check_cterm t3
      end
  | ResE(b,t) -> 
      if List.memq b (!names_to_discharge) then
	raise SurelyNot;
      check_cterm t

and check_cpat = function
    PatVar b -> 
      if List.memq b (!names_to_discharge) then
	raise SurelyNot
  | PatTuple(f,l) -> List.iter check_cpat l
  | PatEqual t -> check_cterm t


(* Conditions of find are transformed only if they
do not contain if/let/find/new. By expansion, if they
contain such a term, it is at the root. 

Therefore, we make sure that we do not transform terms
that contain variables defined in conditions of find.
This avoids creating array references to such variables.
*)

let rec check_find_cond find_indices cur_array defined_refs t =
  match t.t_desc with
    Var _ | FunApp _ -> check_term (true, find_indices) [] cur_array defined_refs t 
  | FindE _ | ResE _ | TestE _ | LetE _ -> check_cterm t; success_no_advice

let rec check_process cur_array defined_refs p =
  match p.i_desc with
    Nil -> success_no_advice
  | Par(p1,p2) ->
      and_ins (check_process cur_array defined_refs p1)
	(check_process cur_array defined_refs p2)
  | Repl(b,p) ->
      check_process (b::cur_array) defined_refs p
  | Input((c,tl),pat,p) ->
      List.iter check_cterm tl;
      let accu = ref [] in
      let ins_pat = check_pat cur_array accu defined_refs pat in
      and_ins ins_pat (check_oprocess cur_array ((!accu) @ defined_refs) p)

and check_oprocess cur_array defined_refs p = 
  match p.p_desc with
    Yield -> success_no_advice
  | Restr(b,p) ->
      check_oprocess cur_array ((b, b.args_at_creation)::defined_refs) p
  | Test(t,p1,p2) ->
      and_ins (check_term not_in_find_cond [] cur_array defined_refs t)
	(and_ins (check_oprocess cur_array defined_refs p1)
	   (check_oprocess cur_array defined_refs p2))
  | Find(l0, p2, _) ->
      let accu = ref (check_oprocess cur_array defined_refs p2) in
      List.iter (fun (bl, def_list, otheruses_list, t, p1) ->
	let accu' = ref ((List.map (fun b -> (b, b.args_at_creation)) bl) @ defined_refs) in
	List.iter (Terms.close_def_subterm accu') def_list;
	let defined_refs' = !accu' in
	List.iter (fun (b,l) -> List.iter check_cterm l) def_list;
	List.iter (fun (b,l) -> List.iter check_cterm l) otheruses_list;
	accu := and_ins (check_find_cond bl cur_array defined_refs' t) 
	     (and_ins (check_oprocess cur_array defined_refs' p1) (!accu))) l0;
      !accu
  | Let(pat,t,p1,p2) ->
      let accu = ref [] in
      let ins_pat = check_pat cur_array accu defined_refs pat in
      let defined_refs' = (!accu) @ defined_refs in
      and_ins ins_pat
	(and_ins (check_term not_in_find_cond (get_binders pat) cur_array defined_refs' t)
	   (and_ins (check_oprocess cur_array defined_refs' p1)
	      (check_oprocess cur_array defined_refs p2)))
  | Output((c,tl),t2,p) ->
      and_ins (map_and_ins (check_term not_in_find_cond [] cur_array defined_refs) tl)
	(and_ins (check_term not_in_find_cond [] cur_array defined_refs t2)
	   (check_process cur_array defined_refs p))
  | EventP(t,p) ->
      and_ins (check_term not_in_find_cond [] cur_array defined_refs t)
	(check_oprocess cur_array defined_refs p)

(* Additional checks for variables in the LHS that are accessed with indices given in argument *)

let check_lhs_array_ref() =
  List.iter (fun mapping ->
    List.iter (fun one_exp -> 
      let bf_array_ref_map = 
	List.map (fun ((b,l),(b',l')) ->
	  (* Find an expression M (mapping') that uses b' associated with b in a standard reference.
	     If there is no such expression, the transformation fails. *)
	  let mapping' =
	    try
	      List.find (fun mapping' ->
		List.exists (fun (b1,b1') -> (b1 == b) && (b1' == b')) mapping'.before_transfo_restr
		  ) (!map)
	    with Not_found ->
	      (* Display.display_var [] b l;
	      print_string " is mapped to ";
	      Display.display_var [] b' l';
	      print_string ".\nI could not find a usage of ";
	      Display.display_binder b;
	      print_string " mapped to ";
	      Display.display_binder b';
	      print_string " in a standard reference.\n"; *)
	      raise SurelyNot
	  in
	  (* Display.display_var [] b l;
	  print_string " is mapped to ";
	  Display.display_var [] b' l';
	  print_string ".\n"; *)
	  (* Verify the condition on a prefix that is a sequence of replication indices:
	     if l has a prefix of length k0 that is a sequence of replication indices then
             mapping and mapping' share (at least) the first k0 sequences of random variables
	     (i.e. the last k0 elements of before_transfo_name_table)
	     { l'/b'.args_at_creation } \circ mapping'.rev_subst_name_indexes[j1-1] \circ ... \circ mapping'.rev_subst_name_indexes[k0] =
	     one_exp.name_indexes_exp[k0]
	     *)
	  let k0 = Terms.len_common_suffix l b.args_at_creation in
	  if k0 > 0 then
	    begin
	      if not (List.for_all2 equal_binder_pair_lists
			(Terms.lsuffix k0 mapping.before_transfo_name_table)
			(Terms.lsuffix k0 mapping'.before_transfo_name_table))
	      then 
		begin
		  (* print_string ("Do not share the first " ^ (string_of_int k0) ^ " sequences of random variables with the expression(s) that map ");
		  Display.display_binder b;
		  print_string " to ";
		  Display.display_binder b';
		  print_string " in a standard reference.\n"; *)
		  raise SurelyNot
		end;
	      (* TO DO *)
	      Parsing_helper.user_error "Error: array references that use both arguments and replication indices are not supported yet in the LHS of equivalences\n"
	    end;
	  ((b,l),(b',l'),mapping')
	    ) one_exp.before_transfo_array_ref_map
      in
      (* Verify the condition on common prefixes:
	 if (b1,l1),(b1',l1'),mapping1' and (b2,l2),(b2',l2'),mapping2' occur in the list,
	 l1 and l2 have a common prefix of length k0 that consists not only of replication indices,
	 then mapping1' and mapping2' share (at least) the first k0 sequences of random variables
	      (i.e. the last k0 elements of before_transfo_name_table)
	 { l1'/b1'.args_at_creation } \circ mapping1'.rev_subst_name_indexes[j1-1] \circ ... \circ mapping1'.rev_subst_name_indexes[k0] =
	 { l2'/b2'.args_at_creation } \circ mapping2'.rev_subst_name_indexes[j2-1] \circ ... \circ mapping2'.rev_subst_name_indexes[k0]
         where j1 = List.length l1, j2 = List.length l2
	 mapping.rev_subst_name_indexes[k] = the k-th element of the list starting from the end (the last element is numbered 1)
      *)
      let rec common_prefix = function
	  ((b1,l1),(b1',l1'),mapping1')::r ->
	    List.iter (function ((b2,l2),(b2',l2'),mapping2') ->
	      let k0 = Terms.len_common_suffix l1 l2 in
	      if k0 > Terms.len_common_suffix l1 b1.args_at_creation then
		begin
		  (* Display.display_var [] b1 l1;
		  print_string " is mapped to ";
		  Display.display_var [] b1' l1';
		  print_string ";\n";
		  Display.display_var [] b2 l2;
		  print_string " is mapped to ";
		  Display.display_var [] b2' l2';
		  print_string (".\nCommon prefix of length " ^ (string_of_int k0) ^ ".\n"); *)
		  if not (List.for_all2 equal_binder_pair_lists
			    (Terms.lsuffix k0 mapping1'.before_transfo_name_table)
			    (Terms.lsuffix k0 mapping2'.before_transfo_name_table))
		  then 
		    begin
		      (* print_string ("The corresponding expressions with standard references do not share the first " ^ (string_of_int k0) ^ " sequences of random variables\n."); *)
		      raise SurelyNot
		    end;
	          (* TO DO *)
		  Parsing_helper.user_error "Error: array references that share arguments are not supported yet in the LHS of equivalences\n"
		end
	      ) r
	| [] -> ()
      in
      common_prefix bf_array_ref_map;

      (* Initialize one_exp.after_transfo_array_ref_map *)
      let (_, name_mapping) = (!equiv) in
      (*  map_list maps arguments of the LHS to arguments of the RHS
	  and replication indices of the LHS to replication indices of the RHS *)
      let args_assq = List.combine mapping.source_args mapping.target_args in
      let rec map_list b_after = function
	  t :: r ->
	    begin
	      match t.t_desc with
		Var(b,l) -> 
		  begin
		    try
		      (* Argument of the LHS -> argument of the RHS *)
		      (Terms.term_from_binder (List.assq b args_assq))::(map_list b_after r)
		    with Not_found -> 
		      (* Not argument of the LHS; must be a replication index *)
		      Terms.lsuffix (1+List.length r) b_after.args_at_creation
		  end
	      | _ ->  Parsing_helper.internal_error "Variable expected as index in array reference"
	    end
	| [] -> []
      in
      (* print_string "Mapping start\n"; *)
      List.iter (fun (b_after,b_before,_) -> 
	let l_b = List.filter (fun ((b,_),_,_) -> b == b_before) bf_array_ref_map in
	List.iter (fun ((_,l),(_,l'),mapping') ->
	  let b_after' = List.assq b_after mapping'.after_transfo_restr in
	  let l = map_list b_after l in
	  (* print_string "Mapping ";
	  Display.display_var [] b_after l;
	  print_string " to ";
	  Display.display_var [] b_after' l';
	  print_newline(); *)
	  one_exp.after_transfo_array_ref_map <- ((b_after, l), (b_after', l')) :: one_exp.after_transfo_array_ref_map
	    ) l_b
	  ) name_mapping

	) mapping.expressions
      ) (!map)

let check_process() =
  let to_do = check_process [] [] (!whole_game).proc in
  if is_success_no_advice to_do then check_lhs_array_ref();
  to_do

(* Second pass: perform the game transformation itself *)

(* Constraint l1 = l2 *)

let rec make_constra_equal l1 l2 =
  match (l1,l2) with
    [],[] -> None
  | (a1::l1),(a2::l2) ->
      begin
      let t = Terms.make_equal a1 a2 in
      match make_constra_equal l1 l2 with
	None -> Some t
      |	Some t' -> Some (Terms.make_and t t')
      end
  | _ -> Parsing_helper.internal_error "Not same length in make_constra_equal"

(* Constraint eq_left = eq_right { cur_array_im / cur_array } *)

let rec make_constra cur_array cur_array_im eq_left eq_right =
  match (eq_left, eq_right) with
    [],[] -> None
  | (a::l),(b::l') -> 
      begin
      let t = Terms.make_equal a (Terms.subst cur_array cur_array_im b) in
      match make_constra cur_array cur_array_im l l' with
	None -> Some t
      |	Some t' -> Some (Terms.make_and t t')
      end
  | _ -> Parsing_helper.internal_error "Not same length in make_constra"
  
let and_constra c1 c2 =
  match (c1, c2) with
    (None, _) -> c2
  | (_, None) -> c1
  | (Some t1, Some t2) -> Some (Terms.make_and t1 t2)

let rename_def_list loc_rename def_list = 
  List.map (fun br ->
    try 
      assq_binderref br loc_rename
    with Not_found -> 
      Parsing_helper.internal_error "variable not found in rename_def_list"
    ) def_list

let restr_to_put = ref []

let rec transform_term t =
  let rec find_map = function
      [] -> (* Mapping not found, the term is unchanged. Visit subterms *)
	Terms.build_term2 t 
	   (match t.t_desc with
	      Var(b,l) -> Var(b, List.map transform_term l)
	    | FunApp(f,l) -> FunApp(f, List.map transform_term l)
	    | TestE _ | LetE _ | FindE _ | ResE _ -> 
		Parsing_helper.internal_error "If, find, let, and new should have been expanded (Cryptotransf.transform_term)")
    | (mapping::l) ->
	let rec find_exp = function
	    [] -> find_map l
	  | (one_exp::l') ->
	      if t == one_exp.source_exp_instance then
	        (* Mapping found; transform the term *)
		begin
		  if debug then
		    begin
		      print_string "Instantiating term ";
		      Display.display_term [] t;
		      print_string " into ";
		      Display.display_term [] mapping.target_exp;
		      print_newline();
		    end;
		  begin
		    (* When restrictions in the image have no corresponding
	               restriction in the source process, just put them
                       immediately before the transformed term *)
		    match mapping.before_transfo_name_table with
		      []::_ ->
			restr_to_put := (List.map snd (List.hd mapping.after_transfo_name_table)) @ (!restr_to_put)
		    | _ -> ()
		  end;
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
      begin
	try 
	  Terms.term_from_binderref (assq_binderref (b,l) loc_rename)
	with Not_found ->
	  (* map array accesses using one_exp.after_transfo_array_ref_map *) 
	  try
	    Terms.term_from_binderref (assq_binderref (b,l) one_exp.after_transfo_array_ref_map)
	  with Not_found -> 
          if not (List.for_all2 Terms.equal_terms l b.args_at_creation) then
	    begin
	      Display.display_var [] b l;
              Parsing_helper.internal_error "Unexpected variable reference in instantiate_term"
	    end;
          try
	    transform_term (List.assq b one_exp.after_transfo_input_vars_exp)
	  with Not_found ->
	    try
	      Terms.term_from_binder (List.assq b one_exp.after_transfo_let_vars)
	    with Not_found ->
              let rec find_var restr indexes =
                match (restr, indexes) with
                  [], [] -> Parsing_helper.internal_error ("Variable " ^ (Display.binder_to_string b) ^ " not found in instantiate_term")
                | (restr1::restrl, (_,index1)::indexl) ->
		    begin
		      try
			Terms.term_from_binderref (List.assq b restr1, index1)
		      with Not_found ->
                        find_var restrl indexl
		    end
		| _ -> Parsing_helper.internal_error "restr and indexes have different lengths"
              in
              find_var mapping.after_transfo_name_table one_exp.name_indexes_exp
      end
  | FunApp(f,l) ->
      Terms.build_term t (FunApp(f, List.map (instantiate_term loc_rename mapping one_exp) l))
  | TestE(t1,t2,t3) ->
      Terms.build_term t (TestE(instantiate_term loc_rename mapping one_exp t1,
				instantiate_term loc_rename mapping one_exp t2,
				instantiate_term loc_rename mapping one_exp t3))
  | FindE(l0, t3, find_info) -> 
      (* - a variable in def_list cannot refer to an index of 
	 another find; this is forbidden in syntax.ml. *)
      let find_exp = ref [] in
      List.iter (fun (bl,def_list,otheruses_list,t1,t2) ->
	let add_find (indexes, constra, var_map) =
	  let loc_rename' = var_map @ loc_rename in
	  find_exp :=
	     (indexes, 
	      begin
		match constra with
		  None -> rename_def_list var_map def_list
		| Some t -> 
		    (* when constra = Some t, I need to add in the def_list the array accesses that occur in t *)
		    let accu = ref (rename_def_list var_map def_list) in
		    Terms.get_deflist_subterms accu t;
		    !accu
	      end, 
	      rename_def_list var_map otheruses_list,
	      begin
		match constra with
		  None -> instantiate_term loc_rename' mapping one_exp t1
		| Some t -> Terms.make_and t (instantiate_term loc_rename' mapping one_exp t1)
	      end,
	      instantiate_term loc_rename' mapping one_exp t2) :: (!find_exp)
	in
	match def_list with
	  (_,(({ t_desc = Var(b0,_) }::_) as l1))::_ ->
	    let l_index = List.length bl in
	    let n = 
	      try
		Terms.find_in_list b0 bl
	      with Not_found -> 
		l_index
		  (*Parsing_helper.internal_error "Variables in right member of equivalences should have as indexes the indexes defined by find\n"*)
	    in
	    let l_cur_array_suffix = List.length l1 - (l_index - n) in
	    (*let cur_array = List.map fst mapping.count in
	    let cur_array_suffix = Terms.lsuffix l_cur_array_suffix cur_array in*)
	    List.iter (fun mapping' ->
	      let cur_var_map = ref [] in
	      let var_not_found = ref [] in
	      let depth_mapping = List.length mapping'.before_transfo_name_table in
	      if depth_mapping >= l_index + l_cur_array_suffix then
	      (* Check that the top-most l_cur_array_suffix sequences of fresh names
		 are common between mapping and mapping' *)
	      if List.for_all2 equal_binder_pair_lists
		  (Terms.lsuffix l_cur_array_suffix mapping'.before_transfo_name_table)
		  (Terms.lsuffix l_cur_array_suffix mapping.before_transfo_name_table) then
	      begin
	      (* Sanity check: check that the fresh names are also common after transformation *)
	      if not (List.for_all2 equal_binder_pair_lists
		  (Terms.lsuffix l_cur_array_suffix mapping'.after_transfo_name_table)
		  (Terms.lsuffix l_cur_array_suffix mapping.after_transfo_name_table)) then
		Parsing_helper.internal_error "Names are common before transformation but not after!";
	      let one_exp0 = List.hd mapping'.expressions in
	      let max_indexes = snd (List.nth one_exp0.name_indexes_exp (depth_mapping - (l_index + l_cur_array_suffix))) in
	      let map_indexes0_binders = List.map (fun t -> new_binder3 t one_exp.cur_array_exp) max_indexes in
	      let map_indexes0 = List.map Terms.term_from_binder map_indexes0_binders in
	      let (find_indexes, map_indexes, constra) =
		if l_cur_array_suffix > 0 then
		  let cur_array_indexes = snd (List.nth one_exp0.name_indexes_exp (depth_mapping - l_cur_array_suffix)) in
	          (* if cur_array_indexes is a suffix of max_indexes *)
		  let cur_array_suffix = 
		    (List.length cur_array_indexes <= List.length max_indexes) &&
		    (List.for_all2 Terms.equal_terms cur_array_indexes 
			(Terms.lsuffix (List.length cur_array_indexes) max_indexes))
		  in
		  if cur_array_suffix then
		      let find_indexes = Terms.remove_suffix (List.length cur_array_indexes) map_indexes0_binders in
		      let first_indexes = Terms.remove_suffix (List.length cur_array_indexes) map_indexes0 in
		      let map_indexes = first_indexes @ (snd (List.nth one_exp.name_indexes_exp (List.length one_exp.name_indexes_exp - l_cur_array_suffix))) in
		      (find_indexes, map_indexes, None)
		  else
		    try
		      let cur_array_indexes0 = reverse_subst_index (List.map Terms.binder_from_term one_exp0.cur_array_exp) max_indexes map_indexes0 cur_array_indexes in
		      let constra = make_constra_equal cur_array_indexes0 (snd (List.nth one_exp.name_indexes_exp (List.length one_exp.name_indexes_exp - l_cur_array_suffix))) in
		      (map_indexes0_binders, map_indexes0, constra)
		    with Failure ->
		      Parsing_helper.internal_error "reverse_subst_index failed in instantiate_term (1)"
		else
		  (map_indexes0_binders, map_indexes0, None)
	      in
	      List.iter (fun (b,l) ->
		try
		  let b' = List.assq b mapping'.after_transfo_restr in
		  let indexes = snd (List.nth one_exp0.name_indexes_exp (depth_mapping - List.length l)) in
		  cur_var_map := ((b,l),(b',reverse_subst_index (List.map Terms.binder_from_term one_exp0.cur_array_exp) max_indexes map_indexes indexes))::(!cur_var_map)
		with Not_found ->
		  var_not_found := (b,l) :: (!var_not_found)
		| Failure ->
		      Parsing_helper.internal_error "reverse_subst_index failed in instantiate_term (2)"
					      ) def_list;
	      if (!var_not_found) == [] then
		begin
	          (* when several mappings have as common names all names referenced in the find
	             and the find does not reference let vars, then only one find expression should be
		     generated for all these mappings (they will yield the same find expression
		     up to renaming of bound variables)
		     The function find previous mapping looks for a previous mapping with
		     all names referenced in the find common with mapping' *) 
		  let rec find_previous_mapping = function
		      [] -> false
		    | (mapping''::l) ->
			if mapping'' == mapping' then false else
			let depth_mapping'' = List.length mapping''.before_transfo_name_table in
			if (depth_mapping'' >= l_index + l_cur_array_suffix) &&
			  (List.for_all2 equal_binder_pair_lists
			     (Terms.skip (depth_mapping - l_index - l_cur_array_suffix) mapping'.before_transfo_name_table)
			     (Terms.skip (depth_mapping'' - l_index - l_cur_array_suffix) mapping''.before_transfo_name_table)) then
			  true
			else
			  find_previous_mapping l
		  in
		  if find_previous_mapping (!map) then
		    ()
		  else
		    add_find (find_indexes, constra, !cur_var_map)
		end
	      else if depth_mapping = l_index + l_cur_array_suffix then
	        (* Some variable was not found in after_transfo_restr;
	           Try to find it in after_transfo_let_vars
	           This is possible only if all indexes in the mapping are defined *)
		(* WARNING!! This code assumes that no find refers at the same time to
                   two let-variables defined in functions in parallel under the same replication
		   ==> we check in check.ml that this never happens. *)
		try 
		  let seen_let_vars = ref [] in
		  List.iter (fun one_exp' ->
		    (* When an expression with the same after_transfo_let_vars has already been seen,
		       we do not repeat the creation of a find. Indeed, this would yield exactly the same
		       references. *)
		    if not (List.memq one_exp'.after_transfo_let_vars (!seen_let_vars)) then
		    let exp_cur_var_map = ref (!cur_var_map) in
		    if (Terms.equal_term_lists (snd (List.hd one_exp'.name_indexes_exp)) one_exp'.cur_array_exp) then
		      begin
			List.iter (fun (b,l) ->
			  let b' = List.assq b one_exp'.after_transfo_let_vars in
			  if List.length b'.args_at_creation != List.length map_indexes then
			    Parsing_helper.internal_error "Bad length for indexes (1)";
			  exp_cur_var_map := ((b,l),(b',map_indexes)) :: (!exp_cur_var_map)
													   ) (!var_not_found);
			seen_let_vars := one_exp'.after_transfo_let_vars :: (!seen_let_vars);
			add_find (find_indexes, constra, !exp_cur_var_map)
		      end
		    else
		      begin
			let exp_map_indexes = List.map (fun t -> new_binder3 t one_exp.cur_array_exp) one_exp'.cur_array_exp in
			let constra2 = 
		    (* Constraint 
		         map_indexes = (snd (List.hd one_exp'.name_indexes_exp)) { exp_map_indexes / one_exp'.cur_array_exp } *)
			  make_constra 
			    (List.map Terms.binder_from_term one_exp'.cur_array_exp) 
			    (List.map Terms.term_from_binder exp_map_indexes)
			    map_indexes (snd (List.hd one_exp'.name_indexes_exp))
			in
			List.iter (fun (b,l) ->
			  let b' = List.assq b one_exp'.after_transfo_let_vars in
			  if List.length b'.args_at_creation != List.length exp_map_indexes then
			    Parsing_helper.internal_error "Bad length for indexes (2)";
			  exp_cur_var_map := ((b,l),(b',List.map Terms.term_from_binder exp_map_indexes)) :: (!exp_cur_var_map)
													       ) (!var_not_found);
			seen_let_vars := one_exp'.after_transfo_let_vars :: (!seen_let_vars);
			add_find (find_indexes @ exp_map_indexes, and_constra constra constra2, !exp_cur_var_map)
		      end
			) mapping'.expressions
		with Not_found ->
	    (* Variable really not found; this mapping does not
	       correspond to the expected function *)
		  ()
              end
		    ) (!map)
	| _ -> Parsing_helper.internal_error "Bad index for find variable") l0;
      Terms.build_term t (FindE(!find_exp, instantiate_term loc_rename mapping one_exp t3, find_info))
  | LetE(pat,t1,t2,topt) ->
      Terms.build_term t (LetE(instantiate_pattern loc_rename mapping one_exp pat,
		      instantiate_term loc_rename mapping one_exp t1,
		      instantiate_term loc_rename mapping one_exp t2,
		      match topt with
			None -> None
		      |	Some t3 -> Some (instantiate_term loc_rename mapping one_exp t3)))
  | ResE(b,t) ->
      Terms.build_term t (ResE((try
	                 List.assq b one_exp.after_transfo_let_vars
                       with Not_found ->
	                 Parsing_helper.internal_error "Variable not found (ResE)"), 
		      instantiate_term loc_rename mapping one_exp t))

and instantiate_pattern loc_rename mapping one_exp = function
    PatVar b ->
      PatVar(try
	List.assq b one_exp.after_transfo_let_vars
      with Not_found ->
	Parsing_helper.internal_error "Variable not found")
  | PatTuple (f,l) -> PatTuple (f,List.map (instantiate_pattern loc_rename mapping one_exp) l)
  | PatEqual t -> PatEqual (instantiate_term loc_rename mapping one_exp t)

let rec transform_pat = function
    PatVar b -> PatVar b
  | PatTuple (f,l) -> PatTuple (f,List.map transform_pat l)
  | PatEqual t -> PatEqual (transform_term t)

(* Conditions of find are transformed only if they
do not contain if/let/find/new. By expansion, if they
contain such a term, it is at the root. *)

let transform_find_cond t =
  match t.t_desc with
    Var _ | FunApp _ -> transform_term t
  | TestE _ | FindE _ | LetE _ | ResE _ -> 
      (* Terms if/let/find/new are never transformed *)
      t

let rec put_restr l p =
  match l with
    [] -> p
  | (a::l) -> Terms.oproc_from_desc (Restr(a, put_restr l p))

(*
None: b is not a name to discharge
Some l: b found as first element of a sequence of variables.
-> put restrictions in l instead of the restriction that creates b
or when l = [],  b found as an element of a sequence of variables,
but not the first one; put no restriction instead of the restriction
that creates b
*)

let rec find_b_rec b = function
    [] -> None
  | (mapping::rmap) ->
      let (_,name_mapping) = !equiv in
      try
	let (b_left,_) = List.find (fun (_,b') -> b' == b) mapping.before_transfo_restr in
	let b_right_list = List.map (fun (x,_,_) -> x) (List.filter (fun (_,b',_) -> b' == b_left) name_mapping) in
	Some (List.map (fun b_right -> List.assq b_right mapping.after_transfo_restr) b_right_list)
      with Not_found ->
	find_b_rec b rmap

let rec check_not_touched t =
  match t.t_desc with
    Var(b,l) -> 
      begin
	match find_b_rec b (!map) with
	  None -> ()
	| Some _ -> Parsing_helper.internal_error "An array index should not be a random number, so should not be touched by cryptographic transformations."
      end
  | FunApp(f,l) -> List.iter check_not_touched l
  | _ -> Parsing_helper.internal_error "If/find/let forbidden in defined condition of find"


let rec update_def_list suppl_def_list (b,l) =
  begin
  match find_b_rec b (!map) with
    None -> ()
  | Some l' -> 
      (* Do not add a condition that is already present *)
      let l' = List.filter (fun b' -> b' != b) l' in
      suppl_def_list := (List.map (fun b' -> (b',l)) l') @ (!suppl_def_list)
  end;
  List.iter check_not_touched l
  (*List.iter (update_def_list_term suppl_def_list) l

and update_def_list_term suppl_def_list t =
  match t.t_desc with
    Var(b,l) -> update_def_list suppl_def_list (b,l)
  | FunApp(f,l) -> List.iter (update_def_list_term suppl_def_list) l
  | _ -> Parsing_helper.internal_error "If/find/let forbidden in defined condition of find"
*)

let rec find_b_otheruses b bef_name_table aft_name_table =
  match bef_name_table, aft_name_table with
    [],[] -> None
  | (l1::r1,l2::r2) ->
      let snd_l1 = List.map snd l1 in
      let snd_l2 = List.map snd l2 in
      if not (List.memq b snd_l1) then find_b_otheruses b r1 r2 else
      Some snd_l2
  | _ -> Parsing_helper.internal_error "different length in find_b"

let rec find_b_rec_otheruses b = function
    [] -> None
  | (mapping::rmap) ->
      match find_b_otheruses b mapping.before_transfo_name_table mapping.after_transfo_name_table with
	None -> find_b_rec_otheruses b rmap
      |	x -> x

exception FalseOtherUses

let rec update_otheruses_list = function
    [] -> []
  | (b,l)::r ->
      List.iter check_not_touched l;
      let r' = update_otheruses_list r in
      match find_b_rec_otheruses b (!map) with
        (* b is unchanged, otheruses(b[l]) remains *)
	None -> (b,l)::r'
	(* When b is mapped to b1...bn by the transformation, we would like
           to replace otheruses(b[l]) with 
	   otheruses(b1[l]) OR ... OR otheruses(bn[l])
           So when n = 0, the condition is false,
              when n = 1, the condition becomes otheruses(b1[l])
              when n > 1, expressing the OR condition would complicate the
              game, so we prefer replacing the condition with "true":
              otheruses(b[l]) is simply removed. *)
      |	Some [] -> 
	  print_string "Warning: an \"otheruses\" condition is false because a cryptographic transformation replaced a probabilistic computation with a deterministic one. This should rarely happen...";
	  raise FalseOtherUses
      |	Some [b'] -> (b',l)::r'
      |	Some _ -> r'

let rec transform_process cur_array p =
  Terms.iproc_from_desc (
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) ->
      Par(transform_process cur_array p1,
	  transform_process cur_array p2)
  | Repl(b,p) ->
      Repl(b, (transform_process ((Terms.term_from_binder b)::cur_array) p))
  | Input((c,tl),pat,p) ->
      let p' = transform_oprocess cur_array p in
      if (!restr_to_put) != [] then
	Parsing_helper.internal_error "restr_to_put should have been cleaned up (input)";
      let pat' = transform_pat pat in
      if (!restr_to_put) = [] then
	Input((c, tl), pat', p')
      else
        (* put restrictions that come from transform_pat *)
	let b = Terms.create_binder "patv" (Terms.new_vname()) Settings.t_bitstring cur_array
	in
	let p'' = Input((c, tl), PatVar b, put_restr (!restr_to_put) 
			  (Terms.oproc_from_desc (Let(pat', Terms.term_from_binder b, p', Terms.yield_proc))))
	in
	restr_to_put := [];
	p'')
	
and transform_oprocess_norestr cur_array p = 
  match p.p_desc with
    Yield -> Terms.yield_proc
  | Restr(b,p) ->
      (* Remove restriction when it is now useless *)
      let p' = transform_oprocess cur_array p in
      begin
	match find_b_rec b (!map) with
	  None -> Terms.oproc_from_desc (Restr(b,p'))
	| Some l ->
	    put_restr l 
	      (if (not (List.memq b l)) && (b.root_def_ref) then
		Terms.oproc_from_desc (Let(PatVar b, Terms.cst_for_type b.btype, p', Terms.yield_proc))
              else
		p')
      end
  | Test(t,p1,p2) ->
      Terms.oproc_from_desc (Test(transform_term t, 
	   transform_oprocess cur_array p1, 
	   transform_oprocess cur_array p2))
  | Find(l0, p2, find_info) ->
      Terms.oproc_from_desc (Find(transform_find_list cur_array l0, 
	   transform_oprocess cur_array p2, find_info))
  | Let(pat,t,p1,p2) ->
      Terms.oproc_from_desc (Let(transform_pat pat, transform_term t, 
	  transform_oprocess cur_array p1, 
	  transform_oprocess cur_array p2))
  | Output((c,tl),t2,p) ->
      Terms.oproc_from_desc (Output((c, List.map transform_term tl), transform_term t2, 
	     transform_process cur_array p))
  | EventP(t,p) ->
      Terms.oproc_from_desc (EventP(transform_term t,
	     transform_oprocess cur_array p))

and transform_find_list cur_array = function
    [] -> []
  | (bl, def_list, otheruses_list, t, p1)::l ->
      try
	let new_def_list = ref def_list in
	List.iter (update_def_list new_def_list) def_list;
	let new_otheruses_list = update_otheruses_list otheruses_list in
	let branch' = (bl, !new_def_list, new_otheruses_list, transform_find_cond t,
	 transform_oprocess cur_array p1) in
	branch'::(transform_find_list cur_array l)
      with FalseOtherUses -> 
	transform_find_list cur_array l

and transform_oprocess cur_array p =
  if (!restr_to_put) != [] then
    Parsing_helper.internal_error "restr_to_put should have been cleaned up";
  let p' = transform_oprocess_norestr cur_array p in
  let p'' = put_restr (!restr_to_put) p' in
  restr_to_put := [];
  p''

let do_crypto_transform p = 
  Terms.array_ref_process p;
  let r = transform_process [] p in
  Terms.cleanup_array_ref();
  r

(* Compute the runtime of the context *)

(* (!Settings.ignore_small_times)>0 when many details should be ignored.*)

let rec make_length_term t =
  match t.t_desc with
    FunApp(f,l) -> 
      Length(f, make_length l)
  | Var(b,l) ->
      Maxlength(!whole_game, Terms.term_from_binder b)
  | TestE _ | LetE _ | FindE _ | ResE _ ->
      Parsing_helper.internal_error "If/let/find/new not allowed in make_length_term"

and make_length = function
    [] -> []
  | (t::l) ->
      let l' = make_length l in
      if t.t_type.toptions land Settings.tyopt_BOUNDED != 0 then
	l'
      else
	(make_length_term t)::l'   (*Maxlength(!whole_game, t)::l'*)

let rec time_list f = function
    [] -> Polynom.zero
  | (a::l) -> Polynom.sum (f a) (time_list f l)
	
let rec get_time_map t = function
    [] -> raise Not_found 
  | (mapping::l) ->
      let rec find_in_exp = function
	  [] -> get_time_map t l
	| one_exp::expl ->
	    if one_exp.source_exp_instance == t then
	      let args = List.map snd one_exp.after_transfo_input_vars_exp in
	      let targs = time_list time_term args in
	      if (!Settings.ignore_small_times)>0 then
		targs
	      else
		(* Number of indexes at that expression in the process *)
		let il = List.length one_exp.cur_array_exp in
		(* Number of indexes at that expression in the equivalence *)
		let ik = List.length mapping.before_transfo_name_table in
		let eqindexty = List.map (fun (brepl, _,_) -> Settings.t_interv(*brepl.btype*)) mapping.count in
		let tupleargs = 
		  Terms.build_term_type Settings.t_bitstring (FunApp(Settings.get_tuple_fun (List.map (fun t -> t.t_type) args), args))
		in
		let t_context = 
		  if (!Settings.front_end) == Settings.Oracles then
		    Add(Add(Add(Mul (Cst (float_of_int (ik*il)), ActTime(AFunApp(Settings.f_plus), [])),
				Mul (Cst (float_of_int (ik*il)), ActTime(AFunApp(Settings.f_mul), []))),
			    Mul(Cst (float_of_int (4*ik+5+2*List.length args)), ActTime(AArrayAccess ik, []))),
			Add(Mul(Cst (float_of_int (2*ik*(ik+1))), ActTime(AReplIndex, [])),
			    Mul(Cst 2.0, ActTime(AArrayAccess il, []))))
		  else
		    Add(Add(Add(ActTime(AOut(eqindexty, t.t_type), make_length [t]),
				Add(Mul (Cst (float_of_int (ik*il)), ActTime(AFunApp(Settings.f_plus), [])),
				    Mul (Cst (float_of_int (ik*il)), ActTime(AFunApp(Settings.f_mul), [])))),
			    Add(Mul(Cst (float_of_int (3*ik)), ActTime(AOut(eqindexty, Settings.t_unit), [])),
				Mul(Cst 2.0, ActTime(AOut(eqindexty, Settings.t_bitstring), make_length [tupleargs])))),
			Add(Add(Mul(Cst (float_of_int (3*ik+3)), ActTime(AIn ik, [])),
				Mul(Cst (float_of_int (2*ik*(ik+1))), ActTime(AReplIndex, []))),
			    Add(ActTime(AArrayAccess il, []), ActTime(AArrayAccess ik, []))))
		in
		let t_indexes = time_list (fun (_,tl) -> time_list time_term tl) one_exp.name_indexes_exp in
		Polynom.sum targs (Polynom.sum t_indexes (Polynom.probaf_to_polynom t_context))
	    else
	      find_in_exp expl
      in
      find_in_exp mapping.expressions

and time_term t =
  try
    (* The term is transformed; compute the time of the context,
       not the time of t itself *)
    get_time_map t (!map)
  with Not_found -> 
    (* The term is not transformed; simply compute the time of t *)
  match t.t_desc with
    Var(b,[]) when Terms.is_repl b ->
      if (!Settings.ignore_small_times)>0 then
	Polynom.zero
      else
	Polynom.probaf_to_polynom (ActTime(AReplIndex, []))
  | Var(b,l) ->
      let tl = time_list time_term l in
      if (!Settings.ignore_small_times)>0 then
	tl
      else
	Polynom.sum tl (Polynom.probaf_to_polynom (ActTime(AArrayAccess (List.length l), [])))
  | FunApp(f,l) ->
      let tl = time_list time_term l in
      if (!Settings.ignore_small_times)>1 && 
	((f==Settings.f_and) || (f==Settings.f_or) || (f==Settings.f_not) ||
	 (f==Settings.get_tuple_fun []) || 
	 ((l == []) && (Terms.equal_terms t (Terms.cst_for_type (snd f.f_type)))))
      then
	(* Ignore &&, ||, not, (), cst_ty 
	   when (!Settings.ignore_small_times)>1 *)
	tl
      else
	Polynom.sum tl (Polynom.probaf_to_polynom (ActTime(AFunApp f, make_length l)))
  | TestE _ | LetE _ | FindE _ | ResE _ ->
      Parsing_helper.internal_error "If/let/find/new unexpected in time_term"


let rec time_term_ignore_tuple t =
  match t.t_desc with
    FunApp(f,l) when f.f_cat == Tuple ->
      time_list time_term_ignore_tuple l
  | _ -> time_term t

let time_term_ignore_top_tuple t =
  match t.t_desc with
    FunApp(f,l) when f.f_cat == Tuple ->
      time_list time_term l
  | _ -> time_term t

let rec time_pat = function
    PatVar b -> 
      if (!Settings.ignore_small_times)>0 then
	Polynom.zero
      else
	Polynom.probaf_to_polynom (ActTime(AArrayAccess (List.length b.args_at_creation), []))
  | PatTuple(f,l) ->
      let tl = time_list time_pat l in
      if (!Settings.ignore_small_times)>1 && 
	(f == Settings.get_tuple_fun []) then
	(* Ignore let () when (!Settings.ignore_small_times)>1 *)
	tl
      else
	Polynom.sum tl (Polynom.probaf_to_polynom (ActTime(APatFunApp f, make_length (List.map Terms.term_from_pat l))))
  | PatEqual t ->
      Polynom.sum (time_term t) (Polynom.probaf_to_polynom (ActTime(AFunApp (Settings.f_comp Equal t.t_type t.t_type), make_length [t])))

let rec time_pat_ignore_tuple = function
    PatTuple(f,l) when f.f_cat == Tuple ->
      time_list time_pat_ignore_tuple l
  | pat -> time_pat pat

let time_pat_ignore_top_tuple = function
    PatTuple(f,l) when f.f_cat == Tuple ->
      time_list time_pat l
  | pat -> time_pat pat

let time_binderref (b,l) = 
  let tl = time_list time_term l in
  if (!Settings.ignore_small_times)>0 then
    tl
  else
    Polynom.sum tl (Polynom.probaf_to_polynom (ActTime(AArrayAccess (List.length l), [])))

let rec time_process p =
  match p.i_desc with
    Nil -> Polynom.zero
  | Par(p1,p2) -> Polynom.sum (time_process p1) (time_process p2)
  | Repl(b,p) -> Polynom.product (time_process p) (Polynom.probaf_to_polynom (Count (Terms.param_from_type b.btype)))
  | Input((c,tl),pat,p) ->
      let ttl = Polynom.sum (Polynom.sum (time_list time_term tl) 
	 ((if (!Settings.ignore_small_times)>1 then time_pat_ignore_tuple else 
	   if (!Settings.front_end) == Settings.Oracles then time_pat_ignore_top_tuple else time_pat) pat)) (time_oprocess p) in
      if ((!Settings.ignore_small_times)>0) || 
         ((!Settings.front_end) == Settings.Oracles) then
	ttl
      else
	Polynom.sum ttl (Polynom.probaf_to_polynom (ActTime(AIn(List.length tl), [])))
      
and time_oprocess p = 
  match p.p_desc with
    Yield -> 
      if ((!Settings.ignore_small_times)>0) || 
         ((!Settings.front_end) == Settings.Oracles) then
	Polynom.zero
      else
	Polynom.probaf_to_polynom (ActTime(AOut([], Settings.t_unit), []))
  | Restr(b,p) ->
      let tp = time_oprocess p in
      if (!Settings.ignore_small_times)>0 then
	tp
      else
	begin
	  (* When b is in names_to_discharge, "new b" is replaced with
	     "let b = cst" in the context *)
	  if List.memq b (!names_to_discharge) then
	    Polynom.sum tp (Polynom.sum 
	      (Polynom.probaf_to_polynom (ActTime(AArrayAccess (List.length b.args_at_creation), [])))
              (time_term (Terms.cst_for_type b.btype)))
	  else
	    Polynom.sum tp (Polynom.probaf_to_polynom 
	      (Add(ActTime(AArrayAccess (List.length b.args_at_creation), []), ActTime(ANew b.btype, []))))
	end
  | Test(t,p1,p2) ->
      let tp = Polynom.sum (time_term t) (Polynom.max (time_oprocess p1) (time_oprocess p2)) in
      if (!Settings.ignore_small_times)>0 then
	tp
      else
	Polynom.sum tp (Polynom.probaf_to_polynom (ActTime(AIf, [])))
  | Find(l0,p2, _) ->
      let rec t_proc = function
	  [] -> time_oprocess p2
	| (_,_,_,_,p1)::l -> Polynom.max (time_oprocess p1) (t_proc l)
      in
      let tp = t_proc l0 in
      let rec prod_count r = function
	  [] -> r
	| (b::bl) -> Polynom.product (Polynom.probaf_to_polynom (Count (Terms.param_from_type b.btype))) (prod_count r bl)
      in
      let max_blen = ref 0 in
      let args_at_creation = ref 0 in
      let rec t_test = function
	  [] -> tp
	| (bl, def_list, otheruses_list, t, _)::l ->
	    let t_test1 = 
	      Polynom.sum (time_list time_binderref def_list)
	     (Polynom.sum (time_list time_binderref otheruses_list)
	     (Polynom.sum (time_term t) 
	     (if (!Settings.ignore_small_times)>0 then 
	       Polynom.zero
	     else
	       Polynom.probaf_to_polynom (
	       match bl with
		 [] -> ActTime(AFind 0, [])
	       | (b::_) ->
		   let blen = List.length bl in
		   let argslen = List.length b.args_at_creation in
		   if blen > !max_blen then
		     begin
		       max_blen := blen;
		       args_at_creation := argslen
		     end;
		   Add(ActTime(AFind blen, []), Mul (Cst(float_of_int blen), ActTime(AArrayAccess argslen, [])))
		     ))))
	    in
	    Polynom.sum (t_test l) (prod_count t_test1 bl)
      in
      let tt = t_test l0 in
      if (!Settings.ignore_small_times)>0 then 
	tt
      else
	Polynom.sum tt (Polynom.probaf_to_polynom (Mul (Cst(float_of_int (!max_blen)), ActTime(AArrayAccess (!args_at_creation), []))))
  | Output((c,tl),t2,p) ->
      let tp = Polynom.sum (time_list time_term tl) 
	  (Polynom.sum ((if (!Settings.ignore_small_times)>1 then time_term_ignore_tuple else
	                 if (!Settings.front_end) == Settings.Oracles then time_term_ignore_top_tuple else time_term) t2) (time_process p)) in
      if ((!Settings.ignore_small_times)>0) ||
         ((!Settings.front_end) == Settings.Oracles) then
	tp
      else
	Polynom.sum tp (Polynom.probaf_to_polynom (ActTime(AOut(List.map (fun t -> t.t_type) tl, t2.t_type), make_length (tl @ [t2]))))
  | Let(pat, t, p1, p2) ->
      Polynom.sum (time_pat pat) (Polynom.sum (time_term t) 
	(Polynom.max (time_oprocess p1) (time_oprocess p2)))
  | EventP(t,p) ->
      (* Events can be ignored Polynom.sum (time_term t) *) (time_oprocess p)


let time_computed = ref None

let compute_runtime() =
   match !time_computed with
    Some t -> t
  | None ->
      let t = 
	let tp = time_process (!whole_game).proc in
	if (!Settings.ignore_small_times)>0 then
	  tp
	else
	  let ((lm, _,_,_),_) = (!equiv) in
	  let rec countfuns = function
	      [] -> 0
	    | (a::l) -> countfuns_fg a + countfuns l
	  and countfuns_fg = function
	      ReplRestr(_,_,fgl) -> 1 + countfuns fgl
	    | Fun _ -> 1
	  in
	  let nnewchannel = 2*(countfuns (List.map fst lm)) in
	  Polynom.sum tp (Polynom.probaf_to_polynom (Mul(Cst (float_of_int nnewchannel), ActTime(ANewChannel, []))))
      in
      let tt = Polynom.polynom_to_probaf t in
      time_computed := Some tt;
      tt

let compute_runtime_for g =
  whole_game := g;
  map := [];
  names_to_discharge := [];
  time_computed := None;
  compute_runtime()

(* Compute the difference of probability *)

(* We represent the number of usages of a repl. binder as follows:
   it is a list of lists of pairs (nt, v) where
       - nt is a name table (names in lhs of equivalence, names in initial process),
         or None
       - v is the number of usages associated with the expression of name table nt
   When several expressions have the same name table nt and it is not None, 
   they should be counted only once. 
   When the name table nt is None, each expression should be counted
   as many times as it appears.
   These pairs are grouped in a list, which is to be understood as a sum.
   (It corresponds to expressions that may be executed consecutively.)
   These lists are themselves grouped in another list, which is to be understood
   as a maximum. (It corresponds to sets of expressions that cannot be both
   evaluated, due to tests (if/find/let).)
*)

let rec get_repl_from_count b_repl = function
    [] -> raise Not_found
  | ((b, ntopt, v)::l) -> 
      if b_repl == Terms.param_from_type b.btype then
	(ntopt, Polynom.probaf_to_polynom v)
      else
	get_repl_from_count b_repl l

let rec get_repl_from_map b_repl exp = function
    [] -> raise Not_found
  | { expressions = e; count = c }::l ->
      if List.exists (fun one_exp -> one_exp.source_exp_instance == exp) e then
	get_repl_from_count b_repl c
      else
	get_repl_from_map b_repl exp l

let equal_nt1 la1 la2 =
  (List.length la1 == List.length la2) && 
  (List.for_all2 (fun (b1, b1') (b2, b2') ->
    (b1 == b2) && (b1' == b2')) la1 la2)

let equal_ntl la1 la2 =
  (List.length la1 == List.length la2) && 
  (List.for_all2 equal_nt1 la1 la2)

let equal_ntopt nt1 nt2 =
  match nt1,nt2 with
    Some n1, Some n2 -> equal_ntl n1 n2
  | _ -> false

let add_repl_count (ntopt, v) l = 
  if ntopt = None then 
    (ntopt, v)::l
  else if List.exists (fun (ntopt',v') -> equal_ntopt ntopt ntopt') l then
    l
  else
    (ntopt, v)::l

let add_repl_countl elem l =
  List.map (add_repl_count elem) l
      
(* merge_count computes the count corresponding to l1 + l2, 
   where l1 and l2 are lists of lists of pairs (nt, v).
   This is done by adding each element of l1 to each element of l2 *)
let rec add_list eleml l =
  match eleml with
    [] -> l
  | (a::eleml') -> add_repl_countl a (add_list eleml' l)

let merge_count l1 l2 =
  List.concat (List.map (fun l -> add_list l l2) l1)

(* Like l1 @ l2 but removes useless empty lists
   This is important for the speed of the probability evaluation... *)
let append l1 l2 =
  if l1 = [[]] then l2 else 
  if l2 = [[]] then l1 else
  l1 @ l2

let rec repl_count_term accu b_repl t =
  let accu' = 
    try 
      add_repl_countl (get_repl_from_map b_repl t (!map)) accu
    with Not_found -> 
      accu
  in
  match t.t_desc with
    Var(_,l) | FunApp(_,l) ->
      repl_count_term_list accu' b_repl l
  | TestE _ | FindE _ | LetE _ | ResE _ -> 
      Parsing_helper.internal_error "If, find, let, and new should have been expanded (Cryptotransf.repl_count_term)"

and repl_count_term_list accu b_repl = function
    [] -> accu
  | (a::l) ->
      repl_count_term_list (repl_count_term accu b_repl a) b_repl l

let rec repl_count_pat accu b_repl = function
    PatVar b -> accu
  | PatTuple(_, l) -> repl_count_pat_list accu b_repl l
  | PatEqual t ->  repl_count_term accu b_repl t

and repl_count_pat_list accu b_repl = function
    [] -> accu
  | (a::l) ->
      repl_count_pat_list (repl_count_pat accu b_repl a) b_repl l

let rec repl_count_process b_repl p =
  match p.i_desc with
    Nil -> [[]]
  | Par(p1,p2) ->
      merge_count (repl_count_process b_repl p1) (repl_count_process b_repl p2) 
  | Repl(_,p) ->
      repl_count_process b_repl p
  | Input((c,tl),pat,p) ->
      repl_count_term_list (repl_count_pat (repl_count_oprocess b_repl p) b_repl pat) b_repl tl

and repl_count_oprocess b_repl p = 
  match p.p_desc with
    Yield -> [[]]
  | Restr(_,p) -> repl_count_oprocess b_repl p
  | Test(t,p1,p2) ->
      repl_count_term (append (repl_count_oprocess b_repl p1) (repl_count_oprocess b_repl p2)) b_repl t
  | Let(pat, t, p1, p2) ->
      repl_count_term (repl_count_pat (append (repl_count_oprocess b_repl p1) (repl_count_oprocess b_repl p2)) b_repl pat) b_repl t
  | Find(l0,p2, _) ->
      let rec find_lp = function
	  [] -> repl_count_oprocess b_repl p2
	| (_,_,_,_,p1)::l -> append (repl_count_oprocess b_repl p1) (find_lp l)
      in
      let accu = find_lp l0 in
      let rec find_lt = function
	  [] -> accu
	| (_,_,_,t,_)::l -> 
	    repl_count_term (find_lt l) b_repl t
      in
      find_lt l0
  | Output((c,tl),t2,p) ->
      repl_count_term_list (repl_count_term (repl_count_process b_repl p) b_repl t2) b_repl tl
  | EventP(t,p) -> 
      repl_count_term (repl_count_oprocess b_repl p) b_repl t

(* Convert a list of list of (nt, count) corresponding to
   the number of usages of a repl. binder into a polynom
   (the first list is a max, the second one a sum) *)

let rec count_to_poly = function
    [] -> Polynom.zero
  | ((_,v)::l) -> Polynom.sum v (count_to_poly l)

let rec countl_to_poly = function
    [] -> Polynom.zero
  | v::l -> Polynom.max (count_to_poly v) (countl_to_poly l)

let rec rename_term map one_exp t =
  match t.t_desc with
    FunApp(f,l) -> 
      Terms.build_term t (FunApp(f, List.map (rename_term map one_exp) l))
  | Var(b,l) -> 
      begin
	if not (List.for_all2 Terms.equal_terms l b.args_at_creation) then
          Parsing_helper.internal_error "Unexpected variable reference in rename_term";
	try
	  List.assq b one_exp.before_transfo_input_vars_exp
	with Not_found ->
	  Terms.term_from_binder (List.assq b map.before_transfo_restr)
	    (* Raises Not_found when the variable is not found.
	       In this case, the considered expression has no contribution 
	       to the maximum length. *)
      end
  | _ -> Parsing_helper.internal_error "If/let/find/res not allowed in rename_term"

let rec make_max = function
    [] -> Zero
  | [a] -> a
  | l -> Max(l)

let rec map_probaf env = function
    (Cst _ | Card _ | TypeMaxlength _) as x -> Polynom.probaf_to_polynom x
  | Proba(p,l) -> Polynom.probaf_to_polynom (Proba(p, List.map (fun prob -> 
      Polynom.polynom_to_probaf (map_probaf env prob)) l))
  | ActTime(f, l) -> 
      Polynom.probaf_to_polynom (ActTime(f, List.map (fun prob -> 
      Polynom.polynom_to_probaf (map_probaf env prob)) l))
  | Maxlength(n,t) ->
      let accu = ref [] in
      List.iter (fun map -> 
	List.iter (fun one_exp -> 
	  try
	    let lt = make_length_term (rename_term map one_exp t) in
	    if not (List.exists (Terms.equal_probaf lt) (!accu)) then
	      accu := lt :: (!accu) 
	  with Not_found -> 
	    ()
	    ) map.expressions
	  ) (!map);
      Polynom.probaf_to_polynom (make_max (!accu))
  | Length(f,l) ->
      Polynom.probaf_to_polynom (Length(f, List.map (fun prob -> 
	Polynom.polynom_to_probaf (map_probaf env prob)) l))
  | Count p -> 
      begin
	try
	  List.assq p (!env)
	with Not_found ->
	  let v = repl_count_process p (!whole_game).proc in
	  let v' = countl_to_poly v in
	  env := (p, v') :: (!env);
	  v'
      end
  | Mul(x,y) -> Polynom.product (map_probaf env x) (map_probaf env y)
  | Add(x,y) -> Polynom.sum (map_probaf env x) (map_probaf env y)
  | Sub(x,y) -> Polynom.sub (map_probaf env x) (map_probaf env y)
  | Div(x,y) -> Polynom.probaf_to_polynom 
	(Div(Polynom.polynom_to_probaf (map_probaf env x), 
	     Polynom.polynom_to_probaf (map_probaf env y)))
  | Max(l) -> 
      let l' = List.map (fun x -> Polynom.polynom_to_probaf (map_probaf env x)) l in
      let rec simplify_max accu = function
	  [] -> accu
	| Zero::l -> simplify_max accu l
	| Max(l')::l -> simplify_max (simplify_max accu l') l
	| a::l -> simplify_max (a::accu) l
      in
      let l'' = simplify_max [] l' in
      Polynom.probaf_to_polynom (make_max l'')
  | Zero -> Polynom.zero
  | AttTime -> 
      Polynom.sum (Polynom.probaf_to_polynom (Time (!whole_game, compute_runtime()))) (Polynom.probaf_to_polynom (AttTime))
  | Time _ -> Parsing_helper.internal_error "Unexpected time"

let compute_proba ((_,_,set,_),_) =
  List.map (function 
      SetProba r -> 
	let probaf' =  map_probaf (ref []) r.proba in
	SetProba { set_name = ""; proba = Polynom.polynom_to_probaf probaf' }
    | SetEvent(f,_) -> 
	SetEvent(f,!whole_game_next)) set


(* Main transformation function 
   with automatic determination of names_to_discharge *)

let rec find_restr accu p =
  match p.i_desc with
    Nil -> ()
  | Par(p1,p2) ->
      find_restr accu p1;
      find_restr accu p2
  | Repl(_,p) -> find_restr accu p
  | Input(_,_,p) -> find_restro accu p

and find_restro accu p =
  match p.p_desc with
    Yield -> ()
  | Let(_,_,p1,p2) | Test(_,p1,p2) -> 
      find_restro accu p1;
      find_restro accu p2
  | Find(l0,p2,_) ->
      List.iter (fun (_,_,_,_,p1) -> find_restro accu p1) l0;
      find_restro accu p2
  | Restr(b,p) ->
      if not (List.memq b (!accu)) then
	accu := b :: (!accu);
      find_restro accu p
  | Output(_,_,p) -> 
      find_restr accu p
  | EventP(_,p) ->
      find_restro accu p

(* Returns either TSuccess (prob, p') -> game transformed into p' with difference of probability prob
   or TFailure l where l is a list of possible transformations:
   values for equiv, names_to_discharge, and preliminary transformations to do *)
let rec try_with_partial_assoc apply_equiv =
  let old_names_to_discharge = !names_to_discharge in
  let to_do = check_process() in
  if (!names_to_discharge != old_names_to_discharge) || ((!rebuild_map_mode) && (is_success_no_advice to_do)) then
    begin
      if is_success_no_advice to_do then rebuild_map_mode := false; (* When I'm just looking for advice, I don't mind if the map of names cannot be fully completed *)
      let (apply_equiv', names_to_discharge', to_do') = try_with_partial_assoc apply_equiv in
      (apply_equiv', names_to_discharge', and_ins to_do to_do')
    end
  else 
    (apply_equiv, !names_to_discharge, to_do)

let try_with_known_names names apply_equiv =
  (* We rebuild the list of names to discharge by adding them one by one.
     This is better for CDH. *)
  names_to_discharge := [];
  map := [];
  rebuild_map_mode := true;
  let rec build_names_to_discharge names apply_equiv =
    names_to_discharge := (List.hd names) :: (!names_to_discharge);
    let res = try_with_partial_assoc apply_equiv in
    let still_to_discharge = List.filter (fun b -> not (List.memq b (!names_to_discharge))) names in
    if still_to_discharge == [] then
      res
    else
      build_names_to_discharge still_to_discharge apply_equiv
  in
  build_names_to_discharge (List.rev names) apply_equiv

(*
  names_to_discharge := names;
  map := [];
  rebuild_map_mode := true;
  try_with_partial_assoc apply_equiv
*)

let rec found_in_fungroup t = function
    ReplRestr(_,_,funlist) ->
      List.exists (found_in_fungroup t) funlist
  | Fun(_,_,res,_) -> res == t

let is_exist t ((lm,_,_,_),_) =
  List.exists (fun (fg, mode) ->
    (mode == ExistEquiv) && (found_in_fungroup t fg)) lm

let rec check_required map = function
    ReplRestr(_,_,fgl) -> List.for_all (check_required map) fgl
  | Fun(_,_,t,(_,options)) ->
    (options != RequiredOpt) ||
    (List.exists (fun mapping -> mapping.source_exp == t) map)

let map_has_exist (((lm, _, _, _),_) as apply_equiv) map =
  (map != []) && (
  (* Either the equivalence has no "Exist" *)
  (List.for_all (fun (fg, mode) -> mode == AllEquiv) lm) ||
  (* or the map maps at least one "Exist" member of the equivalence *)
  (List.exists (fun mapping -> is_exist mapping.source_exp apply_equiv) map))
  &&
  (* At least one element of map has a different expression in the
     left- and right-hand sides of the equivalence *)
  (List.exists (fun mapping ->  
    try
    not (Terms.equal_terms mapping.source_exp 
	   (Terms.subst2 
	      ((List.map2 (fun bt at -> (at, Terms.term_from_binder bt)) mapping.source_args mapping.target_args) @
	       (List.concat (List.map2 (List.map2 (fun (bt,_) (at,_) -> (at, Terms.term_from_binder bt))) mapping.before_transfo_name_table mapping.after_transfo_name_table)))
	      mapping.target_exp))
    with _ -> true
    ) map)
  &&
  (* Check that the functions marked "required" really occur in the map *)
  (List.for_all (fun (fg, _) -> check_required map fg) lm)


let eq_name_set l1 l2 =
  (List.for_all (fun i1 -> List.memq i1 l2) l1) &&
  (List.for_all (fun i2 -> List.memq i2 l1) l2)

let eq_triple (eq1,n1,i1) (eq2,n2,i2) =
  (eq1 == eq2) && (eq_name_set n1 n2) && (eq_ins_set i1 i2)

let is_nil (eq,n,i) = (i == [])

let is_smaller (eq1,n1,i1) (eq2,n2,i2) =
  List.length i1 <= List.length i2

let rec merge_triple ins_accu1 ins_accu2 =
  match (ins_accu1, ins_accu2) with
    (l1,p1)::r1, (l2,p2)::r2 ->
      if p1 < p2 then 
	(* Put p1 first *)
	if is_nil l1 then
	  [(l1,p1)]
	else
	  (l1,p1)::(merge_triple r1 ins_accu2)
      else if p1 > p2 then
	(* Put p2 first *)
	if is_nil l2 then
	  [(l2,p2)]
	else
	  (l2,p2)::(merge_triple ins_accu1 r2)
      else
	(* Put the shortest list first when priorities are equal *)
	if is_nil l1 then
	  [(l1,p1)]
	else if is_nil l2 then
	  [(l2,p2)]
	else if is_smaller l1 l2 then
	  (* Remove duplicates *)
	  if eq_triple l1 l2 then
	    (l1,p1)::(merge_triple r1 r2)
	  else
	    (l1,p1)::(merge_triple r1 ins_accu2)
	else
	  (l2,p2)::(merge_triple ins_accu1 r2)
  | [], ins_accu2 -> ins_accu2
  | ins_accu1, [] -> ins_accu1

type trans_res =
  TSuccessPrio of setf list * game
| TFailurePrio of ((equiv_nm * binder list * instruct list) * int) list


let transfo_expand p =
  Transform.expand_process (do_crypto_transform p)
	
let rec try_with_restr_list apply_equiv = function
    [] -> TFailurePrio []
  | (b::l) ->
        begin
	  rebuild_map_mode := true;
          names_to_discharge := b;
	  global_sthg_discharged := false;
	  map := [];
          try 
            let (apply_eq,discharge_names,to_do) = try_with_partial_assoc apply_equiv in
	    (* If global_sthg_discharged is false, nothing done; b is never used in positions
               in which it can be discharged; try another restriction list *)
	    if not (!global_sthg_discharged) then raise SurelyNot;
	    (* When (!map) == [], nothing done; in fact, b is never used in the game; try another name *)
            if is_success_no_advice to_do then
	      if map_has_exist apply_equiv (!map) then
		begin
		  if debug then 
		    begin
		      print_string "Success with ";
		      Display.display_list Display.display_binder (!names_to_discharge);
		      print_newline()
		    end;
		  let g' = { proc = transfo_expand (!whole_game).proc; game_number = -1 } in
		  whole_game_next := g';
		  TSuccessPrio (compute_proba apply_equiv, g')
		end
	      else
		try_with_restr_list apply_equiv l
            else
            match try_with_restr_list apply_equiv l with
              TSuccessPrio (prob,g') -> TSuccessPrio (prob,g')
            | TFailurePrio l' -> TFailurePrio (merge_triple (List.map (fun (l,p) -> ((apply_eq,discharge_names, l),p)) to_do) l')
          with SurelyNot -> try_with_restr_list apply_equiv l
        end


let try_with_restr_list (((lm, _, _, _),_) as apply_equiv) restr =
  if (List.for_all (fun (fg, mode) -> mode == AllEquiv) lm) then
    (* Try with no name; the system will add the needed names if necessary *)
    try_with_restr_list apply_equiv [[]]
  else
    begin
      (* Try with at least one name *)
      if !stop_mode then
	(* In stop_mode, cannot add names, so fail *)
	TFailurePrio []
      else
	try_with_restr_list apply_equiv (List.map (fun b -> [b]) restr)
    end

let rec build_symbols_to_discharge = function
    ReplRestr(_,_,fun_list) ->
      List.iter build_symbols_to_discharge fun_list
  | Fun(_,_,{ t_desc = FunApp(f,_) },_) ->
      symbols_to_discharge := f :: (!symbols_to_discharge)
  | _ -> ()
      


let crypto_transform stop no_advice (((lm,_,_,_),_) as apply_equiv) names ({ proc = p } as g) = 
  stop_mode := stop;
  no_advice_mode := no_advice;
  equiv := apply_equiv;
  whole_game := g;
  time_computed := None;
  symbols_to_discharge := [];
  List.iter (fun (fg, mode) ->
    if mode == AllEquiv then build_symbols_to_discharge fg) lm;
  Terms.build_def_process None p;
  if !Settings.optimize_let_vars then
    incompatible_terms := incompatible_defs p;
  if (names == []) then
    begin
      (* I need to determine the names to discharge from scratch *)
      let restr = ref [] in
      find_restr restr p;
      match try_with_restr_list apply_equiv (!restr) with
	TSuccessPrio(prob, p') -> TSuccess(prob, p')
      |	TFailurePrio l -> TFailure (List.map (fun (x,p) -> x) l)
    end
  else
    begin
      (* names_to_discharge is at least partly known *)
      try 
        let (apply_eq, discharge_names, to_do) = try_with_known_names names apply_equiv in
        if is_success_no_advice to_do then
	  begin
	    if map_has_exist apply_equiv (!map) then
	      begin
		if debug then 
		  begin
		    print_string "Success with ";
		    Display.display_list Display.display_binder discharge_names;
		    print_newline()
		  end;
		let g' = { proc = transfo_expand p; game_number = -1 } in
		whole_game_next := g';
		TSuccess (compute_proba apply_equiv, g')
	      end
	    else
	      TFailure []
	  end
        else
          TFailure (List.map (fun (l,p) -> (apply_eq,discharge_names, l)) to_do)
      with SurelyNot -> TFailure []
    end
