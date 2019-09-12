open Types

(* Priorities for orienting equalities into rewrite rules *)
let current_max_priority = ref 0
let priority_list = ref []

let rec match_term2 next_f simp_facts bl t t' =
  match t.t_desc with
    ReplIndex(v) when (List.memq v bl) ->
      begin
	if t'.t_type != v.ri_type then
	  raise NoMatch;
	match v.ri_link with
	  NoLink -> Terms.ri_link v (TLink t')
	| TLink t -> if not (Terms.simp_equal_terms simp_facts true t t') then raise NoMatch
      end;
      next_f ()
  | ReplIndex(v) ->
      begin
	match t'.t_desc with
	  ReplIndex(v') when v == v' -> next_f()
	| _ -> if not (Terms.simp_equal_terms simp_facts true t t') then raise NoMatch else next_f()
      end
  | Var(v,l) ->
      begin
	match t'.t_desc with
	  Var(v',l') when v == v' ->
	    match_term_list2 next_f simp_facts bl l l'
	| _ -> if not (Terms.simp_equal_terms simp_facts true t t') then raise NoMatch else next_f()
      end
  | FunApp _ ->
      Parsing_helper.internal_error "Function symbol in Simplify1.match_term2. Should never occur since it is used to match binderrefs only"
  | _ -> Parsing_helper.internal_error "If, find, let, and new should not occur in match_term2"

and match_term_list2 next_f simp_facts bl l l' = 
  match l,l' with
    [],[] -> next_f()
  | a::l,a'::l' ->
      match_term2 (fun () -> match_term_list2 next_f simp_facts bl l l') 
	simp_facts bl a a'
  | _ -> Parsing_helper.internal_error "Different lengths in match_term_list2"


let match_binderref2 next_f simp_facts bl (b,l) (b',l') =
  if b != b' then raise NoMatch;
  match_term_list2 next_f simp_facts bl l l'

let rec match_among next_match simp_facts bl br = function
    [] -> raise NoMatch
  | (br1::brl) ->
      try 
	Terms.ri_auto_cleanup (fun () ->
	  match_binderref2 next_match simp_facts bl br br1)
      with NoMatch ->
	match_among next_match simp_facts bl br brl

let rec match_among_list next_match simp_facts bl def_vars = function
    [] -> next_match()
  | (br1::brl) ->
      match_among (fun () -> 
	match_among_list next_match simp_facts bl def_vars brl) 
	simp_facts bl br1 def_vars
  

(* Test if a branch of find always succeeds *)

exception SuccessBranch of (binder * repl_index * term) list * (binder * repl_index) list

let final_next2 dep_info bl true_facts t1 () =
  let bl' = List.map snd bl in
  let t1' = Terms.copy_term Terms.Links_RI t1 in
  (* Cleanup links, with possibility to restore *)
  let tmp_list = List.map (fun b -> b.ri_link) bl' in
  List.iter (fun b -> b.ri_link <- NoLink) bl';
  (* Raise Contradiction when t1 implied *)
  begin
    try 
      Terms.ri_auto_cleanup (fun () -> 
	ignore (Facts.simplif_add dep_info true_facts (Terms.make_not t1')))
    with Contradiction ->
      (* For the value of bl computed in the links, t1 is true;
	 furthermore match_among_list has checked that all variables
	 in def_list are defined, so this branch of find succeeds *)
      (* print_string "Proved ";
         Display.display_term t1';
         print_newline();*)
      let subst = ref [] in
      let keep_bl = ref [] in
      List.iter2 (fun (b,b') l -> 
	match l with
	  TLink b_im -> subst := (b,b',b_im) :: (!subst)
	| NoLink -> keep_bl := (b,b') :: (!keep_bl)) bl tmp_list;
      raise (SuccessBranch(!subst, !keep_bl))
  end;
  (* Restore links *)
  List.iter2 (fun b l -> b.ri_link <- l) bl' tmp_list;
  (* Backtrack *)
  raise NoMatch

(* Raises SuccessBranch when the branch is proved to succeed for some
   value of the indices. These values are stored in the argument of SuccessBranch *)

let branch_succeeds ((bl, def_list, t1, _): 'b findbranch) dep_info true_facts def_vars =
  let bl'' = List.map snd bl in
  try
    match_among_list (final_next2 dep_info bl true_facts t1) true_facts bl'' def_vars def_list
  with NoMatch -> ()

(* Treatment of elsefind facts *)

let final_next true_facts t () =
  let t' = Terms.copy_term Terms.Links_RI t in
  true_facts := (Terms.make_not t')::(!true_facts);
  (* Backtrack *)
  raise NoMatch

let always_true_def_list_t true_facts t simp_facts bl def_vars def_list =
  try
    match_among_list (final_next true_facts t) simp_facts bl def_vars def_list
  with NoMatch -> ()

let rec add_elsefind dep_info def_vars ((subst, facts, elsefind) as simp_facts) = function
    [] -> simp_facts
  | (((bl, def_list, t1,_):'a findbranch)::l) -> 
      (* When the condition t1 contains if/let/find/new, we simply ignore it when adding elsefind facts. *)
      let simp_facts' = 
	match (bl, def_list, t1.t_desc) with
	  [],[],(Var _ | FunApp _) -> Facts.simplif_add dep_info simp_facts (Terms.make_not t1)
	| _,[],_ -> simp_facts
	| _,_,(Var _ | FunApp _) -> 
	    let bl' = List.map snd bl in
	    let true_facts_ref = ref [] in
	    let simp_facts = (subst, facts, (bl', def_list, t1)::elsefind) in
	    always_true_def_list_t true_facts_ref t1 simp_facts bl' def_vars def_list;
	    Facts.simplif_add_list dep_info simp_facts (!true_facts_ref)
	| _ -> simp_facts
      in
      add_elsefind dep_info def_vars simp_facts' l

let update_elsefind_with_def bl (subst, facts, elsefind) =
  (subst, facts, List.map (Terms.update_elsefind_with_def bl) elsefind)

let convert_elsefind dep_info def_vars ((_, _, elsefind) as simp_facts) =
  let true_facts_ref = ref [] in
  List.iter (fun (bl, def_list, t1) ->
    always_true_def_list_t true_facts_ref t1 simp_facts bl def_vars def_list
    ) elsefind;
  (* print_string "Convert_elsefind: found\n";
  List.iter (fun t -> Display.display_term t; print_newline()) (!true_facts_ref);
  print_newline(); *)
  Facts.simplif_add_list dep_info simp_facts (!true_facts_ref)


(* [is_in_bl bl t] returns true when the term [t] is equal to some
   variable in the list [bl] *)

let is_in_bl bl t =
  match t.t_desc with
    Var(b,l) ->
      (List.memq b bl) && (Terms.is_args_at_creation b l)
  | _ -> false

    
(* [needed_vars vars] returns true when some variables in [vars]
   have array accesses or are used in queries. That is, we must keep
   them even if they are not used in their scope. *)
	
let needed_vars vars q = List.exists (fun b -> Terms.has_array_ref_q b q) vars

let needed_vars_in_pat pat q =
  needed_vars (Terms.vars_from_pat [] pat) q

(* Add lets *)

let rec add_let p = function
    [] -> p
  | ((b, b_im)::l) ->
      Terms.oproc_from_desc (Let(PatVar b, b_im, add_let p l, Terms.oproc_from_desc Yield))

let rec add_let_term p = function
    [] -> p
  | ((b, b_im)::l) ->
      Terms.build_term_type p.t_type (LetE(PatVar b, b_im, add_let_term p l, None))

(* [not_found_repl_index_t ri t] returns either
   [None] when [t] does not contain any replication index of [ri]
   or [Some def_list] where [def_list] is a list of the largest variable
   references in [t] that do not contain indices in [ri] *)

let rec not_found_repl_index_l ri = function
    [] -> None
  | (a::l) ->
      let r1 = not_found_repl_index_l ri l in
      let r2 = not_found_repl_index_t ri a in
      match r1, r2 with
	None, None -> None
      |	Some (def_list1), Some(def_list2) -> Some (def_list1 @ def_list2)
      |	None, Some(def_list2) -> 
	  let accu = ref def_list2 in
	  List.iter (Terms.get_deflist_subterms accu) l;
	  Some(!accu)
      |	Some(def_list1), None ->
	  let accu = ref def_list1 in
	  Terms.get_deflist_subterms accu a;
	  Some(!accu)

and not_found_repl_index_t ri t =
  match t.t_desc with
    Var(_,l) | FunApp(_,l) -> not_found_repl_index_l ri l
  | ReplIndex i -> 
      if List.memq i ri then Some [] else None
  | _ -> Parsing_helper.internal_error "This term should not occur in def_list, in Transf_simplify.not_found_repl_index_t"
      
(* [not_found_repl_index_br accu ri def_list] adds to [accu]
   the largest sub-array-references in [def_list] that do not contain 
   replication indices in [ri]. *)

let not_found_repl_index_br accu ri (b,l) =
  match not_found_repl_index_l ri l with
    Some(def_list) -> List.iter (fun br -> Terms.add_binderref br accu) def_list
  | None -> Terms.add_binderref (b,l) accu 

(* [filter_deflist_indices bl def_list] removes from [def_list] all
   elements that refer to replication indices in [bl].
   Used when we know that the indices in [bl] are in fact not used. *)

let filter_deflist_indices bl def_list =
  let ri = List.map snd bl in
  let accu = ref [] in
  List.iter (not_found_repl_index_br accu ri) def_list;
  !accu
  
