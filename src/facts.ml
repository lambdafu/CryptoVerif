open Types

let filter_ifletfindres l =
  List.filter Terms.check_simple_term l

let true_facts_from_simp_facts (subst, facts, else_find) =
  subst @ facts 

(* Display facts; for debugging *)

let display_elsefind (bl, def_list, t) =
    Display.print_string "for all ";
    Display.display_list Display.display_repl_index bl;
    Display.print_string "; not(defined(";
    Display.display_list (fun (b,l) -> Display.display_var b l) def_list;
    Display.print_string ") && ";
    Display.display_term t;
    Display.print_string ")";
    Display.print_newline()

let display_facts (subst2, facts, elsefind) =
  Display.print_string "Substitutions:\n";
  List.iter (fun t -> Display.display_term t; Display.print_newline()) subst2;
  Display.print_string "Facts:\n";
  List.iter (fun t -> Display.display_term t; Display.print_newline()) facts;
  Display.print_string "Elsefind:\n";
  List.iter display_elsefind elsefind

(* Invariants on [simp_facts]

simp_facts = (subst, facts, elsefind)
subst is a list of rewrite rules t1 -> t2 such that
   * when t1/t2 are variables Var/ReplIndex, they are normalized by the
   other rewrite rules in subst
   * when t1/t2 are function applications FunApp, they are normalized only
   at the root by the other rewrite rules in subst.
   * only Var/ReplIndex/FunApp are allowed in terms in subst.
The reason for not fully normalizing all terms is that we do not want
to replace a variable with its value if it is not necessary for applying
a simplification (because it may make cryptographic primitives appear
at unwanted places, such as conditions of find, and at more occurrences
than needed). Hence, if we replace a variable with a function application,
we stop there, without replacing again other variables inside that function
application.
The rewrite rule t1 -> t2 is represented by an equality
t1 = t2 (where = is either Equal or LetEqual) in subst.
   * LetEqual is used for equalities that come from "let" declarations.
   In this case, t1 is a variable, t2 is its value, and the orientation
   can never be reversed.
   * Equal is used for other equalities.

facts is a list of other known facts

elsefind is a list of elsefind facts:
(bl, def_list, t) means forall bl, not(defined(def_list) && t) 


OLD COMMENTS:
   Apply on demand substitution when 
   - a matching for a reduction rule meets a variable when
   it expects a function symbol
   - unification called when we have an inequality meets a 
   different variable on both sides 
   - we have a variable in a boolean formula (x && ...), ...
   - equality between a variable and a variable or a tuple
   - let (...) = x[...] substitute x

Substitutions map variables x[...] to some term.
   ==> Now, they are rather rewrite rules, since they can map
   terms other than variables...

Difficulty = avoid loops; when should I stop applying substitutions
to avoid cycles? Do not reapply the same subtitution in a term
that comes from its image term, perhaps after transformation.
The difficulty is to follow what the term becomes during these
transformations.
Possible transformations are:
   - applying another substitution
   - applying a reduction rule, which does not change variables.
So keep a mapping (occ, M -> M') of forbidden substitutions,
and update it when applying a substitution. If this substitution
transforms N into N', and occ is in N then add (occ', M -> M')
for each occ' occurrence of a variable in N'.

*)

(* [equal_terms_normal simp_facts t1 t2] tests equality between terms
   in subst, which are normalized as follows:
   * when t1/t2 are variables Var/ReplIndex, they are normalized by the
   other rewrite rules in subst
   * when t1/t2 are function applications FunApp, they are normalized only
   at the root by the other rewrite rules in subst.
   * only Var/ReplIndex/FunApp are allowed in terms in subst.
  *)
    
let equal_terms_normal simp_facts t1 t2 =
  match t1.t_desc, t2.t_desc with
    (Var _ | ReplIndex _), (Var _ | ReplIndex _) ->
      (* Var/ReplIndex are fully normalized, I do not need to consider [simp_facts] *)
      Terms.equal_terms t1 t2
  | (Var _ | ReplIndex _), FunApp _
  | FunApp _, (Var _ | ReplIndex _) ->
      (* Terms are normalized at the root, so Var/ReplIndex cannot be equal to FunApp *)
      false
  | FunApp _, FunApp _ ->
      Terms.simp_equal_terms simp_facts false t1 t2
  | _ -> Parsing_helper.internal_error "terms in subst should be Var/FunApp/ReplIndex"
    
(* Create fresh replication indices *)

(* mapping from terms to fresh replication indices *)
let repl_index_list = ref []

let reset_repl_index_list() =
  repl_index_list := []
    
let new_repl_index_term t =
  let rec find_repl_index = function
      [] ->
	let b' = Terms.create_repl_index "i2" t.t_type in
	repl_index_list := (t,b') :: (!repl_index_list);
	b'
    | ((a,b')::l) ->
	if Terms.equal_terms a t then b' else
	find_repl_index l
  in
  find_repl_index (!repl_index_list)

let new_repl_index b = new_repl_index_term (Terms.term_from_repl_index b)

let replace_term_repl_index t =
  (* When t is already a replication index, leave it unchanged. 
     This is important because we obtain the initial term
     before replacement with replication indices by following
     ri_link once. If we performed the replacement several times
     for the same term, that would not work. *)
  match t.t_desc with
  | ReplIndex _ -> t
  | _ -> 
      let ri = new_repl_index_term t in
      ri.ri_link <- TLink t;
      Terms.term_from_repl_index ri
                 
let rec make_indep simp_facts ((b0,l0,depinfo,side_condition_needed) as bdepinfo) t =
  match t.t_desc with
  | FunApp(f,l) -> Terms.build_term2 t (FunApp(f, List.map (make_indep simp_facts bdepinfo) l))
  | ReplIndex(b) -> t
  | Var(b,l) ->
      (* reconstruct the initial term before replacing some indices with fresh indices *)
      let tinit = Terms.copy_term Terms.Links_RI t in
      if (List.exists (Terms.equal_terms tinit) depinfo.nodep) then
	t
      else if (b != b0 && Terms.is_restr b) ||
      ((not depinfo.other_variables) &&
       (not (List.exists (fun (b',_) -> b' == b) depinfo.dep)))
      then
	Terms.build_term2 t (Var(b, List.map (fun t' ->
	  try
	    make_indep simp_facts bdepinfo t'
	  with Not_found ->
	    replace_term_repl_index t') l))
      else if b == b0 then
	(* reconstruct the initial lists before replacing some indices with fresh indices *)
	let l0init = List.map (Terms.copy_term Terms.Links_RI) l0 in
	let linit = List.map (Terms.copy_term Terms.Links_RI) l in
	if List.for_all2 Terms.equal_terms l0init linit then
	  raise Not_found 
	else 
	  begin
	    let l' = 
	      List.map (fun t' ->
		try
		  make_indep simp_facts bdepinfo t'
		with Not_found ->
		  replace_term_repl_index t') l
	    in
	    side_condition_needed := true;
	    Terms.build_term2 t (Var(b, l'))
	  end
      else
        let t' = Terms.try_no_var simp_facts t in
        if Terms.equal_terms t t' then
	  raise Not_found
        else
          make_indep simp_facts bdepinfo t'
  | _ -> Parsing_helper.internal_error "If/let/find/new unexpected in make_indep"

let default_indep_test dep_info simp_facts t (b,l) =
  try
    let side_condition_needed = ref false in
    let t' = make_indep simp_facts (b,l,dep_info,side_condition_needed) t in
    Some (t', if !side_condition_needed then SideCondToCompute else NoSideCond)
  with Not_found ->
    None

(* [no_dependency_anal] is a particular dependency analysis that works
   without any dependency information, so it can be used as a default. *)

let nodepinfo =
  { args_at_creation_only = false;
    dep = [];
    other_variables = true;
    nodep = [] }
      
let no_dependency_anal = ((default_indep_test nodepinfo), (fun _ _ _ -> None))

(* [indep_test] and [collision_test] extract the 2 functions
   provided by a dependency analysis *)
    
let indep_test (dep_anal_indep_test, _) = dep_anal_indep_test
let collision_test (_, dep_anal_collision_test) = dep_anal_collision_test

(* [orient t1 t2] returns true when the equality t1 = t2
   can be oriented t1 -> t2. 
   One must not orient "t1 -> term that strictly contains t1",
   because that would immediately lead to a loop.
   Other than that, the choices are mostly heuristic.
   We try to make the content of variables explicit by orienting
   Var -> non-Var, except for variables that are large restrictions,
   because their content is defined by the restriction and we can
   use elimination of collisions when these variables are present.
   For terms that start with a function symbol, we prefer orienting
   in the direction that decreases the number of variables; if the
   number of variables is the same, we prefer the direction that 
   decreases the size.
   *)

let rec orient t1 t2 = 
  match t1.t_desc, t2.t_desc with
    (Var(b1,l1), Var(b2,l2)) when
    (not (Terms.refers_to b1 t2)) && (not (Terms.refers_to b2 t1)) &&
    (not (Terms.is_restr b1 && Terms.get_pcoll1_high b1.btype <= !Settings.tysize_MIN_Coll_Elim)) &&
    (not (Terms.is_restr b2 && Terms.get_pcoll1_high b2.btype <= !Settings.tysize_MIN_Coll_Elim)) ->
      (* Both orientations would be possible, try to discriminate using
         priorities *)
      b1.priority >= b2.priority
  | (Var(b,l), _) when
    (not (Terms.refers_to b t2)) && 
    (not (Terms.is_restr b && Terms.get_pcoll1_high b.btype <= !Settings.tysize_MIN_Coll_Elim)) -> true
  | (ReplIndex b1, ReplIndex b2) -> true
  | (Var(b1,l1), Var(b2,l2)) when b1 == b2 -> 
      List.for_all2 orient l1 l2
  | (FunApp(f1,l1), FunApp(f2,l2)) when f1 == f2 ->
      List.for_all2 orient l1 l2
  | (FunApp _, FunApp _) ->
      let v_t1 = Terms.count_var t1 in
      let v_t2 = Terms.count_var t2 in
      (v_t1 > v_t2) || ((v_t1 = v_t2) && (Terms.size t1 >= Terms.size t2))
  | _ -> false
    
let orient_eq t1 t2 =
  if orient t1 t2 then Some(t1,t2) else
  if orient t2 t1 then Some(t2,t1) else None

let prod_orient_eq eq_th l1 l2 =
  match eq_th with 
  | (ACUN(prod, _) | Group(prod, _, _) | CommutGroup(prod, _, _)) -> 
      let rec find_orient t2 seen = function
	  [] -> None
	| (t::l) ->
	    match t.t_desc with
	      Var _ -> 
	        (* We have product (List.rev seen) t l = t2.
		   So t = product (inv (product (List.rev seen))) t2 (inv (product l)). *)
		let t' = Terms.make_inv_prod eq_th seen t2 l in
		if orient t t' then
		  Some (t,t')
		else 
		  find_orient t2 (t::seen) l
	    | _ -> find_orient t2 (t::seen) l
      in
      begin
      match find_orient (Terms.make_prod prod l2) [] l1 with
	None -> find_orient (Terms.make_prod prod l1) [] l2
      |	x -> x
      end
  | _ -> Parsing_helper.internal_error "Expecting a group or xor theory in Facts.prod_orient_eq"

let prod_dep_anal eq_th dep_info simp_facts l1 l2 =
  match eq_th with 
  | (ACUN(prod, _) | Group(prod, _, _) | CommutGroup(prod, _, _)) -> 
      let rec find_orient t2 seen = function
	  [] -> None
	| (t::l) ->
	        (* We have product (List.rev seen) t l = t2.
		   So t = product (inv (product (List.rev seen))) t2 (inv (product l)). *)
	    let t' = Terms.make_inv_prod eq_th seen t2 l in
	    match collision_test dep_info simp_facts t t' with
	      None -> find_orient t2 (t::seen) l
	    | x -> x
      in
      begin
	match find_orient (Terms.make_prod prod l2) [] l1 with
	  None -> find_orient (Terms.make_prod prod l1) [] l2
	| x -> x
      end
  | _ -> Parsing_helper.internal_error "Expecting a group or xor theory in Facts.prod_dep_anal"

(* Apply reduction rules defined by statements to term t *)

(* [get_var_link]: [get_var_link t ()] returns [Some (link, allow_neut)]
   when [t] is variable that can be bound by a product of terms,
   [link] is the current contents of the link of that variable,
   [allow_neut] is true if and only if the variable may be bound to
   the neutral element (provided there is a neutral element for the
   product); it returns [None] otherwise. *)

let get_var_link restr t () = 
  match t.t_desc with
    FunApp _ -> None
  | Var(v,[]) -> 
      (* If v must be a random number, it can correspond only to 1 element of 
	 the matching list l2, so it can be handled like a FunApp term
	 by match_term. *)
      if List.memq v restr then None else Some (v.link, false (* TO DO I consider that v cannot be bound to the neutral element; it would be better to allow the user to set that *))
  | Var _ | ReplIndex _ | TestE _ | FindE _ | LetE _ | ResE _ | EventAbortE _
  | EventE _ | GetE _ | InsertE _ ->
      Parsing_helper.internal_error "Var with arguments, replication indices, if, find, let, new, get, insert, event, and event_abort should not occur in match_assoc"      

let rec match_term simp_facts restr next_f t t' () = 
  let get_var_link = get_var_link restr in
  let rec match_term_rec next_f t t' () =
    Terms.auto_cleanup (fun () -> 
      match t.t_desc with
	Var (v,[]) -> 
        (* Check that types match *)
	  if t'.t_type != v.btype then
	    raise NoMatch;
	  begin
	    match v.link with
	      NoLink -> 
		if List.memq v restr then
	      (* t' must be a variable created by a restriction *)
		  begin
		    if not (t'.t_type == v.btype) then
		      raise NoMatch;
		    match t'.t_desc with
		      Var(b,l) when Terms.is_restr b -> ()
		    | _ -> raise NoMatch
		  end;
		Terms.link v (TLink t')
	    | TLink t -> 
		if not (Terms.simp_equal_terms simp_facts true t t') then raise NoMatch
	  end;
	  next_f()
      | FunApp(f,l) ->
	  Match_eq.match_funapp match_term_rec get_var_link Match_eq.default_match_error simp_facts next_f t t' ()
      | Var _ | ReplIndex _ | TestE _ | FindE _ | LetE _ | ResE _
      | EventAbortE _ | EventE _ | GetE _ | InsertE _ ->
	  Parsing_helper.internal_error "Var with arguments, replication indices, if, find, let, new, get, insert, event, and event_abort should not occur in match_term"
	    )
  in
  match_term_rec next_f t t' ()

let match_term_root_or_prod_subterm simp_facts restr final next_f t t' =
  match t.t_desc with
    FunApp(f,[_;_]) when f.f_eq_theories != NoEq && f.f_eq_theories != Commut ->
      (* f is a binary function with an equational theory that is
	 not commutativity -> it is a product-like function *)
      let l = Terms.simp_prod simp_facts (ref false) f t in
      let l' = Terms.simp_prod simp_facts (ref false) f t' in
      begin
	match f.f_eq_theories with
	  NoEq | Commut -> Parsing_helper.internal_error "Facts.match_term_root_or_prod_subterm: cases NoEq, Commut should have been eliminated"
	| AssocCommut | AssocCommutN _ | CommutGroup _ | ACUN _ ->
	    Match_eq.match_AC (match_term simp_facts restr) (get_var_link restr) Match_eq.default_match_error (fun rest () -> 
	      final (Terms.make_prod f ((next_f())::rest))) simp_facts f true l l' ()
	| Assoc | AssocN _ | Group _ -> 
	    Match_eq.match_assoc_subterm (match_term simp_facts restr) (get_var_link restr) (fun rest_left rest_right () ->
	      final (Terms.make_prod f (rest_left @ (next_f())::rest_right))) simp_facts f l l' ()
      end
  | _ ->
      match_term simp_facts restr (fun () -> final (next_f())) t t' ()

let reduced = ref false

(* [apply_collisions_at_root_once reduce_rec simp_facts final t collisions] 
   applies all collisions in the list [collisions] to the root of term [t].
   It calls the function [final] on each term obtained by applying a collision.
   The function final may raise the exception [NoMatch] so that other 
   possibilities are considered.

   Statements are a particular case of collisions, so this function
   can also be applied with a list of statements in [collisions].

   [reduce_rec f t] must simplify the term [t] knowing the fact [f] 
   in addition to the already known facts. It sets the flag [reduced]
   when [t] has really been modified. *)

type sc_tree =
    SC_And of sc_tree * sc_tree
  | SC_Or of sc_tree * sc_tree
  | SC_Fixed of term list * term list list
  | SC_ToCompute of binder * binder
  | SC_True
  | SC_False

let make_indep_args dep_info simp_facts l brdep =
  List.map (fun t ->
    match indep_test dep_info simp_facts t brdep with
      Some(t', NoSideCond) -> t'
    | _ -> replace_term_repl_index t) l

let check_indep_restr dep_info simp_facts restr_may_be_equal false_redr b1 b2 =
  let (((b1',l1) as br1), t1) =
    match b1.link with
    | TLink ({ t_desc = Var(b,l) } as t) -> ((b,l),t)
    | _ -> Parsing_helper.internal_error "unexpected link in check_indep_restr (1)"
  in
  let (((b2',l2) as br2), t2) =
    match b2.link with
    | TLink ({ t_desc = Var(b,l) } as t) -> ((b,l),t)
    | _ -> Parsing_helper.internal_error "unexpected link in check_indep_restr (2)"
  in
  if (not restr_may_be_equal) && (b1' == b2') then
    begin
      if not false_redr then
	(* Cannot encode a side condition when the result of the reduction is not "false",
	   and when b1' == b2', we are going to have a side condition *)
	raise NoMatch;
      let l1init = List.map (Terms.copy_term Terms.Links_RI) l1 in
      let l2init = List.map (Terms.copy_term Terms.Links_RI) l2 in
      if List.for_all2 Terms.equal_terms l1init l2init then
	(* The restrictions are exactly the same, they cannot be independent *)
	raise NoMatch
    end;
  (* Make sure that the arguments of the restrictions b1' / b2' 
     are independent of each other *)
  let l1' = make_indep_args dep_info simp_facts l1 br2 in
  let l2' = make_indep_args dep_info simp_facts l2 br1 in
  b1.link <- TLink(Terms.build_term2 t1 (Var(b1', l1')));
  b2.link <- TLink(Terms.build_term2 t2 (Var(b2', l2')));
  (* Side condition: when b1' == b2', l1 must be different of l2 *)
  if (not restr_may_be_equal) && (b1' == b2') then
    SC_ToCompute(b1, b2)
  else
    SC_True

let indices_indep_self dep_info simp_facts b =
  let (((b',l) as br), t) =
    match b.link with
    | TLink ({ t_desc = Var(b,l) } as t) -> ((b,l),t)
    | _ -> Parsing_helper.internal_error "unexpected link in check_indep_restr (1)"
  in
  (* Make sure that the arguments of the restrictions b'
     are independent of b'[l] itself *)
  let l' = make_indep_args dep_info simp_facts l br in
  b.link <- TLink(Terms.build_term2 t (Var(b', l')))
      
let rec indep_sc_restr dep_info simp_facts restr_may_be_equal false_redr v = function
    [] -> SC_True
  | v'::l ->
      let sc = indep_sc_restr dep_info simp_facts restr_may_be_equal false_redr v l in
      SC_And (sc, check_indep_restr dep_info simp_facts restr_may_be_equal false_redr v v')
      
let rec indep_sc_restr_list dep_info simp_facts restr_may_be_equal false_redr = function
    [] -> SC_True
  | [v] -> SC_True
  | (v::l) ->
      SC_And (indep_sc_restr dep_info simp_facts restr_may_be_equal false_redr v l,
	      indep_sc_restr_list dep_info simp_facts restr_may_be_equal false_redr l)

      
let rec check_indep_cond dep_info simp_facts false_redr = function
  | IC_Indep(b1, b2) ->
      begin
        (* b1 must be independent of b2 *)
	let t1 = 
	  match b1.link with
	    TLink t -> t
	  | _ -> Parsing_helper.internal_error "unexpected link in apply_red (2)"
	in
	let (b,l) as br2 =
	  match b2.link with
	    TLink { t_desc = Var(b,l) } -> (b,l)
	  | _ -> Parsing_helper.internal_error "unexpected link in apply_red (3)"
	in
	match indep_test dep_info simp_facts t1 br2 with
	| None ->
            (* Display.display_term t1; print_string " depends on "; Display.display_var b l;
	       print_newline(); *)
            SC_False (* t1 may depend on br2; cannot apply the collision *)
	| Some (t1', side_condition) ->
	    if (side_condition != NoSideCond) && not false_redr then
              begin
	        (* Cannot encode a side condition when the result of the reduction is not "false" *)
                (* print_string " indep cond side condition not supported\n"; *)
		SC_False
              end
	    else
	      begin
                (* t1 may be transformed into a term t1' that is independent of br2
		   Store it in the link for b1
		   Note that in case there are several independence conditions
		   on the same variable [b1], the linked term may be rewritten several
		   times. This is why we compute the side conditions after all calls
		   to [indep_test]. *)
		b1.link <- TLink t1';
		match side_condition with
		  NoSideCond -> SC_True
		| SideCondToCompute -> SC_ToCompute(b1, b2)
		| SideCondFixed(l, ll) -> SC_Fixed(l, ll)
	      end
      end
  | IC_True ->
      SC_True
  | IC_And(c1,c2) ->
      begin
	let res1 = check_indep_cond dep_info simp_facts false_redr c1 in
	let res2 = check_indep_cond dep_info simp_facts false_redr c2 in
	match res1, res2 with
	  SC_False, _ | _, SC_False -> SC_False
	| SC_True, _ -> res2
	| _, SC_True -> res1
	| _ ->
	    SC_And(res1, res2)
      end
  | IC_Or(c1, c2) ->
      begin
	let res1 = check_indep_cond dep_info simp_facts false_redr c1 in
	let res2 = check_indep_cond dep_info simp_facts false_redr c2 in
	match res1, res2 with
	| SC_True, _ | _, SC_True -> SC_True
	| SC_False, _ -> res2
	| _, SC_False -> res1
	| _ -> 
	    SC_Or(res1, res2)
      end

let rec compute_and l1 = function
    [] -> []
  | e2::l2 ->
      (List.map (fun e1 -> Terms.make_and e1 e2) l1) @ (compute_and l1 l2)

let rec collect_bargs b accu t =
  match t.t_desc with
    FunApp(f, l) ->
      List.iter (collect_bargs b accu) l
  | Var(b', l) ->
      if (b == b') && not (List.exists (List.for_all2 Terms.equal_terms l) (!accu)) then
	accu := l :: (!accu)
  | ReplIndex _ -> ()
  | _ -> Parsing_helper.internal_error "If/let/find/new unexpected in collect_bargs"
							 
let rec make_side_cond = function
    SC_True -> ([], Terms.make_true())
  | SC_False ->
      Parsing_helper.internal_error "false side condition should have been removed"
  | SC_And(c1, c2) ->
      let c1t, c1p = make_side_cond c1 in
      let c2t, c2p = make_side_cond c2 in
      (c1t @ c2t, Terms.make_and c1p c2p)
  | SC_Or(c1, c2) ->
      let c1t, c1p = make_side_cond c1 in
      let c2t, c2p = make_side_cond c2 in
      (compute_and c1t c2t, Terms.make_or c1p c2p)
  | SC_Fixed(l, bargs) ->
      let side_condition_proba = 
	Terms.make_and_list (List.map (fun l' ->
	  Terms.make_or_list (List.map2 Terms.make_diff l l')
	    ) bargs)
      in
      let side_condition_term = List.map (fun l' -> 
	Terms.make_and_list (List.map2 Terms.make_equal l l')
	  ) bargs
      in
      (side_condition_term, side_condition_proba)
  | SC_ToCompute(b1, b2) ->
      let t1 = 
	match b1.link with
	  TLink t -> t
	| _ -> Parsing_helper.internal_error "unexpected link in apply_red (2)"
      in
      let (b,l) as br2 =
	match b2.link with
	  TLink { t_desc = Var(b,l) } -> (b,l)
	| _ -> Parsing_helper.internal_error "unexpected link in apply_red (3)"
      in
      let args = ref [] in
      collect_bargs b args t1;
      let bargs = !args in
      let side_condition_proba = 
	Terms.make_and_list (List.map (fun l' ->
	  Terms.make_or_list (List.map2 Terms.make_diff l l')
	    ) bargs)
      in
      let init_l = List.map (Terms.copy_term Terms.Links_RI) l in
      let side_condition_term = List.map (fun l' ->
	let init_l' = List.map (Terms.copy_term Terms.Links_RI) l' in
	Terms.make_and_list (List.map2 Terms.make_equal init_l init_l')
	  ) bargs
      in
      (side_condition_term, side_condition_proba)
      
let rec build_indep_map = function
    IC_Indep(b1,b2) ->
      begin
	match b1.link with
	  TLink t -> [(b1,t)]
	| _ -> Parsing_helper.internal_error "unexpected link in apply_red (2)"
      end
  | IC_And(c1, c2) | IC_Or(c1, c2) ->
      (build_indep_map c1) @ (build_indep_map c2)
  | IC_True -> []

let restore_all_links state =
  match !state with
  | None -> ()
  | Some (links, old_current_bound_vars) ->
      assert (!Terms.current_bound_vars == []);
      Terms.current_bound_vars := old_current_bound_vars;
      List.iter (fun (b, t) ->
	b.link <- TLink t) links;
      (* We will not restore the same state again *)
      state := None
      
let cleanup_store_all_links vars next_f =
  let links = List.map (fun b ->
    match b.link with
    | NoLink -> Parsing_helper.internal_error "all variables should be linked in cleanup_store_all_links"
    | TLink t -> b.link <- NoLink; (b, t)) vars
  in
  let old_current_bound_vars = !Terms.current_bound_vars in
  Terms.current_bound_vars := [];
  let state = ref (Some (links, old_current_bound_vars)) in
  try
    next_f state
  with NoMatch ->
    restore_all_links state;
    raise NoMatch
	
let rec apply_collisions_at_root_once reduce_rec dep_info simp_facts final t = function
    [] -> raise NoMatch
  | (restr, forall, redl, proba, redr, indep_cond, side_cond, restr_may_be_equal)::other_coll ->
      try
	match_term_root_or_prod_subterm simp_facts restr final (fun () ->
	  (* Compute the side condition that guarantees that all restrictions are independent,
	     if not [restr_may_be_equal]. Make sure that the indices of restrictions are
	     independent of all restrictions *)
	  List.iter (indices_indep_self dep_info simp_facts) restr;
	  let false_redr = Terms.is_false redr in
	  let sc_indep_restr = indep_sc_restr_list dep_info simp_facts restr_may_be_equal false_redr restr in
	  let (side_condition_term, side_condition_proba) =
	    make_side_cond sc_indep_restr
	  in
	  let sc_term = ref side_condition_term in
	  let sc_proba = ref side_condition_proba in
	  (* check side condition [side_cond] *)
	  if not (Terms.is_true side_cond) then
	    begin
	      let side_cond' = Terms.copy_term Terms.Links_Vars side_cond in
	      if not (Terms.is_true (Terms.apply_eq_reds simp_facts (ref false) side_cond' )) then
		raise NoMatch;
	      sc_proba := Terms.make_and side_cond' (!sc_proba)
	    end;
	  (* reduced term *)
	  let t' = Terms.copy_term Terms.Links_RI
	      (Terms.copy_term Terms.Links_Vars redr)
	  in
          (* print_string "apply_collisions_at_root_once match succeeded\n";
          print_string "at "; print_int t.t_occ; print_string ", ";
          Display.display_term t; print_string " matches ";
          Display.display_term redl;
	  print_string " reduces into ";
	  let redr' = Terms.copy_term Terms.Links_Vars redr in
	  Display.display_term redr';
	  print_string " instantiated ";
	  Display.display_term t';
	  print_newline(); *)
	  (* There is one instance of the collision problem for each value of
	     the variables in [restr_indep_map] i.e. restrictions and 
	     variables with independence conditions. The number of values
	     of other variables does not matter: the adversary breaks the
	     collision problem when it finds values of other variables such 
	     that [redl <> redr and side_cond]. it can make as many attempts
	     as he wishes and can test by himself whether his attempt succeeds.
	     *)
	  let restr_indep_map =
	    (build_indep_map indep_cond) @
	    (List.map (fun restr1 ->
	      match restr1.link with
		TLink trestr -> (restr1,trestr)
	      | _ -> Parsing_helper.internal_error "unexpected link in apply_red (1)"
		    ) restr)
	  in
	  (* Check independence conditions *)
	  begin
	    match check_indep_cond dep_info simp_facts false_redr indep_cond with
	      SC_False ->
		raise NoMatch (* independence conditions not satisfied *)
	    | sc ->
		let (side_condition_term, side_condition_proba) =
		  make_side_cond sc
		in
		sc_term := side_condition_term @ (!sc_term);
		sc_proba := Terms.make_and side_condition_proba (!sc_proba)
	  end;
	  (* [redl'] is the instantiated version of [redl], using terms
	     made independent as needed to apply the collision.
	     Same for [redr']. That allows taking the replication indices
	     introduced by [indep_test dep_info] into account in the probability
	     computation. *)
	  let redl' = Terms.copy_term Terms.Links_Vars redl in
	  let redr' = Terms.copy_term Terms.Links_Vars redr in
	  (* Cleanup early enough, so that the links that we create in this 
	     collision do not risk to interfere with a later application of 
	     the same collision in reduce_rec.
	     Cleanup all links in [restr] and [forall], to be able to reuse the
	     collision without interference. Some of those links may have been
	     set above a [Terms.auto_cleanup] in [match_term], so it is
	     not enough to cleanup using [Terms.cleanup()].
	     Store the links to be able to restore them in case of subsequent
	     failure (exception [NoMatch]) and before calling
	     [Proba.add_proba_red] so that the lengths are correctly 
	     instantiated in that function. *)
	  cleanup_store_all_links (restr @ forall) (fun link_state ->
	    let t'' =
	      if (!sc_term) == [] then
	        (* No side condition, nothing to add *)
		t' 
	      else
		begin
		  if not (Terms.is_false redr) then
	            (* I can test conditions that make restrictions independent only
		       when the result "redr" is false *)
		    raise NoMatch;
	            (* When redr is false, the result "If restrictions
		       independent then redr else t" is equal to
		       "(restrictions not independent) and t" which we
		       simplify.  We keep the transformed value only
		       when t has been reduced, because otherwise we
		       might enter a loop (applying the collision to t
		       over and over again). *)
		  Terms.make_or_list 
		    (List.map (fun f ->
		      let reduced_tmp = !reduced in
		      reduced := false;
		      try 
			let t1 = reduce_rec f t in
			if not (!reduced) then 
			  begin 
			    reduced := reduced_tmp;
                            (* print_string "Could not simplify "; Display.display_term t; print_string " knowing ";
			       Display.display_term f; print_newline(); *)
			    raise NoMatch 
			  end;
			reduced := reduced_tmp;
			Terms.make_and f t1
		      with Contradiction ->
		        (* [reduce_rec] may raise a contradiction when [f] can in fact not be true *)
			Terms.make_false()
			  ) (!sc_term))
		end
	    in
	    if proba != Zero then
	      begin
                (* Instead of storing the term t, I store the term obtained 
                   after the applications of try_no_var in match_term,
                   obtained by (Terms.copy_term redl)
		   
		   We pass the side condition [sc_proba] for probability
		   counting. Several collisions with different [sc_proba]
		   need to be counted several times.  *)
		restore_all_links link_state;
		if not (Proba.add_proba_red redl' redr' (!sc_proba) proba restr_indep_map) then
                  begin
                    (* print_string "Proba too large"; *)
		    raise NoMatch
                  end
	      end;
	    t'')
	    ) redl t
      with NoMatch ->
	Terms.cleanup();
	apply_collisions_at_root_once reduce_rec dep_info simp_facts final t other_coll

let reduce_rec_impossible t = assert false

let apply_statements_at_root_once simp_facts t =
  match t.t_desc with
    FunApp(f,_) ->
      begin
	try 
	  apply_collisions_at_root_once reduce_rec_impossible no_dependency_anal simp_facts (fun t' -> reduced := true; t') t f.f_statements 
	with NoMatch -> t
      end
  | _ -> t

let apply_statements_and_collisions_at_root_once reduce_rec dep_info simp_facts t =
  match t.t_desc with
    FunApp(f,_) ->
      begin
	try 
	  apply_collisions_at_root_once reduce_rec_impossible no_dependency_anal simp_facts (fun t' -> reduced := true; t') t f.f_statements 
	with NoMatch ->
	  try 
	    apply_collisions_at_root_once reduce_rec dep_info simp_facts (fun t' -> reduced := true; t') t f.f_collisions 
	  with NoMatch -> t
      end
  | _ -> t

(* [apply_simplif_subterms_once simplif_root_or_prod_subterm simp_facts t] 
   applies the simplification specified by [simplif_root_or_prod_subterm] 
   to all subterms of [t].

   [simplif_root_or_prod_subterm: term -> term] should simplify only the root
   of the term, or when the term is a product, simplify subproducts,
   but not smaller subterms. When the simplification succeeds, it sets [reduced]
   to true and returns the simplified term. When the simplification fails,
   it returns the initial term and leaves [reduced] unchanged. *)

let rec first_inv inv = function
    [] -> ([], [])
  | (a::l) as x -> 
      match a.t_desc with
	FunApp(f,[t]) when f == inv -> 
	  let (invl, rest) = first_inv inv l in
	  (t::invl, rest)
      |	_ -> 
	  ([], x)

let apply_simplif_subterms_once simplif_root_or_prod_subterm simp_facts t = 
  let rec simplif_rec t =
  match t.t_desc with
    FunApp(f, [_;_]) when f.f_eq_theories != NoEq && f.f_eq_theories != Commut ->
      (* f is a binary function with an equational theory that is
	 not commutativity -> it is a product-like function *)
      let t' = simplif_root_or_prod_subterm t in
      if !reduced then t' else 
      (* We apply the statements only to subterms that are not products by f.
	 Subterms that are products by f are already handled above
	 using [match_term_root_or_prod_subterm]. *)
      let l = Terms.simp_prod simp_facts (ref false) f t in
      Terms.make_prod f (List.map simplif_rec l)
  | FunApp(f, ([t1;t2] as l)) when f.f_cat == Equal || f.f_cat == Diff ->
      let t' = simplif_root_or_prod_subterm t in
      if !reduced then t' else 
      begin
	match Terms.get_prod_list (Terms.try_no_var simp_facts) l with
	  ACUN(xor, neut) ->
	    let t' = Terms.app xor [t1;t2] in
	    let t'' = simplif_rec t' in
	    if !reduced then 
	      begin
		match t''.t_desc with
		  FunApp(xor', [t1';t2']) when xor' == xor ->
		    Terms.build_term2 t (FunApp(f, [t1';t2']))
		| _ -> 
		    Terms.build_term2 t (FunApp(f, [t'';Terms.app neut []]))
	      end
	    else
	      t
	| CommutGroup(prod, inv, neut) -> 
	    let rebuild_term t'' = 
	      (* returns a term equal to [f(t'', neut)] *)
	      let l = Terms.simp_prod simp_facts (ref false) prod t'' in
	      let linv, lno_inv = List.partition (Terms.is_fun inv) l in
	      let linv_removed = List.map (function { t_desc = FunApp(f,[t]) } when f == inv -> t | _ -> assert false) linv in
	      Terms.build_term2 t (FunApp(f, [ Terms.make_prod prod lno_inv; 
					       Terms.make_prod prod linv_removed ]))
	    in	      
	    let t' = Terms.app prod [t1; Terms.app inv [t2]] in
	    let t'' = simplif_rec t' in
	    if !reduced then
	      rebuild_term t''
	    else
	      let t' = Terms.app prod [t2; Terms.app inv [t1]] in
	      (* No need to try subterms of t' inside elements of the product,
		 since they have already been tried above *)
	      let t'' = simplif_root_or_prod_subterm t' in
	      if !reduced then
		rebuild_term t''
	      else
		t
	| Group(prod, inv, neut) ->
	    let rebuild_term t'' =
	      (* returns a term equal to [f(t'', neut)] *)
	      let l = Terms.simp_prod simp_facts (ref false) prod t'' in
	      let (inv_first, rest) = first_inv inv l in
	      let (inv_last_rev, rest_rev) = first_inv inv (List.rev rest) in
		(* if inv_first = [x1...xk], inv_last_rev = [y1...yl],
		   List.rev rest_rev = [z1...zm]
		   then the term we want to rewrite is
		   x1^-1...xk^-1.z1...zm.yl^-1...y1^-1 = neut
		   which is equal to
		   z1...zm = xk...x1.y1...yl *)
	      Terms.build_term2 t (FunApp(f, [ Terms.make_prod prod (List.rev rest_rev) ; 
					       Terms.make_prod prod (List.rev_append inv_first inv_last_rev)]))
	    in
	    let l1 = Terms.simp_prod simp_facts (ref false) prod (Terms.app prod [t1; Terms.app inv [t2]]) in
	    let l2 = Terms.remove_inverse_ends simp_facts (ref false) (prod, inv, neut) l1 in
	    let rec apply_up_to_roll seen' rest' =
	      let t0 = (Terms.make_prod prod (rest' @ (List.rev seen'))) in
	      let t'' = simplif_root_or_prod_subterm t0 in
	      if !reduced then
		rebuild_term t''
	      else
		match rest' with
		  [] -> t
		| a::rest'' -> apply_up_to_roll (a::seen') rest''
	    in
	    let t' = apply_up_to_roll [] l2 in
	    if !reduced then t' else
	    let l3 = List.rev (List.map (Terms.compute_inv (Terms.try_no_var simp_facts) (ref false) (prod, inv, neut)) l2) in
	    let t' = apply_up_to_roll [] l3 in
	    if !reduced then t' else
	    let l1 = Terms.simp_prod simp_facts (ref false) prod t1 in
	    let l2 = Terms.simp_prod simp_facts (ref false) prod t2 in
	    Terms.build_term2 t (FunApp(f, [ Terms.make_prod prod (List.map simplif_rec l1);
					     Terms.make_prod prod (List.map simplif_rec l2) ]))
	| _ -> 
	    Terms.build_term2 t (FunApp(f, List.map simplif_rec l))
      end
  | FunApp(f, l) ->
      let t' = simplif_root_or_prod_subterm t in
      if !reduced then t' else 
      Terms.build_term2 t (FunApp(f, List.map simplif_rec l))
	(* [simplif_rec] always leaves variables unchanged.
	   So if [f] is [LetEqual], its first argument is a variable before
	   simplification and remains a variable after. *)
  | _ -> t
  in
  simplif_rec t

(* For debugging: replace Terms.apply_eq_reds with apply_eq_reds below.

let apply_eq_reds simp_facts reduced t =
  let t' = Terms.apply_eq_reds simp_facts reduced t in
  if !reduced then
    begin
      print_string "apply_eq_reds ";
      Display.display_term t;
      print_string " = ";
      Display.display_term t';
      print_newline()
    end;
  t'
*)

(* [apply_eq_statements_subterms_once simp_facts t] applies the equalities 
   coming from the equational theories and the equality
   statements given in the input file to all subterms of [t]. *)

let apply_eq_statements_subterms_once simp_facts t =
  let t' = Terms.apply_eq_reds simp_facts reduced t in
  if !reduced then t' else 
  apply_simplif_subterms_once (apply_statements_at_root_once simp_facts) simp_facts t

(* [apply_eq_statements_and_collisions_subterms_once reduce_rec simp_facts t] 
   applies the equalities coming from the equational theories, 
   the equality statements, and the collisions given in the input 
   file to all subterms of [t]. *)

let apply_eq_statements_and_collisions_subterms_once reduce_rec dep_info simp_facts t =
  let t' = Terms.apply_eq_reds simp_facts reduced t in
  if !reduced then t' else 
  apply_simplif_subterms_once (apply_statements_and_collisions_at_root_once reduce_rec dep_info simp_facts) simp_facts t

(* For debugging 
let apply_eq_statements_and_collisions_subterms_once reduce_rec simp_facts t =
  let t' = apply_eq_statements_and_collisions_subterms_once reduce_rec simp_facts t in
  if !reduced then
    begin
      print_string "apply_eq_statements_and_collisions_subterms_once ";
      Display.display_term t;
      print_string " = ";
      Display.display_term t';
      print_newline()
    end;
  t'
*)

(* Applying a substitution that maps x[M1,...,Mn] to M' *)

let reduced_subst = ref false

let try_no_var = Terms.try_no_var
let normalize = Terms.normalize

let is_identity link =
  match link.t_desc with
    FunApp(f, [t;t']) when f.f_cat == Equal || f.f_cat == LetEqual ->
      Terms.equal_terms t t'
  | _ -> false

let rec apply_subst1 simp_facts t tsubst =
  match tsubst.t_desc with
    FunApp(f,[redl;redr]) when f.f_cat == Equal || f.f_cat == LetEqual ->
      begin
	match t.t_desc with
	  FunApp _ -> 
	    begin
	      (* When we apply the substitution to a FunApp term, we do not apply
		 it recursively to its subterms, to avoid getting more function
		 symbols than the minimum. 
		 However, we may apply other substitutions to subterms, to make it
		 possible to apply tsubst at the root. This is done by
		 [Terms.simp_equal_terms simp_facts false t redl].

		 It is important that [Terms.simp_equal_terms] never sets [reduced_subst].
		 Otherwise, [apply_subst1] might set [reduced_subst] inside the call
		 to [Terms.simp_equal_terms simp_facts false t redl], even though the
		 equality is false, so the caller of [apply_subst1] would wrongly
		 think that the term has been modified.
		*)
              if Terms.simp_equal_terms simp_facts false t redl then 
		begin
		  reduced_subst := true;
		  redr
		end
              else
		t
            end
	| _ ->
           if Terms.equal_terms t redl then 
	     begin
	       reduced_subst := true;
	       redr
	     end
           else
             match t.t_desc with
               Var(b,l) ->
	         Terms.build_term2 t (Var(b, List.map (fun t' -> apply_subst1 simp_facts t' tsubst) l))
(*    
             | FunApp(f,l) ->
	         Terms.build_term2 t (FunApp(f, List.map (fun t' -> apply_subst1 simp_facts t' tsubst) l))
*)
             | _ -> t
      end
  | _ -> Parsing_helper.internal_error "substitutions should be Equal or LetEqual terms"

(* [apply_reds simp_facts t] applies all equalities coming from the
   equational theories, equality statements, and collisions given in
   the input file to all subterms of the term [t], taking into account
   the equalities in [simp_facts] to enable their application.
   Application is repeated until a fixpoint is reached. *)

let rec apply_reds depth dep_info simp_facts t =
  reduced := false;
  let t' = apply_eq_statements_and_collisions_subterms_once (reduce_rec depth simp_facts) dep_info simp_facts t in
  if !reduced then 
    apply_reds (depth+1) dep_info simp_facts t' 
  else
    t

(* [apply_sub1 simp_facts t link] tries to reduce the term [t]
   using the rewrite rule [link]. 
   It uses [simp_facts] to transform functional subterms of [t]
   to apply the rewrite rule [link]. When the reduction succeeds,
   it returns (true, reduced_term); otherwise, it returns (false, t). *)

and apply_sub1 simp_facts t link = 
  reduced_subst := false;
  let t1 = apply_subst1 simp_facts t link in
  (!reduced_subst, t1)

and apply_sub_list simp_facts t = function
    [] -> (false, t)
  | link::rest ->
      let (reduced, t1) = apply_sub1 simp_facts t link in
      if reduced then
	(reduced, t1)
      else
	apply_sub_list simp_facts t rest
    
(* [apply_eq_st_coll1 simp_facts t] applies all equalities coming from the
   equational theories, equality statements, and collisions given in
   the input file to all subterms of the term [t], taking into account
   the equalities in [simp_facts] to enable their application.
   At most one reduction is done. When the reduction succeeds,
   it returns (true, reduced_term); otherwise, it returns (false, t). *)

and apply_eq_st_coll1 depth dep_info simp_facts t =
  match t.t_desc with
    Var _ | ReplIndex _ ->
      (false, t)
  | FunApp _ ->
      reduced := false;
      let t' = apply_eq_statements_and_collisions_subterms_once (reduce_rec depth simp_facts) dep_info simp_facts t in
      (!reduced, t')
  | _ -> Parsing_helper.internal_error "If/let/find/new not allowed in apply_eq_st_coll1"

(* [apply_root_st_coll1 simp_facts t] applies all equalities coming from the
   equality statements and collisions given in
   the input file to the root of the term [t], taking into account
   the equalities in [simp_facts] to enable their application.
   At most one reduction is done. When the reduction succeeds,
   it returns (true, reduced_term); otherwise, it returns (false, t).

   It is applied only to equalities [t] in [subst_simplify2], so we do not need to check 
   that [t] in [FunApp...]. 
   TO DO For now, we do not use [Terms.apply_eq_reds] because this function
   does not reduce only the root. It may be good to have a function for reducing
   only the root. *)
	
and apply_root_st_coll1 depth dep_info simp_facts t =
  reduced := false;
  let t' = apply_statements_and_collisions_at_root_once (reduce_rec depth simp_facts) dep_info simp_facts t in
  (!reduced, t')
	
(* [reduce_rec simp_facts f t] simplifies the term [t] knowing the fact [f] 
   in addition to the already known facts [simp_facts]. It sets the flag [reduced]
   when [t] has really been modified. *)

and reduce_rec depth simp_facts f t = 
  Terms.auto_cleanup (fun () ->
    let simp_facts' = simplif_add (depth+1) no_dependency_anal simp_facts f in
    apply_eq_statements_subterms_once simp_facts' t)   

(* Replaces each occurence of t in fact with true *)
and replace_with_true modified simp_facts t fact =
  if (fact.t_type = Settings.t_bool) && (not (Terms.is_true fact)) &&
    (if !Settings.simplify_use_equalities_in_simplifying_facts then
      (* This is more precise than Terms.equal_terms t fact,
         but too slow to activate in general *)
      Terms.simp_equal_terms simp_facts true t fact
    else
      Terms.equal_terms t fact) then
    begin
      modified := true;
      Terms.make_true ()
    end
  else
    Terms.build_term2 fact 
      (match fact.t_desc with
      | Var (b,tl) -> Var (b,tl)
      | FunApp(f, [t1;t2]) when f.f_cat == LetEqual ->
	  (* Make sure that the left-hand side of LetEqual is not replaced:
	     it must remain a variable. *)
	  FunApp(f, [t1; replace_with_true modified simp_facts t t2])
      | FunApp (f, l) -> FunApp (f, List.map (replace_with_true modified simp_facts t) l)
      | ReplIndex b -> ReplIndex b
      | _ ->
	  Parsing_helper.internal_error "Only Var, FunApp, ReplIndex should occur in facts in replace_with_true")
      (* ReplIndex can occur here because replication indices can occur as arguments of functions in events *)
	  
(* Simplify existing facts by knowing that the new term t is true, and then simplify the term t by knowing the facts are true *)
and simplify_facts depth dep_info (subst2,facts,elsefind) t =
  let simp_facts = (subst2, [], elsefind) in 
  let mod_facts = ref [] in
  let not_mod_facts = ref [] in
  List.iter
    (fun t' -> 
      let m = ref false in
      let t''=replace_with_true m simp_facts t t' in
      if !m then 
	mod_facts := t'' :: (!mod_facts)
      else
	not_mod_facts := t'' :: (!not_mod_facts)
    )
    facts;
  let m = ref false in
  let t' = List.fold_left (fun nt f -> replace_with_true m simp_facts f nt) t ((!mod_facts)@(!not_mod_facts)) in
  (* not(true) is not simplified in add_fact, simplify it here *)
  let t' = 
    if !m then 
      apply_reds depth dep_info (subst2,(!not_mod_facts),elsefind) t'
    else
      t'
  in  
  t',simplif_add_list depth dep_info (subst2,(!not_mod_facts),elsefind) (!mod_facts) 

(* Add a fact to a set of true facts, and simplify it *)

and add_fact depth dep_info simp_facts fact =
  if (!Settings.max_depth_add_fact > 0) && (depth > !Settings.max_depth_add_fact) then 
    begin
      (*if (!Settings.debug_simplif_add_facts) then*)
	begin
	  print_string "Adding "; Display.display_term fact; print_string " stopped because too deep."; print_newline()
	end;
      simp_facts 
    end
  else
    begin
  if (!Settings.debug_simplif_add_facts) then
    begin
      print_string "Adding "; Display.display_term fact; print_newline()
    end;
  let fact' = try_no_var simp_facts fact in
  let fact',simp_facts = simplify_facts (depth+1) dep_info simp_facts fact' in
  let (subst2,facts,elsefind)=simp_facts in
  match fact'.t_desc with
    FunApp(f,[t1;t2]) when f.f_cat == LetEqual ->
      begin
	match t1.t_desc with
	  Var(b,l) -> 
	    let t1' = Terms.build_term2 t1 (Var(b, List.map (try_no_var simp_facts) l))
	    in
	    let t2' = normalize simp_facts t2 in
	    let rec try_red_t1 = function
		[] -> (* Could not reduce t1' *)
		  subst_simplify2 (depth+1) dep_info simp_facts (Terms.make_let_equal t1' t2')
	      | { t_desc = FunApp(f'',[t1'';t2''])}::l when f''.f_cat == LetEqual ->
		  if Terms.equal_terms t1'' t1' then 
		    simplif_add (depth+1) dep_info simp_facts (Terms.make_equal t2' t2'')
		  else
		    try_red_t1 l
	      | _::l -> try_red_t1 l
	    in
	    try_red_t1 subst2
	| _ ->
	    Display.display_term fact;
	    print_string " reduced into ";
	    Display.display_term fact';
	    Parsing_helper.internal_error "LetEqual terms should have a variable in the left-hand side"
      end
  | FunApp(f,[t1;t2]) when f.f_cat == Equal ->
      let t1' = normalize simp_facts t1 in
      let t2' = normalize simp_facts t2 in
      begin
	match 
	  (match Terms.get_prod Terms.try_no_var_id t1' with 
	    NoEq -> Terms.get_prod Terms.try_no_var_id t2'
	  | x -> x)
          (* try_no_var has always been applied to t1' and t2' before, 
	     so I don't need to reapply it, I can use the identity instead *)
	with
	  NoEq ->
	    begin
	      match (t1'.t_desc, t2'.t_desc) with
		(FunApp(f1,l1), FunApp(f2,l2)) when
		f1.f_cat == Tuple && f2.f_cat == Tuple && f1 != f2 -> 
		  raise Contradiction
	      | (FunApp(f1,l1), FunApp(f2,l2)) when
		(f1.f_options land Settings.fopt_COMPOS) != 0 && f1 == f2 -> 
		  simplif_add_list (depth+1) dep_info simp_facts (List.map2 Terms.make_equal l1 l2)
	      | (Var(b1,l1), Var(b2,l2)) when
		(Terms.is_restr b1) &&
		(Proba.is_large_term t1'  || Proba.is_large_term t2') && (b1 == b2) &&
		(Proba.add_elim_collisions b1 b1) ->
		  simplif_add_list (depth+1) dep_info simp_facts (List.map2 Terms.make_equal l1 l2)
	      | (Var(b1,l1), Var(b2,l2)) when
		(Terms.is_restr b1) && (Terms.is_restr b2) &&
		(Proba.is_large_term t1' || Proba.is_large_term t2') &&
		(b1 != b2) && (Proba.add_elim_collisions b1 b2)->
		  raise Contradiction
	      | (FunApp(f1,[]), FunApp(f2,[]) ) when
		f1 != f2 && (!Settings.diff_constants) ->
		  raise Contradiction
	          (* Different constants are different *)
              | (_, _) ->
		  let default_add() =
		      match orient_eq t1' t2' with
			Some(t1'',t2'') -> 
			  subst_simplify2 (depth+1) dep_info simp_facts (Terms.make_equal t1'' t2'')
		      | None ->
			  (subst2, fact'::facts, elsefind)
		  in		    
		  match collision_test dep_info simp_facts t1' t2' with
		    Some t' ->
		      if Terms.is_false t' then
			raise Contradiction
		      else
			begin
			(* collision_test returns ||_i (side_condition && simplified version of t1' = t2') *)
			match t'.t_desc with
			| FunApp(f, [t1; t2]) when f == Settings.f_and ->
			    (* There is a single case, t' = (side_condition && simplified version of t1' = t2')
			       We avoid a loop in case the simplified version of t1' = t2' is actually t1' = t2'. *)
			    if Terms.equal_terms t2 (Terms.make_equal t1' t2') then
			      let simp_facts1 = default_add() in
			      simplif_add (depth+1) dep_info simp_facts1 t1
			    else
			      simplif_add (depth+1) dep_info simp_facts t'
			| FunApp(f, _) when f == Settings.f_or ->
			    (* There are several cases. It will be difficult to exploit the disjunction,
                               we at least add the equality t1' = t2' which may be easier to exploit. *)
			    let simp_facts1 = default_add() in
			    simplif_add (depth+1) dep_info simp_facts1 t'
			| _ ->
			    simplif_add (depth+1) dep_info simp_facts t'
			end
		  | None ->
		      default_add()
	    end
	| (ACUN(prod, neut) | Group(prod, _, neut) | CommutGroup(prod, _, neut)) as eq_th -> 
	    begin
	      let l1 = Terms.simp_prod simp_facts (ref false) prod t1' in
	      let l2 = Terms.simp_prod simp_facts (ref false) prod t2' in
	      let l1' = List.map (normalize simp_facts) l1 in
	      let l2' = List.map (normalize simp_facts) l2 in
	      (* The argument of add_fact has always been simplified by Terms.apply_eq_reds 
		 So a xor appears only when there are at least 3 factors in total.
		 A commutative group product appears either when there are at least 3 factors,
		 or two factors on the same side of the equality without inverse.
		 A non-commutative group product may appear with two factors on one side and
		 none on the other, when there is no inverse.
		 In all cases, the simplifications FunApp/FunApp or Var/Var cannot be applied,
		 so we just try to apply dependency analysis, and orient the equation when it fails. *)
	      match prod_dep_anal eq_th dep_info simp_facts l1' l2' with
		Some t' ->
		  if Terms.is_false t' then
		    raise Contradiction
		  else
		    simplif_add (depth+1) dep_info simp_facts t'
	      |	None ->
		match prod_orient_eq eq_th l1' l2' with
		  Some(t1'',t2'') -> 
		    subst_simplify2 (depth+1) dep_info simp_facts (Terms.make_equal t1'' t2'')
		| None ->
		    (subst2, fact'::facts, elsefind)
	    end
	| _ -> Parsing_helper.internal_error "Expecting a group or xor theory in Facts.add_fact"
      end
(*  | FunApp(f,[t1;t2]) when f.f_cat == ForAllDiff ->
      let t1' = try_no_var simp_facts t1 in
      let t2' = try_no_var simp_facts t2 in
      begin
      match (t1'.t_desc, t2'.t_desc) with
	(FunApp(f1,l1), FunApp(f2,l2)) when
	(f1.f_options land Settings.fopt_COMPOS) != 0 && f1 == f2 -> 
	  let vars = ref [] in
	  if List.for_all (Terms.single_occ_gvar vars) l1 && List.for_all (Terms.single_occ_gvar vars) l2 then
	    simplif_add (depth+1) dep_info simp_facts (Terms.make_or_list (List.map2 Terms.make_for_all_diff l1 l2))
	  else
	    (subst2, fact'::facts, elsefind)
      | _ -> (subst2, fact'::facts, elsefind)
      end *)
  | FunApp(f,[t1;t2]) when f == Settings.f_and ->
     simplif_add (depth+1) dep_info (add_fact (depth+1) dep_info simp_facts t1) t2
  | Var _ ->
     (* If a boolean variable var is known to be true, add the
        rewrite rule var -> true to subst *)
     subst_simplify2 (depth+1) dep_info simp_facts (Terms.make_equal fact' (Terms.make_true()))
  | FunApp(f,[t1]) when f == Settings.f_not ->
      let t1' = try_no_var simp_facts t1 in
      begin
	match t1'.t_desc with
	| Var _ ->
            (* If not(var) is known to be true for a boolean variable var,
               add the rewrite rule var -> false to subst *)
	    subst_simplify2 (depth+1) dep_info simp_facts (Terms.make_equal t1 (Terms.make_false()))
	| _ ->
	    (* not(true) and not(false) are already simplified,
	       because the library of primitivs gives the equations not(true) = false and not(false) = true. *)
	    let facts' = if List.exists (Terms.equal_terms fact') facts then facts else fact'::facts in
	    (subst2, facts', elsefind)
      end
  | _ -> 
      if Terms.is_false fact' then raise Contradiction else
      if Terms.is_true fact' then simp_facts else
      let facts' = if List.exists (Terms.equal_terms fact') facts then facts else fact'::facts in
      (subst2, facts', elsefind)
    end


(* [subst_simplify2] reduces the equalities in [subst2] using the 
   new substitution [link], and adds [link] to [subst2]. 

   We have the following invariant: either
   - [link] is a LetEqual, and the LHS of [link] could not be reduced
     using LetEqual substitutions in [subst2], or
   - the LHS of [link] has been simplified using [Terms.try_no_var].
   For this reason, when I reduce the LHS of a LetEqual using [link],
   the reduction never happens at the root, so that LHS remains
   a variable and I can keep LetEqual. *)
      
and subst_simplify2 depth dep_info (subst2, facts, elsefind) link =
  if is_identity link then
    (* The newly added substitution [link] is the identity, just ignore it *)
    (subst2, facts, elsefind)
  else
  (* Reduce the equalities in [subst2] using the new [link] *)
  let subst2'' = ref [] in
  let rhs_reduced = ref [] in
  let not_subst2_facts = ref facts in
  let rec apply_eq_st = function
      [] -> ()
    | t0::rest ->
	begin
	  match t0.t_desc with
	    FunApp(f, [t;t']) when f.f_cat == Equal || f.f_cat == LetEqual ->
	      let subst_tmp = (!subst2'') @ rest in
	      let simp_facts_tmp = (subst_tmp, facts, elsefind) in
	      let simp_facts_tmp2 = (link :: subst_tmp, facts, elsefind) in
	      (* Reduce the LHS of the equality t = t' using the new [link] *)
	      let (reduced_root_or_lhs, t1) = apply_sub1 simp_facts_tmp t link in
              (* Reduce the LHS of the equality t = t' using statements and collisions 
		 given in the input file, possibly using the new [link] to enable
		 these reductions *)
	      let (reduced_root_or_lhs, t1) =
		if reduced_root_or_lhs then
		  (reduced_root_or_lhs, t1)
		else
		  apply_eq_st_coll1 depth dep_info simp_facts_tmp2 t
	      in
	      (* Reduce the LHS t of the equality t = t' at the root using other equalities
		 when it is a function application, possibly using the new [link] to enable
		 these reductions.
		 No need to do that when t is a variable, because variable terms are fully
		 normalized, not only at the root. *)
	      let (reduced_root_or_lhs, t1) =
		if reduced_root_or_lhs || (match t.t_desc with FunApp _ -> false | _ -> true) || (not (!Settings.re_reduce_root_sides)) then
		  (reduced_root_or_lhs, t1)
		else
		  apply_sub_list simp_facts_tmp2 t subst_tmp
	      in
              (* Reduce the root of the equality t = t' using statements and collisions 
		 given in the input file, possibly using the new [link] to enable
		 these reductions *)	      
	      let (reduced_root_or_lhs, fact') =
		if reduced_root_or_lhs
		(* To avoid a stupid loop tranforming t into t = true or not(t) into t = false
                   back and forth *) 
	        || (Terms.is_true t) || (Terms.is_false t)
	        || (Terms.is_true t') || (Terms.is_false t') then
		  (reduced_root_or_lhs, Terms.build_term_type Settings.t_bool (FunApp(f,[t1; t'])))
		else
		  apply_root_st_coll1 depth dep_info simp_facts_tmp2 t0
	      in
	      if reduced_root_or_lhs then
		begin
		  if not (List.exists (Terms.equal_terms fact') (!not_subst2_facts)) then
		    not_subst2_facts := fact' :: (!not_subst2_facts)
		end
	      else
	        (* Reduce the RHS of the equality t = t' using the new [link] *)
		let (reduced_rhs, t1') = apply_sub1 simp_facts_tmp t' link in
                (* Reduce the RHS of the equality t = t' using statements and collisions 
		   given in the input file, possibly using the new [link] to enable
		   these reductions *)
		let (reduced_rhs, t1') =
		  if reduced_rhs then
		    (reduced_rhs, t1')
		  else
		    apply_eq_st_coll1 depth dep_info simp_facts_tmp2 t'
		in
	        (* Reduce the RHS t' of the equality t = t' at the root using other equalities
		   when it is a function application, possibly using the new [link] to enable
		   these reductions *)
		let (reduced_rhs, t1') =
		  if reduced_rhs || (match t'.t_desc with FunApp _ -> false | _ -> true) || (not (!Settings.re_reduce_root_sides)) then
		    (reduced_rhs, t1')
		  else
		    apply_sub_list simp_facts_tmp2 t' subst_tmp
		in
		if reduced_rhs then
		  let fact' = Terms.build_term_type Settings.t_bool (FunApp(f,[t; t1'])) in
		  rhs_reduced := fact' :: (!rhs_reduced) 
		else
                  (* if t = t', I can ignore it *) 
		  if not (equal_terms_normal simp_facts_tmp2 t t') then 
		    subst2'' := t0 :: (!subst2'')
	  | _ -> Parsing_helper.internal_error "substitutions should be Equal or LetEqual terms"
	end;
	apply_eq_st rest
  in
  apply_eq_st subst2;
  let (subst2_added_rhs_reduced, facts_to_add, elsefind) =
    specialized_add_list depth dep_info (link :: (!subst2''), !not_subst2_facts, elsefind) (!rhs_reduced)
  in
  simplif_add_list depth dep_info (subst2_added_rhs_reduced,[], elsefind) facts_to_add

and simplif_add depth dep_info simp_facts fact =
  if (!Settings.debug_simplif_add_facts) then
    begin
      print_string "simplif_add "; Display.display_term fact; 
      print_string " knowing\n"; display_facts simp_facts; print_newline();
    end;
  let fact' = apply_reds depth dep_info simp_facts fact in
  add_fact depth dep_info simp_facts fact'

and simplif_add_list depth dep_info simp_facts = function
    [] -> simp_facts
  | (a::l) -> simplif_add_list depth dep_info (simplif_add depth dep_info simp_facts a) l

(* The following functions are specialized to the case in which, in subst_simplify2,
   the added fact [link] reduces the RHS of an existing substitution, but not its LHS.
   These functions guarantee that the orientation of the substitution is not reversed,
   which would cause a possible non-termination. *)

and specialized_add_fact depth dep_info simp_facts fact =
  if (!Settings.max_depth_add_fact > 0) && (depth > !Settings.max_depth_add_fact) then 
    begin
      (*if (!Settings.debug_simplif_add_facts) then*)
	begin
	  print_string "Adding "; Display.display_term fact; print_string " (specialized) stopped because too deep."; print_newline()
	end;
      simp_facts 
    end
  else
    begin
  if (!Settings.debug_simplif_add_facts) then
    begin
      print_string "specialized_add_fact "; Display.display_term fact; print_newline()
    end;
  let (subst2,facts,elsefind)=simp_facts in
  match fact.t_desc with
    FunApp(f,[({ t_desc = Var _ } as t1);t2]) when f.f_cat == LetEqual ->
      let t2' = normalize simp_facts t2 in
      specialized_subst_simplify2 (depth+1) dep_info simp_facts (Terms.make_let_equal t1 t2')
  | FunApp(f,[t1;t2]) when f.f_cat == Equal ->
      let t2' = normalize simp_facts t2 in
      begin
	match (t1.t_desc, t2'.t_desc) with
	  (FunApp(f1,l1), FunApp(f2,l2)) when
	  f1.f_cat == Tuple && f2.f_cat == Tuple && f1 != f2 -> 
	    raise Contradiction
	| (FunApp(f1,l1), FunApp(f2,l2)) when
	  (f1.f_options land Settings.fopt_COMPOS) != 0 && f1 == f2 -> 
	    (subst2, (List.map2 Terms.make_equal l1 l2) @ facts, elsefind)
	| (Var(b1,l1), Var(b2,l2)) when
	  (Terms.is_restr b1) &&
	  (Proba.is_large_term t1  || Proba.is_large_term t2') && (b1 == b2) &&
	  (Proba.add_elim_collisions b1 b1) ->
	    (subst2, (List.map2 Terms.make_equal l1 l2) @ facts, elsefind)
	| (Var(b1,l1), Var(b2,l2)) when
	  (Terms.is_restr b1) && (Terms.is_restr b2) &&
	  (Proba.is_large_term t1 || Proba.is_large_term t2') &&
	  (b1 != b2) && (Proba.add_elim_collisions b1 b2)->
	    raise Contradiction
	| (FunApp(f1,[]), FunApp(f2,[]) ) when
	  f1 != f2 && (!Settings.diff_constants) ->
	    raise Contradiction
	          (* Different constants are different *)
	| (_,_) -> 
	    match collision_test dep_info simp_facts t1 t2' with
	      Some t' ->
		if Terms.is_false t' then 
		  raise Contradiction 
		else
		  (subst2, t' :: facts, elsefind)
	    | None ->
		if not (Terms.is_subterm t1 t2') then
		  specialized_subst_simplify2 (depth+1) dep_info simp_facts (Terms.make_equal t1 t2')
		else
		  (subst2, fact::facts, elsefind)
      end
  | _ -> 
      Parsing_helper.internal_error "specialized_add_fact: t = t' expected"
    end

and specialized_subst_simplify2 depth dep_info (subst2, facts, elsefind) link =
  if is_identity link then
    (* The newly added substitution [link] is the identity, just ignore it *)
    (subst2, facts, elsefind)
  else
  (* Reduce the equalities in [subst2] using the new [link].
     Only the RHS is reduced since we know that the LHS
     is already reduced *)
  let subst2'' = ref [] in
  let rhs_reduced = ref [] in
  let rec apply_eq_st = function
      [] -> ()
    | t0::rest ->
	begin
	  match t0.t_desc with
	    FunApp(f, [t;t']) when f.f_cat == Equal || f.f_cat == LetEqual ->
	      let tmp_subst = (!subst2'') @ rest in
	      let simp_facts_tmp2 = (link :: tmp_subst, facts, elsefind) in
	      (* Reduce the RHS of the equality t = t' using [link] *)
              let (red, t1') = apply_sub1 (tmp_subst, facts, elsefind) t' link in
              (*if red && (Terms.equal_terms t' t1') then
                print_string "Equal (1)\n";*)
              (* Reduce the RHS of the equality t = t' using statements and collisions 
		 given in the input file, possibly using the new [link] to enable
		 these reductions *)
	      let (red, t1') =
		if red then
		  (red, t1')
		else
		  apply_eq_st_coll1 depth dep_info simp_facts_tmp2 t'
	      in
              (*if red && (Terms.equal_terms t' t1') then
                print_string "Equal (2)\n";*)
	      (* Reduce the RHS t' of the equality t = t' at the root using other equalities
       		 when it is a function application, possibly using the new [link] to enable
		 these reductions *)
	      let (red, t1') =
		if red || (match t'.t_desc with FunApp _ -> false | _ -> true) || (not (!Settings.re_reduce_root_sides)) then
		  (red, t1')
		else
		  apply_sub_list simp_facts_tmp2 t' tmp_subst
	      in
              (*if red && (Terms.equal_terms t' t1') then
                print_string "Equal (3)\n";*)
	      if red then
		let fact' = Terms.build_term_type Settings.t_bool (FunApp(f,[t; t1'])) in
		rhs_reduced := fact' :: (!rhs_reduced)
	      else
                (* if t = t', I can ignore it *) 
		if not (equal_terms_normal simp_facts_tmp2 t t') then 
		  subst2'' := t0 :: (!subst2'')
	  | _ -> Parsing_helper.internal_error "substitutions should be Equal or LetEqual terms"
	end;
	apply_eq_st rest
  in
  apply_eq_st subst2;
  specialized_add_list depth dep_info (link :: (!subst2''), facts, elsefind) (!rhs_reduced)
(* It is important not to call [simplif_add_list] as we did before in the following code,
   because it may add substitutions that might reduce the LHS of substitutions to which
   we will apply [specialized_add_list], which does not test reductions of the LHS.
   [simplif_add_list] will be called afterwards in [subst_simplify2], when the calls
   to [specialized_add_list] are finished.

   let (subst2_added_rhs_reduced, facts_to_add, elsefind) =
    specialized_add_list depth dep_info (link :: (!subst2''), facts, elsefind) (!rhs_reduced)
  in
  simplif_add_list depth dep_info (subst2_added_rhs_reduced,[], elsefind) facts_to_add *)

and specialized_simplif_add depth dep_info simp_facts fact =
  if (!Settings.debug_simplif_add_facts) then
    begin
      print_string "specialized_simplif_add "; Display.display_term fact; 
      print_string " knowing\n"; display_facts simp_facts; print_newline();
    end;
  match fact.t_desc with
    FunApp(f,[t;t']) ->
      let t'' = apply_reds depth dep_info simp_facts t' in
      (* if t = t'', I can ignore the added fact *) 
      if Terms.simp_equal_terms simp_facts true t t'' then
	simp_facts
      else
	let fact' = Terms.build_term_type Settings.t_bool (FunApp(f, [t;t''])) in
	specialized_add_fact depth dep_info simp_facts fact'
  | _ ->
      Parsing_helper.internal_error "specialized_add_fact: t = t' expected"

and specialized_add_list depth dep_info simp_facts = function
    [] -> simp_facts
  | (a::l) -> specialized_add_list depth dep_info (specialized_simplif_add depth dep_info simp_facts a) l

(*let simplif_add dep_info s f =
  print_string "Adding "; Display.display_term f;
  print_string " to\n";
  display_facts s; 
  print_newline();
  try 
    let res = simplif_add dep_info s f in
    print_string "Addition done "; display_facts res;
    print_newline();
    res
  with Contradiction ->
    print_string "Contradiction\n\n";
    raise Contradiction

let simplif_add_list dep_info s fl =
  print_string "Adding "; Display.display_list Display.display_term fl;
  print_string " to\n";
  display_facts s; 
  print_newline();
  try
    let res = simplif_add_list dep_info s fl in
    print_string "Addition done "; display_facts res;
    print_newline();
    res
  with Contradiction ->
    print_string "Contradiction\n\n";
    raise Contradiction
*)

let apply_reds dep_info simp_facts t = 
  apply_reds 0 dep_info simp_facts t

let simplif_add dep_info simp_facts fact =
  simplif_add 0 dep_info simp_facts fact

let simplif_add_list dep_info simp_facts fact =
  simplif_add_list 0 dep_info simp_facts fact

let reduce_rec simp_facts =
  reduce_rec 0 simp_facts

let simplif_add_find_cond dep_info simp_facts fact =
  match fact.t_desc with
    Var _ | FunApp _ -> simplif_add dep_info simp_facts fact
  | _ -> simp_facts
    

(* Compute the list of variables that must be defined at a certain
point, taking into account defined conditions of find *)

let rec check_non_nested seen_fsymb seen_binders t =
  match t.t_desc with
    Var(b,l) ->
      (not (List.memq b seen_binders)) &&
      (List.for_all (check_non_nested seen_fsymb (b::seen_binders)) l)
  | ReplIndex _ -> true
  | FunApp(f,l) ->
      (not (List.memq f seen_fsymb)) &&
      (List.for_all (check_non_nested (f::seen_fsymb) seen_binders) l)
  | _ -> 
      Display.display_term t; print_newline();
      Parsing_helper.internal_error "If, find, let, new should have been expanded"

(* Get the node from the p_facts field of a process / the t_facts field of a term *)

let get_initial_history pp =
  match Incompatible.get_facts pp with
    None -> None
  | Some (cur_array,_,_,_,_,_,n) -> 
      Some { current_point = pp;
	     cur_array = List.map Terms.term_from_repl_index cur_array;
	     current_node = n;
	     current_in_different_block = false;
	     def_vars_in_different_blocks = [];
	     def_vars_maybe_in_same_block = [] }
 

(* [is_reachable_same_block n n'] returns true when [n] is reachable from [n']
   within the same input...output block, 
   that is, the variable defined at [n] is defined above the one 
   defined at [n'] and within the same input...output block. *)
let rec is_reachable_same_block n n' =
  if n == n' then true else
  if n'.above_node == n' || 
     (match n'.definition with 
       DInputProcess({ i_desc = Input _}) -> true 
     | _ -> false) then 
    false 
  else
    is_reachable_same_block n n'.above_node

      (* [is_before_same_block pp pp'] is true when the program point [pp]
   may be before [pp'] and in the same input...output block. *)
	
let is_before_same_block pp pp' =
  match Incompatible.get_facts pp, Incompatible.get_facts pp' with
  | Some(_,_,_,_,_,_,n), Some(_,_,_,_,_,_,n') ->
      is_reachable_same_block n n'
  | _ -> true

let get_def_vars_above n =
  List.map Terms.binderref_from_binder (Terms.add_def_vars_node [] n)

(* Given a node, return the variable references whose definition
   is guaranteed by defined conditions above that node. *)
let def_vars_from_node n = n.def_vars_at_def

(* If I know that a node [n] in node_list is executed,
   and it is not before the current node, then 
   all blocks before [n] must be fully executed. *)

let rec transfer_diff_block same_block node_list = function
    [] -> (List.rev same_block, [])
  | ((node_list', indices) as a)::l ->
      if List.for_all (fun n' ->
	List.for_all (fun n ->
	  not (is_reachable_same_block n n')) node_list) node_list'
      then 
	(List.rev same_block, a::l)
      else
	transfer_diff_block (a::same_block) node_list l

let update_history history node_list indices =
  match history with
    None -> None
  | Some h -> 
      let (same_block, new_diff_block) = 
	transfer_diff_block [] node_list h.def_vars_maybe_in_same_block
      in
      let current_diff_block = 
	h.current_in_different_block || (new_diff_block != []) ||
	(List.for_all (fun n ->
	  not (is_reachable_same_block n h.current_node)) node_list)
      in
      Some 
	  { h with
            current_in_different_block = current_diff_block;
            def_vars_in_different_blocks = new_diff_block @ h.def_vars_in_different_blocks;
            def_vars_maybe_in_same_block = (node_list, indices) :: same_block }

(* Take into account variables that must be defined because a block of code
   is always executed until the next output/yield before passing control to
   another block of code *)
let get_def_vars_above2 history n =
  let vars_above_n = Terms.add_def_vars_node [] n in
  match history with
    None -> vars_above_n
  | Some h ->
      if h.current_in_different_block then 
	n.future_binders @ vars_above_n
      else if is_reachable_same_block n h.current_node then
	Terms.intersect (==) 
	  (n.future_binders @ vars_above_n)
	  (Terms.add_def_vars_node [] h.current_node)
      else
	n.future_binders @ vars_above_n

(* Remove variables that are certainly defined from a def_list in a find.
   Variables that are defined above the find (so don't need a "defined"
   condition) are found by "get_def_vars_above def_node". 
   Variables that already have a "defined" condition above the current
   find are found by "def_vars". *)
let reduced_def_list def_node_opt def_list =
  match def_node_opt with
    Some (_, _, _, def_vars, _, _, def_node) ->
      Terms.setminus_binderref def_list (def_vars @ (get_def_vars_above def_node))
  | None -> def_list

(* [get_compatible_def_nodes history def_vars b l] returns the list of 
   possible definitions nodes for [b[l]], compatible with
   the knowledge that the variables in [def_vars] are defined
   and the information in [history]. *)

let display_pp = function
    DTerm t -> Display.display_term t
  | DInputProcess i -> Display.display_process i
  | DProcess p -> Display.display_oprocess "" p
  | _ -> print_string "other"

let get_compatible_def_nodes history def_vars b l =
  List.filter (fun n ->
    (match history with
      None -> true
    | Some h -> Incompatible.is_compatible_history (n,l) h) &&
    (List.for_all (Incompatible.is_compatible_node (b,l) n) def_vars)
      ) b.def 

(* [add_def_vars history def_vars_accu seen_refs br] adds in
   [def_vars_accu] the variables that are known to be defined when [br]
   is defined and [history] corresponds to the current program
   point. [seen_refs] stores the variables already seen to avoid loops.

[add_def_vars] must not be used to remove elements
of def_list, just to test whether all elements of def_list are defined,
in which case for a "find ... defined(def_list) && M", if M is true,
the else branch can be removed. -- Useful to remove the "else" branches
generated by applying the security of a Diffie-Hellman key agreement,
for example. 
Removing all elements of def_list that are already known to be defined
according to [add_def_vars] would remove too many elements, and
break the code of SArename.
Use [reduced_def_list] above to remove useless elements of def_list.
*)

let rec add_def_vars history seen_refs done_refs ((b,l) as br) =
  if (List.for_all (check_non_nested [] [b]) l) &&
    (not (Terms.mem_binderref br (!done_refs))) then
    begin
      done_refs := br :: (!done_refs);
      let nodes_b_def = get_compatible_def_nodes history (!seen_refs) b l in    
      let history = update_history history nodes_b_def l in
      let def_vars_above_def = Terms.intersect_list (==) (List.map (get_def_vars_above2 history) nodes_b_def) in
      let def_vars_at_def = Terms.intersect_list Terms.equal_binderref (List.map def_vars_from_node nodes_b_def) in
      (* put links for the substitution b.args_at_creation -> l *)
      let bindex = b.args_at_creation in
      List.iter2 (fun b t -> b.ri_link <- TLink t) bindex l;
      (* add facts *)
      List.iter (fun b ->
	let new_br = (b, List.map (fun ri -> match ri.ri_link with
	  NoLink -> Terms.term_from_repl_index ri
	| TLink t' -> t') b.args_at_creation)
	in
	Terms.add_binderref new_br seen_refs;
	Terms.add_binderref new_br done_refs
	  ) def_vars_above_def;
      (* compute arguments of recursive call *)
      let def_vars_at_def' = Terms.copy_def_list Terms.Links_RI def_vars_at_def in
      List.iter (fun br -> Terms.add_binderref br seen_refs) def_vars_at_def';
      (* remove the links *)
      List.iter (fun b -> b.ri_link <- NoLink) bindex;
      (* recursive call *)
      List.iter (add_def_vars history seen_refs done_refs) def_vars_at_def'
    end

(* Take into account facts that must be true because a block of code
   is always executed until the next output/yield before passing control to
   another block of code *)
let true_facts_from_node history n =
  match history with
    None -> n.true_facts_at_def
  | Some h ->
      if h.current_in_different_block then
	n.future_true_facts @ n.true_facts_at_def
      else if is_reachable_same_block n h.current_node then
	Terms.intersect Terms.equal_terms (n.future_true_facts @ n.true_facts_at_def) h.current_node.true_facts_at_def
      else
	n.future_true_facts @ n.true_facts_at_def

(* [add_facts] collects the facts that are known to hold when [br = b[l]]
   is defined. The facts are collected in [fact_accu].
   - look for definitions n of binders b,
   - substitute l for b.args_at_creation in n.true_facts_at_def and
     add these facts to [fact_accu]
   - substitute l for b.args_at_creation in n.def_vars_at_def and
     continue recursively with these definitions 
   - If there are several definitions of b, take the intersection
     of lists of facts/defined vars. ("or" would be more precise
     but difficult to implement) 
   - Do not reconsider an already seen pair (b,l), to avoid loops.
     The pairs (b,l) already seen are stored in [done_refs]. *)

let rec add_facts history fact_accu seen_refs done_refs ((b,l) as br) =
  (* print_string "Is defined "; Display.display_var b l; print_newline(); *)
  if (List.for_all (check_non_nested [] [b]) l) &&
    (not (Terms.mem_binderref br (!done_refs))) then
    begin
      done_refs := br :: (!done_refs);
      let nodes_b_def = get_compatible_def_nodes history (!seen_refs) b l in
      begin
	match history with
	  None -> ()
	| Some h ->
	    fact_accu := Incompatible.facts_compatible_history (!fact_accu) (nodes_b_def, l) h
      end;
      let history = update_history history nodes_b_def l in
      let true_facts_at_def = filter_ifletfindres (Terms.intersect_list Terms.equal_terms (List.map (true_facts_from_node history) nodes_b_def)) in
      let def_vars_at_def = Terms.intersect_list Terms.equal_binderref (List.map def_vars_from_node nodes_b_def) in
      (* put links for the substitution b.args_at_creation -> l *)
      let bindex = b.args_at_creation in
      List.iter2 (fun b t -> b.ri_link <- TLink t) bindex l;
      (* add facts *)
      List.iter (fun f -> 
        (* b.args_at_creation -> l *)
	let f = Terms.copy_term Terms.Links_RI f in
	(* print_string "Adding "; Display.display_term f; print_newline(); *)
	if not (List.exists (Terms.equal_terms f) (!fact_accu)) then
	  fact_accu := f :: (!fact_accu)
	  ) true_facts_at_def;
      (* compute arguments of recursive call *)
      let def_vars_at_def' = Terms.copy_def_list Terms.Links_RI def_vars_at_def in
      List.iter (fun br -> Terms.add_binderref br seen_refs) def_vars_at_def';
      (* remove the links *)
      List.iter (fun b -> b.ri_link <- NoLink) bindex;
      (* recursive call *)
      List.iter (add_facts history fact_accu seen_refs done_refs) def_vars_at_def'
    end
      
(* [def_vars_from_defined history def_list] returns the variables that
   are known to be defined when the condition of a find with defined condition 
   [def_list] holds. [history] is the history of the find, at which [def_list]
   is tested (may be returned by [get_initial_history]). *)

let def_vars_from_defined history def_list =
  let subterms = ref [] in
  List.iter (Terms.close_def_subterm subterms) def_list;
  let seen_refs = ref (!subterms) in
  List.iter (add_def_vars history seen_refs (ref [])) (!subterms);
  !seen_refs

(* [facts_from_defined history def_list] returns the facts that
   are known to hold when the condition of a find with defined condition 
   [def_list] holds. [history] is the history of the find, at which [def_list]
   is tested (may be returned by [get_initial_history]). *)

let facts_from_defined history def_list =
  let def_list_subterms = ref [] in
  List.iter (Terms.close_def_subterm def_list_subterms) def_list;
  let fact_accu = ref [] in
  let seen_refs = ref (!def_list_subterms) in
  List.iter (add_facts history fact_accu seen_refs (ref [])) (!def_list_subterms);
  !fact_accu

(* [get_def_vars_at pp] returns the variables that are known
   to be defined at program point [pp]. *)

let get_def_vars_at pp  = 
  match Incompatible.get_facts pp with
    Some (_,_,_,def_vars,_,_,n) ->
      let done_refs = ref (get_def_vars_above n) in
      let seen_refs = ref (def_vars @ (!done_refs)) in
      (* Note: def_vars contains n.def_vars_at_def *)
      let history = get_initial_history pp in
      List.iter (add_def_vars history seen_refs done_refs) def_vars;
      !seen_refs
  | None -> []

(* [get_facts_at pp] returns the facts that are known to hold
   at program point [pp]. *)

let get_facts_at pp =
  match Incompatible.get_facts pp with
    None -> []
  | Some(_,true_facts, _, def_vars, _,_, n) ->
      let fact_accu = ref (filter_ifletfindres true_facts) in
      (* Note: def_vars contains n.def_vars_at_def *)
      let history = get_initial_history pp in
      List.iter (add_facts history fact_accu (ref def_vars) (ref [])) def_vars;
      !fact_accu

(* [get_def_vars_full_block pp] returns the variables that are known
   to be defined at the end of the input...output block containing
   program point [pp]. *)

let get_def_vars_full_block pp  = 
  match Incompatible.get_facts pp with
    Some (_,_,_,def_vars,_,fut_binders,n) ->
      let done_refs =
	ref (List.map Terms.binderref_from_binder
	       (fut_binders @ Terms.add_def_vars_node [] n))
      in
      let seen_refs = ref (def_vars @ (!done_refs)) in
      (* Note: def_vars contains n.def_vars_at_def *)
      let history = get_initial_history pp in
      List.iter (add_def_vars history seen_refs done_refs) def_vars;
      !seen_refs
  | None -> []

(* [get_facts_full_block pp] returns the facts that are known to hold
   at the end of the input...output block containing program point [pp]. *)

let get_facts_full_block pp =
  match Incompatible.get_facts pp with
    None -> []
  | Some(_,true_facts, _, def_vars, fut_true_facts, _, n) ->
      let fact_accu = ref (filter_ifletfindres (fut_true_facts @ true_facts)) in
      (* Note: def_vars contains n.def_vars_at_def *)
      let history = get_initial_history pp in
      List.iter (add_facts history fact_accu (ref def_vars) (ref [])) def_vars;
      !fact_accu

(* [get_elsefind_facts_at pp] returns the elsefind facts that are
   known to hold at program point [pp] *)

let get_elsefind_facts_at pp = 
  match Incompatible.get_facts pp with
    None -> []
  | Some(_, _, elsefind_facts, _, _, _, _) -> elsefind_facts

(* Functions useful to simplify def_list *)

(* [filter_def_list accu l] returns a def_list that contains
   all elements of [accu] and [l] except the elements whose definition
   is implied by the definition of some other element of [l].
   The typical call is [filter_def_list [] l], which returns 
   a def_list that contains all elements of [l] except 
   the elements whose definition is implied by the definition 
   of some other element.*)
	
let rec filter_def_list accu = function
    [] -> accu
  | (br::l) ->
      let implied_br = def_vars_from_defined None [br] in
      let accu' = Terms.setminus_binderref accu implied_br in
      let l' = Terms.setminus_binderref l implied_br in
      filter_def_list (br::accu') l'

(* [remove_subterms accu l] returns a def_list that contains
   all elements of [accu] and [l] except elements that
   also occur as subterms in [l].
   The typical call is  [remove_subterms [] l], which returns
   [l] with elements that occur as subterms removed. *)

let rec remove_subterms accu = function
    [] -> accu
  | (br::l) ->
      let subterms = ref [] in
      Terms.close_def_subterm subterms br;
      let accu' = Terms.setminus_binderref accu (!subterms) in
      let l' = Terms.setminus_binderref l (!subterms) in
      remove_subterms (br::accu') l' 

(* [eq_deflists dl dl'] returns true when the two def_list [dl]
   and [dl'] are equal (by checking mutual inclusion) *)
	
let eq_deflists dl dl' =
  (List.for_all (fun br' -> Terms.mem_binderref br' dl) dl') &&
  (List.for_all (fun br -> Terms.mem_binderref br dl') dl) 

(* [union_list l] returns the union of the lists of binder references
   contained in the list of lists [l] *)

let union_list l =
  let accu = ref [] in
  List.iter (List.iter (fun br -> Terms.add_binderref br accu)) l;
  !accu

(* [put_defined_cond_t def_list t]  returns the binder references
   of [def_list] that occur in [t] *)
    
let rec put_defined_cond_t def_list t =
  match t.t_desc with
    FunApp(f, l) ->
      union_list (List.map (put_defined_cond_t def_list) l)
  | Var(b,l) ->
      let def_list' = union_list (List.map (put_defined_cond_t def_list) l) in
      if Terms.mem_binderref (b,l) def_list then
	(b,l)::def_list'
      else
	def_list'
  | ReplIndex _ -> []
  | _ -> Parsing_helper.internal_error "Term should be expanded in Facts.put_defined_cond_t"

(* [put_defined_cond_pat def_list pat]  returns the binder references
   of [def_list] that occur in [pat] *)

let rec put_defined_cond_pat def_list = function
    PatVar _ -> []
  | PatTuple (_,l) -> union_list (List.map (put_defined_cond_pat def_list) l)
  | PatEqual t -> put_defined_cond_t def_list t

(* [add_def_cond_fc def_list t] adds on of top [t] a test
   that verifies that all variables in [def_list] are defined.
   [add_def_cond_o] is similar for processes. *)
	
let add_def_cond_fc def_list t =
  if def_list != [] then
    Terms.build_term t (FindE([([], def_list, Terms.make_true(), t)], Terms.cst_for_type t.t_type, Nothing))  
  else
    t
      
let add_def_cond_o def_list p =
  if def_list != [] then
    Terms.oproc_from_desc (Find([([], def_list, Terms.make_true(), p)], Terms.oproc_from_desc Yield, Nothing))  
  else
    p

(* [put_defined_cond_fc def_list t] returns [def_list', t']
   where [t'] is [t] modified to add defined conditions 
   for binder references in [def_list].
   [def_list'] are the binder references of [def_list]
   whose definition should be guaranteed above [t']. 
   The binder references in [def_list] are assumed to be actually
   defined when they are used. The defined conditions are
   added just to guarantee the syntactic invariant that 
   definition is checked before the variable is used.
   The defined conditions are added as early as possible in the term [t'],
   while being sure that the variable in question will be used.
   (Otherwise, they could add conditions that are not true,
   so that would modify the semantics of the term.)
   [put_defined_cond_i] and [put_defined_cond_o] are similar
   for processes.
*)
      
let rec put_defined_cond_fc def_list t =
  match t.t_desc with
    FunApp _ | Var _ | ReplIndex _ ->
      let def_list' = put_defined_cond_t def_list t in
      (def_list', t)
  | TestE(t1, t2, t3) ->
      let (def_list2, t2') = put_defined_cond_fc def_list t2 in
      let (def_list3, t3') = put_defined_cond_fc def_list t3 in
      let def_list_common = Terms.union_binderref (put_defined_cond_t def_list t1)
	  (Terms.inter_binderref def_list2 def_list3)
      in
      let def_list_then = Terms.setminus_binderref def_list2 def_list_common in
      let def_list_else = Terms.setminus_binderref def_list3 def_list_common in
      let t3'' = add_def_cond_fc def_list_else t3' in
      let t' =
	if def_list_then != [] then
	  Terms.build_term2 t (FindE([([], def_list_then, t1, t2')], t3'', Nothing))
	else
	  Terms.build_term2 t (TestE(t1, t2', t3''))
      in
      (def_list_common, t')
  | FindE(l0, t3, find_info) ->
      let (def_list3, t3') = put_defined_cond_fc def_list t3 in
      let t3'' = add_def_cond_fc def_list3 t3' in
      let l0' = List.map (fun (bl, def_list0, t1, t2) ->
	let (def_list1, t1') = put_defined_cond_fc def_list t1 in
	let (def_list2, t2') = put_defined_cond_fc def_list t2 in
	(bl, Terms.union_binderref def_list0 (Terms.union_binderref def_list1 def_list2), t1', t2')
	  ) l0
      in
      ([], Terms.build_term2 t (FindE(l0', t3'', find_info)))
  | LetE(PatVar b, t1, t2, None) ->
      let def_list1 = put_defined_cond_t def_list t1 in
      let (def_list2, t2') = put_defined_cond_fc def_list t2 in
      (Terms.union_binderref def_list1 def_list2, Terms.build_term2 t (LetE(PatVar b, t1, t2', None)))
  | LetE(pat, t1, t2, Some t3) ->
      let def_list_pat = put_defined_cond_pat def_list pat in
      let def_list1 = put_defined_cond_t def_list t1 in
      let (def_list2, t2') = put_defined_cond_fc def_list t2 in
      let (def_list3, t3') = put_defined_cond_fc def_list t3 in
      let def_list_common = Terms.union_binderref
	  (Terms.union_binderref def_list_pat def_list1)
	  (Terms.inter_binderref def_list2 def_list3)
      in
      let def_list_in = Terms.setminus_binderref def_list2 def_list_common in
      let def_list_else = Terms.setminus_binderref def_list3 def_list_common in
      let t2'' = add_def_cond_fc def_list_in t2' in
      let t3'' = add_def_cond_fc def_list_else t3' in
      (def_list_common, Terms.build_term2 t (LetE(pat, t1, t2'', Some t3'')))
  | LetE _ -> 
      Parsing_helper.internal_error "When the pattern is not a variable, let should always have an else branch"
  | ResE(b, t1) ->
      let (def_list', t1') = put_defined_cond_fc def_list t1 in
      (def_list', Terms.build_term2 t (ResE(b, t1')))
  | EventAbortE _ -> ([], t)
  | EventE _ | GetE _ | InsertE _ -> Parsing_helper.internal_error "Event/Get/Insert not occur in Facts.put_defined_cond_fc"

let rec put_defined_cond_i def_list p =
  match p.i_desc with
    Nil -> ([], p)
  | Par(p1,p2) ->
      let (def_list1, p1') = put_defined_cond_i def_list p1 in
      let (def_list2, p2') = put_defined_cond_i def_list p2 in
      (Terms.union_binderref def_list1 def_list2, Terms.iproc_from_desc2 p (Par(p1',p2')))
  | Repl(b,p1) ->
      let (def_list1, p1') = put_defined_cond_i def_list p1 in
      (def_list1, Terms.iproc_from_desc2 p (Repl(b,p1')))
  | Input((c,tl), pat, p1) ->
      let def_listl = (List.map (put_defined_cond_t def_list) tl) in
      let def_list_pat = put_defined_cond_pat def_list pat in
      let (def_list1, p1') = put_defined_cond_o def_list p1 in
      let p1'' = add_def_cond_o def_list1 p1' in
      (union_list (def_list_pat::def_listl), Terms.iproc_from_desc2 p (Input((c,tl), pat, p1'')))

and put_defined_cond_o def_list p =
  match p.p_desc with
    Yield | EventAbort _ -> ([], p)
  | Restr(b,p1) ->
      let (def_list1, p1') = put_defined_cond_o def_list p1 in
      (def_list1, Terms.oproc_from_desc2 p (Restr(b, p1')))
  | Test(t, p1, p2) ->
      let (def_list1, p1') = put_defined_cond_o def_list p1 in
      let (def_list2, p2') = put_defined_cond_o def_list p2 in
      let def_list_common = Terms.union_binderref (put_defined_cond_t def_list t)
	  (Terms.inter_binderref def_list1 def_list2)
      in
      let def_list_then = Terms.setminus_binderref def_list1 def_list_common in
      let def_list_else = Terms.setminus_binderref def_list2 def_list_common in
      let p2'' = add_def_cond_o def_list_else p2' in
      let p' =
	if def_list_then != [] then
	  Terms.oproc_from_desc2 p (Find([([], def_list_then, t, p1')], p2'', Nothing))
	else
	  Terms.oproc_from_desc2 p (Test(t, p1', p2''))
      in
      (def_list_common, p')
  | Find(l0, p2, find_info) ->
      let (def_list2, p2') = put_defined_cond_o def_list p2 in
      let p2'' = add_def_cond_o def_list2 p2' in
      let l0' = List.map (fun (bl, def_list0, t, p1) ->
	let (def_list_t, t') = put_defined_cond_fc def_list t in
	let (def_list1, p1') = put_defined_cond_o def_list p1 in
	(bl, Terms.union_binderref def_list0 (Terms.union_binderref def_list_t def_list1), t', p1')
	  ) l0
      in
      ([], Terms.oproc_from_desc2 p (Find(l0', p2'', find_info)))
  | Output((c,tl), t, p1) ->
      let def_listl = (List.map (put_defined_cond_t def_list) tl) in
      let def_listt = put_defined_cond_t def_list t in
      let (def_list1, p1') = put_defined_cond_i def_list p1 in
      (union_list (def_list1::def_listt::def_listl), Terms.oproc_from_desc2 p (Output((c,tl), t, p1')))
  | Let(PatVar b, t, p1, p2) ->
      let def_list_t = put_defined_cond_t def_list t in
      let (def_list1, p1') = put_defined_cond_o def_list p1 in
      (Terms.union_binderref def_list_t def_list1, Terms.oproc_from_desc2 p (Let(PatVar b, t, p1', Terms.oproc_from_desc2 p2 Yield)))
  | Let(pat, t, p1, p2) ->
      let def_list_pat = put_defined_cond_pat def_list pat in
      let def_list_t = put_defined_cond_t def_list t in
      let (def_list1, p1') = put_defined_cond_o def_list p1 in
      let (def_list2, p2') = put_defined_cond_o def_list p2 in
      let def_list_common = Terms.union_binderref
	  (Terms.union_binderref def_list_pat def_list_t)
	  (Terms.inter_binderref def_list1 def_list2)
      in
      let def_list_in = Terms.setminus_binderref def_list1 def_list_common in
      let def_list_else = Terms.setminus_binderref def_list2 def_list_common in
      let p1'' = add_def_cond_o def_list_in p1' in
      let p2'' = add_def_cond_o def_list_else p2' in
      (def_list_common, Terms.oproc_from_desc2 p (Let(pat, t, p1'', p2'')))
  | EventP(t,p1) ->
      let def_listt = put_defined_cond_t def_list t in
      let (def_list1, p1') = put_defined_cond_o def_list p1 in
      (Terms.union_binderref def_listt def_list1, Terms.oproc_from_desc2 p (EventP(t,p1')))
  | Get _ | Insert _ -> Parsing_helper.internal_error "Get/Insert should have been expanded in Facts.put_defined_cond_o"
      
(* [update_def_list_term already_defined newly_defined bl def_list tc' p'] 
   returns an updated find branch [(bl, def_list', tc'', p'')].
   This function should be called after modifying a branch of find 
   (when the find is a term), to make sure that all needed variables are defined.
   It updates in particular [def_list], but may also add defined conditions
   inside [tc'] or [p'].
   [already_defined] is a list of variables already known to be defined
   above the find.
   [newly_defined] is the set of variables whose definition is guaranteed
   by the old defined condition [def_list]; it is used only for a sanity check.
   [bl, def_list, tc', p'] describe the modified branch of find:
   [bl] contains the indices of find
   [def_list] is the old def_list
   [tc'] is the modified condition of the find
   [p'] is the modified then branch of the find. *) 

let update_def_list_term already_defined newly_defined bl def_list tc' p' =
  (* Compute in [accu_needed] the variable references that need to be included in the "defined"
     condition, to make sure that all variable references present in tc' and p'
     are in scope or in a defined condition *)
  let accu_needed = ref [] in
  Terms.get_needed_deflist_term already_defined accu_needed tc';
  (* Replace vars with repl_indices in p', to get the variable
     references that need to occur in the new def_list *)
  let bl_rev_subst = List.map (fun (b,b') -> (b, Terms.term_from_repl_index b')) bl in
  let p'_repl_indices = Terms.subst3 bl_rev_subst p' in
  Terms.get_needed_deflist_term already_defined accu_needed p'_repl_indices;
  (* Compute the subterms of [accu_needed] *)
  let accu_needed_subterm = ref [] in
  List.iter (Terms.close_def_subterm accu_needed_subterm) (!accu_needed);
  let needed_occur = !accu_needed_subterm in
  (* In case the definition of all needed variables 
     cannot be inferred from the original defined condition,
     the defined conditions for the additional variables are put inside tc'/p',
     or in def_list4 in case we are sure that they are defined at this point. *)
  let def_list_inside_tc'_p' = Terms.setminus_binderref needed_occur newly_defined in
  let (needed_occur, tc', p') =
    if def_list_inside_tc'_p' == [] then
      (needed_occur, tc', p')
    else
      let (def_list_tc'', tc'') = put_defined_cond_fc def_list_inside_tc'_p' tc' in
      let def_list_inside_p' = Terms.subst_def_list (List.map snd bl) (List.map (fun (b,_) -> Terms.term_from_binder b) bl) def_list_inside_tc'_p' in
      let (def_list_p'', p'') = put_defined_cond_fc def_list_inside_p' p' in
      let rest_def_list_p' = Terms.subst_def_list3 bl_rev_subst def_list_p'' in
      (Terms.union_binderref (Terms.inter_binderref needed_occur newly_defined)
	 (Terms.union_binderref def_list_tc'' rest_def_list_p'), tc'', p'')
  in
  (* Update the defined condition to include [needed_occur],
     but remove elements that are no longer useful *)
  let implied_needed_occur = def_vars_from_defined None needed_occur in
  let def_list'' = Terms.setminus_binderref 
      (Terms.setminus_binderref def_list implied_needed_occur) already_defined in
  let def_list3 = remove_subterms [] (needed_occur @ (filter_def_list [] def_list'')) in
  let def_list4 = 
    if (List.length def_list3 < List.length def_list) ||
    (not (eq_deflists def_list def_list3)) then
      def_list3 
    else
      def_list
  in
  (bl, def_list4, tc', p')

(* [update_def_list_process already_defined newly_defined bl def_list t' p1'] 
   returns an updated find branch [(bl, def_list', t'', p1'')].
   This function should be called after modifying a branch of find 
   (when the find is a process), to make sure that all needed variables are defined.
   It updates in particular [def_list], but may also add defined conditions
   inside [t'] or [p1'].
   [already_defined] is a list of variables already known to be defined
   above the find.
   [newly_defined] is the set of variables whose definition is guaranteed
   by the old defined condition [def_list]; it is used only for a sanity check.
   [bl, def_list, t', p1'] describe the modified branch of find:
   [bl] contains the indices of find
   [def_list] is the old def_list
   [t'] is the modified condition of the find
   [p1'] is the modified then branch of the find. *) 

let update_def_list_process already_defined newly_defined bl def_list t' p1' =
  (* Compute in [accu_needed] the variable references that need to be included in the "defined"
     condition, to make sure that all variable references present in t' and p1'
     are in scope or in a defined condition *)
  let accu_needed = ref [] in
  Terms.get_needed_deflist_term already_defined accu_needed t';
  (* Replace vars with repl_indices in p1', to get the variable
     references that need to occur in the new def_list *)
  let bl_rev_subst = List.map (fun (b,b') -> (b, Terms.term_from_repl_index b')) bl in
  let p1'_repl_indices = Terms.subst_oprocess3 bl_rev_subst p1' in
  Terms.get_needed_deflist_oprocess already_defined accu_needed p1'_repl_indices;
  (* Compute the subterms of [accu_needed] *)
  let accu_needed_subterm = ref [] in
  List.iter (Terms.close_def_subterm accu_needed_subterm) (!accu_needed);
  let needed_occur = !accu_needed_subterm in
  (* Safety check: check that the definition of all needed variables 
     can be inferred from the original defined condition 
  if not (List.for_all (fun br -> Terms.mem_binderref br newly_defined) needed_occur) then
    begin
      print_string "find ";
      Display.display_list (fun (b, b') -> Display.display_binder b; print_string " = "; Display.display_repl_index b') bl;
      print_string " suchthat defined(";
      Display.display_list (fun (b,tl) -> Display.display_var b tl) def_list;
      print_string ") && ";
      Display.display_term t';
      print_string " then\n";
      Display.display_oprocess "" p1';
      print_string "Needed refs = ";
      Display.display_list (fun (b,tl) -> Display.display_var b tl) needed_occur;
      print_newline();
      print_string "Newly defined = ";
      Display.display_list (fun (b,tl) -> Display.display_var b tl) newly_defined;
      print_newline();
    end; *)
  (* In case the definition of all needed variables 
     cannot be inferred from the original defined condition,
     the defined conditions for the additional variables are put inside t'/p1',
     or in def_list4 in case we are sure that they are defined at this point. *)
  let def_list_inside_t'_p1' = Terms.setminus_binderref needed_occur newly_defined in
  let (needed_occur, t', p1') =
    if def_list_inside_t'_p1' == [] then
      (needed_occur, t', p1')
    else
      let (def_list_t'', t'') = put_defined_cond_fc def_list_inside_t'_p1' t' in
      let def_list_inside_p1' = Terms.subst_def_list (List.map snd bl) (List.map (fun (b,_) -> Terms.term_from_binder b) bl) def_list_inside_t'_p1' in
      let (def_list_p1'', p1'') = put_defined_cond_o def_list_inside_p1' p1' in
      let rest_def_list_p1' = Terms.subst_def_list3 bl_rev_subst def_list_p1'' in
      (Terms.union_binderref (Terms.inter_binderref needed_occur newly_defined)
	 (Terms.union_binderref def_list_t'' rest_def_list_p1'), t'', p1'')
  in
  (* Update the defined condition to include [needed_occur],
     but remove elements that are no longer useful *)
  let implied_needed_occur = def_vars_from_defined None needed_occur in
  let def_list'' = Terms.setminus_binderref
      (Terms.setminus_binderref def_list implied_needed_occur) already_defined in
  let def_list3 = remove_subterms [] (needed_occur @ (filter_def_list [] def_list'')) in
  let def_list4 = 
    if (List.length def_list3 < List.length def_list) ||
    (not (eq_deflists def_list def_list3)) then
      def_list3 
    else
      def_list
  in
  (bl, def_list4, t', p1')


(* [intersect_list_cases accu eq l] is a modified version of [Terms.intersect_list].
   It returns a pair (inter_l, cases_l):
   - [inter_l] contains the elements that appear in all lists in [l], but not in [accu]. 
   - [cases_l] contains, for each list in [l], the elements that do not appear in [inter_l] nor in [accu]
   The function [eq] is used for testing equality between elements. *)

let intersect_list_cases accu eq l =
  let inter_l = 
    List.filter (fun f -> not (List.exists (eq f) accu)) 
      (Terms.intersect_list eq l)
  in
  let cases_l = 
    List.map (fun fl ->
      List.filter (fun f -> 
	not (List.exists (eq f) inter_l ||
             List.exists (eq f) accu)
	  ) fl
	) l
  in
  (inter_l, cases_l)

(* Define [fold_left3], to extend [List.fold_left] to 3 arguments *)

let rec fold_left3 f accu l1 l2 l3 =
  match (l1, l2, l3) with
    ([], [], []) -> accu
  | (a1::l1, a2::l2, a3::l3) -> fold_left3 f (f accu a1 a2 a3) l1 l2 l3
  | (_, _, _) -> invalid_arg "fold_left3"


(* [add_facts_cases / get_facts_at_cases] below are a modified version of
   add_facts/get_facts_at to distinguish cases depending on the
   definition point of variables (instead of taking intersections), to
   facilitate the proof of correspondences.

   The collected facts are stored in [(fact_accu, fact_accu_cases)]:
   - [fact_accu] contains the facts that known to hold
   - [fact_accu_cases] contains facts that hold in some cases: 
   [fact_accu_cases] is a list of list of list of facts, 
   interpreted as a conjunction of a disjunction of a conjunction of facts.
   This conjunction is known to hold. *)

let rec add_facts_cases history (fact_accu, fact_accu_cases) seen_refs done_refs ((b,l) as br) =
  (* done_refs is always included in seen_refs *)
  (* print_string "Is defined "; Display.display_var b l; print_newline(); *)
  if (List.for_all (check_non_nested [] [b]) l) &&
    (not (Terms.mem_binderref br (!done_refs))) then
    begin
      done_refs := br :: (!done_refs);
      let nodes_b_def = get_compatible_def_nodes history (!seen_refs) b l in    
      let history' = update_history history nodes_b_def l in
      let true_facts_at_def_list = 
	List.map (fun n -> 
	  filter_ifletfindres (true_facts_from_node history n)
	    ) nodes_b_def
      in
      let def_vars_at_def_list = List.map def_vars_from_node nodes_b_def in
      (* put links for the substitution b.args_at_creation -> l *)
      let bindex = b.args_at_creation in
      List.iter2 (fun b t -> b.ri_link <- TLink t) bindex l;
      (* rename facts *)
      let true_facts_at_def_list' = 
	List.map (List.map (Terms.copy_term Terms.Links_RI)) true_facts_at_def_list
      in
      (* rename def vars *)
      let def_vars_at_def_list' = 
	List.map (Terms.copy_def_list Terms.Links_RI) def_vars_at_def_list
      in
      (* remove the links *)
      List.iter (fun b -> b.ri_link <- NoLink) bindex;
      (* add facts from compatibility with history *)
      let true_facts_at_def_list' = 
	match history with
	  None -> true_facts_at_def_list'
	| Some h ->
	    List.map2 (fun fact_accu n ->
	      Incompatible.facts_compatible_history fact_accu ([n], l) h
		) true_facts_at_def_list' nodes_b_def
      in
      (* split into cases *)
      let history_cases =
	List.map (fun n -> update_history history [n] l) nodes_b_def
      in
      let (true_facts_at_def_common, true_facts_at_def_cases) = 
	intersect_list_cases (!fact_accu) Terms.equal_terms true_facts_at_def_list'
      in
      let (def_vars_at_def_common, def_vars_at_def_cases) =
	intersect_list_cases (!seen_refs) Terms.equal_binderref def_vars_at_def_list'
      in
      fact_accu := true_facts_at_def_common @ (!fact_accu);
      seen_refs := def_vars_at_def_common @ (!seen_refs);
      (* recursive call *)
      List.iter (add_facts_cases history' (fact_accu, fact_accu_cases) seen_refs done_refs) def_vars_at_def_common;
      (* facts that would be collected thanks to the binderrefs missed due 
	 to the intersection over definitions of b *)
      let true_facts_at_def_cases =
	fold_left3 (fun accu history_1case true_facts_at_def_1case missed_br ->
	  try 
	    let missed_facts = ref [] in
	    let seen_refs_tmp = ref (!seen_refs) in
	    let done_refs_tmp = ref (!done_refs) in
	    List.iter (add_facts history_1case missed_facts seen_refs_tmp done_refs_tmp) missed_br;
	  (* I do not distinguish cases further for simplicity; 
	     doing it might be an improvement, but might be costly *)
	    let true_facts_at_def_from_br_1case = 
	      List.filter (fun f -> not (List.exists (Terms.equal_terms f) (!fact_accu))) (!missed_facts)
	    in
	    (true_facts_at_def_1case @ true_facts_at_def_from_br_1case) :: accu
	  with Contradiction -> 
	    (* This case cannot happen *)
	    accu
	      ) [] history_cases true_facts_at_def_cases def_vars_at_def_cases
      in
      fact_accu_cases := true_facts_at_def_cases :: (!fact_accu_cases);
    end

let get_facts_full_block_cases pp  =
  match Incompatible.get_facts pp with
    None -> [],[]
  | Some(_,true_facts, _, def_vars, fut_true_facts, _, n) ->
      let fact_accu = ref (filter_ifletfindres (fut_true_facts @ true_facts)) in
      let fact_accu_cases = ref [] in
      (* Note: def_vars contains n.def_vars_at_def *)
      let history = get_initial_history pp in
      List.iter (add_facts_cases history (fact_accu, fact_accu_cases) (ref def_vars) (ref [])) def_vars;
      !fact_accu, !fact_accu_cases

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
	ignore (simplif_add dep_info true_facts (Terms.make_not t1')))
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
	  [],[],(Var _ | FunApp _) -> simplif_add dep_info simp_facts (Terms.make_not t1)
	| _,[],_ -> simp_facts
	| _,_,(Var _ | FunApp _) -> 
	    let bl' = List.map snd bl in
	    let true_facts_ref = ref [] in
	    let simp_facts = (subst, facts, (bl', def_list, t1)::elsefind) in
	    always_true_def_list_t true_facts_ref t1 simp_facts bl' def_vars def_list;
	    simplif_add_list dep_info simp_facts (!true_facts_ref)
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
  simplif_add_list dep_info simp_facts (!true_facts_ref)


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
	
let needed_vars vars q = List.exists (fun b -> Array_ref.has_array_ref_q b q) vars

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
  
(***** [simplify_term dep_info simp_facts t] simplifies a term [t] 
       knowing some true facts [simp_facts] and using the 
       dependency analysis [dep_info] *****)

let rec simplify_term_rec dep_info simp_facts t =
  let t' = try_no_var simp_facts t in
  match t'.t_desc with
    FunApp(f, [t1;t2]) when f == Settings.f_and ->
      begin
	try
          (* We simplify t2 knowing t1 (t2 is evaluated only when t1 is true) *)
	  let simp_facts2 = simplif_add dep_info simp_facts t1 in
	  let t2' = simplify_term_rec dep_info simp_facts2 t2 in
          (* we can swap the "and" to evaluate t1 before t2 *)
	  let simp_facts1 = simplif_add dep_info simp_facts t2' in
	  Terms.make_and (simplify_term_rec dep_info simp_facts1 t1) t2'
	with Contradiction -> 
	  (* Adding t1 or t2' raised a Contradiction *)
	  Terms.make_false()
      end
  | FunApp(f, [t1;t2]) when f == Settings.f_or ->
      begin
	try 
          (* We simplify t2 knowing (not t1) (t2 is evaluated only when t1 is false) *)
	  let simp_facts2 = simplif_add dep_info simp_facts (Terms.make_not t1) in
	  let t2' = simplify_term_rec dep_info simp_facts2 t2 in
          (* we can swap the "or" to evaluate t1 before t2 *)
	  let simp_facts1 = simplif_add dep_info simp_facts (Terms.make_not t2') in
	  Terms.make_or (simplify_term_rec dep_info simp_facts1 t1) t2'
	with Contradiction ->
	  (* Adding (not t1) or (not t2') raised a Contradiction, t1 or t2' is always true *)
	  Terms.make_true()
      end
  | FunApp(f, [t1;t2]) when f.f_cat == Equal ->
      let t1' = try_no_var simp_facts t1 in
      let t2' = try_no_var simp_facts t2 in
      begin
	match 
	  (match Terms.get_prod Terms.try_no_var_id t1' with 
	    NoEq -> Terms.get_prod Terms.try_no_var_id t2'
	  | x -> x)
          (* try_no_var has always been applied to t1' and t2' before, 
	     so I don't need to reapply it, I can use the identity instead *)
	with
	  NoEq ->
	    begin
	      match t1'.t_desc, t2'.t_desc with
		(FunApp(f1,l1), FunApp(f2,l2)) when
		(f1.f_options land Settings.fopt_COMPOS) != 0 && f1 == f2 -> 
		  simplify_term_rec dep_info simp_facts (Terms.make_and_list (List.map2 Terms.make_equal l1 l2))
	      | (Var(b1,l1), Var(b2,l2)) when
		(Terms.is_restr b1) &&
		(Proba.is_large_term t1' || Proba.is_large_term t2') && (b1 == b2) &&
		(Proba.add_elim_collisions b1 b1) ->
                  (* add_proba (Div(Cst 1, Card b1.btype)); * number applications *)
		  simplify_term_rec dep_info simp_facts (Terms.make_and_list (List.map2 Terms.make_equal l1 l2))
	      | _ ->
		  try
		    let _ = simplif_add dep_info simp_facts t' in
		    let t = 
		      match collision_test dep_info simp_facts t1' t2' with
			Some t' -> t'
		      | None -> t
		    in
		    apply_reds dep_info simp_facts t 
		  with Contradiction -> 
		    Terms.make_false()
	    end
	| (ACUN(prod, neut) | Group(prod, _, neut) | CommutGroup(prod, _, neut)) as eq_th -> 
	    begin
	      (* The argument of add_fact has always been simplified by Terms.apply_eq_reds 
		 So a xor appears only when there are at least 3 factors in total.
		 A commutative group product appears either when there are at least 3 factors,
		 or two factors on the same side of the equality without inverse.
		 A non-commutative group product may appear with two factors on one side and
		 none on the other, when there is no inverse.
		 In all cases, the simplifications FunApp/FunApp or Var/Var cannot be applied,
		 so we just try to apply dependency analysis, and orient the equation when it fails. *)
	      try
		let _ = simplif_add dep_info simp_facts t' in
		let t = 
		  let l1 = Terms.simp_prod simp_facts (ref false) prod t1' in
		  let l2 = Terms.simp_prod simp_facts (ref false) prod t2' in
		  let l1' = List.map (normalize simp_facts) l1 in
		  let l2' = List.map (normalize simp_facts) l2 in
		  (*print_string "simplify_term "; Display.display_term t;
		  print_string "\nfirst becomes "; Display.display_term (Terms.make_prod prod l1'); print_string " = "; Display.display_term (Terms.make_prod prod l2');
		  print_string "\nprod dep anal\n";*)
		  match prod_dep_anal eq_th dep_info simp_facts l1' l2' with
		    Some t' -> (* print_string "reduces into "; Display.display_term t';*) t'
		  | None -> (* print_string "no change\n";*) t
		in
		apply_reds dep_info simp_facts t 
	      with Contradiction -> 
		Terms.make_false()
	    end
	| _ -> Parsing_helper.internal_error "Expecting a group or xor theory in Facts.add_fact"
      end
  | FunApp(f, [t1;t2]) when f.f_cat == Diff ->
      let t1' = try_no_var simp_facts t1 in
      let t2' = try_no_var simp_facts t2 in
      begin
	match 
	  (match Terms.get_prod Terms.try_no_var_id t1' with 
	    NoEq -> Terms.get_prod Terms.try_no_var_id t2'
	  | x -> x)
          (* try_no_var has always been applied to t1' and t2' before, 
	     so I don't need to reapply it, I can use the identity instead *)
	with
	  NoEq ->
	    begin
	      match t1'.t_desc, t2'.t_desc with
		(FunApp(f1,l1), FunApp(f2,l2)) when
		(f1.f_options land Settings.fopt_COMPOS) != 0 && f1 == f2 -> 
		  simplify_term_rec dep_info simp_facts (Terms.make_or_list (List.map2 Terms.make_diff l1 l2))
		    
	      | (Var(b1,l1), Var(b2,l2)) when
		(Terms.is_restr b1) &&
		(Proba.is_large_term t1' || Proba.is_large_term t2') && (b1 == b2) &&
		(Proba.add_elim_collisions b1 b1) ->
                (* add_proba (Div(Cst 1, Card b1.btype)); * number applications *)
		  simplify_term_rec dep_info simp_facts (Terms.make_or_list (List.map2 Terms.make_diff l1 l2))
	      | _ -> 
		  try
		    let _ = simplif_add dep_info simp_facts (Terms.make_not t') in
		    let t = 
		      match collision_test dep_info simp_facts t1' t2' with
			Some t' -> Terms.make_not t'
		      | None -> t
		    in
		    apply_reds dep_info simp_facts t
		  with Contradiction -> 
		    Terms.make_true()
	    end
	| (ACUN(prod, neut) | Group(prod, _, neut) | CommutGroup(prod, _, neut)) as eq_th -> 
	    begin
	      (* The argument of add_fact has always been simplified by Terms.apply_eq_reds 
		 So a xor appears only when there are at least 3 factors in total.
		 A commutative group product appears either when there are at least 3 factors,
		 or two factors on the same side of the equality without inverse.
		 A non-commutative group product may appear with two factors on one side and
		 none on the other, when there is no inverse.
		 In all cases, the simplifications FunApp/FunApp or Var/Var cannot be applied,
		 so we just try to apply dependency analysis, and orient the equation when it fails. *)
	      try
		let _ = simplif_add dep_info simp_facts (Terms.make_not t') in
		let t = 
		  let l1 = Terms.simp_prod simp_facts (ref false) prod t1' in
		  let l2 = Terms.simp_prod simp_facts (ref false) prod t2' in
		  let l1' = List.map (normalize simp_facts) l1 in
		  let l2' = List.map (normalize simp_facts) l2 in
		  (*print_string "simplify_term "; Display.display_term t;
		  print_string "\nfirst becomes "; Display.display_term (Terms.make_prod prod l1'); print_string " <> "; Display.display_term (Terms.make_prod prod l2');
		  print_string "\nprod dep anal\n";*)
		  match prod_dep_anal eq_th dep_info simp_facts l1' l2' with
		    Some t' -> (* print_string "reduces into "; Display.display_term (Terms.make_not t');*) Terms.make_not t'
		  | None -> (* print_string "no change\n";*) t
		in
		apply_reds dep_info simp_facts t 
	      with Contradiction -> 
		Terms.make_true()
	    end
	| _ -> Parsing_helper.internal_error "Expecting a group or xor theory in Facts.add_fact"
      end
  | _ -> apply_reds dep_info simp_facts t

let rec simplify_bool_subterms dep_info simp_facts t =
  if t.t_type == Settings.t_bool then
    simplify_term_rec dep_info simp_facts t
  else
    match t.t_desc with
      FunApp(f,l) ->
	Terms.build_term2 t (FunApp(f, List.map (simplify_bool_subterms dep_info simp_facts) l))
    | _ -> t
	
let simplify_term dep_info simp_facts t = 
  let t' = apply_reds dep_info simp_facts t in
  simplify_bool_subterms dep_info simp_facts t'

(***** [check_equal t t' simp_facts], defined below, 
       shows that two terms [t] and [t'] are equal (up to negligible probability) *****
(see below for a more detailed interface)
*)

(* [apply_eq add_accu t equalities] applies the equalities of [equalities] 
   to the term [t], at the root or to the immediate subterms in case [t] is
   a product. Each equality is applied at most once.
   It calls the function [add_accu] on each obtained term. 

   [get_var_link_novar] is the [get_var_link] function used for matching
   inside [apply_eq]. It always returns [None] since nothing is considered
   as a variable in this matching: we just want equality of terms.

   [match_term_novar] is the [match_term] function used for matching
   inside [apply_eq]. It just tests equality, since nothing is considered
   as a variable in this matching.
*)
let get_var_link_novar t () = None

let match_term_novar next_f t t' () =
  if Terms.equal_terms t t' then next_f() else raise NoMatch

let apply_eq add_accu t equalities =
  List.iter (fun (left, right) ->
    match t.t_desc, left.t_desc with
      FunApp(f,[_;_]), _ when f.f_eq_theories != NoEq && f.f_eq_theories != Commut ->
      (* f is a binary function with an equational theory that is
	 not commutativity -> it is a product-like function *)
	let l = Terms.simp_prod Terms.simp_facts_id (ref false) f t in
	let l' = Terms.simp_prod Terms.simp_facts_id (ref false) f left in
	begin
	  match f.f_eq_theories with
	    NoEq | Commut -> Parsing_helper.internal_error "Facts.match_term_root_or_prod_subterm: cases NoEq, Commut should have been eliminated"
	  | AssocCommut | AssocCommutN _ | CommutGroup _ | ACUN _ ->
	    (* By commutativity, all possibilities will yield the same result, so we do not raise NoMatch
	       after finding a solution. *)
	      begin
		try 
		  Match_eq.match_AC match_term_novar get_var_link_novar Match_eq.default_match_error (fun rest () -> 
		    add_accu (Terms.make_prod f (right::rest))) Terms.simp_facts_id f true l l' ()
		with NoMatch -> ()
	      end
	  | Assoc | AssocN _ | Group _ -> 
	    (* Try all possibilities *)
	      begin
		try
		  Match_eq.match_assoc_subterm match_term_novar get_var_link_novar (fun rest_left rest_right () ->
		    add_accu (Terms.make_prod f (rest_left @ right::rest_right)); raise NoMatch) Terms.simp_facts_id f l l' ()
		with NoMatch -> ()
	      end
	end
    | _ ->
	if Terms.equal_terms t left then add_accu right
	    ) equalities

(* [apply_colls reduce_rec add_accu t colls] applies the collisions in
   [colls] to the term [t], at the root or in immediate subterms in case
   [t] is a product. Each collision is applied at most once. 
   It calls the function [add_accu] on each obtained term.
   *)

let apply_colls reduce_rec add_accu t colls = 
  try 
    apply_collisions_at_root_once reduce_rec no_dependency_anal Terms.simp_facts_id (fun t' -> add_accu t'; raise NoMatch) t colls
  with NoMatch -> ()
    
(* [simp_eq_diff add_accu t] applies a bunch of simplifications specific 
   to equalities to term [t].
   It calls the function [add_accu] on each obtained term. *)

let simp_eq_diff add_accu t = 
  match t.t_desc with
  | FunApp(f, [t1;t2]) when f.f_cat == Equal ->
      begin
      match (t1.t_desc, t2.t_desc) with
	(FunApp(f1,l1), FunApp(f2,l2)) when
	f1.f_cat == Tuple && f2.f_cat == Tuple && f1 != f2 -> 
	  add_accu (Terms.make_false())
      | (FunApp(f1,l1), FunApp(f2,l2)) when
	(f1.f_options land Settings.fopt_COMPOS) != 0 && f1 == f2 -> 
	  add_accu (Terms.make_and_list (List.map2 Terms.make_equal l1 l2))
      | (Var(b1,l1), Var(b2,l2)) when
	(Terms.is_restr b1) &&
	(Proba.is_large_term t1  || Proba.is_large_term t2) && (b1 == b2) &&
	(Proba.add_elim_collisions b1 b1) ->
	  add_accu (Terms.make_and_list (List.map2 Terms.make_equal l1 l2))
      | (Var(b1,l1), Var(b2,l2)) when
	(Terms.is_restr b1) && (Terms.is_restr b2) &&
	(Proba.is_large_term t1 || Proba.is_large_term t2) &&
	(b1 != b2) && (Proba.add_elim_collisions b1 b2)->
	  add_accu (Terms.make_false())
      | (FunApp(f1,[]), FunApp(f2,[]) ) when
	f1 != f2 && (!Settings.diff_constants) ->
	  add_accu (Terms.make_false())
	          (* Different constants are different *)
      |	_ -> ()
      end
  | FunApp(f, [t1;t2]) when f.f_cat == Diff ->
      begin
      match (t1.t_desc, t2.t_desc) with
	(FunApp(f1,l1), FunApp(f2,l2)) when
	f1.f_cat == Tuple && f2.f_cat == Tuple && f1 != f2 -> 
	  add_accu (Terms.make_true())
      | (FunApp(f1,l1), FunApp(f2,l2)) when
	(f1.f_options land Settings.fopt_COMPOS) != 0 && f1 == f2 -> 
	  add_accu (Terms.make_or_list (List.map2 Terms.make_diff l1 l2))
      | (Var(b1,l1), Var(b2,l2)) when
	(Terms.is_restr b1) &&
	(Proba.is_large_term t1  || Proba.is_large_term t2) && (b1 == b2) &&
	(Proba.add_elim_collisions b1 b1) ->
	  add_accu (Terms.make_or_list (List.map2 Terms.make_diff l1 l2))
      | (Var(b1,l1), Var(b2,l2)) when
	(Terms.is_restr b1) && (Terms.is_restr b2) &&
	(Proba.is_large_term t1 || Proba.is_large_term t2) &&
	(b1 != b2) && (Proba.add_elim_collisions b1 b2)->
	  add_accu (Terms.make_true())
      | (FunApp(f1,[]), FunApp(f2,[]) ) when
	f1 != f2 && (!Settings.diff_constants) ->
	  add_accu (Terms.make_true())
	          (* Different constants are different *)
      |	_ -> ()
      end
  | _ -> ()

(* [apply_eq_and_collisions_subterms_once reduce_rec equalities add_accu t] 
   applies the equalities coming from the equational theories, 
   the equality statements, the collisions given in the input 
   file, and the equalities given in [equalities] from left to right  
   to all subterms of [t]. It applies each equality once, and 
   calls the function [add_accu] on all terms generated by these equalities.
*)

let rec apply_eq_and_collisions_subterms_once reduce_rec equalities add_accu t = 
  let rec apply_list next_f seen = function
      [] -> ()
    | first::rest ->
	apply_eq_and_collisions_subterms_once reduce_rec equalities (fun t'' ->  
	  next_f (List.rev_append seen (t''::rest))
	    ) first;
        apply_list next_f (first::seen) rest
  in

  match t.t_desc with
    FunApp(f, [_;_]) when f.f_eq_theories != NoEq && f.f_eq_theories != Commut ->
      (* f is a binary function with an equational theory that is
	 not commutativity -> it is a product-like function *)
      (* We apply the statements only to subterms that are not products by f.
	 Subterms that are products by f are already handled above
	 using [match_term_root_or_prod_subterm]. *)
      apply_eq add_accu t equalities;
      apply_colls reduce_rec_impossible add_accu t f.f_statements;
      apply_colls reduce_rec add_accu t f.f_collisions;
      let l = Terms.simp_prod Terms.simp_facts_id (ref false) f t in
      apply_list (fun l' -> add_accu (Terms.make_prod f l')) [] l
  | FunApp(f, ([t1;t2] as l)) when f.f_cat == Equal || f.f_cat == Diff ->
      apply_eq add_accu t equalities;
      simp_eq_diff add_accu t;
      apply_colls reduce_rec_impossible add_accu t f.f_statements;
      apply_colls reduce_rec add_accu t f.f_collisions;
      begin
	match Terms.get_prod_list Terms.try_no_var_id l with
	  ACUN(xor, neut) ->
	    let t' = Terms.app xor [t1;t2] in
	    apply_eq_and_collisions_subterms_once reduce_rec equalities (fun t'' ->
	      match t''.t_desc with
		FunApp(xor', [t1';t2']) when xor' == xor ->
		  add_accu (Terms.build_term2 t (FunApp(f, [t1';t2'])))
	      |	_ -> 
		  add_accu (Terms.build_term2 t (FunApp(f, [t'';Terms.app neut []])))
		    ) t'
	| CommutGroup(prod, inv, neut) ->
	    let rebuild_term t'' = 
	      (* calls add_accu on a term equal to FunApp(f, [t'', neut]) *)
	      let l = Terms.simp_prod Terms.simp_facts_id (ref false) prod t'' in
	      let linv, lno_inv = List.partition (Terms.is_fun inv) l in
	      let linv_removed = List.map (function { t_desc = FunApp(f,[t]) } when f == inv -> t | _ -> assert false) linv in
	      add_accu (Terms.build_term2 t (FunApp(f, [ Terms.make_prod prod lno_inv; 
							 Terms.make_prod prod linv_removed ])))
	    in
	    apply_eq_and_collisions_subterms_once reduce_rec equalities rebuild_term (Terms.app prod [t1; Terms.app inv [t2]]);
	    (* Simplify the term t' = t2.t1^-1 just on the product level.
	       The simplification of smaller subterms has already been considered above. *)
	    let t' = Terms.app prod [t2; Terms.app inv [t1]] in
	    apply_eq rebuild_term t' equalities;
	    apply_colls reduce_rec_impossible rebuild_term t' prod.f_statements;
	    apply_colls reduce_rec rebuild_term t' prod.f_collisions
	| Group(prod, inv, neut) ->
	    let rebuild_term t'' =
		  (* calls add_accu on a term equal to FunApp(f, [t'', neut]) *)
		  let l = Terms.simp_prod Terms.simp_facts_id (ref false) prod t'' in
		  let (inv_first, rest) = first_inv inv l in
		  let (inv_last_rev, rest_rev) = first_inv inv (List.rev rest) in
		(* if inv_first = [x1...xk], inv_last_rev = [y1...yl],
		   List.rev rest_rev = [z1...zm]
		   then the term we want to rewrite is
		   x1^-1...xk^-1.z1...zm.yl^-1...y1^-1 = neut
		   which is equal to
		   z1...zm = xk...x1.y1...yl *)
		  add_accu (Terms.build_term2 t (FunApp(f, [ Terms.make_prod prod (List.rev rest_rev) ; 
							     Terms.make_prod prod (List.rev_append inv_first inv_last_rev)])))
	    in
	    let l1 = Terms.simp_prod Terms.simp_facts_id (ref false) prod (Terms.app prod [t1; Terms.app inv [t2]]) in
	    let l2 = Terms.remove_inverse_ends Terms.simp_facts_id (ref false) (prod, inv, neut) l1 in
	    let rec apply_up_to_roll seen' rest' =
	      let t' = Terms.make_prod prod (rest' @ (List.rev seen')) in
	      (* Simplify the term t' = t2.t1^-1 just on the product level.
	         The simplification of smaller subterms is considered below. *)
	      apply_eq rebuild_term t' equalities;
	      apply_colls reduce_rec_impossible rebuild_term t' prod.f_statements;
	      apply_colls reduce_rec rebuild_term t' prod.f_collisions;
	      match rest' with
		[] -> ()
	      | a::rest'' -> apply_up_to_roll (a::seen') rest''
	    in
	    apply_up_to_roll [] l2;
	    let l3 = List.rev (List.map (Terms.compute_inv Terms.try_no_var_id (ref false) (prod, inv, neut)) l2) in
	    apply_up_to_roll [] l3;
	    (* Simplify smaller subterms *)
	    let l1 = Terms.simp_prod Terms.simp_facts_id (ref false) prod t1 in
	    apply_list (fun l' -> add_accu (Terms.app f [Terms.make_prod prod l'; t2])) [] l1;
	    let l2 = Terms.simp_prod Terms.simp_facts_id (ref false) prod t2 in
	    apply_list (fun l' -> add_accu (Terms.app f [t1; Terms.make_prod prod l'])) [] l2
	| _ -> 
	    apply_list (fun l' -> add_accu (Terms.build_term2 t (FunApp(f, l')))) [] l
      end
  | FunApp(f, l) ->
      apply_eq add_accu t equalities;
      apply_colls reduce_rec_impossible add_accu t f.f_statements;
      apply_colls reduce_rec add_accu t f.f_collisions;
      apply_list (fun l' -> add_accu (Terms.build_term2 t (FunApp(f, l')))) [] l
	(* We use this function for rewriting terms in the manual transformation
	   "replace". LetEqual should never appear here. *)
  | Var(b,l) -> 
      apply_eq add_accu t equalities;
      apply_list (fun l' -> add_accu (Terms.build_term2 t (Var(b, l')))) [] l
  | _ -> ()

(*
NOTE: we might want to reimplement apply_eq_reds to add all possible 
rewrites instead of just one.
*)

let apply_eq_and_collisions_subterms_once reduce_rec equalities add_accu t =
  let t' = Terms.apply_eq_reds Terms.simp_facts_id reduced t in
  if !reduced then add_accu t'; 
  apply_eq_and_collisions_subterms_once reduce_rec equalities add_accu t

(* In the function [apply_eq_and_collisions_subterms_once], we apply
   the equalities that come from the game (stored in [equalities]) in
   both directions, but we apply the statements and collisions given
   in the input file only in the direction specified in the input
   file.
   To be able to apply them at least a bit in both directions, 
   we reduce both the initial term [t] and the desired replacement [t']
   by [apply_eq_and_collisions_subterms_once]. The function [test_equal]
   reduces [t'] and calls [test_equal_rewrite_left], which reduces [t].
*)

(* [test_equal_rewrite_left depth reduce_rec equalities seen_left_terms left_terms right_terms]
   is true when a term in [left_terms] can be rewritten into a term in [right_terms] in
   at most [depth] steps. 
   [seen_left_terms] are terms already seen on the left, which do not need to be
   considered any more. *)

let rec test_equal_rewrite_left depth reduce_rec equalities seen_left_terms left_terms right_terms =
  if List.exists (fun tleft ->
    List.exists (Terms.equal_terms tleft) right_terms) left_terms then true else
  if depth <= 0 then false else
  let seen_terms = left_terms @ seen_left_terms in
  let new_terms = ref [] in
  List.iter (apply_eq_and_collisions_subterms_once reduce_rec equalities (fun t' ->
    if (not (List.exists (Terms.equal_terms t') seen_terms)) &&
       (not (List.exists (Terms.equal_terms t') (!new_terms))) then
      new_terms := t' :: (!new_terms)
			   )) left_terms;
  test_equal_rewrite_left (depth-1) reduce_rec equalities seen_terms (!new_terms) right_terms

(* [test_equal depth reduce_rec equalities t right_terms seen_right_terms] is true when
   [t] is equal to a term in [right_terms] by at most [depth] rewriting steps. 
   [seen_right_terms] are terms already seen on the right, which do not need to be
   considered any more. *)

let rec test_equal depth reduce_rec equalities t right_terms seen_right_terms =
  if List.exists (fun tright ->
    test_equal_rewrite_left depth reduce_rec equalities [] [t] right_terms) right_terms then true else
  if depth <= 0 then false else
  let seen_terms = right_terms @ seen_right_terms in
  let new_terms = ref [] in
  List.iter (apply_eq_and_collisions_subterms_once reduce_rec equalities (fun t' ->
    if (not (List.exists (Terms.equal_terms t') seen_terms)) &&
       (not (List.exists (Terms.equal_terms t') (!new_terms))) then
      new_terms := t' :: (!new_terms)
			   )) right_terms;
  test_equal (depth-1) reduce_rec equalities t (!new_terms) seen_terms

(* [check_equal t t' simp_facts] returns true when [t] and [t'] are
   proved equal when the facts in [simp_facts] are true.
   It is called from transf_insert_replace.ml. The probability of collisions
   eliminated to reach that result is taken into account by module [Proba]. *)

let check_equal t t' simp_facts  =
    (Terms.simp_equal_terms simp_facts true t t') || 
    (Terms.simp_equal_terms simp_facts true (simplify_term no_dependency_anal simp_facts t) (simplify_term no_dependency_anal simp_facts t')) ||
    (let equalities = ref [] in
    let (subst, facts, elsefind) = simp_facts in
    List.iter (fun t ->
      match t.t_desc with
	FunApp(f,[t1;t2]) when f.f_cat == Equal || f.f_cat == LetEqual ->
	  equalities := (t1,t2) :: (t2,t1) :: (!equalities)
      |	FunApp(f,[t1;t2]) when f.f_cat == Diff -> 
	  equalities := (t, Terms.make_true()) :: (Terms.make_equal t1 t2, Terms.make_false()) :: 
	                (Terms.make_true(), t) :: (Terms.make_false(), Terms.make_equal t1 t2) :: (!equalities)
      |	_ -> 
	  equalities := (t, Terms.make_true()) :: (Terms.make_true(), t) :: (!equalities)
	) (subst @ facts);
    test_equal (!Settings.max_replace_depth) (reduce_rec simp_facts) (!equalities) t [t'] []
    )




(**** for debug: 
      [display_facts_at p occ] displays the facts that are known
      to hold at the program point (occurrence) [occ] of the process [p].

      [display_fact_pp] performs the actual display.
      The other functions look for the occurrence [occ] inside the
      process [p]. ***)

let display_fact_pp pp = 
  List.iter (fun f -> Display.display_term f; Display.print_newline()) 
    (get_facts_at pp)
  
let rec display_facts_at p occ =
  if p.i_occ = occ then
    display_fact_pp (DInputProcess p)
  else if (p.i_occ <= occ) && (occ <= p.i_max_occ) (* if occ is not in this interval, we know that it does not occur in p, so we do nothing *) then
    match p.i_desc with
        Nil -> ()
      | Par (q,q') -> display_facts_at q occ;display_facts_at q' occ
      | Repl (_,q) -> display_facts_at q occ
      | Input (_,_,p) -> display_facts_at_op p occ

and display_facts_at_op p occ =
  if p.p_occ = occ then
    display_fact_pp (DProcess p)
  else if (p.p_occ <= occ) && (occ <= p.p_max_occ) then
    match p.p_desc with
        Yield| EventAbort _ -> ()
      | Restr (_,p) -> display_facts_at_op p occ
      | Test (t,p,p') -> display_facts_at_t t occ;display_facts_at_op p occ;display_facts_at_op p' occ
      | Find (l,p,_) -> List.iter (fun (_,_,t,p) -> 
	  display_facts_at_t t occ;
	  display_facts_at_op p occ) l; display_facts_at_op p occ
      | Output ((_,tl),t,q) -> List.iter (fun t -> display_facts_at_t t occ) tl;display_facts_at_t t occ;display_facts_at q occ
      | Let (pat,t,p,p') -> display_facts_at_pat pat occ;display_facts_at_t t occ;display_facts_at_op p occ;display_facts_at_op p' occ
      | EventP (t,p) -> display_facts_at_t t occ;display_facts_at_op p occ
      | Insert (_,_,_) | Get (_,_,_,_,_) -> Parsing_helper.internal_error "Get/Insert should not appear at this point"

and display_facts_at_t t occ =
  if t.t_occ = occ then
    display_fact_pp (DTerm t)
  else if (t.t_occ <= occ) && (occ <= t.t_max_occ) then
    match t.t_desc with
        Var (_,tl) -> List.iter (fun t -> display_facts_at_t t occ) tl
      | ReplIndex _ -> ()
      | FunApp (_,tl) -> List.iter (fun t -> display_facts_at_t t occ) tl
      | TestE (t1,t2,t3) -> display_facts_at_t t1 occ;display_facts_at_t t2 occ;display_facts_at_t t3 occ
      | FindE (l,t,_) -> List.iter (fun (_,_,t1,t2) -> 
	  display_facts_at_t t1 occ;
	  display_facts_at_t t2 occ) l; display_facts_at_t t occ
      | LetE (pat,t1,t2,topt) -> display_facts_at_pat pat occ;display_facts_at_t t1 occ;display_facts_at_t t2 occ;(match topt with Some t -> display_facts_at_t t occ| None -> ())
      | ResE (_,t) -> display_facts_at_t t occ
      | EventAbortE f -> ()
      | EventE (t,p) -> display_facts_at_t t occ;display_facts_at_t p occ
      | InsertE (_,_,_) | GetE (_,_,_,_,_) -> Parsing_helper.internal_error "Get/Insert should not appear at this point"

and display_facts_at_pat pat occ =
  match pat with
      PatVar _ -> ()
    | PatTuple (_,pl) -> List.iter (fun pat -> display_facts_at_pat pat occ) pl
    | PatEqual t -> display_facts_at_t t occ



