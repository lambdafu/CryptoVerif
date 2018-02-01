open Types

let whole_game = ref Nil
let game_number = ref (-1)
let array_ref = ref None
let array_ref_def = ref None

let success_check_all_deps = ref [] 
let failure_check_all_deps = ref []
let mem_has_real_uses = ref []

(* Store the difference of probabilities coming from the elimination
   of collisions *)

let proba = ref Zero

let mul(x,y) =
  match x,y with
    Zero, _ | _, Zero | Cst 0.0, _ | _, Cst 0.0 -> Zero
  | Cst 1.0, a -> a
  | a, Cst 1.0 -> a
  | _ -> Mul(x,y)

let rec prod = function
  [] -> Cst 1.0
| [a] -> a
| (a::l) -> mul(a, prod l)

let add(x,y) =
  match x,y with
    Zero, a | a, Zero | Cst 0.0, a | a, Cst 0.0 -> a
  | _ -> Add(x,y)
  
let rec sum = function
  [] -> Zero
| [a] -> a
| (a::l) -> add(a, sum l)

let add_proba p =
  if !proba == Zero then proba := p else proba := add(!proba, p)

let card t =
match t.tcat with
  Interv p -> Count(p)
| _ -> Card(t)

let card_index b =
  prod (List.map (fun t -> card t.t_type) b.args_at_creation)

(* An element (b1,b2) in eliminated_collisions or 
already_counted_eliminated_collisions means that we have used the fact
that collisions between b1 and b2 have negligible probability.
It is in already_counted_eliminated_collisions when the probability of
collision between b1 and b2 has been counted in a previous simplification,
so does not need to be counted again. *)

let already_counted_eliminated_collisions = ref []
let eliminated_collisions = ref [] 

let add_elim_collisions b1 b2 =
  let equal (b1',b2') =
           ((b1 == b1') && (b2 == b2')) ||
           ((b1 == b2') && (b2 == b1'))
  in
  if not ((List.exists equal (!eliminated_collisions)) ||
          (List.exists equal (!already_counted_eliminated_collisions))) then
    eliminated_collisions := (b1, b2) :: (!eliminated_collisions)

let proba_for_collision b1 b2 =
  print_string "Eliminated collisions between ";
  Display.display_binder b1;
  print_string " and ";
  Display.display_binder b2;
  print_string " Probability: ";
  let p = 
    if b1 == b2 then
      mul(Cst 0.5,Div(mul(card_index b1, card_index b1), card b1.btype))
    else
      begin
        if b1.btype != b2.btype then
          Parsing_helper.internal_error "Collision between different types";
        Div(mul(card_index b1, card_index b2), card(b1.btype))
      end
  in
  Display.display_proba 0 p;
  print_newline();
  p

(* An element (t1, t2, b, lopt, T) in term_collisions means that
the equality t1 = t2 was considered impossible; it has
negligible probability because t1 depends on b[lopt] by decompos followed
by compos functions, the types T are the types obtained after applying
the decompos functions (they are large types), and t2 does not depend 
on b *)

let term_collisions = ref []
(* mapping from terms to fresh repl indexes *)
let repl_index_list = ref []

let any_term_name = "?"
let any_term_binder t = 
  let b' = { sname = any_term_name;
	     vname = 0;
	     btype = t;
	     args_at_creation = [];
	     def = [];
	     compatible = Terms.compatible_empty;
	     link = NoLink }
  in
  let rec node = { above_node = node;
		   binders = [b'];
		   true_facts_at_def = [];
		   def_vars_at_def = [];
		   future_binders = []; future_true_facts = [];
		   future_def_vars = [];
		   definition = DNone }
  in
  b'.def <- [node];
  b'

let any_term t = Terms.term_from_binder (any_term_binder t.t_type)

let any_term_pat pat = 
  let t = match pat with
    PatVar b -> b.btype
  | PatTuple(f,_) -> snd f.f_type
  | PatEqual t -> t.t_type
  in
  Terms.term_from_binder (any_term_binder t)

exception NoMatch

let rec match_term2 next_f t t' = 
  match t.t_desc, t'.t_desc with
    Var (v,[]), _ when v.sname==any_term_name -> next_f()
  | Var (v,[]), _ when Terms.is_repl v -> 
    (* Check that types match *)
      if t'.t_type != v.btype then
	raise NoMatch;
      begin
	match v.link with
	  NoLink -> Terms.link v (TLink t')
	| TLink t -> if not (Terms.equal_terms t t') then raise NoMatch;
      end;
      next_f()
  | Var(b,l), Var(b',l') when b == b' -> 
      match_term_list2 next_f l l'
  | FunApp(f,[t1;t2]), FunApp(f',[t1';t2']) when f.f_options land Settings.fopt_COMMUT != 0 && f == f' ->
      (* Commutative function symbols *)
      begin
        try
          Terms.auto_cleanup (fun () ->
	    match_term2 (fun () -> match_term2 next_f t2 t2') t1 t1')
        with NoMatch ->
          match_term2 (fun () -> match_term2 next_f t2 t1') t1 t2'
      end
  | FunApp(f,l), FunApp(f',l') when f == f' ->
      match_term_list2 next_f l l'
  | _ -> raise NoMatch

and match_term_list2 next_f l l' = 
  match l,l' with
    [],[] -> next_f()
  | a::l,a'::l' ->
      match_term2 (fun () -> match_term_list2 next_f l l') a a'
  | _ -> Parsing_helper.internal_error "Different lengths in match_term_list"

let matches t1 t2 t1' t2' =
  try
    Terms.auto_cleanup (fun () ->
      match_term2 (fun () -> match_term2 (fun () -> ()) t2 t2') t1 t1');
    true
  with NoMatch -> false

let add_term_collisions t1 t2 b lopt t =
    (* I remove an entry when another entry is an instance of it,
       obtained by substituting terms for replication indexes *)
  if not (List.exists (fun (t1',t2',b',lopt',t') -> matches t1' t2' t1 t2) (!term_collisions)) then
    term_collisions := (t1,t2,b,lopt,t) :: (List.filter (fun (t1',t2',b',lopt',t') ->  not (matches t1 t2 t1' t2')) (!term_collisions))

let rec collect_array_indexes accu t =
  match t.t_desc with
    Var(b,[]) when Terms.is_repl b ->
	if not (List.memq b (!accu)) then
	  accu := b:: (!accu)
  | Var(b,l) -> List.iter (collect_array_indexes accu) l
  | FunApp(f,l) -> List.iter (collect_array_indexes accu) l
  | _ -> Parsing_helper.internal_error "If/let/find unexpected in collect_array_indexes"

let proba_for_term_collision t1 t2 b lopt tl =
  print_string "Eliminated collisions between ";
  Display.display_term [] t1;
  print_string " and ";
  Display.display_term [] t2;
  print_string " Probability: ";  
  let accu = ref [] in
  collect_array_indexes accu t2;
  collect_array_indexes accu t1;
  let nindex = prod (List.map (fun array_idx -> card array_idx.btype) (!accu))
(*
  collect_array_indexes accu t2;
  let nindex = 
    match lopt with
      Some l -> 
	List.iter (collect_array_indexes accu) l;
	prod (List.map (fun array_idx -> card array_idx.btype) (!accu))
    | None -> 
	(* I check in DepAnal1 that the indexes of b do not depend on b.
	   I take the smallest of (indexes of t1 or t2) and (indexes of b * indexes of t2) *)
	let v1 = mul(card_index b, prod (List.map (fun array_idx -> card array_idx.btype) (!accu)))  in
	let l1 = List.length b.args_at_creation + List.length (!accu) in
	collect_array_indexes accu t1;
	let l2 = List.length !accu in
	if l1 <= l2 then
	  v1
	else
	  prod (List.map (fun array_idx -> card array_idx.btype) (!accu))
*)
  in
  let p = 
    match tl with
      [t] -> Div(nindex, card t)
    | _ -> mul(nindex ,sum (List.map (fun t -> Div(Cst 1.0, card t)) tl))
  in
  Display.display_proba 0 p;
  print_newline();
  print_string "(";
  Display.display_term [] t1;
  print_string " characterizes a part of ";
  begin
  match lopt with
    None ->   Display.display_binder b; print_string "[...]"
  | Some l -> Display.display_var [] b l 
  end;
  print_string " of type(s) ";
  Display.display_list (fun t -> print_string t.tname) tl;
  print_string ";\n ";
  Display.display_term [] t2;
  print_string " does not depend on ";
  begin
  match lopt with
    None ->   Display.display_binder b; print_string "[...]"
  | Some l -> Display.display_var [] b l 
  end;
  print_string ")\n";
  p
  

(* An element (t1,t2,proba,tl) in red_proba means that t1 has been reduced
to t2 using a probabilistic reduction rule, and that the restrictions
in this rule are mapped according to list tl

I have a small doubt here on when exactly we can avoid counting several times
the same elimination of collisions in different games. I do it when the
probability does not depend on the runtime of the game. Would that be ok
even if it depends on it? *)

let already_counted_red_proba = ref []
let red_proba = ref []

let rec instan_time = function
    AttTime -> Add(AttTime, Time (!game_number, Cryptotransf.compute_runtime_for (!game_number) (!whole_game)))
  | Time _ -> Parsing_helper.internal_error "unexpected time"
  | (Cst _ | Count _ | Zero | Card _ | TypeMaxlength _) as x -> x
  | Proba(p,l) -> Proba(p, List.map instan_time l)
  | ActTime(f,l) -> ActTime(f, List.map instan_time l)
  | Maxlength(n,t) -> Maxlength(!game_number, Terms.copy_term t) (* When add_proba_red is called, the variables in the reduction rule are linked to their corresponding term *)
  | Length(f,l) -> Length(f, List.map instan_time l)
  | Mul(x,y) -> Mul(instan_time x, instan_time y)
  | Add(x,y) -> Add(instan_time x, instan_time y)
  | Sub(x,y) -> Sub(instan_time x, instan_time y)
  | Div(x,y) -> Div(instan_time x, instan_time y)
  | Max(l) -> Max(List.map instan_time l)

let add_proba_red t1 t2 proba tl =
  let proba = instan_time proba in
  let equal (t1',t2',proba',tl') =
     (Terms.equal_terms t1 t1') && (Terms.equal_terms t2 t2') && (proba = proba')
  in
  if not ((List.exists equal (!red_proba)) ||
          (List.exists equal (!already_counted_red_proba))) then
    red_proba := (t1,t2,proba,tl) :: (!red_proba)

let proba_for_red_proba t1 t2 proba tl =
  print_string "Reduced ";
  Display.display_term [] t1;
  print_string " to ";
  Display.display_term [] t2;
  print_string " Probability: ";  
  let accu = ref [] in
  List.iter (fun (_,t) -> collect_array_indexes accu t) tl;
  let p = mul(proba, prod (List.map (fun array_idx -> card array_idx.btype) (!accu))) in
  Display.display_proba 0 p;
  print_newline();
  p

(* Initialization of probability counting *)  

let partial_reset process = 
  whole_game := process;
  array_ref := None;
  array_ref_def := None;
  success_check_all_deps := [];
  failure_check_all_deps := [];
  mem_has_real_uses := []

let reset (ac_coll, ac_red_proba) gn process =
  partial_reset process;
  proba := Zero;
  game_number := gn;
  eliminated_collisions := [];
  already_counted_eliminated_collisions := ac_coll;
  term_collisions := [];
  repl_index_list := [];
  red_proba := [];
  already_counted_red_proba := ac_red_proba

(* Final addition of probabilities *)

let final_add_proba() =
  List.iter (fun (b1,b2) -> add_proba (proba_for_collision b1 b2))
    (!eliminated_collisions);
  List.iter (fun (t1,t2,b,lopt,t) -> add_proba (proba_for_term_collision t1 t2 b lopt t))
    (!term_collisions);
  List.iter (fun (t1,t2,proba,tl) -> add_proba (proba_for_red_proba t1 t2 proba tl))
    (!red_proba);
  let r = !proba in
  proba := Zero;
  Polynom.polynom_to_probaf (Polynom.probaf_to_polynom r)

(* Array references? *)

let has_array_ref b =
  match !array_ref, !array_ref_def with
    None, None ->
      let array_ref_tmp = ref [] in
      let array_ref_def_tmp = ref [] in
      Terms.array_ref_process [] array_ref_def_tmp array_ref_tmp (!whole_game);
      array_ref := Some (!array_ref_tmp);
      array_ref_def := Some (!array_ref_def_tmp);
      (List.memq b (!array_ref_tmp)) || (List.memq b (!array_ref_def_tmp))
  | Some array_ref_tmp, Some array_ref_def_tmp ->
      (List.memq b array_ref_tmp) || (List.memq b array_ref_def_tmp)
  | _ -> Parsing_helper.internal_error "Simplify.has_array_ref"

(* On demand substitutions 

let try_no_var (subst, facts) t =
   when t is FunApp(_), return t itself.
   when t is Var(_), try applying substitutions until t becomes FunApp(_)
   if impossible, return t itself.

   It may be necessary to apply subtitutions to strict subterms of t
   in order to be able to apply another substitution to t itself.

   Apply on demand substitution when 
   - a matching for a reduction rule meets a variable when
   it expects a function symbol
   - unification called when we have an inequality meets a 
   different variable on both sides 
   - we have a variable in a boolean formula (x && ...), ...
   - equality between a variable and a variable or a tuple
   - let (...) = x[...] substitute x

Substitutions map variables x[...] to some term.

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


(* Applying a substitution that maps x[M1,...,Mn] to M' *)

let reduced_subst = ref false

let rec apply_subst1 t tsubst =
(*  match t.t_desc with
    FunApp(f,l) -> t
  | _ -> *)
     match tsubst.t_desc with
       FunApp(f,[redl;redr]) when f.f_cat == Equal || f.f_cat == LetEqual ->
         begin
           if Terms.equal_terms t redl then 
	     begin
	       reduced_subst := true;
	       redr
	     end
           else
             match t.t_desc with
               Var(b,l) ->
	         { t_desc = Var(b, List.map (fun t' -> apply_subst1 t' tsubst) l);
	           t_type = t.t_type;
	           t_occ = t.t_occ;
		   t_loc = t.t_loc }
             | FunApp(f,l) when f.f_cat != Equal && f.f_cat != LetEqual ->
	         { t_desc = FunApp(f, List.map (fun t' -> apply_subst1 t' tsubst) l);
	           t_type = t.t_type;
	           t_occ = t.t_occ;
		   t_loc = t.t_loc } 
             | _ -> t
         end
     | _ -> Parsing_helper.internal_error "substitutions should be Equal or LetEqual terms"

let rec apply_all_subst t = function
    [] -> t
  | (a::l) ->
      let t' = apply_subst1 t a in
      if !reduced_subst then t' else apply_all_subst t l

let rec try_no_var ((subst2, _, _) as simp_facts) t =
(*  print_string "try_no_var ";
  Display.display_term [] t;
  print_newline();*)
  match t.t_desc with
    FunApp(_,_) (*-> t*)
  | Var(_,_) -> 
      reduced_subst := false;
      let t' = apply_all_subst t subst2 in
      if !reduced_subst then 
	try_no_var simp_facts t' 
      else
	t
  | TestE _ | FindE _ | LetE _ | ResE _ -> 
      Parsing_helper.internal_error "If, find, let, and new should not occur in try_no_var"

(* unify_terms tests equality between t and t', modulo rewrite rules in 
   simp_facts
   Returns the common form when they are equal;
   raises NoMatch otherwise.  *)

let rec unify_terms simp_facts t t' =
  (* print_string "Trying to unify "; Display.display_term [] t; print_string " and "; Display.display_term [] t'; print_newline(); *)
  match t.t_desc,t'.t_desc with
    ((TestE _ | FindE _ | LetE _ | ResE _), _)
  | (_, (TestE _ | FindE _ | LetE _ | ResE _)) ->
      Parsing_helper.internal_error "If, find, let, and new should not occur in unify_terms"
  | (Var(b,l), Var(b',l')) when Terms.equal_terms t t' -> t
  | _ ->
      let t1 = try_no_var simp_facts t in
      let t1' = try_no_var simp_facts t' in
      match (t1.t_desc, t1'.t_desc) with
	Var(b,l), Var(b',l') -> if Terms.equal_terms t1 t1' then t1 else raise NoMatch
      | FunApp(f,[t1;t2]), FunApp(f',[t1';t2']) when f == f' && f.f_options land Settings.fopt_COMMUT != 0 ->
          (* Commutative function symbols *)
          begin
          try
            { t_desc = FunApp(f, [unify_terms simp_facts t1 t1';
                                  unify_terms simp_facts t2 t2']);
              t_type = t.t_type;
              t_occ = t.t_occ;
	      t_loc = Parsing_helper.dummy_ext }
          with NoMatch ->
            { t_desc = FunApp(f, [unify_terms simp_facts t1 t2';
                                  unify_terms simp_facts t2 t1']);
              t_type = t.t_type;
              t_occ = t.t_occ;
	      t_loc = Parsing_helper.dummy_ext }
          end
      |	FunApp(f,l), FunApp(f',l') when f == f' ->
	  { t_desc = FunApp(f, List.map2 (unify_terms simp_facts) l l');
            t_type = t.t_type;
            t_occ = t.t_occ;
	    t_loc = Parsing_helper.dummy_ext }
      |	_ -> raise NoMatch


(* simp_equal_terms tests equality between t1 and t2, modulo rewrite rules in 
   simp_facts. Returns true when equal, false otherwise.  *)

let simp_equal_terms simp_facts t1 t2 =
  try 
    ignore(unify_terms simp_facts t1 t2); 
    true 
  with NoMatch -> 
    false

(* Apply reduction rules defined by statements to term t *)

let rec match_term next_f simp_facts restr t t' = 
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
	    v.link <- TLink (unify_terms simp_facts t t')
      end;
      next_f()
  | FunApp(f,[t1;t2]) when f.f_options land Settings.fopt_COMMUT != 0 ->
      (* Commutative function symbols *)
      begin
	match (try_no_var simp_facts t').t_desc with
	  FunApp(f',[t1';t2']) when f == f' ->
            begin
              try
                Terms.auto_cleanup (fun () ->
	          match_term (fun () -> match_term next_f simp_facts restr t2 t2') simp_facts restr t1 t1')
              with NoMatch ->
                match_term (fun () -> match_term next_f simp_facts restr t2 t1') simp_facts restr t1 t2'
            end
	| _ -> raise NoMatch
      end
  | FunApp(f,l) ->
      begin
	match (try_no_var simp_facts t').t_desc with
	  FunApp(f',l') when f == f' ->
	    match_term_list next_f simp_facts restr l l'
	| _ -> raise NoMatch
      end
  | Var _ | TestE _ | FindE _ | LetE _ | ResE _ ->
      Parsing_helper.internal_error "Var with arguments, if, find, let, and new should not occur in match_term"

and match_term_list next_f simp_facts restr l l' = 
  match l,l' with
    [],[] -> next_f()
  | a::l,a'::l' ->
      match_term (fun () -> match_term_list next_f simp_facts restr l l') 
	simp_facts restr a a'
  | _ -> Parsing_helper.internal_error "Different lengths in match_term_list"

let reduced = ref false

(* Display facts; for debugging *)

let display_facts (subst2, facts, elsefind) =
  print_string "Substitutions:\n";
  List.iter (fun t -> Display.display_term [] t; print_newline()) subst2;
  print_string "Facts:\n";
  List.iter (fun t -> Display.display_term [] t; print_newline()) facts;
  print_string "Elsefind:\n";
  List.iter (fun (bl, def_list, otheruses_list, t) ->
    print_string "for all ";
    Display.display_list Display.display_binder bl;
    print_string "; not(defined(";
    Display.display_list (fun (b,l) -> Display.display_var [] b l) def_list;
    print_string ") && ";
    Display.display_term [] t;
    print_string ")";
    print_newline()
    ) elsefind


(* apply_not_red implements reduction rules 
     not (x = y) -> x != y
     not (x != y) -> x = y
     x = x -> true
     x != x -> false
(These rules cannot be stored in file default, because there are several
functions for = and for !=, one for each type.)
*)

let rec apply_not_red simp_facts t =
  match t.t_desc with
    FunApp(fnot, [t']) when fnot == Settings.f_not ->
      begin
      let t' = try_no_var simp_facts t' in
      match t'.t_desc with
	FunApp(feq, [t1;t2]) when feq.f_cat == Equal ->
	  reduced := true;
	  Terms.make_diff t1 t2
      |	FunApp(fdiff, [t1;t2]) when fdiff.f_cat == Diff ->
	  reduced := true;
	  Terms.make_equal t1 t2
      |	_ -> Terms.make_not (apply_not_red simp_facts t')
      end
  | FunApp(f,[t1;t2]) when f.f_cat == Equal && (simp_equal_terms simp_facts t1 t2) ->
      reduced := true;
      Terms.make_true()
  | FunApp(f,[t1;t2]) when f.f_cat == Diff && (simp_equal_terms simp_facts t1 t2) ->
      reduced := true;
      Terms.make_false()
  | FunApp(f,[t1;t2]) when f == Settings.f_and ->
      Terms.make_and (apply_not_red simp_facts t1) (apply_not_red simp_facts t2)
  | FunApp(f,[t1;t2]) when f == Settings.f_or ->
      Terms.make_or (apply_not_red simp_facts t1) (apply_not_red simp_facts t2)
  | FunApp(f,l) ->
    { t_desc = FunApp(f, List.map (apply_not_red simp_facts) l);
      t_type = t.t_type;
      t_occ = t.t_occ;
      t_loc = Parsing_helper.dummy_ext }
  | _ -> t

let rec apply_red simp_facts t (restr,proba,redl,redr) =
(*  print_string "apply_red ";
  Display.display_term [] redl;
  print_string " -> ";
  Display.display_term [] redr;
  print_string " to ";
  Display.display_term [] t;
  print_newline();
  print_string " knowing\n";
  display_facts simp_facts;
  print_newline();*)
  match t.t_desc with
    FunApp(f,l) ->
      begin
	try
	  match_term (fun () -> 
	    let t' = Terms.copy_term redr in
	    if proba != Zero then
	      begin
              (* Instead of storing the term t, I store the term obtained 
                 after the applications of try_no_var in match_term,
                 obtained by (Terms.copy_term redl) *)
		add_proba_red (Terms.copy_term redl) t' proba (List.map (fun restr1 ->
		  match restr1.link with
		    TLink trestr -> (restr1,trestr)
		  | _ -> Parsing_helper.internal_error "unexpected link in apply_red") restr)
	      end;
	    Terms.cleanup();
	    reduced := true;
	    t'
	      ) simp_facts restr redl t
	with NoMatch ->
	  Terms.cleanup();
	  { t_desc = FunApp(f, List.map (fun t' -> apply_red simp_facts t' (restr, proba, redl, redr)) l);
	    t_type = t.t_type;
	    t_occ = t.t_occ;
	    t_loc = Parsing_helper.dummy_ext }
      end
  | _ -> t

let apply_statement simp_facts t (vl,t_state) =
  match t_state.t_desc with
    FunApp(f, [t1;t2]) when f.f_cat == Equal ->
      apply_red simp_facts t ([],Zero,t1,t2)
  | FunApp(f, [t1;t2]) when f.f_cat == Diff ->
      apply_red simp_facts (apply_red simp_facts t 
	([],Zero,t_state, Terms.make_true())) 
	([],Zero,Terms.make_equal t1 t2, Terms.make_false())
  | _ -> apply_red simp_facts t ([],Zero,t_state, Terms.make_true())

let rec apply_all_red simp_facts t = function
    [] -> 
(*      print_string "Doing not red"; print_newline();*)
      let t' = apply_not_red simp_facts t in
      if !reduced then t' else t
  | (((a1,a2) as a)::l) ->
(*      print_string "Apply statement ";
      Display.display_term [] a2;
      print_newline();*)
      let t' = apply_statement simp_facts t a in
      if !reduced then t' else apply_all_red simp_facts t l

let apply_collision simp_facts t (restr, forall, t1, proba, t2) =
  apply_red simp_facts t (restr,proba,t1,t2)

let rec apply_all_coll simp_facts t = function
    [] -> t
  | (a::l) ->
      let t' = apply_collision simp_facts t a in
      if !reduced then t' else apply_all_coll simp_facts t l

let apply_statements_and_collisions simp_facts t =
(*  print_string "starting apply_statements_and_collisions\n";
  Display.display_term [] t;
  print_string " knowing\n";
  display_facts simp_facts;*)
  let t' = apply_all_red simp_facts t (!Transform.statements) in
(*  print_string "in apply_statements_and_collisions";
  print_newline();*)
  if !reduced then t' else
  apply_all_coll simp_facts t (!Transform.collisions) 

let rec apply_reds simp_facts t =
  reduced := false;
  let t' = apply_statements_and_collisions simp_facts t in
  if !reduced then 
    apply_reds simp_facts t' 
  else
    t

(* Compute the list of variables that must be defined at a certain
point, taking into account defined conditions of find *)

exception Contradiction

let rec intersect_list eqtest = function
    [] -> raise Contradiction
  | [a] -> a
  | (a::l) -> Terms.intersect eqtest a (intersect_list eqtest l)

let rec check_non_nested seen_fsymb seen_binders t =
  match t.t_desc with
    Var(b,l) ->
      (not (List.memq b seen_binders)) &&
      (List.for_all (check_non_nested seen_fsymb (b::seen_binders)) l)
  | FunApp(f,l) ->
      (not (List.memq f seen_fsymb)) &&
      (List.for_all (check_non_nested (f::seen_fsymb) seen_binders) l)
  | _ -> Parsing_helper.internal_error "If, find, let should have been expanded"

(* Get the node at which the find indices of a find are defined.
   This is the node at which the definition requirements in the "defined" condition
   are checked. *)
let get_node_for_find_branch def_node_opt bl =
  match def_node_opt with
    None -> None
  | Some n -> 
      match bl with
	[] -> Some n
      |	(b::_) -> 
	  try
	    Some (List.find (fun n' -> n'.above_node == n) b.def)
	  with Not_found ->
	    Parsing_helper.internal_error "Could not find defining node for find index"

(* is_reachable n n' returns true when n is reachable from n' *)
let rec is_reachable n n' =
  if n == n' then true else
  if n'.above_node == n' then false else
  is_reachable n n'.above_node

let rec close_node accu n =
  List.iter (fun b' ->
    accu := ((b',b'.args_at_creation))::(!accu)
      ) n.binders;
  if n.above_node != n then
    close_node accu n.above_node

let get_def_vars_above n =
  let accu = ref [] in
  close_node accu n; 
  !accu

(* Take into account variables that must be defined because a block of code
   is always executed until the next output/yield before passing control to
   another block of code *)
let def_vars_from_node current_node_opt n =
  match current_node_opt with
    Some current_node ->
      if is_reachable n current_node then
	Terms.intersect Terms.equal_binderref (n.future_def_vars @ n.def_vars_at_def) current_node.def_vars_at_def
      else
	n.future_def_vars @ n.def_vars_at_def
  | None -> n.def_vars_at_def

(* Take into account variables that must be defined because a block of code
   is always executed until the next output/yield before passing control to
   another block of code *)
let get_def_vars_above2 current_node_opt n =
  match current_node_opt with
    Some current_node ->
      if is_reachable n current_node then
	Terms.intersect Terms.equal_binderref 
	  ((List.map (fun b -> (b, b.args_at_creation)) n.future_binders) @ 
	   (get_def_vars_above n))
	  (get_def_vars_above current_node)
      else
	(List.map (fun b -> (b, b.args_at_creation)) n.future_binders) @ 
	(get_def_vars_above n)
  | None -> get_def_vars_above n

(* Remove variables that are certainly defined from a def_list in a find *)
let reduced_def_list def_node_opt def_list =
  match def_node_opt with
    Some def_node ->
      Terms.setminus_binderref def_list (get_def_vars_above def_node)
  | None -> def_list

(* More precise solution, but must not be used to remove elements
of def_list, just to test whether all elements of def_list are defined,
in which case for a "find ... defined(def_list) && M", if M is true,
the else branch can be removed. -- Useful to remove the "else" branches
generated by applying the security of a Diffie-Hellman key agreement,
for example. 
Removing useful elements of def_list breaks the code of SArename *)

let rec add_def_vars current_node def_vars_accu seen_refs (b,l) =
  if (List.for_all (check_non_nested [] [b]) l) &&
    (not (Terms.mem_binderref (b,l) (!seen_refs))) then
    begin
      seen_refs := (b,l) :: (!seen_refs);
      let def_vars_above_def = intersect_list Terms.equal_binderref (List.map (get_def_vars_above2 current_node) b.def) in
      let def_vars_at_def = intersect_list Terms.equal_binderref (List.map (def_vars_from_node current_node) b.def) in
      (* b.args_at_creation -> l *)
      let def_vars_above_def = (b,l)::(List.map (fun (b',l') ->
	(b', List.map (Terms.subst (List.map Terms.binder_from_term b.args_at_creation) l) l')) def_vars_above_def)
      in
      let def_vars_at_def = List.map (fun (b',l') ->
	(b', List.map (Terms.subst (List.map Terms.binder_from_term b.args_at_creation) l) l')) def_vars_at_def 
      in
      (* add facts *)
      List.iter (fun br -> 
	Terms.add_binderref br def_vars_accu) def_vars_above_def;
      (* recursive call *)
      List.iter (add_def_vars current_node def_vars_accu seen_refs) def_vars_at_def
    end

let get_def_vars_at nopt =
  match nopt with
    Some n ->
      let def_vars_accu = ref (get_def_vars_above n) in
      let seen_refs = ref [] in
      List.iter (add_def_vars nopt def_vars_accu seen_refs) n.def_vars_at_def;
      Some (!def_vars_accu)
  | None -> None


(* Return variables defined above the process p that defines variable b.
   The variables defined by p itself are excluded. *)
let get_def_vars_at_proc p b =
  let node = 
    List.find (fun n -> match n.definition with
      DProcess p' -> p' == p 
    | _ -> false) b.def
  in
  let n = node.above_node in
  let def_vars_accu = ref (get_def_vars_above n) in
  let seen_refs = ref [] in
  List.iter (add_def_vars (Some n) def_vars_accu seen_refs) n.def_vars_at_def;
  !def_vars_accu

(* Dependency analysis
   When M1 characterizes a part of x of a large type T
   and M2 does not depend on x, then M1 = M2 fails up to
   negligible probability.
   The module FindCompos defines "characterize"
   The modules DepAnal1 and DepAnal2 perform dependency analyses
   Function dependency_collision concludes *)

let repl_index_counter = ref 0

let new_repl_index_term t =
  let rec find_repl_index = function
      [] ->
	incr repl_index_counter;
	let b' = { sname = "!2";
		   vname = !repl_index_counter;
		   btype = t.t_type;
		   args_at_creation = [];
		   def = [];
		   compatible = Terms.compatible_empty;
		   link = NoLink }
	in
	let rec node = { above_node = node;
			 binders = [b'];
			 true_facts_at_def = [];
			 def_vars_at_def = [];
			 future_binders = []; future_true_facts = [];
			 future_def_vars = [];
			 definition = DFunRepl }
	in
	b'.def <- [node];
	repl_index_list := (t,b') :: (!repl_index_list);
	b'
    | ((a,b')::l) ->
	if Terms.equal_terms a t then b' else
	find_repl_index l
  in
  find_repl_index (!repl_index_list)

let new_repl_index b = new_repl_index_term (Terms.term_from_binder b)


module FindCompos : sig

type status = Compos | Decompos | Any

type charac_type =
    CharacType of typet
  | CharacTypeOfVar of binder

type 'a depinfo =
   (binder * (status * 'a)) list option * term list
      (* The dependency information has two components (dep, nodep):
	 If dep = Some l where l is a list of (variable, ...), such that it 
	 is guaranteed only variables in this list depend on the considered 
	 variable x[l].
	 If dep = None, we have no information of this kind; any variable 
	 may depend on x.
	 nodep is a list of terms that are guaranteed not to depend on x[l].
	 *)

val init_elem : 'a depinfo

val depends : (binder * 'a depinfo) -> term -> bool

  (* is_indep (b, depinfo) t returns a term independent of b
     in which some array indexes in t may have been replaced with
     fresh replication indexes. When t depends on b by variables
     that are not array indexes, raise Not_found *)
val is_indep : (binder * 'a depinfo) -> term -> term

val remove_dep_array_index : (binder * 'a depinfo) -> term -> term
val remove_array_index : term -> term

val find_compos : ((binder * (status * 'a)) -> term list -> (status * charac_type) option) -> 'a depinfo -> (binder * (status * 'a)) -> term -> (status * charac_type * term) option

val find_compos_list : ((binder * (status * 'a)) -> term list -> (status * charac_type) option) -> 'a depinfo -> (binder * (status * 'a)) list -> term -> (status * charac_type * term * binder * 'a) option

end
=
struct

let init_elem = (None, [])

let rec depends ((b, (dep,nodep)) as bdepinfo) t = 
  match t.t_desc with
    FunApp(f,l) -> List.exists (depends bdepinfo) l
  | Var(b',[]) when Terms.is_repl b' -> false
  | Var(b',l) ->
      (not (List.exists (Terms.equal_terms t) nodep)) && 
      ((
       ((b == b') || (not (Terms.is_restr b'))) &&
       (match dep with
	 None -> true
       | Some dl -> List.exists (fun (b'',_) -> b'' == b') dl
	  )) || (List.exists (depends bdepinfo) l))
  | _ -> Parsing_helper.internal_error "If/let/find/new unexpected in DepAnal1.depends"

let rec is_indep ((b0, (dep,nodep)) as bdepinfo) t =
  { t_desc = 
    begin
      match t.t_desc with
	FunApp(f,l) -> FunApp(f, List.map (is_indep bdepinfo) l)
      | Var(b,[]) when Terms.is_repl b -> t.t_desc
      |	Var(b,l) ->
	  if (List.exists (Terms.equal_terms t) nodep) then
	    t.t_desc 
	  else if (b != b0 && Terms.is_restr b) || (match dep with
	      None -> false
	    | Some dl -> not (List.exists (fun (b',_) -> b' == b) dl))
	  then
	    Var(b, List.map (fun t' ->
	      try
		is_indep bdepinfo t'
	      with Not_found ->
		Terms.term_from_binder (new_repl_index_term t')) l)
	  else
	    raise Not_found
      | _ -> Parsing_helper.internal_error "If/let/find/new unexpected in is_indep"
    end;
    t_type = t.t_type;
    t_occ = t.t_occ;
    t_loc = Parsing_helper.dummy_ext}

let rec remove_dep_array_index ((b0, (dep,nodep)) as bdepinfo) t =
  { t_desc = 
    begin
      match t.t_desc with
	FunApp(f,l) -> FunApp(f, List.map (remove_dep_array_index bdepinfo) l)
      | Var(b,[]) when Terms.is_repl b -> t.t_desc
      |	Var(b,l) ->
	  if (List.exists (Terms.equal_terms t) nodep) then
	    t.t_desc 
	  else 
	    Var(b, List.map (fun t' -> 
	      if depends bdepinfo t' then
		Terms.term_from_binder (new_repl_index_term t')
	      else
		t') l)
      | _ -> Parsing_helper.internal_error "If/let/find/new unexpected in remove_dep_array_index"
    end;
    t_type = t.t_type;
    t_occ = t.t_occ;
    t_loc = Parsing_helper.dummy_ext }

let rec remove_array_index t =
  { t_desc = 
    begin
      match t.t_desc with
	FunApp(f,l) -> FunApp(f, List.map remove_array_index l)
      | Var(b,[]) when Terms.is_repl b -> t.t_desc
      |	Var(b,l) ->
	  Var(b, List.map (fun t' ->
	    match t'.t_desc with
	      Var(b',[]) when Terms.is_repl b' -> t'
	    | _ -> Terms.term_from_binder (new_repl_index_term t')
		  ) l)
      | _ -> Parsing_helper.internal_error "If/let/find/new unexpected in remove_dep_array_index"
    end;
    t_type = t.t_type;
    t_occ = t.t_occ;
    t_loc = Parsing_helper.dummy_ext }

(* Same as apply_reds but do not apply collisions, and apply statements
   only at the root of the term *)
let apply_statement2 t t_state =
  match t_state.t_desc, t.t_desc with
    FunApp(f1, [redl;redr]), FunApp(f,l) when f1.f_cat == Equal ->
      begin
	try
	  match_term (fun () -> 
	    let t' = Terms.copy_term redr in
	    Terms.cleanup();
	    reduced := true;
	    t'
	      ) ([],[],[]) [] redl t
	with NoMatch ->
	  Terms.cleanup();
	  t
      end
  | _ -> t

let rec apply_all_red2 t = function
    [] -> t
  | ((_,t_state)::l) ->
      let t' = apply_statement2 t t_state in
      if !reduced then t' else apply_all_red2 t l

let rec apply_statements t =
  reduced := false;
  let t' = apply_all_red2 t (!Transform.statements) in
  if !reduced then 
    apply_statements t' 
  else
    t


(* find_compos b t returns true when t characterizes b: only one
value of b can yield a certain value of t *)

type status = Compos | Decompos | Any

type charac_type =
    CharacType of typet
  | CharacTypeOfVar of binder

type 'a depinfo =
  (binder * (status * 'a)) list option * term list

let rec find_decompos_bin check ((b,_) as b_st) b' t t' =
  (Terms.is_large t.t_type) && (t'.t_type == t.t_type) &&
  (match t.t_desc, t'.t_desc with
    Var(b1,l), Var(b1',l') when 
    (b == b1 && b' == b1') || (b == b1' && b' == b1) -> 
      (check b_st l != None) && (check b_st l' != None)
  | FunApp(f,l), FunApp(f',l') when 
      (f.f_options land Settings.fopt_UNIFORM) != 0  && (f == f') ->
      List.exists2 (find_decompos_bin check b_st b') l l'
  | _ -> false)
  
let rec find_compos_bin check ((b,(st,_)) as b_st) b' fact =
  match fact.t_desc with
   FunApp(f,[t1;t2]) when f.f_cat == Equal ->
      begin
      match (t1.t_desc, t2.t_desc) with
      	Var(b1,l1), Var(b2,l2) when (b1 == b && b2 == b') ->
	  if check b_st l2 != None then check b_st l1 else None
      |	Var(b1,l1), Var(b2,l2) when (b1 == b' && b2 == b) -> 
	  if check b_st l1 != None then check b_st l2 else None
      |	(FunApp(f1,l1), FunApp(f2,l2)) when
	(f1.f_options land Settings.fopt_COMPOS) != 0 && f1 == f2 -> 
	  find_compos_bin_l check b_st b' l1 l2
      |	(FunApp(f1,l1), FunApp(f2,l2)) when
	(f1.f_options land Settings.fopt_UNIFORM) != 0  && f1 == f2 ->
	  if (Terms.is_large t1.t_type) && (st = Decompos) && 
	    (List.exists2 (find_decompos_bin check b_st b') l1 l2)
	  then Some (Decompos, CharacType t1.t_type)  else None
      |	_ -> None
      end
  | FunApp(f,[t1;t2]) when f == Settings.f_and ->
      begin
	match find_compos_bin check b_st b' t1 with
	  None -> find_compos_bin check b_st b' t2
	| x -> x
      end
  | _ -> None
    
and find_compos_bin_l check b_st b' l1 l2 =
  match (l1,l2) with
    [],[] -> None
  | (a1::l1,a2::l2) ->
      begin
      match find_compos_bin check b_st b' (apply_statements (Terms.make_equal a1 a2)) with
	None -> find_compos_bin_l check b_st b' l1 l2
      |	Some(_, charac_type) -> Some(Compos,charac_type)
      end
  | _ -> Parsing_helper.internal_error "Lists of different lengths in find_compos_bin_l"
      
let rec subst depinfo assql t =
  { t_desc = 
    begin
      match t.t_desc with
	Var(b,l) -> Var(
	  (try List.assq b (!assql) with Not_found ->
            (* Do not rename variables that do not depend on the
	       variable argument of find_compos *)
	    if (Terms.is_restr b) || (Terms.is_repl b) ||
	       (match depinfo with
	         (Some dl,tl) ->
		   (not (List.exists (fun (b',_) -> b' == b) dl)) ||
		   (List.exists (Terms.equal_terms t) tl)
	       | (None, tl) -> List.exists (Terms.equal_terms t) tl)
	    then b else 
	    let r = Terms.new_binder b in
	    assql := (b,r)::(!assql);
	    r), List.map (subst depinfo assql) l)
      | FunApp(f,l) -> FunApp(f, List.map (subst depinfo assql) l)
      |	_ -> Parsing_helper.internal_error "If, find, and let should not occur in subst"
    end;
    t_type = t.t_type;
    t_occ = Terms.new_occ();
    t_loc = Parsing_helper.dummy_ext }

let rec find_decompos check ((b, _) as b_st) t =
  (Terms.is_large t.t_type) && 
  (match t.t_desc with
    Var(b',l) when b == b' -> 
      check b_st l != None
  | FunApp(f,l) when (f.f_options land Settings.fopt_UNIFORM) != 0 ->
      List.exists (find_decompos check b_st) l
  | _ -> false)

let rec find_compos check depinfo ((b,(st,_)) as b_st) t =
  if st = Any then None else
  match t.t_desc with
    Var(b',l) when b == b' -> 
      begin
	match check b_st l with
	  None -> None
	| Some(st, ch_ty) -> Some(st, ch_ty, t)
      end
  | FunApp(f,l) when (f.f_options land Settings.fopt_COMPOS) != 0 ->
      begin
	match find_compos_l check depinfo b_st l with
	  None -> None
	| Some(st, ch_ty, l') -> Some(st, ch_ty, 
				      { t_desc = FunApp(f,l');
					t_type = t.t_type;
					t_occ = t.t_occ;
					t_loc = Parsing_helper.dummy_ext })
      end
  | FunApp(f,l) when (f.f_options land Settings.fopt_UNIFORM) != 0 ->
      if (Terms.is_large t.t_type) && (st = Decompos) && 
	(List.exists (find_decompos check b_st) l)
      then Some (Decompos, CharacType t.t_type, t)  else None
  | Var _ -> None
  | _ -> 
      (* In a simpler version, we would remove 
	 find_compos_bin, find_compos_bin_l, find_decompos_bin, subst,
	 apply_statement2, apply_all_red2, apply_statements
	 and replace this case with None
	 *)
      let vcounter = !Terms.vcounter in
      let b' = Terms.new_binder b in
      let t' = subst depinfo (ref [(b, b')]) t in
      let f1 = apply_statements (Terms.make_equal t t') in
      let r = 
	match find_compos_bin check b_st b' f1 with
	  None -> None
	| Some(st,ch_ty) -> Some(st, ch_ty, t)
      in
      Terms.vcounter := vcounter; (* Forget created variables *)
      r

and find_compos_l check depinfo b_st = function
    [] -> None
  | (a::l) ->
      match find_compos check depinfo b_st a with
	None -> 
	  begin
	    match find_compos_l check depinfo b_st l with
	      None -> None
	    | Some(st, charac_type, l') -> Some(st, charac_type, (any_term a)::l')
	  end
      |	Some(_, charac_type, a') -> Some(Compos,charac_type, a'::List.map any_term l)

let find_compos_list check depinfo seen_list t =
  let rec test_l = function
    [] -> None
  | (((b, (st, x)) as b_st)::l) -> 
      match find_compos check depinfo b_st t with
	None -> test_l l
      |	Some(st,charac_type,t') -> Some(st,charac_type,t',b,x)
  in
  test_l seen_list

end

module DepAnal1 :
sig
  exception BadDep
  val check_all_deps : binder -> binder list * (term * term * typet list) list
  val find_compos_glob : binder -> term list -> term -> (typet * term) option
end
=
struct

(* Find all variables that depend on a certain variable, provided
   these variables are not output (raises BadDep when some
   of these variables may be output)

   When tests depend on these variables, they must always yield
   the same result up to a negligible probability.

(1) Activate advice? (See comments and display of "Manual advice:" below)
Guesses some useful SArename, but makes the proof of 
event endB(x, y, na, nb) ==> beginA(x, y, na, nb) fail for 
needham-schroeder-pkcorr3BlockAuth
7/7/2008 Now, this problem seems to have disappeared

TO DO (2) The dependency analysis tends to be too sensitive to the syntax.
For example, the test let (..., =M, =A) = r always fails when M is a 
large type and A is a small type, both not depending on r, and r is random.
However, the other test let (...., x, =A) = r in if x = M then...
yields a bad dependency (comparison with the small type A).
*)

open FindCompos

type branch = OnlyThen | OnlyElse | BothDepB | BothIndepB

let collisions_for_current_check_dependency = ref []

let equal_charac_type c1 c2 =
  match (c1,c2) with
    CharacType t1, CharacType t2 -> t1 == t2
  | CharacTypeOfVar b1, CharacTypeOfVar b2 -> b1 == b2
  | _ -> false

let add_collisions_for_current_check_dependency ((t1,t2,c) as proba_info) =
  if not (List.exists (fun (t1',t2',c') ->
    Terms.equal_terms t1 t1' && Terms.equal_terms t2 t2' && equal_charac_type c c')
      (!collisions_for_current_check_dependency)) then
    collisions_for_current_check_dependency := proba_info ::
       (!collisions_for_current_check_dependency)

exception BadDep

let depends seen_list t = 
  List.exists (fun (b, _) -> Terms.refers_to b t) seen_list

(* find_compos b t returns true when t characterizes b: only one
value of b can yield a certain value of t *)

let find_compos_list seen_list l =
  let check (b, (st, _)) l =
    if List.exists (depends seen_list) l then
      None
    else
      Some (st, CharacTypeOfVar b)
  in
  FindCompos.find_compos_list check (Some seen_list, []) seen_list l

let get_std_charac_type b = function
    CharacType t -> t
  | CharacTypeOfVar b' -> 
      if b != b' then Parsing_helper.internal_error "should be b";
      b.btype

let find_compos_glob b l' t =
  let check (b, (st, _)) l = 
    if List.for_all2 Terms.equal_terms l l' then
      Some (st, CharacTypeOfVar b) 
    else
      None
  in
  match FindCompos.find_compos check (None, []) (b,(Decompos, ref [CharacType b.btype])) t with
    Some(_, charac_type, t') -> Some(get_std_charac_type b charac_type, t')
  | None -> None

(* almost_indep_test seen_list t checks that the result of test t does not
depend on variables in seen_list, up to negligible probability.
Raises BadDep when the result may depend on variables in seen_list.
Returns Some true when the test is true with overwhelming probability
Returns Some false when the test is false with overwhelming probability
Returns None when the result cannot be evaluated. *)

let rec almost_indep_test seen_list t =
  match t.t_desc with
    FunApp(f,[t1;t2]) when f == Settings.f_and ->
      begin
	match (almost_indep_test seen_list t1,
	       almost_indep_test seen_list t2) with
	  (OnlyElse, _) | (_, OnlyElse) -> OnlyElse
	| (OnlyThen, x) -> x
	| (x, OnlyThen) -> x
	| (BothDepB, _) | (_, BothDepB) -> BothDepB
	| (BothIndepB, BothIndepB) -> BothIndepB
      end
  | FunApp(f,[t1;t2]) when f == Settings.f_or ->
      begin
	match (almost_indep_test seen_list t1,
	       almost_indep_test seen_list t2) with
	  (OnlyThen, _) | (_, OnlyThen) -> OnlyThen
	| (OnlyElse, x) -> x
	| (x, OnlyElse) -> x
	| (BothDepB, _) | (_, BothDepB) -> BothDepB
	| (BothIndepB, BothIndepB) -> BothIndepB
      end
  | FunApp(f,[t1]) when f == Settings.f_not ->
      begin
	match almost_indep_test seen_list t1 with
	  OnlyThen -> OnlyElse
	| OnlyElse -> OnlyThen
	| x -> x
      end
(* Be careful: do not use or-patterns with when: 
   If both patterns of the or succeed but the when clause fails for the 
   first one and succeeds for the second one, Caml considers that the
   match fails.
*)
  | FunApp(f,[t1;t2]) 
    when ((f.f_cat == Equal) || (f.f_cat == Diff)) && (Terms.is_large t1.t_type) ->
      begin
	match find_compos_list seen_list t1 with
	  Some(_, charac_type,t1',_,_) ->
	    if depends seen_list t2 then
	      BothDepB
	    else 
	      begin
                (* add probability *)
		add_collisions_for_current_check_dependency (t1', t2, charac_type);
		if (f.f_cat == Diff) then OnlyThen else OnlyElse
	      end
	| None -> match find_compos_list seen_list t2 with
	    Some(_,charac_type,t2',_,_) ->
	    if depends seen_list t1 then
	      BothDepB
	    else 
	      begin
                (* add probability *)
		add_collisions_for_current_check_dependency (t2', t1, charac_type);
		if (f.f_cat == Diff) then OnlyThen else OnlyElse
	      end
	  | None ->
	      if depends seen_list t then 
		BothDepB
	      else
		BothIndepB
      end
  | _ -> 
      if depends seen_list t then 
	BothDepB
      else
	BothIndepB

(* checkassign1 is called when the assigned term characterizes b
   Returns false when the let is always going to take the else branch
   up to negligible probability.
   Returns true when the let can take both branches
   tmp_bad_dep is set to true when there is a bad dependency except when
   the let always takes the else branch. *)
let rec check_assign1 ((t1, t2, charac_type) as proba_info) vars_to_add tmp_bad_dep seen_list st = function
    PatVar b ->
      begin
	let charac_type' = 
	  if st = Decompos then CharacType b.btype else charac_type 
	in
	try 
	  let (st',proba_info_list) = List.assq b (!seen_list) in
	  if st != st' then
	    tmp_bad_dep := true
	  else if not (List.exists (fun (t1', t2', charac_type'') ->
	    (Terms.equal_terms t1 t1') && (Terms.equal_terms t2 t2') &&
	    (equal_charac_type charac_type' charac_type'')) (!proba_info_list))
	  then
	    proba_info_list := (t1, t2, charac_type') :: (!proba_info_list)
	with Not_found ->
	  vars_to_add := (b,(st, ref [t1, t2, charac_type'])) :: (!vars_to_add)
      end;
      true
  | PatTuple(f,l) ->
      if st != Decompos then tmp_bad_dep := true;
      List.for_all (check_assign1 proba_info vars_to_add tmp_bad_dep seen_list st) l
  | PatEqual t ->
      if (depends (!seen_list) t) || 
        (not (Terms.is_large t.t_type)) then
	begin
	  tmp_bad_dep := true;
	  true
	end
      else
	begin
	  (* add probability *)
	  add_collisions_for_current_check_dependency proba_info;
	  false
	end

(* check_assign2 is called when the assigned term does not depend on b
   Returns Some(charac_type, t') when the let is always going to take the 
   else branch up to negligible probability. t' is the term with which
   the collision is eliminated and charac_type the type of the part of 
   t' characterized by the value of the pattern.
   Returns None when the let can take both branches 
   tmp_bad_dep is set to true when there is a bad dependency except when
   the let always takes the else branch. *)
let rec check_assign2 seen_list to_advise tmp_bad_dep = function
    PatVar b ->
      if List.exists (fun (b',_) -> b == b') (!seen_list) then
	begin
	  to_advise := Terms.add_eq (SArenaming b) (!to_advise);
	  tmp_bad_dep := true
	end;
      None
  | PatTuple(f,l) ->
      begin
        match check_assign2_list seen_list to_advise tmp_bad_dep l with
	  None -> None
	| Some(charac_type, l') ->
	    Some (charac_type, { t_desc = FunApp(f,l');
				 t_type = snd f.f_type;
				 t_occ = Terms.new_occ();
				 t_loc = Parsing_helper.dummy_ext })
      end
  | PatEqual t ->
      match find_compos_list (!seen_list) t with
	Some (status, charac_type,t',_,_) when Terms.is_large t.t_type ->
	  Some(charac_type, t')
      |	_ ->
	begin
	  if depends (!seen_list) t then
	    tmp_bad_dep := true;
	  None
	end

and check_assign2_list seen_list to_advise tmp_bad_dep = function
    [] -> None
  | (a::l) ->
      match check_assign2 seen_list to_advise tmp_bad_dep a with
	None -> 
	  begin
	    match check_assign2_list seen_list to_advise tmp_bad_dep l with
	      None -> None
	    | Some(charac_type, l') -> Some(charac_type, (any_term_pat a)::l')
	  end
      |	Some(charac_type, a') -> Some(charac_type, a'::(List.map any_term_pat l))

let rec check_depend_process cur_array seen_list = function
    Nil -> ()
  | Par(p1,p2) -> 
      check_depend_process cur_array seen_list p1;
      check_depend_process cur_array seen_list p2
  | Repl(b,p) -> check_depend_process (b::cur_array) seen_list p
  | Input((c,tl),pat,p) -> 
      if List.exists (depends (!seen_list)) tl then raise BadDep;
      (* Create a dummy variable for the input message *)
      let b = { sname = "dummy_input";
		vname = Terms.new_vname();
		btype = (Terms.term_from_pat pat).t_type;
		args_at_creation = List.map Terms.term_from_binder cur_array;
		def = [];
		compatible = Terms.compatible_empty;
		link = NoLink }
      in
      let t2 = Terms.term_from_binder b in
      let tmp_bad_dep = ref false in
      let to_advise = ref [] in
      match check_assign2 seen_list to_advise tmp_bad_dep pat with
	Some(charac_type, t1) -> 
	  add_collisions_for_current_check_dependency (t1, t2, charac_type);
      |	None ->
	begin
	  if (!tmp_bad_dep) then
	    begin
	      if (!to_advise) != [] then
		begin
                  if !Settings.no_advice_simplify then 
                    begin
		      print_string "Manual advice: ";
		      Display.display_list Display.display_instruct (!to_advise);
		      print_newline()
                    end
                  else
		     List.iter (fun x -> Transform.advise := Terms.add_eq x (!Transform.advise)) (!to_advise)
		end;
	      raise BadDep
	    end;
	  check_depend_oprocess cur_array seen_list p
	end

and check_depend_oprocess cur_array seen_list = function
    Yield -> ()
  | Restr(b,p) -> check_depend_oprocess cur_array seen_list p
  | Test(t,p1,p2) -> 
      begin
	match almost_indep_test (!seen_list) t with
	  BothDepB -> raise BadDep
	| BothIndepB -> 
	    check_depend_oprocess cur_array seen_list p1;
	    check_depend_oprocess cur_array seen_list p2
	| OnlyThen -> 
	    check_depend_oprocess cur_array seen_list p1
	| OnlyElse -> 
	    check_depend_oprocess cur_array seen_list p2
      end
  | Find(l0,p2,_) ->
      let always_then = ref false in
      List.iter (fun (bl,def_list,otheruses_list,t,p1) ->
	List.iter (fun (b, l) -> 
	  if List.exists (depends (!seen_list)) l then raise BadDep) def_list;
	(*Is it really necessary to test otheruses_list?*)
	List.iter (fun (b, l) -> 
	  if List.exists (depends (!seen_list)) l then raise BadDep) otheruses_list;

	(* Compute the probability that the test fails.
	   For that, replace bl' with new replication indexes, since the
	   test fails only when it fails for _all_ values of bl' *)
	if (!Terms.current_bound_vars) != [] then
	  Parsing_helper.internal_error "current_bound_vars should be cleaned up (simplify, 1)";
	List.iter (fun b -> 
	  let b' = new_repl_index b in
	  Terms.link b (TLink (Terms.term_from_binder b'))) bl;
	let t' = Terms.copy_term3 t in
	Terms.cleanup();
        match almost_indep_test (!seen_list) t' with
	  BothDepB -> raise BadDep
	| OnlyThen ->
	    if def_list == [] && otheruses_list == [] then always_then := true;
	    check_depend_oprocess cur_array seen_list p1
	| BothIndepB ->
            check_depend_oprocess cur_array seen_list p1
	| OnlyElse -> ()) l0;
      if not (!always_then) then
	check_depend_oprocess cur_array seen_list p2
  | Output((c,tl),t2,p) ->
      if (List.exists (depends (!seen_list)) tl) || (depends (!seen_list) t2) then raise BadDep;
      check_depend_process cur_array seen_list p
  | Let(pat,t,p1,p2) ->
      begin
	match find_compos_list (!seen_list) t with
	  Some (st, charac_type,t',_,_) ->
	    begin
	      let vars_to_add = ref [] in
	      let tmp_bad_dep = ref false in
	      if check_assign1 (t', Terms.term_from_pat pat, charac_type) vars_to_add tmp_bad_dep seen_list st pat then
		begin
		  if (!tmp_bad_dep) || (match pat with PatVar _ -> false | _ -> true) then raise BadDep;
		  List.iter (function ((b,_) as b_st) ->
                    (*print_string "Adding ";
                      Display.display_binder b0;
                      print_newline();*)
		    if not (Terms.is_assign b) then
		      raise BadDep;
		    seen_list := b_st :: (!seen_list)) (!vars_to_add);
		  check_depend_oprocess cur_array seen_list p1;
		end
	    end
	| None ->
	    if depends (!seen_list) t then
	      raise BadDep
	    else
	      begin
		let to_advise = ref [] in
		let tmp_bad_dep = ref false in
		match check_assign2 seen_list to_advise tmp_bad_dep pat with
		  Some(charac_type, t1) ->
		    (* add probability *)
		    add_collisions_for_current_check_dependency (t1, t, charac_type)
		| None ->
		  begin
		    if (!tmp_bad_dep) then
		      begin
			if (!to_advise) != [] then
			  begin
			    if !Settings.no_advice_simplify then 
			      begin
				print_string "Manual advice: ";
				Display.display_list Display.display_instruct (!to_advise);
				print_newline()
			      end
			    else
			       List.iter (fun x -> Transform.advise := Terms.add_eq x (!Transform.advise)) (!to_advise)
			  end;
			raise BadDep
		      end;
		    check_depend_oprocess cur_array seen_list p1
		  end;
	      end;
      end;
      check_depend_oprocess cur_array seen_list p2
  | EventP(t,p) ->
      check_depend_oprocess cur_array seen_list p
      
let rec check_depend_iter seen_list =
  if List.exists (fun (b0, _) -> Transform.occurs_in_queries b0) (!seen_list) then
    raise BadDep;
  let old_seen_list = !seen_list in
  check_depend_process [] seen_list (!whole_game);
  if (!seen_list) != old_seen_list then check_depend_iter seen_list

let rec get_type_from_charac seen_list vlist = function
    CharacType t -> [t]
  | CharacTypeOfVar b -> 
      if List.memq b seen_list then
	raise BadDep;
      let (st, proba_info_list) = List.assq b vlist in
      List.concat (List.map (fun (_,_,charac_type) -> get_type_from_charac (b::seen_list) vlist charac_type) (!proba_info_list))

let check_all_deps b0 =
  (*print_string "Doing check_all_deps ";
  Display.display_binder b0;
  print_newline();*)
  collisions_for_current_check_dependency := [];
  let dummy_term = Terms.term_from_binder b0 in
  let b0st = (b0, (Decompos, ref [dummy_term, dummy_term, CharacType b0.btype])) in
  let seen_vars = ref [b0st] in
  check_depend_iter seen_vars;
  (*print_string "Success\n";*)
  let vars_charac_type = 
    List.map (fun (b, (st, proba_info_list)) -> (b, List.concat (List.map (fun (_,_,charac_type) -> get_type_from_charac [b] (!seen_vars) charac_type) (!proba_info_list)))) (!seen_vars)
  in
  let proba_info = List.map (fun (t1, t2, c) ->
    (t1, t2, match c with
      CharacType t -> [t]
    | CharacTypeOfVar b -> List.assq b vars_charac_type)) (!collisions_for_current_check_dependency)
  in
  (List.map fst (!seen_vars), proba_info)

(* Memoizing version of check_all_deps *)

let check_all_deps b0 =
  try 
    List.assq b0 (!success_check_all_deps)
  with Not_found -> 
    if List.memq b0 (!failure_check_all_deps) then raise BadDep
    else
      try 
	let res = check_all_deps b0 in
	success_check_all_deps := (b0, res) :: (!success_check_all_deps);
	res
      with BadDep ->
	failure_check_all_deps := b0 :: (!failure_check_all_deps);
	raise BadDep

end (* module DepAnal1 *)

module DepAnal2 :
sig
  type dep_info 
  type elem_dep_info = (typet * term) FindCompos.depinfo

  val init : dep_info

  (* find_compos_glob depinfo b t   returns Some ty when
     t characterizes a part of b of type ty, knowing the dependency
     information given in depinfo. Otherwise, returns None. *)
  val find_compos_glob : elem_dep_info -> binder -> term -> (typet * term) option

  val update_dep_info : dep_info -> inputprocess -> dep_info
  val update_dep_infoo : dep_info -> process -> process * dep_info list 

  val get_dep_info : dep_info -> binder -> elem_dep_info

  (* is_indep (b, depinfo) t returns a term independent of b
     in which some array indexes in t may have been replaced with
     fresh replication indexes. When t depends on b by variables
     that are not array indexes, raise Not_found *)
  val is_indep : (binder * elem_dep_info) -> term -> term
end
= 
struct

(* Second dependency analysis: take into account the freshness
   of the random number b to determine precisely which expressions depend on b
   for expressions defined before the first output that follows the choice
   of b
   dep = List of variables that may depend on b, with their associated
         "find_compos" status
   nodep:term list = List of terms that do not depend on b
   under_b:bool = True when we are under the "new" that chooses b
   res_accu: term list option ref = List of terms that do not depend on b
   in the whole protocol. Initialized to None.
 *)

open FindCompos

type elem_dep_info = (typet * term) FindCompos.depinfo
type dep_info = (binder * elem_dep_info) list
      (* list of (b, (dep, nodep)), where 
	 dep is either Some l, where l is a list variables that depend on b, 
	 with their associated status and a term that describes how to 
	 compute this variable from b;
         nodep is a list of terms that do not depend on b[b.args_at_creation]
	 *)

let init = []

let rec subterms accu t =
  match t.t_desc with
    Var(_,l) | FunApp(_,l) -> 
      if List.exists (Terms.equal_terms t) accu then
	subterms_list accu l 
      else 
	subterms_list (t::accu) l
  | _ -> Parsing_helper.internal_error "If/let/find/res unexpected in subterms"
	
and subterms_list accu = function
    [] -> accu
  | (a::l) -> subterms_list (subterms accu a) l

let depends = FindCompos.depends

let is_indep = FindCompos.is_indep
    
(* find_compos b t returns true when t characterizes b: only one
value of b can yield a certain value of t *)

let check (b, (st, (bct, _))) l =
  if List.for_all2 Terms.equal_terms l b.args_at_creation then
    Some (st, CharacType bct)
  else
    None

let find_compos_list (b, ((dep, nodep) as depinfo)) t =
  let seen_list' = match dep with
    Some seen_list -> seen_list
  | None -> [(b,(Decompos, (b.btype, Terms.term_from_binder b)))]
  in
  match FindCompos.find_compos_list check depinfo seen_list' t with
    Some(st, CharacType charac_type, t', b', (_,assign)) -> Some(st, charac_type, t', b', assign)
  | Some _ -> Parsing_helper.internal_error "CharacTypeOfVar should not be used in DepAnal2"
  | None -> None

let find_compos_glob depinfo b t =
  match FindCompos.find_compos check depinfo (b,(Decompos, (b.btype, Terms.term_from_binder b))) t with
    Some(_, CharacType charac_type, t') -> Some(charac_type, t')
  | Some _ -> Parsing_helper.internal_error "CharacTypeOfVar should not be used in DepAnal2"
  | None -> None

let subst b t t' =
  Terms.auto_cleanup (fun () ->
    Terms.link b (TLink t);
    Terms.copy_term3 t')

exception Else

(* checkassign1 is called when the assigned term depends on b with status st
   Raises Else when only the else branch of the let may be taken *)
let rec check_assign1 ((t1, t2, b, charac_type) as proba_info) bdep_info st pat =
  match pat with
    PatVar b -> ()
  | PatTuple(f,l) ->
      let st' = if st != Decompos then Any else st in
      List.iter (check_assign1 proba_info bdep_info st') l
  | PatEqual t ->
      if (depends bdep_info t) || 
        (not (Terms.is_large t.t_type)) || (st == Any) then
	()
      else
	begin
	  (* add probability *)
	  add_term_collisions t1 t2 b (Some b.args_at_creation) [charac_type];
	  raise Else
	end

(* check_assign2 is called when the assigned term does not depend on b
   Return None when both branches may be taken and
          Some(charac_type, t') when only the else branch of the let
          may be taken. t' is the term with which the collision is
          eliminated and charac_type is the type of the part of t'
          characterized by the value of t' *)
let rec check_assign2 bdepinfo = function
    PatVar _ ->
      None
  | PatTuple(f,l) ->
      begin
        match check_assign2_list bdepinfo l with
	  None -> None
	| Some(charac_type, l') ->
	    Some(charac_type, { t_desc = FunApp(f,l');
				t_type = snd f.f_type;
				t_occ = Terms.new_occ();
				t_loc = Parsing_helper.dummy_ext })
      end
  | PatEqual t ->
      match find_compos_list bdepinfo t with
	Some (status, charac_type, t', b2, b2fromb) when Terms.is_large t.t_type ->
	  Some (charac_type, subst b2 b2fromb t')
      |	_ ->
	  None

and check_assign2_list bdepinfo = function
    [] -> None
  | (a::l) ->
      match check_assign2 bdepinfo a with
	None -> 
	  begin
	    match check_assign2_list bdepinfo l with
	      None -> None
	    | Some(charac_type, l') -> Some(charac_type, (any_term_pat a)::l')
	  end
      |	Some(charac_type, a') -> Some(charac_type, a'::(List.map any_term_pat l))
      
let rec remove_dep_array_index_pat bdepinfo = function
    PatVar b -> PatVar b
  | PatTuple(f,l) ->
      PatTuple(f, List.map (remove_dep_array_index_pat bdepinfo) l)
  | PatEqual t ->
      PatEqual (FindCompos.remove_dep_array_index bdepinfo t)

let rec depends_pat bdepinfo = function
    PatVar _ ->
      false
  | PatTuple(f,l) ->
      List.exists (depends_pat bdepinfo) l
  | PatEqual t ->
      depends bdepinfo t

let rec simplify_term remapping dep_info t =
  match t.t_desc with
    FunApp(f,[t1;t2]) when f == Settings.f_and ->
      Terms.make_and (simplify_term remapping dep_info t1) (simplify_term remapping dep_info t2)
  | FunApp(f,[t1;t2]) when f == Settings.f_or ->
      Terms.make_or (simplify_term remapping dep_info t1) (simplify_term remapping dep_info t2)
  | FunApp(f,[t1]) when f == Settings.f_not ->
      let t' = simplify_term remapping dep_info t1 in
      if Terms.is_false t' then Terms.make_true() else
      if Terms.is_true t' then Terms.make_false() else
      Terms.make_not t'
  | FunApp(f,[t1;t2]) 
    when ((f.f_cat == Equal) || (f.f_cat == Diff)) && (Terms.is_large t1.t_type) ->
      begin
	let t1' = remapping t1 in
	let t2' = remapping t2 in
	let rec try_dep_info = function
	    [] -> t
	  | ((b, _) as bdepinfo)::restl ->
	      let t1'' = remove_dep_array_index bdepinfo t1' in
	      match find_compos_list bdepinfo t1'' with
		Some(_, charac_type, t1''', b2, b2fromb) ->
		  begin
		    try 
		      let t2'' = is_indep bdepinfo t2' in
                      (* add probability *)
		      add_term_collisions (subst b2 b2fromb t1''') t2'' b (Some b.args_at_creation) [charac_type];
		      if (f.f_cat == Diff) then Terms.make_true() else Terms.make_false()
		    with Not_found ->
		      try_dep_info restl
		  end
	      | None -> 
		  let t2'' = remove_dep_array_index bdepinfo t2' in
		  match find_compos_list bdepinfo t2'' with
		  Some(_,charac_type, t2''', b2, b2fromb) ->
		    begin
		      try 
			let t1'' = is_indep bdepinfo t1' in
                        (* add probability *)
			add_term_collisions (subst b2 b2fromb t2''') t1'' b (Some b.args_at_creation) [charac_type];
			if (f.f_cat == Diff) then Terms.make_true() else Terms.make_false()
		      with Not_found ->
			try_dep_info restl
		    end
		| None ->
		    try_dep_info restl
	in
	try_dep_info dep_info
      end
  | _ -> t

(* Takes a dep_info as input and returns the new dep_info for the subprocesses
   of the input process p *)

let update_dep_info dep_info p = dep_info

(* Takes a dep_info as input and returns a simplified process and
   the list of new dep_info's for the subprocesses *)

let rec update_dep_infoo dep_info = function
    Yield -> (Yield,[])
  | (Restr(b,p)) as p' ->
      let b_term = Terms.term_from_binder b in
      let dep_info' = List.map (fun (b', (dep, nodep)) -> (b', (dep, b_term::nodep))) dep_info in
      if Terms.is_large b.btype then
	let def_vars = get_def_vars_at_proc p' b in
	(Restr(b,p), [(b, (Some [b, (Decompos, (b.btype, Terms.term_from_binder b))], 
			   (List.map Terms.term_from_binderref def_vars))) :: dep_info' ])
      else
	(Restr(b,p), [dep_info'])
  | Test(t,p1,p2) ->
      let t' = simplify_term (fun x -> x) dep_info t in
      if Terms.is_true t' then
	begin
	  Transform.changed := true;
	  update_dep_infoo dep_info p1
	end
      else if Terms.is_false t' then
	begin
	  Transform.changed := true;
	  update_dep_infoo dep_info p2
	end
      else
	let r = List.map (function ((b, (dep, nodep)) as bdepinfo) ->
	  if depends bdepinfo t' then
	    (b, (None, nodep))
	  else
	    bdepinfo) dep_info
	in
	if not (Terms.equal_terms t t') then Transform.changed := true;
	(Test(t',p1,p2), [r])
  | Find(l0,p2,dn) ->
       let always_then = ref false in
       let rec simplify_find = function
          [] -> []
        | (bl, def_list, otheruses_list, t, p1)::l ->
            let l' = simplify_find l in
            let bl' = List.map new_repl_index bl in
            let t' = simplify_term (fun x -> 
	       if (!Terms.current_bound_vars) != [] then
	         Parsing_helper.internal_error "current_bound_vars should be cleaned up (simplify, 1)";
               List.iter2 (fun b b' -> 
	         Terms.link b (TLink (Terms.term_from_binder b'))) bl bl';
	       let x' = Terms.copy_term3 x in
	       Terms.cleanup();
               x') dep_info t
            in
            if Terms.is_false t' then 
	      begin
		Transform.changed := true;
		l'
	      end 
	    else 
	      begin
		if Terms.is_true t' && def_list == [] then always_then := true;
		if not (Terms.equal_terms t t') then Transform.changed := true;
		(bl, def_list, otheruses_list, t', p1)::l'
	      end
       in
       let l0' = simplify_find l0 in
       begin
	 match l0' with
	   [] -> 
	     Transform.changed := true;
             update_dep_infoo dep_info p2
	 | [([],[],_,t, p1)] when Terms.is_true t ->
	     Transform.changed := true;
	     update_dep_infoo dep_info p1
	 | _ ->
         (* For each b in dep_info.in_progress, does the branch taken
            depend on b? *)
         let dep_b = List.map (fun bdepinfo ->
	   let tmp_bad_dep = ref false in
	   List.iter (fun (bl, def_list, otheruses_list, t, p1) ->
	     List.iter (fun (b, l) -> 
	       if List.exists (depends bdepinfo) l
               then tmp_bad_dep := true) def_list;
	     List.iter (fun (b, l) -> 
	       if List.exists (depends bdepinfo) l
               then tmp_bad_dep := true) otheruses_list;
	     if depends bdepinfo t then tmp_bad_dep := true
		  ) l0';
           !tmp_bad_dep) dep_info 
	 in

         (* Dependence info for the "then" branches *)
         let dep_info_list = List.map (fun (bl, def_list, _, _, _) ->
	   let this_branch_node = get_node_for_find_branch (!dn) bl in
	   let def_vars_accu = ref def_list in
	   let seen_refs = ref [] in
	   List.iter (fun br -> try 
	     add_def_vars this_branch_node def_vars_accu seen_refs br
	   with Contradiction -> ()
	       (* For simplicity, I ignore when a variable can in fact not be defined. I could remove that branch of the find to be more precise *)) def_list;
           let nodep_add = subterms_list (List.map Terms.term_from_binder bl)
             (List.map Terms.term_from_binderref (!def_vars_accu))
	       (* I add variables by closing recursively variables
	          that must be defined *)
           in
	   List.map2 (fun dep1 ((b, (dep, nodep)) as bdepinfo) ->
	     if dep1 then
	       (b, (None, nodep))
	     else
	       (b, (dep, (List.filter (fun t -> not (depends bdepinfo t)) nodep_add) @ nodep))
		 ) dep_b dep_info
             ) l0' 
	 in
         (* Dependence info for the else branch *)
	 let dep_info_else = List.map2 
	     (fun dep1 ((b, (dep, nodep)) as bdepinfo) ->
	       if dep1 then
		 (b, (None, nodep))
	       else
		 bdepinfo) dep_b dep_info
	 in
         (Find(l0',(if !always_then then Yield else p2),dn), dep_info_else :: dep_info_list)
       end
  | Let(pat, t, p1, p2) ->
      begin
        match pat with
          PatVar b' -> 
            let dep_info' = 
              List.map (fun ((b, (dep, nodep)) as bdepinfo) ->
		if depends bdepinfo t then
		  match dep with
		    None -> bdepinfo
		  | Some dl ->
                      match find_compos_list bdepinfo t with
	                Some (st, charac_type, t', b2, b2fromb) -> 
			  (b, (Some ((b',(st, (charac_type, subst b2 b2fromb t')))::dl), nodep))
                      | None -> 
			  let rec find_dep = function
			      [] -> 
				Parsing_helper.internal_error "t does not depend on b; this should have been detected by depends before"
                                (*(b, (dep, (Terms.term_from_binder b')::nodep))*)
			    | (b2, (_, (_, b2fromb)))::dep' ->
				if Terms.refers_to b2 t then
				  (b, (Some ((b', (Any, (b.btype, subst b2 b2fromb t)))::dl), nodep))
				else
				  find_dep dep'
			  in
			  find_dep dl
		else
		  (b, (dep, (Terms.term_from_binder b')::nodep))
                 ) dep_info 
            in
	    if p2 != Yield then Transform.changed := true;
            (Let(pat, t, p1, Yield), [dep_info'])
        | _ -> 
            let bl = Terms.vars_from_pat [] pat in
            let bl_terms = List.map Terms.term_from_binder bl in
	    try        
	      (* status is true when the chosen branch may depend on b *)
              let status ((b, _) as bdepinfo) =
		let t' = FindCompos.remove_dep_array_index bdepinfo t in
		let pat' = remove_dep_array_index_pat bdepinfo pat in
		match find_compos_list bdepinfo t' with
		  Some (st, charac_type, t'', b2, b2fromb) ->
		    check_assign1 (subst b2 b2fromb t'', Terms.term_from_pat pat', b, charac_type) bdepinfo st pat';
		    true
		| None ->
		    begin
		      if depends bdepinfo t' then () else
		      match check_assign2 bdepinfo pat' with
			None -> ()
		      |	Some(charac_type, t1') ->
			  (* Add probability *)
			  add_term_collisions t1' t' b (Some b.args_at_creation) [charac_type];
			  raise Else
		    end;
		    (depends bdepinfo t) || (depends_pat bdepinfo pat)
	      in
	      (* dependency information for the "in" and "else" branches *)
	      let dep_info' = List.map (fun ((b, (dep, nodep)) as bdepinfo) ->
		if status bdepinfo then
		  (b, (None, nodep)), (b, (None, nodep))
		else
		  (b, (dep, bl_terms @ nodep)), bdepinfo
		    ) dep_info
	      in
	      let dep_info1, dep_info2 = List.split dep_info' in
              (Let(pat, t, p1, p2), [dep_info1; dep_info2])
	    with Else ->         
	      Transform.changed := true;
	      update_dep_infoo dep_info p2
      end
  | Output(_,_,p) as p' ->
      (p', [List.map (fun (b, (dep, nodep)) -> (b, (None, nodep))) dep_info])
  | EventP(_,p) as p' ->
      (p', [dep_info])

  let get_dep_info dep_info b =
    try 
      List.assq b dep_info
    with Not_found ->
      (None, []) (* Not found *)

end (* Module DepAnal2 *)

let rec try_no_var_rec simp_facts t =
  let t' = try_no_var simp_facts t in(* Risk of non-termination? *)
  match t'.t_desc with
    FunApp(f,l) -> 
      { t_desc = FunApp(f, List.map (try_no_var_rec simp_facts) l);
	t_occ = t'.t_occ;
	t_type = t'.t_type;
	t_loc = Parsing_helper.dummy_ext }
  | _ -> t'

let activate_dep_coll = ref true

let rec dependency_collision_rec1 t1 t2 t =
  match t.t_desc with
    Var(b,l) when (Terms.is_restr b) && (Terms.is_large b.btype) && (not (Terms.refers_to b t2)) ->
      begin
	match DepAnal1.find_compos_glob b l t1 with
	  None -> false
	| Some(charac_type, t1') -> 
	    try 
	      let (vlist, collision_info) = DepAnal1.check_all_deps b in
	      if not (List.exists (fun b' -> Terms.refers_to b' t2 || List.exists (Terms.refers_to b') l) vlist) then
		begin
		  (* add probability *)
		  List.iter (fun (t1,t2,tl) -> add_term_collisions t1 t2 b None tl)
		    ((t1', t2, [charac_type]) :: collision_info);
		  true
		end
	      else
		false
	    with DepAnal1.BadDep ->
	      false
      end
  | FunApp(f,l) ->
      List.exists (dependency_collision_rec1 t1 t2) l
  | _ -> false

let rec dependency_collision_rec2 dep_info t1 t2 t =
  match t.t_desc with
    Var(b,l) when (Terms.is_restr b) && (Terms.is_large b.btype) && (not (Terms.refers_to b t2)) ->
      begin
	(List.for_all2 Terms.equal_terms l b.args_at_creation) &&
	(let depinfo = DepAnal2.get_dep_info dep_info b in
	 let t1' = FindCompos.remove_dep_array_index (b,depinfo) t1 in
	 match DepAnal2.find_compos_glob depinfo b t1' with
	   None -> false
	 | Some(charac_type, t1'') ->
	    try 
	      let t2' = DepAnal2.is_indep (b,depinfo) t2 in
	      (* add probability *)
	      add_term_collisions t1'' t2' b (Some b.args_at_creation) [charac_type];
	      true
	    with Not_found -> false)
      end 
  | FunApp(f,l) ->
      List.exists (dependency_collision_rec2 dep_info t1 t2) l
  | _ -> false

let rec dependency_collision_rec3 t1 t2 t =
  match t.t_desc with
    Var(b,l) when (Terms.is_restr b) && (Terms.is_large b.btype) && (not (Terms.refers_to b t2)) ->
      begin
	let check (b, (st, _)) tl =
	  if List.for_all2 Terms.equal_terms tl l then
	    Some (st, FindCompos.CharacType b.btype) 
	  else 
	    None
	in
	match FindCompos.find_compos check FindCompos.init_elem (b, (FindCompos.Decompos, b.btype)) t1 with
	  Some(_, FindCompos.CharacType charac_type, t1') -> 
	    begin
	      try 
		let t2' = FindCompos.is_indep (b,FindCompos.init_elem) t2  in
	        (* add probability *)
		add_term_collisions t1' t2' b (Some l) [charac_type];
		true
	      with Not_found -> 
		false
	    end
       | _ -> false
      end 
  | FunApp(f,l) ->
      List.exists (dependency_collision_rec3 t1 t2) l
  | _ -> false

let dependency_collision dep_info simp_facts t1 t2 = 
  let t1' = try_no_var_rec simp_facts t1 in
  let t2' = try_no_var_rec simp_facts t2 in
  (dependency_collision_rec2 dep_info t1' t2' t1') ||
  (dependency_collision_rec2 dep_info t2' t1' t2') ||
  (repl_index_list := [];
   let t1'' = FindCompos.remove_array_index t1' in
   let t2'' = FindCompos.remove_array_index t2' in
   (dependency_collision_rec3 t1'' t2'' t1'') ||
   (dependency_collision_rec3 t2'' t1'' t2'')) ||
  (dependency_collision_rec1 t1' t2' t1') ||
  (dependency_collision_rec1 t2' t1' t2')

(* Add a fact to a set of true facts, and simplify it *)

let is_tuple t =
  match t.t_desc with
    FunApp(f, _) when (f.f_options land Settings.fopt_COMPOS) != 0 -> true
  | _ -> false

let is_pat_tuple = function
    PatTuple (f,_) -> true
  | _ -> false

let rec orient t1 t2 = 
  match t1.t_desc, t2.t_desc with
    (Var(b,l), _) when
    (not (match t2.t_desc with
            FunApp(f,_) when (f.f_options land Settings.fopt_DECOMPOS) != 0 -> true
          | _ -> Terms.refers_to b t2)) && 
    (not (Terms.is_restr b)) -> true
  | (Var(b1,l1), Var(b2,l2)) when
    (b1 == b2) && (List.for_all2 orient l1 l2) -> true
  | (FunApp(f1,l1), FunApp(f2,l2)) when
    (f1 == f2) && (List.for_all2 orient l1 l2) -> true
  | _ -> false
    
let rec add_fact dep_info ((subst2, facts, elsefind) as simp_facts) fact =
  (* print_string "Adding "; Display.display_term [] fact; print_newline(); *)
  let fact' = try_no_var simp_facts fact in
  match fact'.t_desc with
    FunApp(f,[t1;t2]) when f.f_cat == LetEqual ->
      begin
	match t1.t_desc with
	  Var(b,l) -> 
	    let t1' = { t_desc = Var(b, List.map (try_no_var simp_facts) l);
			t_type = t1.t_type;
			t_occ = Terms.new_occ();
			t_loc = Parsing_helper.dummy_ext }
	    in
	    let t2' = try_no_var simp_facts t2 in
	    let rec try_red_t1 = function
		[] -> (* Could not reduce t1' *)
		  subst_simplify2 dep_info simp_facts (Terms.make_let_equal t1' t2')
	      | { t_desc = FunApp(f'',[t1'';t2''])}::l when f''.f_cat == LetEqual ->
		  if Terms.equal_terms t1'' t1' then 
		    simplif_add dep_info simp_facts (Terms.make_equal t2' t2'')
		  else
		    try_red_t1 l
	      | _::l -> try_red_t1 l
	    in
	    try_red_t1 subst2
	| _ -> 
	    Parsing_helper.internal_error "LetEqual terms should have a variable in the left-hand side"
      end
  | FunApp(f,[t1;t2]) when f.f_cat == Equal ->
      let t1' = try_no_var simp_facts t1 in
      let t2' = try_no_var simp_facts t2 in
      begin
      match (t1'.t_desc, t2'.t_desc) with
        (FunApp(f1,l1), FunApp(f2,l2)) when
	f1.f_cat == Tuple && f2.f_cat == Tuple && f1 != f2 -> 
	  raise Contradiction
      | (FunApp(f1,l1), FunApp(f2,l2)) when
	(f1.f_options land Settings.fopt_COMPOS) != 0 && f1 == f2 -> 
	  simplif_add_list dep_info simp_facts (List.map2 Terms.make_equal l1 l2)
      | (Var(b1,l1), Var(b2,l2)) when
	(Terms.is_restr b1) &&
	Terms.is_large b1.btype && b1 == b2 ->
	  add_elim_collisions b1 b1;
          (* add_proba (Div(Cst 1, Card b1.btype)); * number applications *)
	  simplif_add_list dep_info simp_facts (List.map2 Terms.make_equal l1 l2)
      | (Var(b1,l1), Var(b2,l2)) when
	(Terms.is_restr b1) && (Terms.is_restr b2) &&
	(Terms.is_large b1.btype || Terms.is_large b2.btype) &&
	b1 != b2 ->
	  add_elim_collisions b1 b2;
	  raise Contradiction
      | (_,_) when (!activate_dep_coll) && (dependency_collision dep_info simp_facts t1' t2') ->
	  raise Contradiction
      | (FunApp(f1,[]), FunApp(f2,[]) ) when
	f1 != f2 && (!Settings.diff_constants) ->
	  raise Contradiction
	  (* Different constants are different *)
      | (_, _) when orient t1' t2' ->
	  subst_simplify2 dep_info simp_facts (Terms.make_equal t1' t2')
      | (_, _) when orient t2' t1' -> 
	  subst_simplify2 dep_info simp_facts (Terms.make_equal t2' t1')
      | _ -> (subst2, fact'::facts, elsefind)
      end
  | FunApp(f,[t1;t2]) when f == Settings.f_and ->
      simplif_add dep_info (add_fact dep_info simp_facts t1) t2
  | _ -> 
      if Terms.is_false fact' then raise Contradiction else
      if Terms.is_true fact' then simp_facts else
      (subst2, fact'::facts, elsefind)

and subst_simplify2 dep_info (subst2, facts, elsefind) link =
  print_string "subst_simplify2 starts";
  print_newline();
  let subst2'' = ref [] in
  let not_subst2_facts = ref [] in
  List.iter (fun t0 ->
    match t0.t_desc with
      FunApp(f, [t;t']) when f.f_cat == Equal || f.f_cat == LetEqual ->
	(* When f.f_cat == LetEqual, t itself cannot be reduced by link,
	   since otherwise the left-hand side of link is t, and this
           term should have been reduced into t' by t0 before.
	   However, subterms of t may be reduced by link.
	   
	   When f.f_cat == LetEqual and we reduce only t' (not t),
	   we might directly add 
	   Terms.make_let_equal t (try_no_var simp_facts t1') to subst2''
	   However, it is not clear what "simp_facts" should really be...
         *)
	let (t1, t1', reduced) = 
	  match t'.t_desc with
	    Var _ ->
	      reduced_subst := false;
	      let t1 = apply_subst1 t link in
	      let t1' = apply_subst1 t' link in
	      (t1,t1',!reduced_subst)
	  | FunApp _ ->
	      reduced_subst := false;
	      let t1 = apply_subst1 t link in
	      let red = !reduced_subst in
	      (* Applying reductions here slows down simplification *)
	      reduced := false;
	      print_string "Before apply_statements_and_collisions";
	      print_newline();
	      let t1' = apply_statements_and_collisions (link :: (!subst2''), facts, elsefind) t' in
	      print_string "After apply_statements_and_collisions";
	      print_newline();
	      (t1, t1', red || (!reduced))
	  | _ -> Parsing_helper.internal_error "If/let/find/test not allowed in subst_simplify2"
	in
	if reduced then
	  not_subst2_facts := { t_desc = FunApp(f,[t1; t1']);
				t_type = Settings.t_bool;
				t_occ = Terms.new_occ();
				t_loc = Parsing_helper.dummy_ext }
	     :: (!not_subst2_facts)
	else
	  subst2'' := t0 :: (!subst2'')
    | _ -> Parsing_helper.internal_error "substitutions should be Equal or LetEqual terms"
    ) subst2;
  print_string "subst_simplify2 ends";
  print_newline();
  simplif_add_list dep_info (link :: (!subst2''),[], elsefind) ((!not_subst2_facts) @ facts)

and simplif_add dep_info ((subst2, facts, elsefind) as simp_facts) fact =
  print_string "simplif_add "; Display.display_term [] fact; 
  print_string " knowing\n"; display_facts simp_facts; print_newline();
  let fact' = apply_reds simp_facts fact in
  print_string "after apply_reds\n";
  print_newline();
  add_fact dep_info simp_facts fact'

and simplif_add_list dep_info simp_facts = function
    [] -> simp_facts
  | (a::l) -> simplif_add_list dep_info (simplif_add dep_info simp_facts a) l


let simplif_add dep_info s f =
  print_string "Adding "; Display.display_term [] f;
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
  print_string "Adding "; Display.display_list (Display.display_term []) fl;
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


(* Put a term in the form or (and (...)) *)

let rec get_or t =
  match t.t_desc with
    FunApp(f, [t1;t2]) when f == Settings.f_or ->
      (get_or t1) @ (get_or t2)
  | _ -> [t]

let rec make_and1 a = function
    [] -> Parsing_helper.internal_error "make_and1 empty"
  | [b] -> Terms.make_and b a
  | (b::l2) -> Terms.make_or (Terms.make_and a b) (make_and1 a l2)

let rec make_and2 l1 = function
    [] -> Parsing_helper.internal_error "make_and2 empty"
  | [a] -> make_and1 a l1
  | (a::l2) -> Terms.make_or (make_and1 a l1) (make_and2 l1 l2)

let make_and_distr t1 t2 =
  if (Terms.is_false t1) || (Terms.is_false t2) then Terms.make_false() else
  if Terms.is_true t1 then t2 else
  if Terms.is_true t2 then t1 else
  (* If t1 or t2 is "or", distribute *)
  make_and2 (get_or t1) (get_or t2)

let rec or_and_form t =
  match t.t_desc with
    FunApp(f, [t1;t2]) when f == Settings.f_and ->
      make_and_distr (or_and_form t1) (or_and_form t2)
  | FunApp(f, [t1;t2]) when f == Settings.f_or ->
      Terms.make_or (or_and_form t1) (or_and_form t2)
  | _ -> t

(* Simplify a term knowing some true facts *)

let rec simplify_term_rec dep_info simp_facts t =
  let t' = try_no_var simp_facts t in
  match t'.t_desc with
    FunApp(f, [t1;t2]) when f == Settings.f_and ->
      Terms.make_and (simplify_term_rec dep_info simp_facts t1) (simplify_term_rec dep_info simp_facts t2)
  | FunApp(f, [t1;t2]) when f == Settings.f_or ->
      Terms.make_or (simplify_term_rec dep_info simp_facts t1) (simplify_term_rec dep_info simp_facts t2)
  | FunApp(f, [t1;t2]) when f.f_cat == Equal ->
      let t1' = try_no_var simp_facts t1 in
      let t2' = try_no_var simp_facts t2 in
      begin
	match t1'.t_desc, t2'.t_desc with
	  (FunApp(f1,l1), FunApp(f2,l2)) when
	  f1.f_cat == Tuple && f2.f_cat == Tuple && f1 != f2 -> 
	    Terms.make_false()
	| (FunApp(f1,l1), FunApp(f2,l2)) when
	  (f1.f_options land Settings.fopt_COMPOS) != 0 && f1 == f2 -> 
	    Terms.make_and_list (List.map2 (fun t1 t2 -> simplify_term_rec dep_info simp_facts (Terms.make_equal t1 t2)) l1 l2)
	| (Var(b1,l1), Var(b2,l2)) when
	  (Terms.is_restr b1) &&
	  Terms.is_large b1.btype && b1 == b2 ->
	    add_elim_collisions b1 b1;
          (* add_proba (Div(Cst 1, Card b1.btype)); * number applications *)
	    Terms.make_and_list (List.map2 (fun t1 t2 -> simplify_term_rec dep_info simp_facts (Terms.make_equal t1 t2)) l1 l2)
	| (Var(b1,l1), Var(b2,l2)) when
	  (Terms.is_restr b1) && (Terms.is_restr b2) &&
	  (Terms.is_large b1.btype || Terms.is_large b2.btype) &&
	  b1 != b2 ->
	    add_elim_collisions b1 b2;
	    Terms.make_false()
	| (_,_) when dependency_collision dep_info simp_facts t1' t2' ->
	    Terms.make_false()
	| (FunApp(f1,[]), FunApp(f2,[])) when
	  f1 != f2 && (!Settings.diff_constants) ->
	    Terms.make_false()
	(* Different constants are different *)
	| _ -> t
      end
  | FunApp(f, [t1;t2]) when f.f_cat == Diff ->
      let t1' = try_no_var simp_facts t1 in
      let t2' = try_no_var simp_facts t2 in
      begin
	match t1'.t_desc, t2'.t_desc with
	  (FunApp(f1,l1), FunApp(f2,l2)) when
	  f1.f_cat == Tuple && f2.f_cat == Tuple && f1 != f2 -> 
	    Terms.make_true()
	| (FunApp(f1,l1), FunApp(f2,l2)) when
	  (f1.f_options land Settings.fopt_COMPOS) != 0 && f1 == f2 -> 
	    Terms.make_or_list (List.map2 (fun t1 t2 -> simplify_term_rec dep_info simp_facts (Terms.make_diff t1 t2)) l1 l2)

	| (Var(b1,l1), Var(b2,l2)) when
	  (Terms.is_restr b1) &&
	  Terms.is_large b1.btype && b1 == b2 ->
	    add_elim_collisions b1 b1;
      (* add_proba (Div(Cst 1, Card b1.btype)); * number applications *)
	    Terms.make_or_list (List.map2 (fun t1 t2 -> simplify_term_rec dep_info simp_facts (Terms.make_diff t1 t2)) l1 l2)
	| (Var(b1,l1), Var(b2,l2)) when
	  (Terms.is_restr b1) && (Terms.is_restr b2) &&
	  (Terms.is_large b1.btype || Terms.is_large b2.btype) &&
	  b1 != b2 ->
	    add_elim_collisions b1 b2;
	    Terms.make_true()
	| (_,_) when dependency_collision dep_info simp_facts t1' t2' ->
	    Terms.make_true()
	| (FunApp(f1,[]), FunApp(f2,[])) when
	  f1 != f2 && (!Settings.diff_constants) ->
	    Terms.make_true()
	    (* Different constants are different *)
	| _ -> t
      end
  | _ -> t

let simplify_term dep_info keep_tuple ((subst2, facts, elsefind) as simp_facts) t = 
  let t' = 
    if keep_tuple then 
      try_no_var simp_facts t 
    else
      t
  in
  let t'' = apply_reds simp_facts t' in
  let t''' = 
    if t''.t_type == Settings.t_bool then
      simplify_term_rec dep_info simp_facts t''
    else
      t''
  in
  if !Settings.minimal_simplifications then
    begin
      if Terms.is_true t''' || Terms.is_false t''' || (not (Terms.equal_terms t' t''')) ||
         (keep_tuple && is_tuple t''' && not (is_tuple t)) then
	begin
	  if not (Terms.is_true t || Terms.is_false t) then Transform.changed := true;
	  t'''
	end
      else
	(* The change is not really useful, don't do it *)
	t
    end
  else
    begin
      if not (Terms.equal_terms t t''') then Transform.changed := true;
      t'''
    end

(*
let simplify_term dep_info k s t =
  print_string "Simplifying "; Display.display_term [] t;
  print_string " knowing\n";
  display_facts s; 
  print_newline();
  let res = simplify_term dep_info k s t in
  print_string "Simplify done "; Display.display_term [] res;
  print_newline();
  res
*)

(* Simplify pattern *)

let rec simplify_pat dep_info true_facts = function
    (PatVar b) as pat -> pat
  | PatTuple (f,l) -> PatTuple (f,List.map (simplify_pat dep_info true_facts) l)
  | PatEqual t -> PatEqual (simplify_term dep_info false true_facts t)

(* facts_from_defined def_list: 
       for each (b,l) in def_list,
       look for definitions n of binders b,
       substitute l for b.args_at_creation in n.true_facts_at_def and
       add these facts to the returned list 
       substitute l for b.args_at_creation in n.def_vars_at_def and
       continue recursively with these definitions 
       If there are several definitions of b, take the intersection
       of lists of facts/defined vars. ("or" would be more precise
       but difficult to implement) 
       Do not reconsider an already seen pair (b,l), to avoid loops.*)


(* Take into account facts that must be true because a block of code
   is always executed until the next output/yield before passing control to
   another block of code *)
let true_facts_from_node current_node_opt n =
  match current_node_opt with
    Some current_node ->
  if is_reachable n current_node then
    Terms.intersect Terms.equal_terms (n.future_true_facts @ n.true_facts_at_def) current_node.true_facts_at_def
else
  n.future_true_facts @ n.true_facts_at_def
  | None -> 
      n.true_facts_at_def

let rec add_facts current_node fact_accu seen_refs (b,l) =
  (* print_string "Is defined "; Display.display_var [] b l; print_newline(); *)
  if (List.for_all (check_non_nested [] [b]) l) &&
    (not (Terms.mem_binderref (b,l) (!seen_refs))) then
    begin
      seen_refs := (b,l) :: (!seen_refs);
      let true_facts_at_def = intersect_list Terms.equal_terms (List.map (true_facts_from_node current_node) b.def) in
      let def_vars_at_def = intersect_list Terms.equal_binderref (List.map (def_vars_from_node current_node) b.def) in
      let bindex = List.map Terms.binder_from_term b.args_at_creation in
      (* add facts *)
      List.iter (fun f -> 
        (* b.args_at_creation -> l *)
	let f = Terms.subst bindex l f in
	(* print_string "Adding "; Display.display_term [] f; print_newline(); *)
	if not (List.memq f (!fact_accu)) then
	  fact_accu := f :: (!fact_accu)) true_facts_at_def;
      (* recursive call *)
      List.iter (fun (b',l') ->
        (* b.args_at_creation -> l *)
	add_facts current_node fact_accu seen_refs (b', List.map (Terms.subst bindex l) l')
	  ) def_vars_at_def
    end
      
let facts_from_defined current_node bl def_list =
  let def_list_subterms = ref [] in
  List.iter (Terms.close_def_subterm def_list_subterms) def_list;
  let fact_accu = ref [] in
  let seen_refs = ref [] in
  List.iter (fun (b,l) ->
    if not (List.exists (fun b' -> b == b' && List.for_all2 Terms.equal_terms l b'.args_at_creation) bl) then
      add_facts current_node fact_accu seen_refs (b,l)
	) (!def_list_subterms);
  !fact_accu


let add_def_vars_with_subterms bl def_vars_accu seen_refs br =
  let subterms = ref [] in
  Terms.close_def_subterm subterms br;
  List.iter (fun (b,l) ->
    if not (List.exists (fun b' -> b == b' && List.for_all2 Terms.equal_terms l b'.args_at_creation) bl) then
      add_def_vars None def_vars_accu seen_refs (b,l)
    else
      def_vars_accu := (b,l) :: (!def_vars_accu)
				  ) (!subterms)

let rec filter_def_list bl accu = function
    [] -> accu
  | (br::l) ->
      let implied_accu = ref [] in
      add_def_vars_with_subterms bl implied_accu (ref []) br;
      let accu' = Terms.setminus_binderref accu (!implied_accu) in
      let l' = Terms.setminus_binderref l (!implied_accu) in
      filter_def_list bl (br::accu') l'

let rec remove_subterms accu = function
    [] -> accu
  | (br::l) ->
      let subterms = ref [] in
      Terms.close_def_subterm subterms br;
      let accu' = Terms.setminus_binderref accu (!subterms) in
      let l' = Terms.setminus_binderref l (!subterms) in
      remove_subterms (br::accu') l' 


let rec match_term2 next_f simp_facts bl t t' =
  match t.t_desc with
    Var(v,l) when (List.memq v bl) && (List.for_all2 Terms.equal_terms l v.args_at_creation) ->
      begin
	if t'.t_type != v.btype then
	  raise NoMatch;
	match v.link with
	  NoLink -> Terms.link v (TLink t')
	| TLink t -> ignore (unify_terms simp_facts t t')
      end;
      next_f ()
  | Var(v,l) ->
      begin
	match t'.t_desc with
	  Var(v',l') when v == v' ->
	    match_term_list2 next_f simp_facts bl l l'
	| _ -> raise NoMatch
      end
  | FunApp(f,[t1;t2]) when f.f_options land Settings.fopt_COMMUT != 0 ->
      (* Commutative function symbols *)
      begin
	match t'.t_desc with
	  FunApp(f',[t1';t2']) when f == f' ->
	    begin
	      try
		Terms.auto_cleanup (fun () ->
		  match_term2 (fun () -> match_term2 next_f simp_facts bl t2 t2') simp_facts bl t1 t1')
	      with NoMatch ->
		match_term2 (fun () -> match_term2 next_f simp_facts bl t2 t1') simp_facts bl t1 t2'
	    end
	| _ -> raise NoMatch
      end
  | FunApp(f,l) ->
      begin
	match t'.t_desc with
	  FunApp(f',l') when f == f' ->
	    match_term_list2 next_f simp_facts bl l l'
	| _ -> raise NoMatch
      end
  | _ -> Parsing_helper.internal_error "If, find, and let should not occur in match_term2"

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
	Terms.auto_cleanup (fun () ->
	  match_binderref2 next_match simp_facts bl br br1)
      with NoMatch ->
	match_among next_match simp_facts bl br brl

let rec match_among_list next_match simp_facts bl def_vars = function
    [] -> next_match()
  | (br1::brl) ->
      match_among (fun () -> 
	match_among_list next_match simp_facts bl def_vars brl) 
	simp_facts bl br1 def_vars
  

let final_next dep_info bl true_facts t () =
  let t' = Terms.copy_term3 t in
  (* Cleanup links, with possibility to restore *)
  let tmp_list = List.map (fun b -> b.link) bl in
  List.iter (fun b -> b.link <- NoLink) bl;
  (* Raise Contradiction when t implied *)
  Terms.auto_cleanup (fun () -> 
    (* TO DO It would be possible to improve this when t' is the conjunction
       of terms in tl:
       replace true_facts := simplif_add (!true_facts) (Terms.make_not t') with
       if List.for_all (fun t -> 
         try
           ignore(simplif_add true_facts (Terms.make_not t));
           false
         with Contradiction -> true) tl then raise Contradiction *)
    (* print_string "Adding ";
    Display.display_term [] (Terms.make_not t');
    print_newline();*)
    true_facts := simplif_add dep_info (!true_facts) (Terms.make_not t'));
  (* Restore links *)
  List.iter2 (fun b l -> b.link <- l) bl tmp_list;
  (* Backtrack *)
  raise NoMatch

let always_true_def_list_t dep_info bl simp_facts t def_vars_opt def_list =
  match def_vars_opt with
    Some def_vars ->
      begin
      try
	match_among_list (final_next dep_info bl simp_facts t) (!simp_facts) bl def_vars def_list
      with NoMatch -> ()
      end
  | None -> 
      if def_list == [] then
	simp_facts := simplif_add dep_info (!simp_facts) (Terms.make_not t)

(* Treatment of elsefind facts *)

let rec add_elsefind dep_info def_vars_opt ((subst, facts, elsefind) as simp_facts) = function
    [] -> simp_facts
  | ((bl, def_list, otheruses_list, t1,_)::l) -> 
      let simp_facts' = 
	match (bl, def_list, otheruses_list) with
	  [],[],[] -> simplif_add dep_info simp_facts (Terms.make_not t1)
	| _,[],_ -> simp_facts (*should not happen*)
	| _ -> 
	    let simp_facts_ref = ref (subst, facts, (bl, def_list, otheruses_list, t1)::elsefind) in
	    always_true_def_list_t dep_info bl simp_facts_ref t1 def_vars_opt def_list;
	    !simp_facts_ref
      in
      add_elsefind dep_info def_vars_opt simp_facts' l

let not_deflist b (_, def_list, _, _) =
  List.for_all (fun (b',l) ->
    (b != b') && (not (List.exists (Terms.refers_to b) l))) def_list

let not_deflist_l bl elsefind =
  List.for_all (fun b -> not_deflist b elsefind) bl

let rec filter_elsefind f (subst, facts, elsefind) =
  (subst, facts, List.filter f elsefind)

let convert_elsefind dep_info def_vars_opt ((subst, facts, elsefind) as simp_facts) =
  let simp_facts_ref = ref simp_facts in
  List.iter (fun (bl, def_list, otheruses_list, t1) ->
    always_true_def_list_t dep_info bl simp_facts_ref t1 def_vars_opt def_list
      ) elsefind;
  !simp_facts_ref



(* Try to determine when a defined condition is always false
   b = variable
   pp = program point, at which we test whether b is defined
   lcp = length of the longest common prefix between the current replication
   indexes at pp and the indexes of b
   cur_array = current replication indexes at pp
   is_comp: bool ref, set to true when b may be defined at pp

   check_compatible ... p returns a pair (has_b,has_pp) where
   has_b is true when b is defined in p
   has_pp is true when pp is a branch in a subprocess of p
 *)

exception Compatible

let rec check_compatible lcp b pp def_node_opt = function
    Nil -> (false, false)
  | Par(p1,p2) ->
      let (has_b1, has_pp1) = check_compatible lcp b pp def_node_opt p1 in
      let (has_b2, has_pp2) = check_compatible lcp b pp def_node_opt p2 in
      if (has_b1 && has_pp2) || (has_b2 && has_pp1) then
	raise Compatible;
      (has_b1 || has_b2, has_pp1 || has_pp2)
  | (Repl(b',p) as p') ->
      if lcp <= 0 then
	(* When lcp <= 0, we have Compatible as soon as b is defined in p and pp occurs in p,
           and this can be tested very efficiently using definition nodes *)
	let (has_b, has_pp) =
	  match def_node_opt with
	    None -> check_compatible (lcp-1) b pp def_node_opt p
	  | Some pp_node ->
	      (* Returns true when p' is above node n *)
	      let rec find p' n =
		match n.definition with
		  DInputProcess p'' when p'' == p' -> true
		| _ -> if n.above_node == n then false else find p' n.above_node
	      in
	      (List.exists (find p') b.def, find p' pp_node)
	in
	if (has_b || (b' == b)) && has_pp then
	  raise Compatible;
	(has_b || (b' == b), has_pp)
      else
	let (has_b, has_pp) = check_compatible (lcp-1) b pp def_node_opt p in
	if (b' == b) && has_pp then
	  raise Compatible;
	(has_b || (b' == b), has_pp)
  | Input(_,pat, p) ->
      let (has_b, has_pp) = check_compatibleo lcp b pp def_node_opt p in
      let has_b2 = Terms.occurs_in_pat b pat in
      if has_b2 && has_pp then
	raise Compatible;
      (has_b || has_b2, has_pp)

and check_compatibleo lcp b pp def_node_opt = function
    Yield -> (false, false)
  | Restr(b',p) ->
      let (has_b, has_pp) = check_compatibleo lcp b pp def_node_opt p in
      if (b' == b) && has_pp then
	raise Compatible;
      (has_b || (b' == b), has_pp)
  | Test(_, p1, p2) -> 
      let (has_b1, has_pp1) = check_compatibleo lcp b pp def_node_opt p1 in
      let (has_b2, has_pp2) = check_compatibleo lcp b pp def_node_opt p2 in
      (has_b1 || has_b2, has_pp1 || has_pp2)
  | Find(l0, p2, _) ->
      let (has_b2, has_pp2) = check_compatibleo lcp b pp def_node_opt p2 in
      let rec check_l = function
	  [] -> (false, false)
	| ((bl,def_list,_,_,p1)::l) ->
	    let (has_br, has_ppr) = check_l l in
	    let (has_b1, has_pp1) = check_compatibleo lcp b pp def_node_opt p1 in
	    let has_b0 = List.memq b bl in
	    if has_b0 && (has_pp1 || (def_list == pp)) then
	      raise Compatible;
	    (has_br || has_b1 || has_b0, has_ppr || has_pp1 || (def_list == pp))
      in
      let (has_bl, has_ppl) = check_l l0 in
      (has_bl || has_b2, has_ppl || has_pp2)
  | Let(pat, _, p1, p2) ->
      let (has_b1, has_pp1) = check_compatibleo lcp b pp def_node_opt p1 in
      let (has_b2, has_pp2) = check_compatibleo lcp b pp def_node_opt p2 in
      let has_b3 = Terms.occurs_in_pat b pat in
      if has_b3 && has_pp1 then 
	raise Compatible;
      (has_b1 || has_b2 || has_b3, has_pp1 || has_pp2)
  | Output(_,_,p) ->
      check_compatible lcp b pp def_node_opt p 
  | EventP(_,p) ->
      check_compatibleo lcp b pp def_node_opt p 


let check_compatible_main b args pp cur_array simp_facts def_node_opt =
  let rec get_lcp l1 l2 = 
    match (l1,l2) with
      ({ t_desc = Var(b1,[]) }::l1',b2::l2') when b1 == b2 ->
	1 + get_lcp l1' l2' 
    | (t::l1',b2::l2') ->
	begin
	  match try_no_var simp_facts t with
	    { t_desc = Var(b1,[]) } when b1 == b2 ->
	      1 + get_lcp l1' l2' 
	  | _ -> 0
	end
    | _ -> 0
  in
  let lcp = get_lcp (List.rev args) (List.rev cur_array) in
  try
    let (has_b, has_pp) = check_compatible lcp b pp def_node_opt (!whole_game) in
    if not has_pp then
      Parsing_helper.internal_error "Program point not found in check_compatible_deflist; deflist probably altered since whole_game was set";
    false
  with Compatible ->
    true


let rec check_compatible_deflist pp cur_array simp_facts def_node_opt def_list =
  List.for_all (fun (b,l) -> check_compatible_main b l pp cur_array simp_facts def_node_opt) def_list


let is_compatible simp_facts (b,args) (b',args') =
  (b == b') || 
  (
  let l = List.length args in
  let l' = List.length args' in
  let min = if l > l' then l' else l in
  let args_skip = Terms.skip (l-min) args in
  let args_skip' = Terms.skip (l'-min) args' in
  (not (List.for_all2 Terms.equal_terms args_skip args_skip')) ||
  (Binderset.mem b'.compatible b) || 
  (Binderset.mem b.compatible b')
      )

let rec check_compatible2_main simp_facts = function
    [] -> true
  | (a::l) -> 
      (List.for_all (is_compatible simp_facts a) l) &&
      (check_compatible2_main simp_facts l)

let rec check_compatible2_deflist cur_array simp_facts old_def_list def_list =
  (* First simplify the terms in the list of defined variables *)
  let old_def_list = List.map (fun (b,l) -> (b, List.map (try_no_var simp_facts) l)) old_def_list in
  let def_list = List.map (fun (b,l) -> (b, List.map (try_no_var simp_facts) l)) def_list in
  (* Then remove the already defined variables from the new def_list *)
  let new_def_list = List.filter (fun br -> not (Terms.mem_binderref br old_def_list)) def_list in
  (* Check that the newly defined variables are compatible with each other *)
  (check_compatible2_main simp_facts new_def_list) && 
  (* ... and with all the previously defined variables *)
  (List.for_all (fun br -> List.for_all (is_compatible simp_facts br) new_def_list) old_def_list)


(* Return true when b has an array reference in t with
   indexes different from the indexes at creation *)

let rec has_array_access b t =
  match t.t_desc with
    Var(b',l) -> 
      ((b == b') && not (List.for_all2 Terms.equal_terms l b.args_at_creation)) ||
      (List.exists (has_array_access b) l)
  | FunApp(f,l) ->
      List.exists (has_array_access b) l
  | _ -> 
      Parsing_helper.internal_error "If/let/find/new unexpected in has_array_access"

let has_array_access_br b (b',l) =
  ((b == b') && not (List.for_all2 Terms.equal_terms l b.args_at_creation)) ||
  (List.exists (has_array_access b) l)

(* Remove branches with condition "otheruses" when there are no
   other uses of the considered variable *)

let rec has_real_uses uses_to_ignore b t =
  match t.t_desc with
    Var(b', l) ->
      (List.exists (has_real_uses uses_to_ignore b) l) ||
      ((b' == b) && (not (List.exists (Terms.equal_term_lists l) uses_to_ignore)))
  | FunApp(f,l) ->
      List.exists (has_real_uses uses_to_ignore b) l
  | _ -> 
      Parsing_helper.internal_error "If/let/find/new unexpected in has_real_uses"

let has_real_uses_br uses_to_ignore b (b',l) =
  (List.exists (has_real_uses uses_to_ignore b) l) ||
  ((b' == b) && (not (List.exists (Terms.equal_term_lists l) uses_to_ignore)))

let rec has_real_uses_pat uses_to_ignore b = function
    PatVar _ -> false
  | PatTuple(f,l) -> List.exists (has_real_uses_pat uses_to_ignore b) l
  | PatEqual t -> has_real_uses uses_to_ignore b t

let rec has_real_usesp uses_to_ignore b = function
    Nil -> false
  | Par(p1,p2) ->
      (has_real_usesp uses_to_ignore b p1) ||
      (has_real_usesp uses_to_ignore b p2)
  | Repl(_,p) -> 
      has_real_usesp uses_to_ignore b p
  | Input((c,tl),pat,p) ->
      (List.exists (has_real_uses uses_to_ignore b) tl) ||
      (has_real_uses_pat uses_to_ignore b pat) ||
      (has_real_usespo uses_to_ignore b p)

and has_real_usespo uses_to_ignore b = function
    Yield -> false
  | Restr(_,p) -> has_real_usespo uses_to_ignore b p
  | Test(t,p1,p2) ->
      (has_real_uses uses_to_ignore b t) ||
      (has_real_usespo uses_to_ignore b p1) ||
      (has_real_usespo uses_to_ignore b p2)
  | Find(l0,p2,_) ->
      (List.exists (fun (bl,def_list,otheruses_list,t,p1) -> 
	let rec extract_b = function
	    [] -> uses_to_ignore
	  | ((b',l)::r) ->
	      if b' == b then l::(extract_b r) else extract_b r
	in
	let uses_to_ignore' = extract_b otheruses_list in
	List.exists (has_real_uses_br uses_to_ignore' b) def_list ||
	List.exists (has_real_uses_br uses_to_ignore' b) otheruses_list ||
	(has_real_uses uses_to_ignore' b t) ||
	(has_real_usespo uses_to_ignore' b p1)
	  ) l0) ||
      (has_real_usespo uses_to_ignore b p2)      
  | Let(pat, t, p1, p2) ->
      (has_real_uses_pat uses_to_ignore b pat) ||
      (has_real_uses uses_to_ignore b t) ||
      (has_real_usespo uses_to_ignore b p1) ||
      (has_real_usespo uses_to_ignore b p2)      
  | Output((c,tl),t2,p) ->
      (List.exists (has_real_uses uses_to_ignore b) tl) ||
      (has_real_uses uses_to_ignore b t2) ||
      (has_real_usesp uses_to_ignore b p)
  | EventP(t,p) ->
      (has_real_uses uses_to_ignore b t) ||
      (has_real_usespo uses_to_ignore b p)
      
let has_real_uses_main b =
  try 
    List.assq b (!mem_has_real_uses)
  with Not_found ->
    let b_uses = has_real_usesp [] b (!whole_game) in
    mem_has_real_uses := (b, b_uses) :: (!mem_has_real_uses);
    b_uses

(* Test equality of processes modulo renaming of variables.
   Used to simplify tests and find: when all branches are equal,
   the test/find can be removed.
   There is room for more general equivalences between processes,
   but this is already a first step.
 *)

let equal_oprocess dep_info true_facts p p' =

let equal_terms_ren map t t' = 
  if t.t_type != t'.t_type then false else
  let mapped_t = Terms.subst3 (List.map (fun (b,b') -> (b, Terms.term_from_binder b')) map) t in
  simp_equal_terms true_facts mapped_t t'
in

let eq_binderref map br br' = equal_terms_ren map (Terms.term_from_binderref br) (Terms.term_from_binderref br')
in
  
let eq_deflist map dl dl' = 
  (List.for_all (fun br' -> List.exists (fun br -> eq_binderref map br br') dl) dl') &&
  (List.for_all (fun br -> List.exists (fun br' -> eq_binderref map br br') dl') dl) 
in

let rec equal_pat_ren map map_ref pat pat' =
  match pat, pat' with
    PatVar b, PatVar b' ->
      if b != b' then map_ref := (b,b') :: (!map_ref);
      (b == b') || 
      ((b.btype == b'.btype) && 
       (not (has_array_ref b)) && (not (has_array_ref b')))
  | PatTuple(f,l), PatTuple(f',l') ->
      (f == f') && (List.for_all2 (equal_pat_ren map map_ref) l l')
  | PatEqual t, PatEqual t' -> 
      equal_terms_ren map t t' 
  | _ -> false
in

let rec equal_process map p p' =
  match p, p' with
    Nil, Nil -> true
  | Par(p1,p2), Par(p1',p2') -> 
      (equal_process map p1 p1') && (equal_process map p2 p2')
  | Repl(b,p), Repl(b',p') -> 
      if b == b' then
	equal_process map p p'
      else
	(b.btype == b'.btype) && (equal_process ((b,b')::map) p p')
  | Input((c,tl), pat, p), Input((c',tl'), pat', p') ->
      (c == c') && (List.length tl == List.length tl') &&
      (List.for_all2 (equal_terms_ren map) tl tl') &&
      (let map_ref = ref map in
      let eq_pat = equal_pat_ren map map_ref pat pat' in
      eq_pat && (equal_oprocess (!map_ref) p p'))
  | _ -> false

and equal_oprocess map p p' =
  match p, p' with
    Yield, Yield -> true
  | Restr(b,p), Restr(b',p') ->
      if b == b' then
	equal_oprocess map p p'
      else 
	(b.btype == b'.btype) &&
	(not (has_array_ref b)) && (not (has_array_ref b')) &&
	(equal_oprocess ((b,b')::map) p p')
  | Test(t,p1,p2), Test(t',p1',p2') ->
      (equal_terms_ren map t t') &&
      (equal_oprocess map p1 p1') &&
      (equal_oprocess map p2 p2')
  | Let(pat, t, p1, p2), Let(pat', t', p1', p2') ->
      (equal_terms_ren map t t') &&
      (equal_oprocess map p2 p2') &&
      (let map_ref = ref map in
      let eq_pat = equal_pat_ren map map_ref pat pat' in
       eq_pat && (equal_oprocess (!map_ref) p1 p1'))
  | Output((c,tl),t2,p), Output((c',tl'),t2',p') ->
      (c == c') && (List.length tl == List.length tl') &&
      (List.for_all2 (equal_terms_ren map) tl tl') &&
      (equal_terms_ren map t2 t2') &&
      (equal_process map p p')
  | EventP(t,p), EventP(t',p') ->
      (equal_terms_ren map t t') &&
      (equal_oprocess map p p')
  | Find(l,p,_), Find(l',p',_) ->
      (equal_oprocess map p p') && (List.length l == List.length l') &&
      (List.for_all2 (fun 
	(bl, def_list, otheruses_list, t, p1)
	  (bl', def_list', otheruses_list', t', p1') ->
	    (List.length bl == List.length bl') && 
	    (let map_ref = ref map in
	    let eq_bl = List.for_all2 (fun b b' -> 
	      if b == b' then true else
	      if (b.btype == b'.btype) && 
		(not (has_array_ref b)) && (not (has_array_ref b')) then 
		begin
		  map_ref := (b,b') :: (!map_ref); 
		  true 
		end
              else 
		false) bl bl' in
	    eq_bl &&
	    (eq_deflist (!map_ref) def_list def_list') &&
	    (eq_deflist (!map_ref) otheruses_list otheruses_list') &&
	    (equal_terms_ren (!map_ref) t t') &&
	    (equal_oprocess (!map_ref) p1 p1')
	    )
	) l l')
  | _ -> false
in 

equal_oprocess [] p p'


let needed_vars vars =
  (List.exists has_array_ref vars) ||
  (List.exists Transform.occurs_in_queries vars)

let needed_vars_in_pat pat =
  needed_vars (Terms.vars_from_pat [] pat)

(* Simplification of processes *)

let rec simplify_process cur_array dep_info true_facts p = 
  let dep_info' = DepAnal2.update_dep_info dep_info p in
  match p with
    Nil -> Nil
  | Par(p1,p2) -> Par(simplify_process cur_array dep_info' true_facts p1,
		      simplify_process cur_array dep_info' true_facts p2)
  | Repl(b,p) -> Repl(b, simplify_process (b::cur_array) dep_info' true_facts p)
  | Input((c,tl), pat, p) ->
      begin
	match true_facts with
	  (_,_,[]) -> ()
	| _ -> Parsing_helper.internal_error "There should be no elsefind facts at inputs"
      end;
      Input((c, List.map (fun t -> simplify_term dep_info false true_facts t) tl), 
	    simplify_pat dep_info true_facts pat, 
	    simplify_oprocess cur_array dep_info' true_facts p)


and simplify_oprocess cur_array dep_info true_facts p =
  let (p', dep_info_list') = DepAnal2.update_dep_infoo dep_info p in
  match p' with
    Yield -> Yield
  | Restr(b,p) -> 
      let true_facts = filter_elsefind (not_deflist b) true_facts in
      let p' = simplify_oprocess cur_array (List.hd dep_info_list') true_facts p in
      if not ((has_array_ref b) || (Terms.refers_to_oprocess b p)) then
	begin
	  Transform.changed := true;
	  p'
	end
      else
	Restr(b, p')
  | Test(t, p1, p2) ->
      begin
	(* If p1 and p2 are equal, we can remove the test *)
      if equal_oprocess dep_info true_facts p1 p2 then
	begin
	  Transform.changed := true;
	  simplify_oprocess cur_array dep_info true_facts p2
	end
      else
      let t' = simplify_term dep_info false true_facts t in
      let t_or_and = or_and_form t' in
      try
	let p2' = simplify_oprocess cur_array (List.hd dep_info_list') (simplif_add dep_info true_facts (Terms.make_not t')) p2 in
	simplify_if (List.hd dep_info_list') cur_array true_facts p1 p2' t_or_and
      with Contradiction ->
	Transform.changed := true;
	simplify_oprocess cur_array (List.hd dep_info_list') true_facts p1
      end
  | Find(l0, p2, def_node_opt) ->
      begin
	(* If the processes in all branches are equal and the variables
	   defined by the find are not needed (no array reference, do not occur
	   in queries), we can remove the find *)
      if List.for_all (fun (bl, def_list, otheruses_list, t, p1) ->
	(equal_oprocess dep_info true_facts p1 p2) &&
	(not (needed_vars bl))) l0 then
	begin
	  Transform.changed := true;
	  simplify_oprocess cur_array dep_info true_facts p2
	end
      else	
      let dep_info_else :: dep_info_then = dep_info_list' in
      match l0 with
	[([],def_list,[],t1,p1)] when reduced_def_list (!def_node_opt) def_list = [] -> 
	  Transform.changed := true;
	  simplify_oprocess cur_array dep_info true_facts (Test(t1,p1,p2))
      |	_ -> 
      let def_vars_opt = get_def_vars_at (!def_node_opt) in
      let p2' = 
	if p2 == Yield then Yield else
	try
	  simplify_oprocess cur_array dep_info_else (add_elsefind dep_info_else def_vars_opt true_facts l0) p2
	with Contradiction ->
	  Transform.changed := true;
	  Yield
      in
      let rec simplify_findl dep_info_l1 l1 = 
	match (dep_info_l1,l1) with
	  [],[] -> []
	| (dep_infoi::dep_info_l),((bl, def_list, otheruses_list, t, p1)::l) ->
	    begin
	    let l' = simplify_findl dep_info_l l in
	    try
	      let this_branch_node = get_node_for_find_branch (!def_node_opt) bl in 
	      let true_facts = filter_elsefind (not_deflist_l bl) true_facts in
	      let facts_def_list = facts_from_defined this_branch_node bl def_list in
	      let true_facts' = simplif_add_list dep_infoi true_facts facts_def_list in
	      let def_list' = reduced_def_list (!def_node_opt) def_list in
	      let t' = simplify_term dep_infoi false true_facts' t in
	      let tf' = simplif_add dep_infoi true_facts' t' in
              begin
		(* The otheruses condition is false, i.e., the considered variable
		   has no other uses. *)
		if List.exists (fun (b,_) -> not (has_real_uses_main b)) otheruses_list then
		  raise Contradiction
	      end;
	      (* The "defined" conditions cannot hold
		 Using def_list as a marker for the program point.
		 It is important that def_list still has physically the same value as
		 in the initial process; in particular, that it is not modified by
		 DepAnal2.update_dep_infoo. *)
	      let def_vars_accu = ref def_list' in
	      let seen_refs = ref [] in
	      List.iter (add_def_vars this_branch_node def_vars_accu seen_refs) def_list';
	      (* check_compatible_deflist checks that the variables in (!def_vars_accu) can be defined
	         at the current program point *)
	      if not (check_compatible_deflist def_list cur_array tf' (!def_node_opt) (!def_vars_accu)) then
		raise Contradiction;
	      (* check_compatible2_deflist checks that all pairs of variables that must be defined can be simultaneously defined. Useful in some examples, but costly! *)
	      if !Settings.detect_incompatible_defined_cond then
		begin
		  let old_def_vars = 
		    match def_vars_opt with
		      None -> []
		    | Some l -> l
		  in
		  if not (check_compatible2_deflist cur_array tf' old_def_vars (!def_vars_accu)) then
		    raise Contradiction
		end;
	      let def_vars_opt' = 
		match def_vars_opt with
		  None -> Some (!def_vars_accu)    (* Using (!def_vars_accu) instead of def_list' on this line and the next is more precise *)
		| Some d -> Some ((!def_vars_accu) @ d)
	      in
	      let tf' = convert_elsefind dep_infoi def_vars_opt' tf' in
	      let p1' = simplify_oprocess cur_array dep_infoi tf' p1 in
	      let accu_def_list = ref def_list' in 
	      List.iter (Terms.get_deflist_subterms accu_def_list) facts_def_list;
	      let accu_needed = ref [] in
	      Terms.get_deflist_subterms accu_needed t';
	      Terms.get_deflist_oprocess accu_needed p1';
	      let needed_occur = 
		(reduced_def_list (!def_node_opt) 
		   (Terms.inter_binderref (!accu_needed) (!accu_def_list))) in
	      let implied_needed_occur = ref [] in
	      let seen_refs = ref [] in
	      List.iter (add_def_vars_with_subterms bl implied_needed_occur seen_refs) needed_occur;
	      let def_list'' = Terms.setminus_binderref def_list' (!implied_needed_occur) in
	      let def_list3 = remove_subterms [] (needed_occur @ (filter_def_list bl [] def_list'')) in

	      (* When i = M implied by def_list & t, remove i from bl
		 and substitute M for i *)
	      let keep_bl = ref [] in
	      let subst = ref [] in
	      List.iter (fun b -> 
		let b_im = try_no_var tf' (Terms.term_from_binder b) in
		if (Terms.refers_to b b_im) || (has_array_access b t') ||
		   (List.exists (has_array_access_br b) def_list') ||
		   (List.exists (has_array_access_br b) otheruses_list) ||
		   (List.exists (fun (b',_) -> (b == b')) otheruses_list)
		then
		  keep_bl := b :: (!keep_bl)
		else
		  subst := (b, b_im) :: (!subst)
					  ) bl;
	      let bl = !keep_bl in
	      if (!subst) != [] then Transform.changed := true;
	      let def_list_tmp = ref [] in
	      List.iter (fun br ->
		Terms.get_deflist_subterms def_list_tmp 
		  (Terms.subst3 (!subst) (Terms.term_from_binderref br))) def_list3;
	      let def_list3 = !def_list_tmp in 
	      let otheruses_list = List.map (fun (b,l) ->
		(b, List.map (Terms.subst3 (!subst)) l)) otheruses_list in
	      let t' = Terms.subst3 (!subst) t' in
	      let rec add_let p = function
		  [] -> p
		| ((b, b_im)::l) ->
		    Let(PatVar b, b_im, add_let p l, Yield)
	      in
	      let p1' = add_let (Terms.subst_oprocess3 (!subst) p1') (!subst) in
	      (* End of "When i = M implied by def_list & t, remove i from bl
		 and substitute M for i"*)


	      (bl, def_list3, otheruses_list, t', p1') :: l'
	      (*let t_or_and = or_and_form t' in
	      simplify_find true_facts' l' bl def_list' t_or_and p1 *)
	    with Contradiction ->
	      Transform.changed := true;
	      l'
	    end
	| _ -> Parsing_helper.internal_error "Different lengths in simplify/Find"
      in
      let l0' = simplify_findl dep_info_then l0 in
      if l0' == [] then
	begin
	  Transform.changed := true;
	  p2'
	end
      else
	begin
	  if (p2' == Yield) && (List.for_all (fun (bl,_,_,t,p1) ->
	    (p1 == Yield) && (not (List.exists has_array_ref bl)) &&
	    (not (List.exists Transform.occurs_in_queries bl))
	    ) l0') then
	    begin
	      Transform.changed := true;
	      Yield
	    end
	  else
	    Find(l0', p2', ref None)
	end
      end
  | Let(pat, t, p1, p2) ->
      begin
	(* If p1 and p2 are equal and the variables in the pattern pat are
           not needed (no array reference, do not occur in queries), 
	   we can remove the let *)
      if (equal_oprocess dep_info true_facts p1 p2) &&
         (not (needed_vars_in_pat pat)) then
	begin
	  Transform.changed := true;
	  simplify_oprocess cur_array dep_info true_facts p2
	end
      else
      let true_facts' = filter_elsefind (not_deflist_l (Terms.vars_from_pat [] pat)) true_facts in
      match dep_info_list' with
	[dep_info_in; dep_info_else] ->
	  let t' = simplify_term dep_info (is_pat_tuple pat) true_facts t in
	  simplify_let dep_info_else true_facts dep_info dep_info_in cur_array true_facts' p1 p2 t' pat
      |	[dep_info_in] -> 
	  let t' = simplify_term dep_info (is_pat_tuple pat) true_facts t in
	  simplify_let dep_info true_facts dep_info dep_info_in cur_array true_facts' p1 Yield t' pat 
      |	_ -> Parsing_helper.internal_error "Bad dep_info_list' in case Let"
      end
  | Output((c,tl),t2,p) ->
      (* Remove all "Elsefind" facts since variables may be defined 
         between the output and the following input *)
      let (subst, facts, _) = true_facts in
      let true_facts' = (subst, facts, []) in
      Output((c, List.map (fun t -> simplify_term dep_info false true_facts t) tl), 
	     simplify_term dep_info false true_facts t2,
	     simplify_process cur_array (List.hd dep_info_list') true_facts' p)
  | EventP(t,p) ->
      EventP(simplify_term dep_info false true_facts t,
	     simplify_oprocess cur_array (List.hd dep_info_list') true_facts p)

and simplify_if dep_info cur_array true_facts ptrue pfalse t' =
  match t'.t_desc with
    FunApp(f, []) when f == Settings.c_false -> 
      Transform.changed := true;
      pfalse
  | FunApp(f, []) when f == Settings.c_true -> 
      Transform.changed := true;
      simplify_oprocess cur_array dep_info true_facts ptrue
  | FunApp(f, [t1; t2]) when f == Settings.f_or ->
      Transform.changed := true;
      simplify_if dep_info cur_array true_facts ptrue (simplify_if dep_info cur_array true_facts ptrue pfalse t2) t1
  | _ -> 
      try
	let ptrue' =  simplify_oprocess cur_array dep_info (simplif_add dep_info true_facts t') ptrue in
	if (ptrue' == Yield) && (pfalse == Yield) then 
	  begin
	    Transform.changed := true;
	    Yield
	  end
	else
	  Test(t', ptrue', pfalse)
      with Contradiction ->
	Transform.changed := true;
	pfalse

(*
and simplify_find true_facts accu bl def_list t' ptrue = 
  match t'.t_desc with
    FunApp(f, []) when f == Settings.c_false -> 
      Transform.changed := true;
      accu
  | FunApp(f, [t1; t2]) when f == Settings.f_or ->
      Transform.changed := true;
      simplify_find true_facts (simplify_find true_facts accu bl def_list t2 ptrue) bl def_list t1 ptrue
  | _ -> 
      try
	let tf' = simplif_add true_facts t' in
	(bl, def_list, t', simplify_oprocess tf' ptrue) :: accu
      with Contradiction ->
	Transform.changed := true;
	accu
*)

and simplify_let dep_info_else true_facts_else dep_info dep_info_in cur_array true_facts ptrue pfalse t' = function
    (PatVar b) as pat -> 
      if pfalse != Yield then Transform.changed := true;
      Let(pat, t', simplify_oprocess cur_array dep_info_in (simplif_add dep_info_in true_facts (Terms.make_let_equal 
	(Terms.term_from_binder b) t')) ptrue, Yield)
  | PatEqual t ->
      Transform.changed := true;
      simplify_oprocess cur_array dep_info true_facts (Test(Terms.make_equal t t', ptrue, pfalse))
  | (PatTuple (f,l)) as pat ->
      begin
	try 
	  let res = simplify_oprocess cur_array dep_info true_facts 
	      (Terms.put_lets l (Terms.split_term f t') ptrue pfalse)
	  in
	  Transform.changed := true;
	  res
	with 
	  Not_found -> 
	    begin
	      try
		let ptrue' = simplify_oprocess cur_array dep_info_in (simplif_add dep_info_in true_facts 
		   (Terms.make_equal (Terms.term_from_pat pat) t')) ptrue
		in
		if (ptrue' == Yield) && (pfalse == Yield) &&
		  (not (needed_vars_in_pat pat)) then
		  begin
		    Transform.changed := true;
		    Yield
		  end
		else
		  Let(pat, t', ptrue', simplify_oprocess cur_array dep_info_else true_facts_else pfalse)
	      with Contradiction ->
		Transform.changed := true;
		simplify_oprocess cur_array dep_info_else true_facts_else pfalse
	    end
	| Terms.Impossible -> 
	    Transform.changed := true;
	    simplify_oprocess cur_array dep_info_else true_facts_else pfalse
      end

let rec simplify_main1 iter process =
  let tmp_changed = !Transform.changed in
  partial_reset process;
  Transform.changed := false;
  Terms.build_def_process None process;
  if !Settings.detect_incompatible_defined_cond then
    Terms.build_compatible_defs process;
  let p' = simplify_process [] DepAnal2.init ([],[],[]) process in
  let res = 
    if (!Transform.changed) && (iter != 1) then 
      simplify_main1 (iter-1) p'
    else
      begin
	print_string ("Run simplify " ^ (string_of_int ((!Settings.max_iter_simplif) - iter + 1)));
	if !Transform.changed then 
	  print_string " time(s). Maximum reached.\n"
	else
	  print_string " time(s). Fixpoint reached.\n";
	p'
      end
  in
  Transform.changed := (!Transform.changed) || tmp_changed;
  if !Settings.detect_incompatible_defined_cond then
    Terms.empty_comp_process process;
  res


let simplify_main internal_info gn process =
  reset internal_info gn process;
  let res_process = simplify_main1 (!Settings.max_iter_simplif) process in
  (* Add probability for eliminated collisions *)
  let proba = final_add_proba() in
  let internal_info' =
    ((!eliminated_collisions) @ (!already_counted_eliminated_collisions),
     (!red_proba) @ (!already_counted_red_proba)) 
  in
  eliminated_collisions := [];
  red_proba := [];
  (res_process, proba, internal_info', None)


(* Show that elements of the array b at different indexes are always
   different (up to negligible probability).
   This is useful for showing secrecy of a key.
 *)


let make_indexes b =
  List.map (fun t -> 
    let v = Terms.new_binder (Terms.binder_from_term t) in
    let rec def_node = { above_node = def_node; binders = [];
			 true_facts_at_def = []; def_vars_at_def = []; 
			 future_binders = []; future_true_facts = [];
			 future_def_vars = [];
			 definition = DNone }
    in
    let def_node2 = { above_node = def_node; binders = [v];
		      true_facts_at_def = []; def_vars_at_def = []; 
		      future_binders = []; future_true_facts = [];
		      future_def_vars = [];
		      definition = DNone }
    in
    v.def <- [def_node2];
    Terms.term_from_binder v) b.args_at_creation

let collect_facts accu (def,bindex,index) =
  let fact_accu = ref accu in
  let seen_refs = ref [] in
  (* add facts *)
  List.iter (fun f -> 
    let f = Terms.subst bindex index f in
    if not (List.memq f (!fact_accu)) then
      fact_accu := f :: (!fact_accu)) def.true_facts_at_def;
  (* recursive call *)
  List.iter (fun (b',l') ->
    add_facts None fact_accu seen_refs (b', List.map (Terms.subst bindex index) l')
      ) def.def_vars_at_def;
  (* Result *)
  !fact_accu

let rec collect_facts_list bindex index1 = function
    [] -> []
  | (d::l) ->
      let l' = collect_facts_list bindex index1 l in
      try
	(d, collect_facts [] (d,bindex,index1))::l'
      with Contradiction ->
	l'

let check_distinct b internal_info gn process =
  reset internal_info gn process;
  Terms.build_def_process None process;
  let index1 = make_indexes b in
  let index2 = make_indexes b in
  let diff_index = Terms.make_or_list (List.map2 Terms.make_diff index1 index2) in
  let bindex = List.map Terms.binder_from_term b.args_at_creation in
  let d1withfacts = collect_facts_list bindex index1 b.def in
  let d2withfacts = collect_facts_list bindex index2 b.def in
  let r = 
  List.for_all (fun (d1,d1facts) ->
    List.for_all (fun (d2,d2facts) ->
      match d1.definition, d2.definition with
	DProcess (Restr _), DProcess (Restr _) -> true
      | DProcess (Restr _), 
	    (DProcess (Let(PatVar _,{ t_desc = Var(b',l) },_,_))
	    |DTerm { t_desc = LetE(PatVar _, { t_desc = Var(b',l) },_,_) }) ->
		if not (Terms.is_restr b') then
		  Parsing_helper.internal_error "restriction should be checked when testing secrecy";
		(b != b') || 
		(
		try
		  let eq_b = Terms.make_and_list 
		      (List.map2 Terms.make_equal index1 (List.map (Terms.subst bindex index2) l))
		  in
		  let facts1 = diff_index :: eq_b :: d1facts @ d2facts in
		  ignore (simplif_add_list DepAnal2.init ([],[],[]) facts1);
		  false
		with Contradiction -> true
		    )
      |	(DProcess (Let(PatVar _,{ t_desc = Var(b',l) },_,_))
        |DTerm { t_desc = LetE(PatVar _, { t_desc = Var(b',l) },_,_) }), DProcess (Restr _) ->
	  true (* The symmetric case will be checked by the previous pattern *)
      |	(DProcess (Let(PatVar _,{ t_desc = Var(b1',l1) },_,_))
        |DTerm { t_desc = LetE(PatVar _, { t_desc = Var(b1',l1) },_,_) }),
	  (DProcess (Let(PatVar _,{ t_desc = Var(b2',l2) },_,_))
          |DTerm { t_desc = LetE(PatVar _, { t_desc = Var(b2',l2) },_,_) }) ->
		if not ((Terms.is_restr b1') && (Terms.is_restr b2')) then
		  Parsing_helper.internal_error "restriction should be checked when testing secrecy";
		(b1' != b2') || 
		(
		try
		  let eq_b = Terms.make_and_list 
		      (List.map2 Terms.make_equal 
			 (List.map (Terms.subst bindex index1) l1) 
			 (List.map (Terms.subst bindex index2) l2))
		  in
		  let facts1 = diff_index :: eq_b :: d1facts @ d2facts in
		  ignore (simplif_add_list DepAnal2.init ([],[],[]) facts1);
		  false
		with Contradiction -> true
		    )
      | _ -> 
	  Parsing_helper.internal_error "definition cases should be checked when testing secrecy"
	  ) d2withfacts
      ) d1withfacts
  in
  if r then
    begin
      (* Add probability for eliminated collisions *)
      (true, final_add_proba())
    end
  else
    (false, Zero)

        (*
        print_string "Facts for check_distinct 1:\n";
        List.iter (fun t -> Display.display_term [] t; print_newline()) facts1;

        print_string "Facts for check_distinct 2:\n";
        display_facts facts;
        *)

(* Check correspondence assertions *)

let rec guess_by_matching next_f simp_facts t t' = 
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
  | FunApp(f,[t1;t2]) when f.f_options land Settings.fopt_COMMUT != 0 ->
      (* Commutative function symbols *)
      begin
	match (try_no_var simp_facts t').t_desc with
	  FunApp(f',[t1';t2']) when f == f' ->
            begin
              try
                Terms.auto_cleanup (fun () ->
	          guess_by_matching (fun () -> guess_by_matching next_f simp_facts t2 t2') simp_facts t1 t1')
              with NoMatch ->
                guess_by_matching (fun () -> guess_by_matching next_f simp_facts t2 t1') simp_facts t1 t2'
            end
	| _ -> next_f()
      end
  | FunApp(f,l) ->
      begin
	match (try_no_var simp_facts t').t_desc with
	  FunApp(f',l') when f == f' ->
	    guess_by_matching_list next_f simp_facts l l'
	| _ -> next_f()
      end
  | Var _ | TestE _ | FindE _ | LetE _ | ResE _ ->
      Parsing_helper.internal_error "Var with arguments, if, find, let, and new should not occur in guess_by_matching"

and guess_by_matching_list next_f simp_facts l l' = 
  match l,l' with
    [],[] -> next_f()
  | a::l,a'::l' ->
      guess_by_matching (fun () -> guess_by_matching_list next_f simp_facts l l') 
	simp_facts a a'
  | _ -> Parsing_helper.internal_error "Different lengths in guess_by_matching_list"

let guess_by_matching_same_root next_f simp_facts t t' = 
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
  | FunApp(f,[t1;t2]) when f.f_options land Settings.fopt_COMMUT != 0 ->
      (* Commutative function symbols *)
      begin
	match (try_no_var simp_facts t').t_desc with
	  FunApp(f',[t1';t2']) when f == f' ->
            begin
              try
                Terms.auto_cleanup (fun () ->
	          guess_by_matching (fun () -> guess_by_matching next_f simp_facts t2 t2') simp_facts t1 t1')
              with NoMatch ->
                guess_by_matching (fun () -> guess_by_matching next_f simp_facts t2 t1') simp_facts t1 t2'
            end
	| _ -> raise NoMatch
      end
  | FunApp(f,l) ->
      begin
	match (try_no_var simp_facts t').t_desc with
	  FunApp(f',l') when f == f' ->
	    guess_by_matching_list next_f simp_facts l l'
	| _ -> raise NoMatch
      end
  | Var _ | TestE _ | FindE _ | LetE _ | ResE _ ->
      Parsing_helper.internal_error "Var with arguments, if, find, let, and new should not occur in guess_by_matching"

let get_facts_at true_facts n =
  let fact_accu = ref true_facts in
  List.iter (add_facts (Some n) fact_accu (ref [])) n.def_vars_at_def;
  !fact_accu

let rec collect_vars accu t =
  match t.t_desc with
    Var(b,[]) -> accu := b :: (!accu)
  | FunApp(f,l) -> List.iter (collect_vars accu) l
  | _ -> Parsing_helper.internal_error "expecting variable or function in collect_vars"

let show_fact facts fact =
  Terms.auto_cleanup (fun () ->
      try
	ignore (simplif_add DepAnal2.init facts (Terms.make_not fact));
(*	print_string "Failed to prove "; 
	Display.display_term [] fact;
	print_newline();*)
	false
      with Contradiction ->
(*	print_string "Proved "; 
	Display.display_term [] fact;
	print_newline();*)
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

let check_inj_compat (simp_facts, injrepidxs, _, begin_sid) facts' injrepidxs' begin_sid' =
  Terms.auto_cleanup (fun () ->
    try
      let facts_with_inj1 = simplif_add_list DepAnal2.init simp_facts facts' in
      (* injrepidxs \neq injrepidxs' *)
      let diff_fact = Terms.make_or_list (List.concat (List.map2 
	(List.map2 Terms.make_diff) injrepidxs injrepidxs')) in
      let facts_with_inj2 = simplif_add DepAnal2.init facts_with_inj1 diff_fact in
      (* begin_sid = begin_sid' *)
      let eq_facts = List.map2 Terms.make_equal begin_sid begin_sid' in
      let _ = simplif_add_list DepAnal2.init facts_with_inj2 eq_facts in
      raise NoMatch
    with Contradiction ->
      ())

let add_inj simp_facts injrepidxs vars fact' fact injinfo =
  match fact'.t_desc with
    FunApp(_, { t_desc = FunApp(_, begin_sid) }::_) ->
      begin
	let (subst, facts, _) = simp_facts in
	let nsimpfacts = subst @ facts in 
	let new_vars = List.map (fun b -> Terms.term_from_binder (Terms.new_binder b)) vars in
	let new_facts = List.map (Terms.subst vars new_vars) nsimpfacts in
	let new_injrepidxs = List.map (List.map (Terms.subst vars new_vars)) injrepidxs in
	let new_begin_sid = List.map (Terms.subst vars new_vars) begin_sid in
(*
	print_string "Checking inj compatiblity\n";
	display_facts simp_facts;
	print_string "New facts\n";
	List.iter (fun f -> Display.display_term [] f; print_newline()) new_facts;
	print_string "Inj rep idxs:";
	Display.display_list (Display.display_list (Display.display_term [])) injrepidxs;
	print_string "\nNew inj rep idxs:";
	Display.display_list (Display.display_list (Display.display_term [])) new_injrepidxs;
	print_string "\nBegin sid:";
	Display.display_list (Display.display_term []) begin_sid;
	print_string "\nNew begin sid:";
	Display.display_list (Display.display_term []) new_begin_sid;
	print_string "\n\n";
*)
	check_inj_compat (simp_facts, injrepidxs, vars, begin_sid) new_facts new_injrepidxs new_begin_sid;
	try
	  let l = List.assq fact injinfo in
	  List.iter (fun lelem -> check_inj_compat lelem new_facts new_injrepidxs new_begin_sid) l;
	  (fact, (simp_facts, injrepidxs, vars, begin_sid) :: l) :: (List.filter (fun (f, _) -> f != fact) injinfo)
	with Not_found ->
	  (fact, [(simp_facts, injrepidxs, vars, begin_sid)]) ::injinfo 
      end
  | _ -> Parsing_helper.internal_error "event should have session id"

(* try to find a instance of fact in the list of facts given as
last argument *)
let rec prove_by_matching next_check simp_facts injrepidxs vars injinfo is_inj fact = function
    [] -> raise NoMatch
  | (fact'::l) ->
      let tmp_proba = !proba in
      let tmp_eliminated_collisions = !eliminated_collisions in
      let tmp_term_collisions = !term_collisions in
      let tmp_red_proba = !red_proba in
      try
	Terms.auto_cleanup (fun () ->
          (* When I am trying to prove an event, the root symbol is
             the event symbol, and it must really be the same for
             fact and fact'. When I am trying to prove another fact,
             it is a good heuristic, since a variable can be bound
             only when at least the root symbol is the same *)
	  guess_by_matching_same_root (fun () ->
(*	    print_string "Found ";
	    Display.display_term [] fact';
	    print_string " as instance of ";
	    Display.display_term [] fact;
	    print_newline();*)
	    (* Check that all variables of fact are instantiated *)
	    let vars_fact = ref [] in
	    collect_vars vars_fact fact;
	    if not ((List.for_all (fun b -> (b.link != NoLink)) (!vars_fact)) &&
                    (* ... and that fact' is equal to fact *)
	            show_fact simp_facts (Terms.make_equal fact' (Terms.copy_term fact)))
	    then raise NoMatch;
	    if is_inj then 
	      next_check (add_inj simp_facts injrepidxs vars fact' fact injinfo)
	    else
	      next_check injinfo
	    ) simp_facts fact fact');
      with NoMatch -> 
	proba := tmp_proba;
	eliminated_collisions := tmp_eliminated_collisions;
	term_collisions := tmp_term_collisions;
	red_proba := tmp_red_proba;
	prove_by_matching next_check simp_facts injrepidxs vars injinfo is_inj fact l

let rec check_term next_check ((_,facts2,_) as facts) injrepidxs vars injinfo = function
    QAnd(t,t') ->
      check_term (fun injinfo' -> check_term next_check facts injrepidxs vars injinfo' t')
	facts injrepidxs vars injinfo t
  | QOr(t,t') ->
      begin
	let tmp_proba = !proba in
	let tmp_eliminated_collisions = !eliminated_collisions in
	let tmp_term_collisions = !term_collisions in
	let tmp_red_proba = !red_proba in
	try
	  Terms.auto_cleanup (fun () ->
	    check_term next_check facts injrepidxs vars injinfo t)
	with NoMatch ->
	  proba := tmp_proba;
	  eliminated_collisions := tmp_eliminated_collisions;
	  term_collisions := tmp_term_collisions;
	  red_proba := tmp_red_proba;
	  check_term next_check facts injrepidxs vars injinfo t'
      end
  | QTerm t2 ->
      begin
	(* Try to find an instance of t2 in simp_facts *)
	let tmp_proba = !proba in
	let tmp_eliminated_collisions = !eliminated_collisions in
	let tmp_term_collisions = !term_collisions in
	let tmp_red_proba = !red_proba in
	try
	  prove_by_matching next_check facts injrepidxs vars injinfo false t2 facts2
	with NoMatch -> 
	  proba := tmp_proba;
	  eliminated_collisions := tmp_eliminated_collisions;
	  term_collisions := tmp_term_collisions;
	  red_proba := tmp_red_proba;
	  (* If failed, try to prove t2 by contradiction,
	     when t2 is fully instantiated *)
	  let vars_t2 = ref [] in
	  collect_vars vars_t2 t2;
	  if (List.for_all (fun b -> (b.link != NoLink)) (!vars_t2)) &&
	    (show_fact facts (Terms.copy_term t2))
	      then next_check injinfo else raise NoMatch
      end
  | QEvent(is_inj,t2) ->
      begin
	(* Try to find an instance of t2 in simp_facts *)
	let tmp_proba = !proba in
	let tmp_eliminated_collisions = !eliminated_collisions in
	let tmp_term_collisions = !term_collisions in
	let tmp_red_proba = !red_proba in
	try
	  prove_by_matching next_check facts injrepidxs vars injinfo is_inj t2 facts2
	with NoMatch -> 
	  proba := tmp_proba;
	  eliminated_collisions := tmp_eliminated_collisions;
	  term_collisions := tmp_term_collisions;
	  red_proba := tmp_red_proba;
	  raise NoMatch
      end
      

let check_corresp (t1,t2) internal_info gn p =
   Terms.auto_cleanup (fun () ->
(* Dependency collision must be desactivated, because otherwise
   it may consider the equality between t1 and t1' below as an unlikely
   collision, because t1 does not depend on variables in the process *)
  activate_dep_coll := false;
(*  print_string "Trying to prove ";
  Display.display_query (QEventQ(t1,t2));*)
  reset internal_info gn p;
  let event_accu = ref [] in
  Terms.build_def_process (Some event_accu) p;
  let vars_t1 = ref [] in
  List.iter (fun (_, t) -> collect_vars vars_t1 t) t1;
  let vars_t1' = List.map (fun b ->
    let rec def_node = { above_node = def_node; binders = [];
			 true_facts_at_def = []; def_vars_at_def = []; 
			 future_binders = []; future_true_facts = [];
			 future_def_vars = [];
			 definition = DNone }
    in
    b.def <- [def_node];
    let b' = Terms.new_binder b in
    Terms.link b (TLink (Terms.term_from_binder b'));
    b') (!vars_t1)
  in
  let collect_facts1 next_f facts injrepidxs vars (is_inj,t) =
    List.for_all (fun (t1',true_facts,node) ->
      match t.t_desc,t1'.t_desc with
	FunApp(f,idx::l),FunApp(f',idx'::l') ->
	  if f == f' then
	    try
	      let end_sid = 
		match idx'.t_desc with
		  FunApp(_,lsid) -> lsid
		| _ -> Parsing_helper.internal_error "Session ids should occur first in the arguments of events"
	      in
	      let bend_sid = List.map Terms.binder_from_term end_sid in
	      let new_bend_sid = List.map Terms.new_binder bend_sid in
	      let new_end_sid = List.map Terms.term_from_binder new_bend_sid in
	      let eq_facts = List.map2 Terms.make_equal (List.map Terms.copy_term l) (List.map (Terms.subst bend_sid new_end_sid) l') in
	      let new_facts = List.map (Terms.subst bend_sid new_end_sid) (get_facts_at true_facts node) in
(*
              print_string "\nFound ";
              Display.display_term [] t1';
              print_string " with facts\n";
              List.iter (fun t -> Display.display_term [] t; print_newline()) (eq_facts @ new_facts);
*)
	      let facts1 = Terms.auto_cleanup (fun () -> simplif_add_list DepAnal2.init facts new_facts) in
(*            print_string "First step without contradiction\n"; *)
	      let facts' = Terms.auto_cleanup (fun () -> simplif_add_list DepAnal2.init facts1 eq_facts) in
(*            print_string "After simplification ";
              display_facts facts'; *)
	      if not is_inj then
		next_f facts' injrepidxs (new_bend_sid @ vars)
	      else
		next_f facts' (new_end_sid :: injrepidxs) (new_bend_sid @ vars)
	    with Contradiction -> 
(*            print_string "Contradiction. Proof succeeded.\n";*)
	      true
	  else 
	    true
      | _ -> Parsing_helper.internal_error "event expected in check_corresp"
	    ) (!event_accu)
  in
  let rec collect_facts_list next_f facts injrepidxs vars = function
      [] -> next_f facts injrepidxs vars
    | (a::l) -> collect_facts1 (fun facts' injrepidxs' vars' -> collect_facts_list next_f facts' injrepidxs' vars' l) facts injrepidxs vars a
  in  
  let injinfo = ref [] in
  let r =
    collect_facts_list (fun facts' injrepidxs' vars' ->
      try 
	Terms.auto_cleanup (fun () -> 
	  check_term (fun injinfo' -> injinfo := injinfo'; true) facts' injrepidxs' vars' (!injinfo) t2)
      with NoMatch -> 
	false
	  ) ([],[],[]) [] vars_t1' t1
  in
  activate_dep_coll := true;
  if r then
    begin
      (* Add probability for eliminated collisions *)
      (true, final_add_proba())
    end
  else
    (false, Zero))
