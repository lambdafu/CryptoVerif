open Types

(* 1. Is a type large? (i.e. the inverse of its cardinal is negligible) *)

let is_large t =
  (t.tsize >= !Settings.tysize_MIN_Auto_Coll_Elim)

let elim_collisions_on_password_occ = ref []

let is_large_term t =
  (is_large t.t_type) || 
  ((t.t_type.tsize >= 1) && 
   (List.exists (function
     | CollVars l ->
	 begin
	   match t.t_desc with
	     Var(b,_) ->
	       let bname = Display.binder_to_string b in
	       List.mem bname l
	   | _ -> false
	 end
     | CollTypes l -> List.mem t.t_type.tname l
     | CollTerms l -> List.mem t.t_occ l
	 ) (!elim_collisions_on_password_occ)))

(* 2. Cardinality functions *)

let card t =
match t.tcat with
  Interv p -> Count(p)
| _ -> 
    if t.toptions land Settings.tyopt_BOUNDED != 0 then
      Card(t)
    else
      Parsing_helper.internal_error "Cardinal of unbounded type"

let card_index b =
  Polynom.p_prod (List.map (fun ri -> card ri.ri_type) b.args_at_creation)

(* 3. Computation of probabilities of collisions *)

(* Tests if proba_l/proba is considered small enough to eliminate collisions *)

let is_smaller proba_l factor_bound  =
  (* Sort the factor_bound and proba_l by decreasing sizes *)
  let factor_bound_sort = List.sort (fun (b1size, b1exp) (b2size, b2exp) -> compare b2size b1size) factor_bound in
  let proba_l = List.map (fun b -> Terms.param_from_type b.ri_type) proba_l in
  let proba_l_sort = List.sort (fun p1 p2 -> compare p2.psize p1.psize) proba_l in
  (* Check that factor_bound >= proba_l *)
  let rec ok_bound factor_bound proba_l =
    match (factor_bound, proba_l) with
      _, [] -> true
    | [], _ -> false
    | ((bsize, bexp):: rest), p::prest ->
	if p.psize <= bsize then
	  if bexp > 1 then ok_bound ((bsize, bexp-1)::rest) prest
	  else ok_bound rest prest
	else
	  false
  in
  ok_bound factor_bound_sort proba_l_sort

let rec order_of_magnitude probaf =
  match probaf with
  | Add(p1,p2) ->
      max (order_of_magnitude p1) (order_of_magnitude p2)
  | Zero | EpsRand _ -> min_int
  | Max(l) ->
      Terms.max_list order_of_magnitude l
  | Cst _ -> 0
  | PColl1Rand t | PColl2Rand t -> - t.tsize
  | Card t -> t.tsize
  | Div(p1, p2) ->
      Terms.minus (order_of_magnitude p1) (order_of_magnitude p2)
  | Mul(p1, p2) ->
      Terms.plus (order_of_magnitude p1) (order_of_magnitude p2)
  | Proba _ -> (* We accept probabilities of collision statements *)
      min_int
  | _ ->
      Parsing_helper.internal_error "Unexpected probability in Proba.is_smaller_proba_type"

let rec is_1_over_card_t ty = function
  | Add(p, EpsRand _) -> is_1_over_card_t ty p
  | Div(Cst 1.0, Card ty') -> ty == ty'
  | _ -> false
		
let is_small_enough_coll_elim (proba_l, (proba_t, dep_types, full_type, indep_types)) =
  try
    let size_proba =
      if !Settings.trust_size_estimates then
	Terms.plus (order_of_magnitude proba_t) (Terms.sum_list (fun ty -> ty.tsize) dep_types)
      else
	if dep_types == [] then
	  order_of_magnitude proba_t
	else if is_1_over_card_t full_type proba_t then
	  - (Terms.max_list (fun ty -> ty.tsize) indep_types)
	else
	  raise Not_found
    in
    List.exists (fun (factor_bound, type_bound) ->
    (size_proba <= - type_bound) && 
    (is_smaller proba_l factor_bound)
	) (!Settings.allowed_collisions)
  with Not_found ->
    false
	
let is_small_enough_collision proba_l =
  List.exists (is_smaller proba_l) (!Settings.allowed_collisions_collision)
  

let whole_game = ref Terms.empty_game

(* Probability of collision between a random value of type [t],
   and an independent value. The collision occurs [num] times. *)

let pcoll1rand t =
  if t.toptions land Settings.tyopt_NONUNIFORM != 0 then
    PColl1Rand t
  else
    let p = Div(Cst 1.0, card t) in
    if t.toptions land Settings.tyopt_FIXED != 0 then
      p
    else if t.toptions land Settings.tyopt_BOUNDED != 0 then
      begin
	if (!Settings.ignore_small_times) > 0 then
	  p
	else
	  Add(p, EpsRand t)
      end
    else
      Parsing_helper.internal_error "Collisions eliminated with type that cannot be randomly chosen"

(* Probability of collision between two random values of type [t].
   The collision occurs [num] times. *)

let pcoll2rand t =
  if t.toptions land Settings.tyopt_NONUNIFORM != 0 then
    PColl2Rand t 
  else 
    pcoll1rand t

(* An element (b1,b2) in eliminated_collisions means that we 
have used the fact
that collisions between b1 and b2 have negligible probability. *)

let eliminated_collisions = ref [] 

let add_elim_collisions b1 b2 =
  let equal (b1',b2') =
           ((b1 == b1') && (b2 == b2')) ||
           ((b1 == b2') && (b2 == b1'))
  in
  if not (List.exists equal (!eliminated_collisions)) then
    begin
      if is_small_enough_coll_elim (b1.args_at_creation @ b2.args_at_creation, (pcoll1rand b1.btype, [], b1.btype, [b1.btype])) then
	begin
	  eliminated_collisions := (b1, b2) :: (!eliminated_collisions);
	  true
	end
      else
	false
    end
  else
    true

let proba_for_collision b1 b2 =
  print_string "Eliminated collisions between ";
  Display.display_binder b1;
  print_string " and ";
  Display.display_binder b2;
  print_string " Probability: ";
  let p1 = pcoll2rand b1.btype in
  let p = 
    if b1 == b2 then
      Polynom.p_mul(Polynom.p_mul(Cst 0.5,Polynom.p_mul(card_index b1, card_index b1)),p1)
    else
      begin
        if b1.btype != b2.btype then
          Parsing_helper.internal_error "Collision between different types";
        Polynom.p_mul(Polynom.p_mul(card_index b1, card_index b2),p1)
      end
  in
  Display.display_proba 0 p;
  print_newline();
  p

(* An element (t1,t2,proba,tl) in red_proba means that t1 has been reduced
to t2 using a probabilistic reduction rule, and that the restrictions
in this rule are mapped according to list tl

I have a small doubt here on when exactly we can avoid counting several times
the same elimination of collisions in different games. I do it when the
probability does not depend on the runtime of the game. Would that be ok
even if it depends on it? *)

let red_proba = ref []

let rec instan_time = function
    AttTime -> Add(AttTime, Time (!whole_game, Computeruntime.compute_runtime_for (!whole_game)))
  | Time _ -> Parsing_helper.internal_error "unexpected time"
  | (Cst _ | Count _ | OCount _ | Zero | Card _ | TypeMaxlength _
     | EpsFind | EpsRand _ | PColl1Rand _ | PColl2Rand _ | ProbaIndepCollOfVar _) as x -> x
  | Proba(p,l) -> Proba(p, List.map instan_time l)
  | ActTime(f,l) -> ActTime(f, List.map instan_time l)
  | Maxlength(n,t) -> Maxlength(!whole_game, Terms.copy_term Terms.Links_Vars t) (* When add_proba_red is called, the variables in the reduction rule are linked to their corresponding term *)
  | Length(f,l) -> Length(f, List.map instan_time l)
  | Mul(x,y) -> Mul(instan_time x, instan_time y)
  | Add(x,y) -> Add(instan_time x, instan_time y)
  | Sub(x,y) -> Sub(instan_time x, instan_time y)
  | Div(x,y) -> Div(instan_time x, instan_time y)
  | Max(l) -> Max(List.map instan_time l)

let rec collect_array_indexes accu t =
  match t.t_desc with
    ReplIndex(b) ->
	if not (List.memq b (!accu)) then
	  accu := b:: (!accu)
  | Var(b,l) -> List.iter (collect_array_indexes accu) l
  | FunApp(f,l) -> List.iter (collect_array_indexes accu) l
  | _ -> Parsing_helper.internal_error "If/let/find/new unexpected in collect_array_indexes"

let add_proba_red t1 t2 side_cond proba tl =
  let proba = instan_time proba in
  let equal (t1',t2',side_cond',proba',tl') =
     (Terms.equal_terms t1 t1') && (Terms.equal_terms t2 t2') && (Terms.equal_terms side_cond side_cond') && (Terms.equal_probaf proba proba')
  in
  if not (List.exists equal (!red_proba)) then
    begin
      let accu = ref [] in
      List.iter (fun (_,t) -> collect_array_indexes accu t) tl;
      if is_small_enough_collision (!accu) then
	begin
	  red_proba := (t1,t2,side_cond,proba,tl) :: (!red_proba);
	  true
	end
      else
	false
    end
  else
    true

let proba_for_red_proba t1 t2 side_cond proba tl =
  print_string "Reduced ";
  Display.display_term t1;
  print_string " to ";
  Display.display_term t2;
  if not (Terms.is_true side_cond) then
    begin
      print_string " where ";
      Display.display_term side_cond
    end;
  print_string " Probability: ";  
  let accu = ref [] in
  List.iter (fun (_,t) -> collect_array_indexes accu t) tl;
  let p = Polynom.p_mul(proba, Polynom.p_prod (List.map (fun array_idx -> card array_idx.ri_type) (!accu))) in
  Display.display_proba 0 p;
  print_newline();
  p


(* Initialization *)

let reset coll_elim g =
  whole_game := g;
  elim_collisions_on_password_occ := coll_elim;
  eliminated_collisions := [];
  red_proba := []

(* Final addition of probabilities *)

let final_add_proba coll_list =
  let proba = ref Zero in
  let add_proba p =
    if !proba == Zero then proba := p else proba := Polynom.p_add(!proba, p)
  in
  List.iter (fun (b1,b2) -> add_proba (proba_for_collision b1 b2))
    (!eliminated_collisions);
  List.iter (fun (t1,t2,side_cond,proba,tl) -> add_proba (proba_for_red_proba t1 t2 side_cond proba tl))
    (!red_proba);
  List.iter add_proba coll_list;
  let r = Polynom.polynom_to_probaf (Polynom.probaf_to_polynom (!proba)) in
  eliminated_collisions := [];
  red_proba := [];
  elim_collisions_on_password_occ := [];
  whole_game := Terms.empty_game;
  if r == Zero then [] else [ SetProba r ]

let get_current_state() =
  (!eliminated_collisions, !red_proba)

let restore_state (ac_coll, ac_red_proba) =
  eliminated_collisions := ac_coll;
  red_proba := ac_red_proba
