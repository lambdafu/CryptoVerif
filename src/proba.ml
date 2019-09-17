open Types

(* 1. Is a type large? (i.e. the inverse of its cardinal is negligible) *)

let is_large t =
  Terms.get_pcoll1_high t <= - !Settings.tysize_MIN_Auto_Coll_Elim

let elim_collisions_on_password_occ = ref []

let is_large_term t =
  (is_large t.t_type) || 
  ((Terms.get_pcoll1_high t.t_type <= - !Settings.tysize_MIN_Coll_Elim) && 
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

(* We are using interval arithmetic, where bounds are represented
   by pairs (sign, exp) meaning sign * 2^exp. Hence, each value is
   represented by an interval ((sign_min, exp_min), (sign_max, exp_max)),
   meaning that sign_min * 2^exp_min <= v <= sign_max * 2^exp_max.
   The exponents are constrained to be in the interval [min_f, max_f],
   so min_f may in fact represent any value less than min_f,
   and max_f may represent any value greater than max_f.

   Invariants: 
   sign_min, sign_max \in {-1, 0, 1}
   exp_min, exp_max \in [min_f, max_f]
   If sign_min = 0, then exp_min = 0.0; same for the max.
   sign_min * 2^exp_min <= sign_max * 2^exp_max, so
   - sign_min <= sign_max.
   - If sign_min = sign_max = 1, then exp_min <= exp_max
   - If sign_min = sign_max = -1, then exp_min >= exp_max *)

let min_f = float_of_int min_int
let max_f = float_of_int max_int
let zero_interv = ((0, 0.0), (0, 0.0))
let log2cst = log 2.0

(* [bound r] makes sure that the result [r] is in the interval [min_f, max_f] *)
let bound r =
  if r < min_f then min_f else if r > max_f then max_f else r
      
let log2 x = bound((log x)/. log2cst)
    
let log2_1p x = bound((log1p x)/. log2cst)

(* [plus s x y] adds the exponents [x] and [y], making sure that
   the result is in the interval [min_f, max_f], and that it
   represents an interval that contains the real value for sure.

   The argument [s] is useful for the latter point.
   - When [s > 0], the greater the result, the larger the interval
   (either the result is used as upper bound of the interval and the
   upper bound in question is positive, i.e. signmax = 1, 
   or the result is used as lower bound of the interval and the
   lower bound in question is negative, i.e. signmin = -1).
   Hence if [x] or [y] is [max_f], since it may represent a value
   larger than [max_f], the result is [max_f], even when [x + y < max_f]. 
   - Symetrically, when [s < 0], the smaller the result, the larger 
   the interval.
   (either the result is used as upper bound of the interval and the
   upper bound in question is negative, i.e. signmax = -1, 
   or the result is used as lower bound of the interval and the
   lower bound in question is positive, i.e. signmin = 1).
   Hence, if [x] or [y] is [min_f], since it may represent a value
   smaller than [min_f], the result is [min_f], even when [x + y > min_f]. 
*)
let plus s x y =
  if s > 0 then 
    if x = max_f || y = max_f then max_f else bound(x +. y)
  else
    if x = min_f || y = min_f then min_f else bound(x +. y)

(* [minus s x] negates [x], making sure that
   the result is in the interval [min_f, max_f], and that it
   represents an interval that contains the real value for sure.
   The argument [s] plays the same role as in [plus] above *)
let minus s x =
  if s > 0 then
    if x = min_f then max_f else bound (-. x)
  else
    if x = max_f then min_f else bound (-. x)

(* [is_greater v1 v2] is true when [v1] is greater than [v2] *)
let is_greater (s1, e1) (s2, e2) =
  if s2 > s1 then false else
  if s1 > s2 then true else
  (* s1 = s2 *)
  match s1 with
  | 1 -> e1 > e2
  | -1 -> e1 < e2
  | 0 -> false
  | _ -> Parsing_helper.internal_error "unexpected sign"
  
let max_v v1 v2 =
  if is_greater v1 v2 then v1 else v2

let min_v v1 v2 =
  if is_greater v1 v2 then v2 else v1

let rec max_list f = function
  | [] -> (-1, max_f), (-1, max_f)
  | a::l ->
      let (mina, maxa) = f a in
      let (minl, maxl) = max_list f l in
      (max_v mina minl, max_v maxa maxl)

(* [add_v dir v1 v2] returns the interval bound corresponding to [v1 + v2],
   when [v1], [v2] are bounds represented as pairs (sign,exp) meaning
   sign * 2^exp.
   [dir > 0] when the bound is an upper bound,
   [dir < 0] when the bound is a lower bound. *)
let add_v dir ((s1, e1) as v1) ((s2, e2) as v2) =
  if s1 = 0 then v2 else
  if s2 = 0 then v1 else
  if e1 = e2 && s1 <> s2 then (0,0.0) else
  if e1 >= e2 then
    (* s1 * 2^e1 + s2 * 2^e2 = s1 * 2^e1 * (1 + s2/s1 * 2^{e2-e1})
                             = s1 * 2^(e1 + log2(1 + s2/s1 * 2^{e2-e1})) *)
    (s1, plus (s1*dir) e1 (log2_1p (float_of_int s2 /. float_of_int s1 *. 2. ** (e2 -. e1))))
  else
    (* same as above, swapping v2 and v1 *)
    (s2, plus (s2*dir) e2 (log2_1p (float_of_int s1 /. float_of_int s2 *. 2. ** (e1 -. e2))))
  
(* [add_interv i1 i2] returns the interval of x1 + x2, when
   [x1 \in i1] and [x2 \in i2]. *)
let add_interv (min1,max1) (min2,max2) =
  (add_v (-1) min1 min2, add_v 1 max1 max2)

(* [mult_v dir v1 v2] returns the interval bound corresponding to [v1 * v2],
   when [v1], [v2] are bounds represented as pairs (sign,exp) meaning
   sign * 2^exp.
   [dir > 0] when the bound is an upper bound,
   [dir < 0] when the bound is a lower bound. *)
let mult_v dir (s1, e1) (s2, e2) =
  let sign = s1*s2 in
  if sign = 0 then (0, 0.0) else
  (sign, plus (sign*dir) e1 e2)
      
(* [mult_interv i1 i2] returns the interval of x1 * x2, when
   [x1 \in i1] and [x2 \in i2]. *)
let mult_interv (min1,max1) (min2,max2) =
  let v1min = mult_v (-1) min1 min2 in
  let v2min = mult_v (-1) min1 max2 in
  let v3min = mult_v (-1) max1 max2 in
  let v4min = mult_v (-1) max1 min2 in
  let min = min_v (min_v v1min v2min) (min_v v3min v4min) in
  let v1max = mult_v 1 min1 min2 in
  let v2max = mult_v 1 min1 max2 in
  let v3max = mult_v 1 max1 max2 in
  let v4max = mult_v 1 max1 min2 in
  let max = max_v (max_v v1max v2max) (max_v v3max v4max) in
  (min, max)

(* [order_of_magnitude_aux probaf] returns an interval
   containing for sure the value of [probaf], given the estimates
   provided by the user *)
let rec order_of_magnitude_aux probaf =
  match probaf with
  | Add(p1,p2) ->
      add_interv (order_of_magnitude_aux p1) (order_of_magnitude_aux p2)
  | Sub(p1,p2) ->
      let ((sign2min, e2min), (sign2max, e2max)) = order_of_magnitude_aux p2 in
      add_interv (order_of_magnitude_aux p1) ((-sign2max, e2max), (-sign2min, e2min))
  | Zero -> zero_interv
  | EpsRand _ | EpsFind -> let v = (1, min_f) in (v,v)
  | Max(l) ->
      max_list order_of_magnitude_aux l 
  | Cst x ->
      if x = 0.0 then zero_interv else
      if x < 0.0 then
	let v = (-1, log2 (-. x)) in
	(v,v)
      else
	let v = (1, log2 x) in
	(v,v)
  | PColl1Rand t ->
      ((1, float_of_int (Terms.get_pcoll1_low t)),
       (1, float_of_int (Terms.get_pcoll1_high t)))
  | PColl2Rand t ->
      ((1, float_of_int (Terms.get_pcoll2_low t)),
       (1, float_of_int (Terms.get_pcoll2_high t)))
  | Card t ->
      ((1, float_of_int (Terms.get_size_low t)),
       (1, float_of_int (Terms.get_size_high t)))
  | Count p -> (1,0.0),(1, float_of_int p.psize)
  | Div(p1, p2) ->
      let ((sign2min, e2min), (sign2max, e2max)) = order_of_magnitude_aux p2 in
      if sign2min <= 0 && sign2max >= 0 then
        ((-1, max_f), (1, max_f)) (* may divide by 0, can take any value *)
      else (* sign2max = sign2min *)
	mult_interv (order_of_magnitude_aux p1)
	  ((sign2max, minus (-sign2max) e2max), (sign2min, minus sign2min e2min))
	(* s*2^e2min <= p2 <= s*2^e2max
	   s*2^-e2max <= 1/p2 <= s*2^-e2min *)
  | Mul(p1, p2) ->
      mult_interv (order_of_magnitude_aux p1) (order_of_magnitude_aux p2)
  | Proba (p,_) ->
      if !Settings.trust_size_estimates then
        (1, min_f), (1, float_of_int (- p.pestimate))
      else
	zero_interv (* Accept all collisions *)
  | _ ->
      Parsing_helper.internal_error "Unexpected probability in Proba.is_smaller_proba_type"

(* [order_of_magnitude probaf] returns an integer [n] such that
   [probaf <= 2^n] ([n] is typically negative) *)
let order_of_magnitude probaf =
  let (_, (sign_max, exp_max)) = order_of_magnitude_aux probaf in
  match sign_max with
  | 1 -> int_of_float (ceil exp_max) 
  | 0 | -1 -> min_int
  | _ -> Parsing_helper.internal_error "unexpected sign"

(* [is_1_over_card_t ty probaf] returns true when [probaf = 1/|ty|]
   (up to probability eps_rand) *)
let rec is_1_over_card_t ty = function
  | Add(p, EpsRand _) -> is_1_over_card_t ty p
  | Div(Cst 1.0, Card ty') -> ty == ty'
  | _ -> false
		
let is_small_enough_coll_elim (proba_l, (proba_t, dep_types, full_type, indep_types)) =
  if !Settings.trust_size_estimates then
    Terms.plus (order_of_magnitude proba_t)
      (Terms.plus (Terms.sum_list Terms.get_size_high dep_types)
	 (Terms.sum_list (fun ri -> Terms.get_size_high ri.ri_type) proba_l))
      <= - (!Settings.tysize_MIN_Coll_Elim)
  else
    try
      let size_proba =
	if dep_types == [] then
	  order_of_magnitude proba_t
	else if is_1_over_card_t full_type proba_t then
	  - (Terms.max_list Terms.get_size_low indep_types)
	else
	  raise Not_found
      in
      List.exists (fun (factor_bound, type_bound) ->
	(size_proba <= - type_bound) && 
	(is_smaller proba_l factor_bound)
	  ) (!Settings.allowed_collisions)
    with Not_found ->
      false
	
let is_small_enough_collision (proba_l, proba) =
  if !Settings.trust_size_estimates then
    Terms.plus (order_of_magnitude proba)
	 (Terms.sum_list (fun ri -> Terms.get_size_high ri.ri_type) proba_l)
      <= - (!Settings.tysize_MIN_Coll_Elim)
  else
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
      if is_small_enough_coll_elim (b1.args_at_creation @ b2.args_at_creation, (pcoll2rand b1.btype, [], b1.btype, [b1.btype])) then
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
      if is_small_enough_collision (!accu, proba) then
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
