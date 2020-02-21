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

let min_f = float_of_int Settings.min_exp
let max_f = float_of_int Settings.max_exp
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
  | 0 | -1 -> Settings.min_exp
  | _ -> Parsing_helper.internal_error "unexpected sign"

(* [is_1_over_card_t ty probaf] returns true when [probaf = 1/|ty|]
   (up to probability eps_rand) *)
let rec is_1_over_card_t ty = function
  | Add(p, EpsRand _) -> is_1_over_card_t ty p
  | Div(Cst 1.0, Card ty') -> ty == ty'
  | _ -> false
		
let is_small_enough_coll_elim p =
  (* The probability is
     \prod_{ri \in p.p_ri_list} |ri.ri_type| * p.p_proba * \prod_{T \in p.p_dep_types} T *)
  if !Settings.trust_size_estimates then
    let prod_ri_list = Terms.sum_list (fun ri -> Terms.get_size_high ri.ri_type) p.p_ri_list in
    (Terms.plus (order_of_magnitude p.p_proba)
       (Terms.plus (Terms.sum_list Terms.get_size_high p.p_dep_types) prod_ri_list)
       <= - (!Settings.tysize_MIN_Coll_Elim))
    ||
      ((is_1_over_card_t p.p_full_type p.p_proba) &&
       (match p.p_indep_types_option with
       | Some indep_types ->
	   (* proba_t = 1/|p.p_full_type| and \prod_{T \in p.p_dep_types} T <= |p.p_full_type| / \prod_{T \in indep_types} |T|
	      so the probability is <= \prod_{ri \in p.p_ri_list} |ri.ri_type| / \prod_{T \in indep_types} |T| *)
	   Terms.plus (order_of_magnitude (Div(Cst 1.0, Polynom.p_prod (List.map (fun ty -> Card ty) indep_types))))
	     prod_ri_list
	     <= - (!Settings.tysize_MIN_Coll_Elim)
       | None -> false))
  else
    try
      let size_proba =
	if p.p_dep_types == [] then
	  order_of_magnitude p.p_proba
	else if is_1_over_card_t p.p_full_type p.p_proba then
	  match p.p_indep_types_option with
	  | Some indep_types -> - (Terms.max_list Terms.get_size_low indep_types)
	  | None -> raise Not_found
	else
	  raise Not_found
      in
      List.exists (fun (factor_bound, type_bound) ->
	(size_proba <= - type_bound) && 
	(is_smaller p.p_ri_list factor_bound)
	  ) (!Settings.allowed_collisions)
    with Not_found ->
      false
	
let is_small_enough_collision p =
  if !Settings.trust_size_estimates then
    is_small_enough_coll_elim p
  else
    (p.p_dep_types == []) && (List.exists (is_smaller p.p_ri_list) (!Settings.allowed_collisions_collision))
  

let whole_game = ref Terms.empty_game
let time_for_whole_game = ref None
    
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

let eliminated_collisions = ref ([] : binder_coll_t list)

let equal_coll (b1, b2) (b1',b2') =
  ((b1 == b1') && (b2 == b2')) ||
  ((b1 == b2') && (b2 == b1'))
  
let add_elim_collisions b1 b2 =
  let new_coll = (b1, b2) in
  if not (List.exists (equal_coll new_coll) (!eliminated_collisions)) then
    begin
      if is_small_enough_coll_elim
	  { p_ri_list = b1.args_at_creation @ b2.args_at_creation;
	    p_proba = pcoll2rand b1.btype;
	    p_dep_types = [];
	    p_full_type = b1.btype;
	    p_indep_types_option = None } then
	begin
	  eliminated_collisions := new_coll :: (!eliminated_collisions);
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


let red_proba = ref ([]: red_proba_t list)
    
let get_time() =
  match !time_for_whole_game with
  | Some t -> t
  | None ->
      let t = Time (!whole_game, Computeruntime.compute_runtime_for (!whole_game)) in
      time_for_whole_game := Some t;
      t
    
let rec collect_array_indexes accu t =
  match t.t_desc with
    ReplIndex(b) ->
	if not (List.memq b (!accu)) then
	  accu := b:: (!accu)
  | Var(b,l) -> List.iter (collect_array_indexes accu) l
  | FunApp(f,l) -> List.iter (collect_array_indexes accu) l
  | _ -> Parsing_helper.internal_error "If/let/find/new unexpected in collect_array_indexes"

(* [match_term_any_var any_vars_opt next_f t t' ()] calls [next_f()] when [t']
   is an instance of [t], with
   any value for the [?] variables when [any_vars_opt == None],
   values stored in links for variables in the list [any_vars] 
   when [any_vars_opt = Some any_vars],
   and values stored in links for replication indices.
   It raises [NoMatch] when [t'] is not an instance of [t]. *)

let any_term_name = "?"

let match_term_any_var any_vars_opt = 
  (* [get_var_link] function associated to [match_term_any_var].
     See the interface of [Terms.match_funapp] for the 
     specification of [get_var_link]. *)
  let get_var_link t () =
    match t.t_desc, any_vars_opt with
      Var (v,[]), None when v.sname==any_term_name -> Some(v.link, true)
    | Var (v,[]), Some any_vars when List.memq v any_vars -> Some(v.link, true)
    | ReplIndex (v), _ -> Some(v.ri_link, false)
    | _ -> None
  in
  let cleanup =
    if any_vars_opt == None then
      Terms.ri_auto_cleanup_failure
    else
      fun f -> Terms.auto_cleanup (fun () ->
       Terms.ri_auto_cleanup f)
  in
  let rec aux next_f t t' () =
    cleanup (fun () ->
      match t.t_desc, t'.t_desc, any_vars_opt with
      | Var(v,[]), _, None when v.sname==any_term_name -> next_f()
      | Var(v,[]), _, Some any_vars when List.memq v any_vars -> 
          (* Check that types match *)
          if t'.t_type != v.btype then
            raise NoMatch;
          begin
            match v.link with
            | NoLink -> Terms.link v (TLink t')
            | TLink t -> if not (Terms.equal_terms t t') then raise NoMatch
          end;
          next_f()
      | ReplIndex(v), _, _ -> 
          (* Check that types match *)
	  if t'.t_type != v.ri_type then
	    raise NoMatch;
	  begin
	    match v.ri_link with
	      NoLink -> Terms.ri_link v (TLink t')
	    | TLink t -> if not (Terms.equal_terms t t') then raise NoMatch
	  end;
	  next_f()
      | Var(b,l), Var(b',l'), _ when b == b' -> 
	  Match_eq.match_term_list aux next_f l l' ()
      | FunApp(f,l), FunApp(f',l'), _ when f == f' ->
	  Match_eq.match_funapp aux get_var_link Match_eq.default_match_error Terms.simp_facts_id next_f t t' ()
      | _ -> raise NoMatch
	    )
  in
  aux 
    
(* The function [instantiate_ri_list] replace indices with their
   value stored in links, inside the [p_ri_list] field
   of [probaf_mul_types].
   The functions [copy_probaf], [copy_probaf_mul_types],
   [copy_instantiated_coll_statement], [copy_red_proba] copy 
   respectively probabilities, probaf_mul_types, instantiated
   collision statements, and red_proba_t, following links
   according to [transf] (see [Terms.copy_transf]). 
   For [copy_probaf_mul_types] and [copy_red_proba], 
   [transf] must be [Terms.Links_RI] or [Terms.Links_RI_Vars],
   to be coherent with following links in replication indices
   in [instantiate_ri_list].
   *)
    
let rec instantiate_ri_list accu = function
  | [] -> accu
  | ri::ri_list ->
      match ri.ri_link with
      | NoLink -> instantiate_ri_list (ri::accu) ri_list
      | TLink t ->
	  let l = ref accu in
	  collect_array_indexes l t;
	  instantiate_ri_list (!l) ri_list

let copy_probaf transf p =
  let rec aux = function
  | Time(g,x) -> Time(g, aux x)
  | (AttTime | Cst _ | Count _ | OCount _ | Zero | Card _ | TypeMaxlength _
     | EpsFind | EpsRand _ | PColl1Rand _ | PColl2Rand _) as x -> x
  | Proba(p,l) -> Proba(p, List.map aux l)
  | ActTime(f,l) -> ActTime(f, List.map aux l)
  | Maxlength(g,t) -> Maxlength(g, Terms.copy_term transf t)
  | Length(f,l) -> Length(f, List.map aux l)
  | Mul(x,y) -> Mul(aux x, aux y)
  | Add(x,y) -> Add(aux x, aux y)
  | Sub(x,y) -> Sub(aux x, aux y)
  | Div(x,y) -> Div(aux x, aux y)
  | Max(l) -> Max(List.map aux l)
  in
  aux p
    
let copy_probaf_mul_types transf p =
  (* Note: in case probaf refers to terms (via maxlength), we
     might need to instantiate probaf as well. That is not
     common for collisions, but I do it for safety. *)
  { p with
    p_ri_list = instantiate_ri_list [] p.p_ri_list;
    p_proba = copy_probaf transf p.p_proba }
	
let copy_instantiated_coll_statement transf ic =
  { ic_restr = List.map (Terms.copy_term transf) ic.ic_restr;
    ic_redl = Terms.copy_term transf ic.ic_redl;
    ic_proba = copy_probaf transf ic.ic_proba;
    ic_redr = Terms.copy_term transf ic.ic_redr;
    ic_indep_cond = Terms.copy_term transf ic.ic_indep_cond;
    ic_side_cond = Terms.copy_term transf ic.ic_side_cond;
    ic_restr_may_be_equal = ic.ic_restr_may_be_equal }
    
let copy_red_proba transf r =
  let instan_binding (b,t) = (b, Terms.copy_term transf t) in
  { r_coll_statement = r.r_coll_statement;
    r_restr_indep_map = List.map instan_binding r.r_restr_indep_map;
    r_any_var_map_list = { source = r.r_any_var_map_list.source;
			   images = List.map (List.map (Terms.copy_term transf))
			     r.r_any_var_map_list.images };
    r_i_coll_statement = copy_instantiated_coll_statement transf r.r_i_coll_statement;
    r_proba = copy_probaf_mul_types transf r.r_proba }

(* [equal_probaf_mul_types p p'] returns true when the
   [probaf_mul_types] elements [p] and [p'] represent
   the same probability *)
    
let equal_probaf_mul_types p p' =
  (Terms.equal_lists_sets_q p.p_ri_list p'.p_ri_list) &&
  (Terms.equal_probaf p.p_proba p'.p_proba) &&
  (Terms.equal_lists (==) p.p_dep_types p'.p_dep_types) &&
  (match p.p_indep_types_option, p'.p_indep_types_option with
  | None, None -> true
  | Some l, Some l' -> (* full_type does not matter when indep_types = None *)
      (p.p_full_type == p'.p_full_type) && (Terms.equal_lists (==) l l')
  | _ -> false)

(* [match_instantiated_coll_statement any_vars next_f ic ic'] 
   performs matching on instantiated collision statements. 
   It calls [next_f()] when [ic'] is an instance of [ic], 
   with replication indices and variables in [any_vars] (in [ic]) linked
   to the values that transform [ic] into [ic'].
   It raises [NoMatch] when [ic'] is not an instance of [ic].

   [match_red r r'] returns [Some r''] when the [red_proba_t] element
   [r'] is a particular case [r]. Then [r''] is a modified version of
   [r] with added elements in [r_any_var_map_list], so that [r'']
   includes both [r] and [r']. 
   Otherwise, it returns [None]. *)
    
let match_instantiated_coll_statement any_vars next_f ic ic' =
  if ic.ic_restr_may_be_equal != ic'.ic_restr_may_be_equal then raise NoMatch;
  let match_term = match_term_any_var (Some any_vars) in
  (* All variables are instantiated by matching [redl] with [redl'] *)
  match_term (fun () ->
    let proba_i = copy_probaf Terms.Links_RI_Vars ic.ic_proba in
    if not (Terms.equal_probaf proba_i ic'.ic_proba) then raise NoMatch;
    let redr_i = Terms.copy_term Terms.Links_RI_Vars ic.ic_redr in
    if not (Terms.equal_terms redr_i ic'.ic_redr) then raise NoMatch;
    let indep_cond_i = Terms.copy_term Terms.Links_RI_Vars ic.ic_indep_cond in
    if not (Terms.equal_terms indep_cond_i ic'.ic_indep_cond) then raise NoMatch;
    let side_cond_i = Terms.copy_term Terms.Links_RI_Vars ic.ic_side_cond in
    if not (Terms.equal_terms side_cond_i ic'.ic_side_cond) then raise NoMatch;
    let restr_i = List.map (Terms.copy_term Terms.Links_RI_Vars) ic.ic_restr in
    if not (Terms.equal_lists_sets Terms.equal_terms restr_i ic'.ic_restr) then raise NoMatch;
    next_f ()
      ) ic.ic_redl ic'.ic_redl ()

let instantiate_any_var_image any_vars any_vars' any_vars_image' =
  List.iter2 (fun b t -> b.link <- TLink t) any_vars' any_vars_image';
  let any_var_image'' =
    List.map (fun b ->
      Terms.copy_term Terms.Links_Vars (Terms.get_tlink b)) any_vars
  in
  List.iter (fun b -> b.link <- NoLink) any_vars';
  any_var_image''
    
let matches_red r r' =
  try 
    match_instantiated_coll_statement r.r_any_var_map_list.source
      (fun () -> 
	let proba_inst = copy_probaf_mul_types Terms.Links_RI_Vars r.r_proba in
	if equal_probaf_mul_types proba_inst r'.r_proba then
          (* matches *)
	  let any_var_map_list'' =
	    { source = r.r_any_var_map_list.source;
	      images = 
	      List.fold_left (fun accu elem ->
		let elem_i = instantiate_any_var_image r.r_any_var_map_list.source r'.r_any_var_map_list.source elem in
		if List.exists (Terms.equal_term_lists elem_i) accu then accu else elem_i::accu
			      ) r.r_any_var_map_list.images r'.r_any_var_map_list.images
	    }
	  in
	  Some { r with r_any_var_map_list = any_var_map_list'' }
	else
	  None
	(* For speed, we do not reconsider other ways to match the 3 terms
	   when the probabilities differ, so we return None instead of 
	   raising NoMatch  *)
	      ) r.r_i_coll_statement r'.r_i_coll_statement
  with NoMatch ->
    None

(* [includes_red red1 red2] is true when the [red_proba_t] element
   [red1] includes [red2] *)
      
let includes_red red1 red2 =
  match matches_red red1 red2 with
  | None -> false
  | Some red1' ->
      (* Check that [red1' = red1]. The only change is that elements may be added to [r_any_var_map_list] *)
      List.length red1.r_any_var_map_list.images = List.length red1'.r_any_var_map_list.images

(* [equal_red red1 red2] is true when the [red_proba_t] elements
   [red1] and [red2] are equal *)
	
let equal_red red1 red2 =
  (includes_red red1 red2) && (includes_red red2 red1)

(* [add_proba_red_inside new_red] adds an element [new_red: red_proba_t] to
   [red_proba]. It tries to merge with existing elements in [red_proba_t]
   if possible. *)
    
let add_proba_red_inside new_red =
  if is_small_enough_collision new_red.r_proba then
    begin
      let rec find_more_general_coll = function
	  [] -> raise Not_found
	| (red :: rest) ->
	    match matches_red red new_red with
	      Some red'' -> red'' :: rest
	    | None -> red :: (find_more_general_coll rest)
      in
      begin
	try
	  red_proba := find_more_general_coll (!red_proba)
	with Not_found ->
	  let new_red_ref = ref new_red in
	  let red_proba' = List.filter (fun red -> 
	    match matches_red (!new_red_ref) red with
	      None -> true
	    | Some red'' -> new_red_ref := red''; false) (!red_proba)
	  in
	  red_proba := (!new_red_ref) :: red_proba'
      end;
      true
    end
  else
    false

(**** Registering an application of a collision statement in [red_proba] *)

(* [occurs_proba any_var_map p] is true when a variable in [any_var_map]
   occurs in the probability [p]. *)
      
let occurs_proba any_var_map p =
  let rec aux = function
    | Maxlength(_,t) ->
	List.exists (fun (b,_) -> Terms.refers_to b t) any_var_map
    | Zero | Cst _ | Count _ | OCount _ | Card _ | EpsFind | EpsRand _
    | PColl2Rand _ | PColl1Rand _ | AttTime | TypeMaxlength _ | Time _ -> false
    | Proba(_,l) | Max(l) | ActTime(_,l) | Length(_,l) ->
	List.exists aux l
    | Add(p1,p2) | Mul(p1,p2) | Sub(p1,p2) | Div(p1,p2) ->
	(aux p1) || (aux p2)
  in
  aux p

(* [forget_array_args t] returns the term obtained by removing
   array indices from all variables in [t]. Used for the 
   terms [t] in the probability formula [Maxlength(g,t)] *)
    
let rec forget_array_args t =
  match t.t_desc with
  | Var(b,_) -> Terms.term_from_binder b
  | FunApp(f,l) ->
      Terms.build_term t (FunApp(f, List.map forget_array_args l))
  | _ -> assert false

(* special function symbol to encode independence conditions 
   as terms *)
	
let indep_fun = { f_name = "independent-of";
		  f_type = [Settings.t_any; Settings.t_any], Settings.t_bool;
		  f_cat = Std;
		  f_options = 0;
		  f_statements = [];
		  f_collisions = [];
		  f_eq_theories = NoEq;
		  f_impl = No_impl;
		  f_impl_inv = None;
		}

(* [copy_indep_cond transf ic] copies the independence condition [ic]
   following links according to [transf], and transforming the result
   into a term *)
    
let rec copy_indep_cond transf = function
  | IC_True -> Terms.make_true()
  | IC_Or(c1, c2) -> Terms.make_or (copy_indep_cond transf c1) (copy_indep_cond transf c2)
  | IC_And(c1, c2) -> Terms.make_and (copy_indep_cond transf c1) (copy_indep_cond transf c2)
  | IC_Indep(b1, b2) ->
      Terms.app indep_fun [ Terms.copy_term transf (Terms.term_from_binder b1);
			    Terms.copy_term transf (Terms.term_from_binder b2) ]

(* [instantiate_coll_statement c restr_indep_map] instantiate the
   collision statement [c] by replacing variables according to
   [restr_indep_map]. The result is an instantiated collision
   statement, of type [instantiated_collision].
   The change of type is because restrictions become
   variables potentially with array indices, so they are represented
   as [term] rather than [binder], and instantiated
   independence conditions are represented as [term] instead of
   [indep_cond] because variables inside the condition become
   terms, and because that makes easier to program matching
   on instantiated independence conditions, using functions on terms. *)
	
let instantiate_coll_statement c restr_indep_map =
  List.iter (fun (b,t) -> b.link <- TLink t) restr_indep_map;
  let c' =
    { ic_restr = List.map Terms.get_tlink c.c_restr;
      ic_redl = Terms.copy_term Terms.Links_Vars c.c_redl;
      ic_proba = copy_probaf Terms.Links_Vars c.c_proba;
      ic_redr = Terms.copy_term Terms.Links_Vars c.c_redr;
      ic_indep_cond = copy_indep_cond Terms.Links_Vars c.c_indep_cond;
      ic_side_cond = Terms.copy_term Terms.Links_Vars c.c_side_cond;
      ic_restr_may_be_equal = c.c_restr_may_be_equal }
  in
  List.iter (fun (b,t) -> b.link <- NoLink) restr_indep_map;
  c' 

(* [add_proba_red coll_statement restr_indep_map any_var_map]
   adds the probability information for applying the collision
   statement [coll_statement] with variables instantiated
   as specified by [restr_indep_map] and [any_var_map]. *)
    
let add_proba_red coll_statement restr_indep_map any_var_map =
  let accu = ref [] in
  List.iter (fun (_,t) -> collect_array_indexes accu t) restr_indep_map;
  let indices = !accu in
  let any_var_map_list =
    { source = List.map fst any_var_map;
      images = 
        if occurs_proba any_var_map coll_statement.c_proba then
	  [List.map (fun (b, t) -> forget_array_args t) any_var_map]
	else
	  []
    }
  in
  let instantiated_coll_statement = instantiate_coll_statement coll_statement restr_indep_map in
  add_proba_red_inside { r_coll_statement = coll_statement;
			 r_restr_indep_map = restr_indep_map;
			 r_any_var_map_list = any_var_map_list;
			 r_i_coll_statement = instantiated_coll_statement;
			 r_proba = { p_ri_list = indices;
				     p_proba = coll_statement.c_proba;
				     p_dep_types = [];
				     p_full_type = coll_statement.c_redl.t_type;
				     p_indep_types_option = None }}

(* [proba_for probaf_mul_types] returns the probability equal
   to the probability multiplied by cardinals of types in
   [probaf_mul_types]. It also displays this probability. *)

let proba_for p =
  let lindex = List.map (fun array_idx -> card array_idx.ri_type) p.p_ri_list in
  let ltypes = List.map (fun ty -> Card ty) p.p_dep_types in
  let p = Polynom.p_prod (p.p_proba :: ltypes @ lindex) in
  print_string " Probability: ";  
  Display.display_proba 0 p;
  print_newline();
  p

(* [instan_time restr_indep_map any_var_map_list p] instantiates
   the runtime of the adversary, using the runtime of the current
   game, in the probability [p] and instantiates variables in
   [Maxlength(g,t)] inside [p] according to [restr_indep_map]
   and [any_var_map_list] *)
    
let rec instan_time restr_indep_map any_var_map_list p =
  let rec aux = function
    | AttTime -> Add(AttTime, get_time())
    | Time _ -> Parsing_helper.internal_error "unexpected time"
    | (Cst _ | Count _ | OCount _ | Zero | Card _ | TypeMaxlength _
      | EpsFind | EpsRand _ | PColl1Rand _ | PColl2Rand _) as x -> x
    | Proba(p,l) -> Proba(p, List.map aux l)
    | ActTime(f,l) -> ActTime(f, List.map aux l)
    | (Max _ | Maxlength _) as y ->
	let accu = ref Polynom.empty_max_accu in
	let rec add_max = function
	  | Max(l) -> List.iter add_max l
	  | Maxlength(g,t) ->
	      List.iter (fun (b,t) ->
		b.link <- TLink t) restr_indep_map;
	      begin
		match any_var_map_list.images with
		| [] -> 
		    Computeruntime.make_length_term accu (!whole_game)
		      (Terms.copy_term Terms.Links_Vars t);
		| _ ->
		    List.iter (fun any_var_map ->
		      List.iter2 (fun b t ->
			b.link <- TLink t) any_var_map_list.source any_var_map;
		      Computeruntime.make_length_term accu (!whole_game)
			(Terms.copy_term Terms.Links_Vars t)
			) any_var_map_list.images;
		    List.iter (fun b ->
		      b.link <- NoLink) any_var_map_list.source
	      end;
	      List.iter (fun (b,t) ->
		b.link <- NoLink) restr_indep_map
	  | x -> Polynom.add_max accu (aux x)
	in
	add_max y;
	Polynom.p_max (!accu)
    | Length(f,l) -> Length(f, List.map aux l)
    | Mul(x,y) -> Mul(aux x, aux y)
    | Add(x,y) -> Add(aux x, aux y)
    | Sub(x,y) -> Sub(aux x, aux y)
    | Div(x,y) -> Div(aux x, aux y)
  in
  aux p
    
(* [proba_for_red_proba r] displays and records the probability
   for applying a collision statement as specified by
   [r: red_proba_t] *)
    
let proba_for_red_proba r =
  print_string "Applied ";
  Display.display_collision r.r_coll_statement;
  if r.r_restr_indep_map != [] then
    begin
      print_string " with ";
      Display.display_list (fun (b, t) ->
	Display.display_binder b;
	print_string " -> ";
	Display.display_term t
	  ) (List.rev r.r_restr_indep_map)
    end;
  let proba = instan_time r.r_restr_indep_map r.r_any_var_map_list r.r_proba.p_proba in
  proba_for { r.r_proba with p_proba = proba }


(* Initialization *)

let reset coll_elim g =
  whole_game := g;
  time_for_whole_game := None;
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
  List.iter (fun red_proba_info -> add_proba (proba_for_red_proba red_proba_info))
    (!red_proba);
  List.iter add_proba coll_list;
  let r = Polynom.polynom_to_probaf (Polynom.probaf_to_polynom (!proba)) in
  eliminated_collisions := [];
  red_proba := [];
  elim_collisions_on_password_occ := [];
  whole_game := Terms.empty_game;
  time_for_whole_game := None;
  if r == Zero then [] else [ SetProba r ]

let get_current_state() =
  (!eliminated_collisions, !red_proba)

let restore_state (ac_coll, ac_red_proba) =
  eliminated_collisions := ac_coll;
  red_proba := ac_red_proba

let get_and_empty_state() =
  let res = (!eliminated_collisions, !red_proba) in
  eliminated_collisions := [];
  red_proba := [];
  res
