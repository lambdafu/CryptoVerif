open Types

(* 1. Operations on polynoms *)

let ovf_exp = "Overflow in exponent"
  
let zero = []
    
let equal_factor (p,n) (p',n') = (n==n') && (Terms.equal_probaf p p')

let rec remove_factor f = function
    [] -> raise Not_found
  | (a::l) -> if equal_factor f a then l else a::(remove_factor f l)

let same_monomial m1 m2 =
  let m2ref = ref m2 in
  try 
    List.iter (fun f -> m2ref := remove_factor f (!m2ref)) m1;
    (!m2ref) = []
  with Not_found -> false

let rec find_monomial m = function
    [] -> raise Not_found
  | (((coef,a) as x)::l) -> 
      if same_monomial a m then (coef,l) else 
      let (coef',l') = find_monomial m l in
      (coef',x::l')

(* [sum p1 p2] is the polynom [p1 + p2], where [p1] and [p2] are polynoms *)
	
let rec sum p1 = function
    [] -> p1
  | ((coef,a)::l) ->
      try
	let (coef',l') = find_monomial a p1 in
	let coefs = coef +. coef' in
	if coefs = 0.0 then
	  sum l' l
	else
	  (coefs,a)::(sum l' l)
      with Not_found ->
	(coef,a)::(sum p1 l)

(* [max p1 p2] is a polynom upper bound of the maximum of two polynoms 
   [p1] and [p2], assuming all variables are positive or zero *)
		     
let max_float a b =
  if a > b then a else b

let rec max p1 = function
    [] -> p1
  | ((coef,a)::l) ->
      try
	let (coef',l') = find_monomial a p1 in
	(max_float coef coef',a)::(max l' l)
      with Not_found ->
	(coef,a)::(max p1 l)

(* [sub p1 p2] is the polynom [p1 - p2], where [p1] and [p2] are polynoms *)
		     
let rec sub p1 = function
    [] -> p1
  | ((coef,a)::l) ->
      try
	let (coef',l') = find_monomial a p1 in
	let coefd = coef' -. coef in
	if coefd = 0.0 then
	  sub l' l
	else
	  (coefd,a)::(sub l' l)
      with Not_found ->
	(0. -. coef,a)::(sub p1 l)

(* [product p1 p2] is the polynom [p1 * p2], where [p1] and [p2] are polynoms *)

let rec product_monomial m1 = function
    [] -> m1
  | (e,n)::l -> 
      try
	let n' = List.assoc e m1 in
	(e,Parsing_helper.add_check_overflow ovf_exp Parsing_helper.dummy_ext n n')::
	(product_monomial (remove_factor (e,n') m1) l)
      with Not_found ->
	(e,n)::(product_monomial m1 l)

let rec product_pol_monomial (coef,a) = function
    [] -> []
  | (coef',a')::l -> 
      sum [coef *. coef', product_monomial a a'] (product_pol_monomial (coef,a) l)

let rec product p1 = function
    [] -> []
  | a::l -> sum (product_pol_monomial a p1) (product p1 l)

(* [power_to_polynom to_polynom to_proba p n] is the polynom
   [to_polynom (p^n)] where [p] is a probability formula, and
   [to_polynom] maps probability formulas to polynoms and maps
   product, division, and power to product, division, and power
   respectively.

   [to_proba] is a function that takes a probability formula [f]
   and its conversion [p = to_polynom f], and returns a 
   probability formula equal to [p].
   Two cases can happen:
   1/ [to_polynom] maps each probability formula to a polynom
   representing the same value, i.e. [to_polynom = probaf_to_polynom]. 
   In this case, we can use [to_proba = fun f p -> f]: 
   [to_proba] reuses the original probability formula [f] as conversion
   of [p]. This is what happen in [probaf_to_polynom] below.
   2/ [to_polynom] modifies the probability formula.
   In this case, we should use [to_proba = fun f p -> polynom_to_probaf p].
   This is what happens in the exported function [power_to_polynom_map]. *)
	
let power_monomial a n =
  List.map (fun (p,n') ->
    (p, Parsing_helper.mul_check_overflow ovf_exp Parsing_helper.dummy_ext n' n)) a
	
let p_inv = function
  | Div(Cst 1.0, x) -> x
  | Div(x,y) -> Div(y,x)
  | y -> Div(Cst 1.0, y)
	
let power_inv_monomial a n =
  List.map (fun (p,n') ->
    (p_inv p, Parsing_helper.mul_check_overflow ovf_exp Parsing_helper.dummy_ext n' n)) a

let power (coef,a) n =
  if n = 0 then
    [1.0, []]
  else if n > 0 then
    [coef ** (float_of_int n), power_monomial a n]
  else (* n < 0 *)
    [coef ** (float_of_int n), power_inv_monomial a (-n)]
    
let power_to_polynom to_polynom to_proba p n =
  let rec aux f n = 
    match n with
    | 0 -> [1.0, []]
    | 1 -> to_polynom f
    | 2 ->
	let p = to_polynom f in
	product p p
    | _ ->
	match f with
	| Mul(x,y) -> product (aux x n) (aux y n)
	| Div(x,y) ->
	    if n = min_int then
	      Parsing_helper.raise_user_error "overflow in exponent";
	    product (aux x n) (aux y (-n))
	| Power(x,n') ->
	    aux x
	      (Parsing_helper.mul_check_overflow ovf_exp Parsing_helper.dummy_ext n' n)
	| _ ->
	    match to_polynom f with
	    | [] -> []
	    | [monomial] -> power monomial n
	    | p ->
		let f' = to_proba f p in 
		if n > 0 then
		  [1.0,[f',n]]
		else
		  [1.0,[p_inv f',-n]]
  in
  aux p n

(* Tests. They answer true only when the result is true.
   In case the result is not know for sure, they answer false. *)

let is_constant = function
  | [] | [_,[]] -> true
  | _ -> false
    
let is_zero p = (p = [])

let rec is_proba_nonnegative = function
  | Proba _ | Count _ | OCount _ | Zero | Card _ | EpsFind | EpsRand _
  | PColl2Rand _ | PColl1Rand _ | AttTime | Time _ | ActTime _
  | Maxlength _ | TypeMaxlength _ | Length _ ->
      true
  | Cst f -> f >= 0.0
  | Max l -> List.exists is_proba_nonnegative l
  | Min l -> List.for_all is_proba_nonnegative l
  | Add(p1,p2) | Mul(p1,p2) | Div(p1,p2) | OptimIf(_, p1, p2) ->
      (is_proba_nonnegative p1) && (is_proba_nonnegative p2)
  | Sub _ -> false
  | Power(p,n) ->
      (n mod 2 = 0) || (is_proba_nonnegative p)
    
let is_factor_nonnegative (f,n) =
  (n mod 2 = 0) ||
  (is_proba_nonnegative f)
    
let is_monomial_nonnegative (coef,a) =
  (coef >= 0.0) && (List.for_all is_factor_nonnegative a)
    
let is_nonnegative p =
  List.for_all is_monomial_nonnegative p
    
let rec is_proba_positive = function
  | Card _ | EpsFind | EpsRand _ | PColl2Rand _ | PColl1Rand _
  | AttTime | Time _ | ActTime _ | Maxlength _ | TypeMaxlength _ ->
      true
  | Proba _ | Count _ | OCount _ | Zero | Length _ ->
      false
  | Cst f -> f > 0.0
  | Max l -> List.exists is_proba_positive l
  | Min l -> List.for_all is_proba_positive l
  | Add(p1,p2) ->
      ((is_proba_positive p1) && (is_proba_nonnegative p2)) ||
      ((is_proba_positive p2) && (is_proba_nonnegative p1))
  | Mul(p1,p2) | Div(p1,p2) | OptimIf(_, p1, p2) ->
      (is_proba_positive p1) && (is_proba_positive p2)
  | Sub _ -> false
  | Power(p,n) ->
      is_proba_positive p

let is_factor_positive (f,n) =
  is_proba_positive f

let is_monomial_positive (coef,a) =
  (coef > 0.0) && (List.for_all is_factor_positive a)

let is_positive p =
  (List.for_all is_monomial_nonnegative p) &&
  (List.exists is_monomial_positive p)

(* 2. Basic operations on probabilities, with simple simplifications *) 

let p_div(x,y) =
  match x,y with
    Zero, _ | Cst 0.0, _ -> Zero
  | Cst x', Cst y' -> if y' <> 0.0 then Cst (x' /. y') else Div(x,y)
  | _, Cst 1.0 -> x
  | _ -> Div(x,y)

let p_mul(x,y) =
  match x,y with
    Zero, _ | _, Zero | Cst 0.0, _ | _, Cst 0.0 -> Zero
  | Cst 1.0, a -> a
  | a, Cst 1.0 -> a
  | Div(Cst 1.0,x'),_ -> Div(y,x')
  | _,Div(Cst 1.0,y') -> Div(x,y')
  | _ -> Mul(x,y)

let rec p_prod = function
  [] -> Cst 1.0
| [a] -> a
| (a::l) -> p_mul(a, p_prod l)

let p_add(x,y) =
  match x,y with
    Zero, a | a, Zero | Cst 0.0, a | a, Cst 0.0 -> a
  | _ -> Add(x,y)

let p_sub(x,y) =
  match x,y with
  | a, Zero | a, Cst 0.0 -> a
  | _ -> Sub(x,y)
	
let rec p_sum = function
  | [] -> Zero
  | [a] -> a
  | (a::l) -> p_add(a, p_sum l)

type minmax_val =
  | MNone
  | MCst of float

type minmax_accu = minmax_val * probaf list

      (* max_accu = (MNone, l) -> take the maximum of l
                    (MCst x, l) -> take max(x, maximum of l) *)
      

let empty_minmax_accu = (MNone, [])
      
let p_max = function
  | MNone, [] -> Cst neg_infinity
  | MCst 0.0, [] -> Zero
  | MCst x, [] -> Cst x
  | MNone, [a] -> a
  | MCst 0.0, l -> Max(Zero :: l)
  | MCst x, l -> Max((Cst x)::l)
  | MNone, l -> Max(l)

let maxmval mv1 mv2 =
  match mv1,mv2 with
  | MNone, _ -> mv2
  | _, MNone -> mv1
  | MCst x, MCst y -> 
      if x >= y then mv1 else mv2
	
let rec add_max accu = function
  | Max(l) -> List.iter (add_max accu) l
  | x ->
      let (mval, l) = !accu in
      match x with
      | Cst y -> accu := (maxmval (MCst y) mval, l)
      | Zero -> accu := (maxmval (MCst 0.0) mval, l)
      | _ -> 
	  if not (List.exists (Terms.equal_probaf x) l) then
	    accu := (mval, x :: l)


      (* min_accu = (MNone, l) -> take the minimum of l
                    (MCst x, l) -> take min(x, minimum of l) *)
      

let p_min = function
  | MNone, [] -> Cst infinity
  | MCst 0.0, [] -> Zero
  | MCst x, [] -> Cst x
  | MNone, [a] -> a
  | MCst 0.0, l -> Min(Zero :: l)
  | MCst x, l -> Min((Cst x)::l)
  | MNone, l -> Min(l)

let minmval mv1 mv2 =
  match mv1,mv2 with
  | MNone, _ -> mv2
  | _, MNone -> mv1
  | MCst x, MCst y -> 
      if x >= y then mv2 else mv1
	
let rec add_min accu = function
  | Min(l) -> List.iter (add_min accu) l
  | x ->
      let (mval, l) = !accu in
      match x with
      | Cst y -> accu := (minmval (MCst y) mval, l)
      | Zero -> accu := (minmval (MCst 0.0) mval, l)
      | _ -> 
	  if not (List.exists (Terms.equal_probaf x) l) then
	    accu := (mval, x :: l)

(* 3.1 Conversion probaf_to_polynom *)

let rec probaf_to_polynom = function
    Zero -> []
  | Cst n -> if n = 0.0 then [] else [n,[]]
  | Mul(f1,f2) -> product (probaf_to_polynom f1) (probaf_to_polynom f2)
  | Add(f1,f2) -> sum (probaf_to_polynom f1) (probaf_to_polynom f2)
  | Sub(f1,f2) -> sub (probaf_to_polynom f1) (probaf_to_polynom f2)
  | Power(f,n) ->
      power_to_polynom probaf_to_polynom (fun f p -> f) f n
  | Div(Cst 1.0, Mul(x,y)) ->
      probaf_to_polynom (Mul(p_inv x, p_inv y))
  | Div(Cst 1.0, _) as prob -> [1.0,[prob,1]]
  | Div(f1,f2) -> probaf_to_polynom (Mul(f1, p_inv f2))
  | prob -> [1.0,[prob,1]]


(* 3.2 Conversion polynom_to_probaf *)

let rec factor_to_probaf (a,n) =
  if n < 1 then
    Parsing_helper.internal_error "not a polynomial in factor_to_probaf" 
  else if n = 1 then
    a 
  else 
    Power(a,n)

let rec factor_to_list f =
  [factor_to_probaf f]

type monomial_decomp =
    { small_factors : probaf;
      large_factors : probaf list;
      denominator : probaf list }

let rec split_monomial = function
    [] -> { small_factors = Cst 1.0;
	    large_factors = [];
	    denominator = [] }
  | ((a,n) as f)::r ->
      let r' = split_monomial r in
      match a with
	Count _ | OCount _  -> 
	  let l = factor_to_probaf f in
	  { r' with small_factors = p_mul (l, r'.small_factors) }
      |	Div(Cst 1.0, x) -> 
	  let l = factor_to_list (x,n) in
	  { r' with denominator = l @ r'.denominator }
      |	_ ->
	  let l = factor_to_list f in
	  { r' with large_factors = l @ r'.large_factors }
	  
let split_coef_monomial (coef, a) =
  let r = split_monomial a in
  { r with small_factors = p_mul(Cst coef, r.small_factors) }

let rec remove_eq_probaf a = function
    [] -> raise Not_found
  | (b::r) ->
      if Terms.equal_probaf a b then r else b::(remove_eq_probaf a r)

let rec equal_prod l1 l2 =
  match l2 with
    [] -> l1 == []
  | (a::r) ->
      try
	let l1' = remove_eq_probaf a l1 in
	equal_prod l1' r
      with Not_found -> false

let same_large_factors r r' =
  (equal_prod r.large_factors r'.large_factors) &&
  (equal_prod r.denominator r'.denominator)

let rec add_decomp r = function
    [] -> [r]
  | (a::l) ->
      if same_large_factors r a then
	let new_small_factors =
	  match r.small_factors with
	  | Cst coef when coef < 0.0 ->
	      (* Write [a.small_factors - (-coef)] rather than
                 [a.small_factors + coef] when [coef < 0] *)
	      p_sub(a.small_factors, Cst (-. coef))
	  | Mul(Cst coef, rest) when coef < 0.0 ->
	      (* Write [a.small_factors - (-coef) * rest] rather than
                 [a.small_factors + coef * rest] when [coef < 0] *)
	      p_sub(a.small_factors, p_mul(Cst (-. coef), rest))
	  | _ ->
	      p_add(a.small_factors, r.small_factors)
	in
	{ a with small_factors = new_small_factors }::l
      else
	a::(add_decomp r l)

let rec polynom_to_monomial_decomp = function
    [] -> []
  | coef_a::r ->
      let split_coef_a = split_coef_monomial coef_a in
      let decomp_r = polynom_to_monomial_decomp r in
      add_decomp split_coef_a decomp_r


let monomial_decomp_to_probaf l =
  p_sum (List.map (fun a -> p_div(p_mul(a.small_factors, p_prod a.large_factors), p_prod a.denominator)) l)

let polynom_to_probaf x =
  let (positive_part, negative_part) = List.partition (fun (coef, _) -> coef >= 0.0) x in
  (* Put the positive monomials last, so that they are added first by 
     [polynom_to_monomial_decomp], and we get (positive term - negative term)
     in the final probability formula. *)
  monomial_decomp_to_probaf (polynom_to_monomial_decomp (negative_part @ positive_part))


(* [power_to_polynom_map f x n] is the polynom [f (x^n)] where [x] is
   a probability formula, and [f] maps probability formulas to
   polynoms and maps product, division, and power to product,
   division, and power respectively. *)

let power_to_polynom_map f x n =
  power_to_polynom f (fun f p -> polynom_to_probaf p) x n
