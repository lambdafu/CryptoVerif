open Types

(* 1. Operations on polynoms *)

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

let rec sum p1 = function
    [] -> p1
  | ((coef,a)::l) ->
      try
	let (coef',l') = find_monomial a p1 in
	(coef+.coef',a)::(sum l' l)
      with Not_found ->
	(coef,a)::(sum p1 l)

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

let rec sub p1 = function
    [] -> p1
  | ((coef,a)::l) ->
      try
	let (coef',l') = find_monomial a p1 in
	(coef'-.coef,a)::(sub l' l)
      with Not_found ->
	(0.-.coef,a)::(sub p1 l)

let rec product_monomial m1 = function
    [] -> m1
  | (e,n)::l -> 
      try
	let n' = List.assoc e m1 in
	(e,n + n')::(product_monomial (remove_factor (e,n') m1) l)
      with Not_found ->
	(e,n)::(product_monomial m1 l)

let rec product_pol_monomial (coef,a) = function
    [] -> []
  | ((coef',a')::l) -> 
      sum [coef *. coef', product_monomial a a'] (product_pol_monomial (coef,a) l)

let rec product p1 = function
    [] -> []
  | (a::l) -> sum (product_pol_monomial a p1) (product p1 l)


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
  
let rec p_sum = function
  | [] -> Zero
  | [a] -> a
  | (a::l) -> p_add(a, p_sum l)

type max_val =
  | MNone
  | MCst of float

type max_accu = max_val * probaf list

      (* max_accu = (MNone, l) -> take the maximum of l
                    (MCst x, l) -> take max(x, maximum of l) *)
      

let empty_max_accu = (MNone, [])
      
let p_max = function
  | MNone, [] -> Cst neg_infinity
  | MCst 0.0, [] -> Zero
  | MCst x, [] -> Cst x
  | MNone, [a] -> a
  | MCst 0.0, l -> Max(Zero :: l)
  | MCst x, l -> Max((Cst x)::l)
  | _, l -> Max(l)

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

(* 3.1 Conversion probaf_to_polynom *)

let rec probaf_to_polynom = function
    Zero -> []
  | Cst n -> [n,[]]
  | Mul(f1,f2) -> product (probaf_to_polynom f1) (probaf_to_polynom f2)
  | Add(f1,f2) -> sum (probaf_to_polynom f1) (probaf_to_polynom f2)
  | Sub(f1,f2) -> sub (probaf_to_polynom f1) (probaf_to_polynom f2)
  | Div(Cst 1.0, Mul(x,y)) -> probaf_to_polynom (Mul(Div(Cst 1.0, x), Div(Cst 1.0, y)))
  | Div(Cst 1.0, _) as prob -> [1.0,[prob,1]]
  | Div(f1,f2) -> probaf_to_polynom (Mul(f1, Div(Cst 1.0, f2)))
  | prob -> [1.0,[prob,1]]


(* 3.2 Conversion polynom_to_probaf *)

let rec factor_to_probaf (a,n) =
  if n < 1 then
    Parsing_helper.internal_error "not a polynomial in factor_to_probaf" 
  else if n = 1 then
    a 
  else 
    Mul(a,factor_to_probaf (a,n-1))

let rec factor_to_list (a,n) =
  if n < 1 then
    Parsing_helper.internal_error "not a polynomial in factor_to_probaf" 
  else if n = 1 then
    [a] 
  else 
    a :: (factor_to_list (a,n-1))

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
      |	Add _ | Mul _ | Sub _ | Div _ | Zero | Cst _ ->
	  Parsing_helper.internal_error "Should have been removed when generating polynoms"
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
	{ a with small_factors = p_add(a.small_factors, r.small_factors) }::l
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
  monomial_decomp_to_probaf (polynom_to_monomial_decomp x)
