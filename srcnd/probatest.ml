(* Unit testing for proba.ml, order_of_magnitude_aux *)

let inv_v (sign, exp) =
  (sign = -1 || sign = 0 || sign = 1) &&
  (if sign = 0 then exp = 0.0 else true) &&
  (exp >= min_f) && (exp <= max_f)

let inv (min, max) =
  (inv_v min) && (inv_v max) &&
  (not (is_greater min max))

let display_v (sign, exp) =
  if sign = 0 then
    print_string "0"
  else
    begin
      if sign = -1 then print_string "-";
      print_string "2^";
      print_float exp;
      print_string " = ";
      print_float ((float_of_int sign) *. 2.0 ** exp)
    end
    
let display_interv (min, max) probaf =
  display_v min;
  print_string " <= ";
  Display.display_proba 0 probaf;
  print_string " <= ";
  display_v max;
  if inv (min, max) then
    print_string " inv OK"
  else
    print_string " **inv BROKEN!!**"
      
let test probaf =
  let interv = order_of_magnitude_aux probaf in
  display_interv interv probaf;
  print_newline()

let test2 probaf =
  let res = order_of_magnitude probaf in
  Display.display_proba 0 probaf;
  print_string " <= 2^";
  print_int res;
  print_newline()
    
let t_nonce = { tname = "nonce";
	       tcat = BitString;
	       toptions = Settings.tyopt_FIXED + Settings.tyopt_BOUNDED;
	       tsize = Some (80,100);
	       tpcoll = Some (80,100);
               timplsize = Some(1);
               tpredicate = Some "always_true";
               timplname = Some "bool";
               tserial = Some ("bool_from","bool_to");
               trandom = Some ("rand_bool") }

let t_nonce2 = { tname = "nonce2";
	       tcat = BitString;
	       toptions = Settings.tyopt_FIXED + Settings.tyopt_BOUNDED;
	       tsize = Some (82,102);
	       tpcoll = Some (82,102);
               timplsize = Some(1);
               tpredicate = Some "always_true";
               timplname = Some "bool";
               tserial = Some ("bool_from","bool_to");
               trandom = Some ("rand_bool") }
    
let t_nonce3 = { tname = "nonce3";
	       tcat = BitString;
	       toptions = Settings.tyopt_FIXED + Settings.tyopt_BOUNDED + Settings.tyopt_NONUNIFORM;
	       tsize = Some (82,102);
	       tpcoll = Some (40,60);
               timplsize = Some(1);
               tpredicate = Some "always_true";
               timplname = Some "bool";
               tserial = Some ("bool_from","bool_to");
               trandom = Some ("rand_bool") }

let t_any = { tname = "any";
	       tcat = BitString;
	       toptions = Settings.tyopt_FIXED + Settings.tyopt_BOUNDED + Settings.tyopt_NONUNIFORM;
	       tsize = Some (0,max_int);
	       tpcoll = Some (0,max_int);
               timplsize = Some(1);
               tpredicate = Some "always_true";
               timplname = Some "bool";
               tserial = Some ("bool_from","bool_to");
               trandom = Some ("rand_bool") }

let p1 = { pname = "p20";
	   psize = 20 }
    
let p2 = { pname = "p40";
	   psize = 40 }
    
let _ =
  test (Card Settings.t_bitstring);
  test (Div(Cst 1.0, Card Settings.t_bitstring));
  test (Div(Cst 1.0, Card Settings.t_bool));
  test (Div(Cst 1.0, Card t_nonce));
  test (Add(Div(Cst 1.0, Card t_nonce2),Div(Cst 1.0, Card t_nonce)));
  test (Sub(Div(Cst 1.0, Card t_nonce2),Div(Cst 1.0, Card t_nonce)));
  test (Add(Div(Cst 1.0, Card t_nonce3),Div(Cst 1.0, Card t_nonce)));
  test (Add(Div(Cst 1.0, Card t_nonce),PColl1Rand t_nonce3));
  test (PColl1Rand t_any);
  test (Card t_any);
  test (Cst 3.0);
  test (Count p1);
  test (Count p2);
  test (Mul(PColl1Rand t_nonce3, Count p1));
  test (Mul(PColl1Rand t_nonce3, Count p2));
  test (Div(Cst (-1.0), Card t_nonce));
  test (Mul(Count p2, Div(Cst (-1.0), Card t_nonce)));
  let zcent = Sub(PColl1Rand t_any, Cst 0.5) in
  test zcent;
  test (Div(Cst 1.0, zcent));
  test (Mul(PColl1Rand t_nonce3, zcent));
  test (PColl2Rand t_nonce3);
  test (Zero);
  test (EpsRand t_nonce3);
  test (EpsFind);
  test (Max[Count p1; Count p2]);
  test2 (Div(Cst 1.0, zcent));

