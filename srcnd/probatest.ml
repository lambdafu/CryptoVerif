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
    
let display_interv (min, max) vname =
  display_v min;
  print_string " <= ";
  print_string vname;
  print_string " <= ";
  display_v max;
  if inv (min, max) then
    print_string " inv OK"
  else
    print_string " **inv BROKEN!!**"
      
