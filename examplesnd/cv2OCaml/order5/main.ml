open Base
open Crypto

let _ = 
try
  let f = WLSK_Init.init() in
  let (), r = f("NONCEXXX") in
  let (a,b,c) = unconcat_str_str_str r in
  if b = "A" then print_string "CORRECT: " else print_string "ERROR: ";
  print_string b;
  print_newline()
with Match_fail ->
  print_string "ERROR: raised Match_fail";
  print_newline()
