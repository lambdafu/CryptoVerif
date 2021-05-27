open Base
open Crypto

let _ = 
  let f = WLSK_Init.init() in
  let (), r = f("NONCEXXX") in
  let (a,b,c) = unconcat_str_str_str r in
  if b = "A" then print_string "CORRECT: " else print_string "ERROR: ";
  print_string b;
  print_newline()
