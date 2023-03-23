open Base
open Crypto

let _ = 
  let f = WLSK_Init.init() in
  try
    let (), r = f("NONCEXXX") in
    print_string "ERROR: result ";
    print_string r;
    print_newline()
  with Match_fail ->
    print_string "CORRECT: raised Match_fail";
    print_newline()

    
