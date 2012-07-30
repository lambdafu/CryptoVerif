open Base

let _ =
  for i = 1 to 1000 do
    let r = get_from_table "test_tbl" (function [a;b] -> (a,b) | _ -> raise Match_fail) in
    List.iter (function (a,b) -> print_string a; print_string " "; print_string b; print_newline()) r;
    print_string "END_TABLE\n"
  done
