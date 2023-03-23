open Base

let _ = 
  for n = 1 to 1000 do
    insert_in_table "test_tbl" [string_of_int n; string_of_int n]
  done
