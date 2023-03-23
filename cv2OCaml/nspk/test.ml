

(*protocol test *)

(*init S key*)
print_string "Ostart...";print_newline ();
let ostart=ONS_Keygen.init () in
let (_,pkS) = ostart () in

(*init A key*)
print_string "OAGK...";print_newline ();
let oagk = ONS_AGenKey.init () in
let (_,pkA) = oagk () in

(*init B key*)
print_string "OBGK...";print_newline ();
let obgk = ONS_BGenKey.init () in
let (_,pkB) = obgk () in
let b=Base.input_string_from_file "idB" in

(*A 1*)
print_string "OA1...";print_newline ();
let oa1 = ONS_A.init () in
let (oa3, hA,hB) = oa1 b in
print_string (hA^","^hB);print_newline ();

(*S 2*)
print_string "OS13";print_newline ();
let os13 = ONS_S.init () in
let (_,rk,h2,s) = os13 (hA, hB) in

(*A 3*)
print_string "OA3";print_newline ();
let (oa5,c) = oa3 (rk, h2, s) in

(*B 4*)
print_string "OB7";print_newline ();
let ob7 = ONS_B.init () in
let (ob9,hB',hA') = ob7 c in

(*S 5*)
print_string "OS13'";print_newline ();
let os13' = ONS_S.init () in
let (_,rk',h2',s') = os13' (hB', hA') in

(*B 6*)
print_string "OB9";print_newline ();
let (ob11, c') = ob9 (rk', h2', s') in

(*A 7*)
print_string "OA5";print_newline ();
let (_,m) = oa5 c' in

(*B 8*)
print_string "OB11";print_newline ();
let _ = ob11 m in
  ()


