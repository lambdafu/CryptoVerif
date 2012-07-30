exception File
exception Table
exception Pad
exception PK_EncDec
exception Signature
exception Sym_injbot
exception Sym_r
exception Sym_r_injbot
exception MAC
exception DH

let test_files () =
  print_string "test files...\n";
  let x= Base.compos ["pk"; "test"] in
    Base.output_string_to_file "t" x;
    let x' = Base.input_string_from_file "t" in
    let [y;z]=Base.decompos x' in
      if (y <> "pk" || z <> "test") then
        raise File

let test_tables () =
  print_string "test tables...\n";
  let x= Base.compos ["pk"; "test"] in
  Base.insert_in_table "tl" ["pk";x];
  Base.insert_in_table "tl" ["pk";x];
  let l=Base.get_from_table "tl" Base.id in
  let x'=List.hd (List.tl (List.hd (List.tl l))) in
  let [y;z]=Base.decompos x' in
    if (y <> "pk" || z <> "test") then
      raise Table

let test_pad () =
  print_string "test pad...\n";
  let m="jikzfgboeijgb" in
  let x=Crypto.pad Cryptokit.Padding.length 256 m in
  let y=Crypto.pad_inv Cryptokit.Padding.length x in
    if y <> "jikzfgboeijgb" then
      raise Pad


let is_alphabetic c=
  (c>='A' && c <='Z') || (c>='a' && c <='z') || (c>='0' && c <='9')

let hex_of_char c=
  Printf.sprintf "%02x" (int_of_char c)

let rec string_fold f s r=
  match s with 
      "" -> r
    | s -> (f s.[0] (string_fold f (String.sub s 1 ((String.length s)-1)) r))

let alphabetize_string s=
  string_fold 
    (
      fun c s -> 
        if is_alphabetic c then 
          (String.make 1 c)^s 
        else 
          ("_"^(hex_of_char c)^s)
    ) s ""


let test_pk (pk,sk) =
  print_string "test pk...\n";
  let m="message" in
  let m2=Crypto.pk_dec (Crypto.pk_enc m pk) sk in
    (match m2 with 
         None -> print_string "None\n"; raise PK_EncDec
       | Some m' -> 
           if m' <> "message" then
             raise PK_EncDec)
       


let test_sign (pk,sk)=
  print_string "test pksign...\n";
  let m="My signed message" in
  let s= Crypto.pk_sign Cryptokit.Hash.sha1 Cryptokit.Padding.length m sk in
  let b= Crypto.pk_check_sign Cryptokit.Hash.sha1 Cryptokit.Padding.length m pk s in
    if (not b) then
      raise Signature

let test_sign2 (pk,sk) =
  print_string "test rsassa_pss...\n";
  let m="My signed message 2" in
  let s = Crypto.rsassa_pss_sign 20 m sk in
  let b = Crypto.rsassa_pss_verify 20 m pk s in
    if (not b) then
      raise Signature

let test_symr () =
  print_string "test symr...\n";
  let m="A message" in
  let k=Crypto.sym_kgen "ABCDEF0123456789" in
  let e=Crypto.sym_r_enc (Cryptokit.Cipher.aes ~mode:Cryptokit.Cipher.CBC ~pad:Cryptokit.Padding.length) m k "0123456789ABCDEF" in
  let d=Crypto.sym_r_dec 16 (Cryptokit.Cipher.aes ~mode:Cryptokit.Cipher.CBC ~pad:Cryptokit.Padding.length) e k in
    begin
      try
        if (m <> (Crypto.injbot_inv d)) then
          raise Sym_r
      with 
        | Base.Match_fail -> raise Sym_r_injbot
    end

let test_mac () =
  print_string "test mac...\n";
  let k=Crypto.mac_kgen "random" in
  let m="A MAC message" in
  let mac=Crypto.mac Cryptokit.MAC.hmac_sha1 m k in
  let b=Crypto.mac_check Cryptokit.MAC.hmac_sha1 m k mac in
    if (not b) then
      raise MAC
        
let test_dh () =
  print_string "test DH...\n";
  let r=Crypto.dh_rand Crypto.dh_group14 () in
  let r'=Crypto.dh_rand Crypto.dh_group14 () in
  let m=Crypto.dh_message Crypto.dh_group14 r in
  let m'=Crypto.dh_message Crypto.dh_group14 r' in
  if Crypto.dh_exp Crypto.dh_group14 m r' <> Crypto.dh_exp Crypto.dh_group14 m' r then
    raise DH


let _ = 
  test_files ();
  test_tables ();
  test_pad ();
  let (pk,sk) = Crypto.pk_kgen 1024 () in
    test_sign2 (pk,sk);
    test_pk (pk,sk);
    test_sign (pk,sk);
  test_symr ();
  test_mac ();
  test_dh ()
    
