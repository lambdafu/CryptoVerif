exception Bad_call
exception Match_fail
exception Abort
exception Bad_file of string
exception Integer_too_large

(* Predicates, to test whether a value belongs to a type.
   * [always_true] is always true; this predicate can be used
   for types such that the Caml representation always 
   corresponds to a valid CryptoVerif value 
   * [sizep n] is true for strings of [n] bits ([n] multiple of 8).
   It is used for fixed-length types. *)

let always_true _ = true

let sizep n s = (String.length s = n)

(* Reading from and writing to a file *)

let input_string_from_file file =
  try
    let f = open_in_bin file in
    let n = in_channel_length f in
    let s = really_input_string f n in
    close_in f;
    s
  with _ -> raise (Bad_file file)

let output_string_to_file file s =
  try
    let f = open_out_bin file in
    output_string f s;
    close_out f
  with _ -> raise (Bad_file file)

(* [exc_bad_file fname f v] calls [f v]; if it raises [Match_fail], 
   raises [Bad_file fname] instead. This function is useful because
   when deserialization fails, it raises [Match_fail]. When we use
   deserialization for reading a file, we want to raise [Bad_file]
   instead. *)

let exc_bad_file fname f v =
  try
    f v 
  with Match_fail ->
    raise (Bad_file fname)

(* Random number generation. *)

let rng_ref = ref None

let rng()=
  match !rng_ref with
    Some r -> r
  | None -> 
      let r = Cryptokit.Random.pseudo_rng (Cryptokit.Random.string Cryptokit.Random.secure_rng 20) in
      rng_ref := Some r;
      r

let rand_string i () =
  Cryptokit.Random.string (rng()) i

let rand_bool () =
  (( (Char.code ((Cryptokit.Random.string (rng()) 1).[0])) mod 2) = 0)

(* [rand_list l] returns a random element of [l].
   It is used for implementing "get": when several elements satisfy
   the desired condition, one of them is chosen randomly. *)

let rand_list = function
    [x] -> x
  | l -> List.nth l (Random.int (List.length l))

(* [compos] concatenates bitstrings, with length indications,
   so that the initial bitstrings can be recovered. 
   [decompos] recovers the initial bitstrings. 
   These functions are used for building and breaking tuples.
   When [decompos] fails, raises [Match_fail] *)

let char4_of_int s i n=
  let n0=(n lsr 24) land 255 in
  let n1=(n lsr 16) land 255 in
  let n2=(n lsr  8) land 255 in
  let n3= n         land 255 in
    Bytes.set s i (char_of_int n0);
    Bytes.set s (i+1) (char_of_int n1);
    Bytes.set s (i+2) (char_of_int n2);
    Bytes.set s (i+3) (char_of_int n3)

let int_of_char4 s i=
  if String.length s < i+4 then
    raise Match_fail
  else
    let n0=int_of_char s.[i] in
    let n1=int_of_char s.[i+1] in
    let n2=int_of_char s.[i+2] in
    let n3=int_of_char s.[i+3] in
      (n0 lsl 24) lor (n1 lsl 16) lor (n2 lsl 8) lor n3

let compos (l:string list) : string =
  let rec tot_len = function
      [] -> 4
    | s::l -> 4 + (String.length s) + tot_len l
  in
  let len = tot_len l in
  let buf = Bytes.create len in
  char4_of_int buf 0 (List.length l);
  let rec repr i = function
      s::l -> 
	let len_s = String.length s in
	char4_of_int buf i len_s;
	String.blit s 0 buf (i+4) len_s;
	repr (i+4+len_s) l
    | [] -> ()
  in
  repr 4 l;
  Bytes.unsafe_to_string buf

let decompos b =
  let nb=int_of_char4 b 0 in
  if nb < 0 then raise Match_fail;
  let rec derepr i j=
    try
      if j>0 then
        let n = int_of_char4 b i in
        (String.sub b (i+4) n)::(derepr (i+4+n) (j-1))
      else
	begin
	  if i != String.length b then raise Match_fail;
          []
	end
    with Invalid_argument _ -> raise Match_fail
  in
  derepr 4 nb

(* Read from and write to a table
   [get_from_table] is used for implementing "get"
   [insert_in_table] is used for implementing "insert" *)

let get_from_table file filter =
  let f=
    try
      open_in_bin file
    with _ -> raise (Bad_file file)
  in
  let rec read_all acc =
    try 
      let ncomp = input_binary_int f in
      if ncomp < 0 then raise (Bad_file file);
      let rec read_rec n =
	if n = 0 then 
	  []
	else
	  let len = input_binary_int f in
	  let s = really_input_string f len in
	  s :: (read_rec (n-1))
      in
      let record = 
	try
	  read_rec ncomp
	with Invalid_argument _ -> raise (Bad_file file)
      in
      try
	read_all ((filter record)::acc)
      with Match_fail -> 
	read_all acc
    with End_of_file -> acc (* Accept End_of_file in the middle of a record, just ignoring that record.
			       The goal is to support insertion of elements in the table while 
			       the table is being read. *)
  in
  let r = read_all [] in
  begin
    try
      close_in f
    with _ -> raise (Bad_file file)
  end;
  r

let insert_in_table file l =
  try
    let c=open_out_gen [Open_wronly;Open_append;Open_creat;Open_binary] 384 (*0600*) file in
    output_binary_int c (List.length l);
    List.iter (fun a ->
      output_binary_int c (String.length a);
      output_string c a) l;
    close_out c
  with _ -> raise (Bad_file file)

(* Serialization and deserialization functions for the default types:
   bitstring, bool, bitstringbot.
   When deserialization fails, raises Match_fail *)

let id x=x 

let bool_from s = 
  if String.length s <> 1 then raise Match_fail
  else
    if s.[0]='\000' then false
    else
      if s.[0]='\001' then true
      else raise Match_fail

let bool_to b =
  String.make 1 (match b with true -> '\001' | false -> '\000')

let size_from n s =
  if not (sizep n s) then
    raise Match_fail;
  s

let stringbot_from s =
  if s = "" then raise Match_fail
  else
    if s.[0]='N' then None
    else
      if s.[0]='S' then
        Some (String.sub s 1 ((String.length s)-1))
      else
        raise Match_fail

let stringbot_to = function
    None -> "N"
  | Some s -> "S"^s


let ceildiv n x =
  if n mod x = 0 then
    n/x
  else
    (n/x)+1

let i2osp x l =
  let lmax = if (Sys.word_size = 32) then 4 else 8 in
    if (l < lmax && x>(1 lsl (8*l))) then 
      raise Integer_too_large
    else
      let s = Bytes.create l in
      for i=0 to (l-1) do
        Bytes.set s i (char_of_int ((x lsr (8*(l-i-1))) land 255))
      done;
      Bytes.unsafe_to_string s
  
let rec osp2i s i l =
  if l = 1 then int_of_char s.[i]
  else
    (256*int_of_char s.[i])+(osp2i s (i+1) (l-1))
