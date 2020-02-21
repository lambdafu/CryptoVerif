type front_end =
  | Channels
  | Oracles
  | ProVerif

let front_end = ref Channels

(* Inside [macro], % is replaced with n
   and [$format$sep$] is replaced with
   [format_1 sep ... sep format_n] where 
   [format_i] is obtained by replacing % with i in [format] *)
                    
let print_macro macro n =
  let repeat s sep =
    for i = 1 to n do
      for k = 0 to String.length s - 1 do
        if s.[k] = '%' then
          print_int i
        else
          print_char s.[k]
      done;
      if i < n then print_string sep
    done
  in
  let len = String.length macro in
  let rec aux pos =
    if pos >= len then () else
    if macro.[pos] = '%' then
      begin
        print_int n;
        aux (pos+1)
      end
    else if macro.[pos] = '$' then
      begin
        let pos2 = String.index_from macro (pos+1) '$' in
        let pos3 = String.index_from macro (pos2+1) '$' in
        let format = String.sub macro (pos+1) (pos2-pos-1) in
        let sep = String.sub macro (pos2+1) (pos3-pos2-1) in
        repeat format sep;
        aux (pos3+1)
      end
    else
      begin
        print_char macro.[pos];
        aux (pos+1)
      end
  in
  aux 0

(* Random oracles *)
    
let rom_hash_prefix =
"(******************************* Hash functions (ROM) ****************************)

(* Hash function in the random oracle model
   key: type of the key of the hash function, which models the choice of the hash function, must be \"bounded\", typically \"fixed\"
   hashinput%: type of the %-th input of the hash function
   hashoutput: type of the output of the hash function, must be \"bounded\" or \"nonuniform\" (typically \"fixed\"), and \"large\".

   hash: the hash function.
   WARNING: hash is a keyed hash function.
   The key must be generated once and for all at the beginning of the game 
   and the hash oracle must be made available to the adversary,
   by including the process hashoracle(k) where k is the key.
   qH is the number of calls to hashoracle.

   The types key, hashinput%, and hashoutput must be declared before
   this macro. The function hash, the process hashoracle, and
   the parameter qH are defined by this macro. They must not
   be declared elsewhere, and they can be used only after expanding the
   macro.

   ADDED ARGUMENTS:
   r: variable containing the random result of the hash function
   x%: variables containing the arguments of the hash function
   ch1, ch2: channels for input/output in the hash oracle.

 *)\n\n"

let rom_hash_macro() =
"def ROM_hash_refactored_%(key, $hashinput%$, $, hashoutput, hash, hashoracle, r, $x%$, $, ch1, ch2, qH) {

param Nh, N, Neq, Ncoll.

fun hash(key, $hashinput%$, $):hashoutput.

equiv(rom(hash)) special rom(\"key_first\", hash, (hk, r, x, y, z, u), (\"large\")).

param qH [noninteractive].

channel ch1, ch2.
let hashoracle(k: key) = 
        foreach iH <= qH do
	in(ch1, ($x%: hashinput%$, $));
        out(ch2, hash(k, $x%$, $)).

}\n\n"


let rom_hash_suffix =
"def ROM_hash_refactored(key, hashinput, hashoutput, hash, hashoracle, r, x1, ch1, ch2, qH) {
expand ROM_hash_refactored_1(key, hashinput, hashoutput, hash, hashoracle, r, x1, ch1, ch2, qH).
}\n\n"

(* Split a value *)

let split_prefix = "(* split_N defines functions to split a value into N values.

  input_t: type of the input value
  part%_t: types of the output parts
  concat(part1_t, ..., partN_t): input_t: function that takes N parts as input and returns the corresponding value.
  part%: variable that contains a part 

  input_t and part%_t must be defined before.
  concat is defined by this macro. *)\n\n"

let split_macro() =
  "def split_%(input_t, $part%_t$, $, concat, $part%$, $) {

  fun concat($part%_t$, $): input_t [data].

  param N.
  equiv(splitter(concat))
     foreach i <= N do r <-R input_t; 
       Or() := return(r)
    <=(0)=>
     foreach i <= N do $part% <-R part%_t;$ $
       Or() := return(concat($part%$, $)).

}\n\n"
    
    
    
let args_seen = ref 0
let start = ref 1
let final = ref 1
                
let bound s =
  try
    let n = int_of_string s in
    begin
    match !args_seen with
      0 -> start := n; final := n
    | 1 -> final := n
    | _ -> print_string "You should at most give the starting number and the ending one.\n"; exit 2
    end;
    incr args_seen
  with _ ->
    print_string "All non-option arguments should be integers.\n"; exit 2 
     
let _ =
  Arg.parse
    [ ]
    bound ("Crypto library generator, by Bruno Blanchet\nCopyright ENS-CNRS-Inria, distributed under the CeCILL-B license\nUsage:\n  hashgen [options] n\nto print random oracle macro with n arguments\n  hashgen [options] n1 n2\nto print random oracle macros with n1 to n2 arguments\nOptions:")

let _ =
  if !final < !start then
    begin
      print_string "The 2nd argument should be larger than the first one.\n";
      exit 2
    end;
  (* ROM *)
  print_string rom_hash_prefix;
  for n = !start to !final do
    print_macro (rom_hash_macro()) n
  done;
  print_string rom_hash_suffix;
  (* Split *)
  print_string split_prefix;
  for n = !start to !final do
    print_macro (split_macro()) n
  done
  
    
