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

let rom_hash_macro() =
  if (!front_end) = ProVerif then
"def ROM_hash_%(key, $hashinput%$, $, hashoutput, hash, hashoracle, qH) {
    
fun hash(key, $hashinput%$, $):hashoutput.

param qH [noninteractive].
channel ch1, ch2.

let hashoracle(k: key) = 
        foreach iH <= qH do
	in(ch1, ($x%: hashinput%$, $));
        out(ch2, hash(k, $x%$, $)).

}

"	
  else
"def ROM_hash_%(key, $hashinput%$, $, hashoutput, hash, hashoracle, qH) {

param Nh, N, Neq, Ncoll.

fun hash(key, $hashinput%$, $):hashoutput.

equiv(rom(hash))
      foreach ih <= Nh do k <-R key;
        (foreach i <= N do OH($x%: hashinput%$, $) := return(hash(k, $x%$, $)) |
         foreach ieq <= Neq do Oeq($x%': hashinput%$, $, r': hashoutput) := return(r' = hash(k, $x%'$, $)) |
         foreach icoll <= Ncoll do Ocoll($y%: hashinput%$, $, $z%: hashinput%$, $) := 
                 return(hash(k, $y%$, $) = hash(k, $z%$, $)))
       <=((#Oeq + #Ocoll) * Pcoll1rand(hashoutput))=>
      foreach ih <= Nh do 
        (foreach i <= N do OH($x%: hashinput%$, $) := 
	   find[unique] u <= N suchthat defined($x%[u]$, $, r[u]) && $x% = x%[u]$ && $ then return(r[u]) else
           r <-R hashoutput; return(r) |
         foreach ieq <= Neq do Oeq($x%': hashinput%$, $, r': hashoutput) := 
           find[unique] u <= N suchthat defined($x%[u]$, $, r[u]) && $x%' = x%[u]$ && $ then return(r' = r[u]) else
	   return(false) |
         foreach icoll <= Ncoll do Ocoll($y%: hashinput%$, $, $z%: hashinput%$, $) := 
                 return($y% = z%$ && $)).

param qH [noninteractive].\n\n"
  ^
  (if (!front_end) = Channels then
"channel ch1, ch2.
let hashoracle(k: key) = 
        foreach iH <= qH do
	in(ch1, ($x%: hashinput%$, $));
        out(ch2, hash(k, $x%$, $))."
  else
"let hashoracle(k: key) = 
        foreach iH <= qH do
	OH($x%: hashinput%$, $) :=
        return(hash(k, $x%$, $)).")
  ^"\n\n}\n\n"

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
    [ "-out", Arg.String (function 
	"channels" -> front_end := Channels
      | "oracles" -> front_end := Oracles
      | "proverif" -> front_end := ProVerif
      | _ ->
          print_string "Command-line option -out expects argument either \"channels\" or \"oracles\".\n";
          exit 2),
      "channels / -out oracles \tchoose the front-end";
    ]
    bound ("Crypto library generator, by Bruno Blanchet\nCopyright ENS-CNRS-Inria, distributed under the CeCILL-B license\nUsage:\n  hashgen [options] n\nto print random oracle macro with n arguments\n  hashgen [options] n1 n2\nto print random oracle macros with n1 to n2 arguments\nOptions:")

let _ =
  if !final < !start then
    begin
      print_string "The 2nd argument should be larger than the first one.\n";
      exit 2
    end;
  for n = !start to !final do
    print_macro (rom_hash_macro()) n
  done
    
    
