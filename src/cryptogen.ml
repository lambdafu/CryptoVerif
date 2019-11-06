type front_end =
  | Channels
  | Oracles
  | ProVerif

let front_end = ref Channels

let start = ref 1
let final = ref 1

(* [copy f] returns the concatenation of
   [f n (string_of_int n)] for [n] from 1 to
   [!max_copy] *) 
    
let max_copy = ref 5
    
let copy f =
  let rec aux n =
    if n = !max_copy then
      f n (string_of_int n)
    else
      (f n (string_of_int n)) ^ (aux (n+1))
  in 
  aux 1
    
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

let var_arg_macro prefix macro suffix =
  print_string prefix;
  for n = !start to !final do
    print_macro macro n
  done;
  if !start = 1 then
    print_string suffix
  
    
(* Random oracles *)

let equiv_random_fun name proba is_large =
  
    (* Separator between oracle definitions *)
    let osep = " |\n         " in
    (* Oracle declaration for oracle name [ocur] *)
    let odecl ocur is_eq =
      "foreach i <= N"^ocur^" do O"^ocur^"($x"^ocur^"_%: input%$, $"^(if is_eq then ", r"^ocur^": output" else "") ^") := "
    in
    (* Find prefix *)
    let find_pref k' =
      if k' = 1 then "find[unique]" else "orfind"
    in
    (* Conditions of find: collision between the current call to [ocur] and a call to [other],
       the found call is indexed by [u] 
       First, when the oracle [other] chooses a fresh random r[other]. *)
    let collision ocur other =
      " u <= N"^other^" suchthat defined($x"^other^"_%[u]$, $, r"^other^"[u]) && $x"^ocur^"_% = x"^other^"_%[u]$ && $ then "
    in
    (* Second, when the oracle [other] makes no choice *)
    let collision_no_r ocur other =
      " u <= N"^other^" suchthat defined($x"^other^"_%[u]$, $) && $x"^ocur^"_% = x"^other^"_%[u]$ && $ then "
    in
    (* Possible oracle results *)
    (* f of the current argument *)
    let f_ret ocur =
      "return(f(k, $x"^ocur^"_%$, $))"
    in
    (* Image by f returned by a previous call to [other] *)
    let found_f_ret other =
      "return(f(k, $x"^other^"_%[u]$, $))"
    in
    (* Fresh random value *)
    let rand_ret ocur =
      "r"^ocur^" <-R output; return(r"^ocur^")"
    in
    (* Random value returned by a previous call to [other] *)
    let found_rand_ret other =
      "return(r"^other^"[u])"
    in
    (* Equality between the output argument and f of the input argument *)
    let eq_f_ret ocur =
      "return(r"^ocur^" = f(k, $x"^ocur^"_%$, $))"
    in
    (* Equality between the output argument and the image by f returned by a previous call to [other] *)
    let eq_found_f_ret ocur other =
      "return(r"^ocur^" = f(k, $x"^other^"_%[u]$, $))"
    in
    (* Equality between the output argument and the random value returned by a previous call to [other] *)
    let eq_out_ret ocur other =
      "return(r"^ocur^" = r"^other^"[u])" 
    in
    let ev_ret = "event_abort ev_coll" in
    let sum s1 s2 =
      match s1,s2 with
      | "","" -> "0"
      | "",_ -> s2
      | _,"" -> s1
      | _ -> s1^" + "^s2
    in
    let ncalls =
      if is_large then
	"N + Neq + 2 * Ncoll"
      else
	"N"
    in
    let maxlength =
      if is_large then
	"$max(maxlength(x%), maxlength(xeq%), maxlength(y%), maxlength(z%))$, $"
      else
	"$maxlength(x%)$, $"
    in
    let proba_coll =
      if is_large then "Neq * Pcoll1rand(output) + Ncoll * Pcoll2rand(output)" else ""
    in
    let ncalls_partial =
      if is_large then
	"N + Ncut + Neq + Neqcut"^
	(copy (fun k sk -> " + N"^sk^" + Neq"^sk))^
	" + 2 * Ncoll"
      else
	"N + Ncut "^(copy (fun k sk -> " + N"^sk))
    in
    let maxlength_partial =
      if is_large then
	"$max(maxlength(x_%), maxlength(xcut_%), maxlength(xeq_%), maxlength(xeqcut_%)"^
	(copy (fun k sk -> ", maxlength(x"^sk^"_%), maxlength(xeq"^sk^"_%)"))^
	", maxlength(y%), maxlength(z%))$, $"
      else
	"$max(maxlength(x_%), maxlength(xcut_%)"^
	(copy (fun k sk -> ", maxlength(x"^sk^"_%)"))^")$, $"
    in
    let proba_coll_partial =
      if is_large then
	"("^(copy (fun k sk -> (if k > 1 then " + " else "") ^ ("Neq"^sk)))^") * Pcoll1rand(output) + Ncoll * Pcoll2rand(output)"
      else
	""
    in
    "param N, Ncut"^(copy (fun k sk -> ", N"^sk))^".\n"^
    (if is_large then
      "param Neq, Neqcut"^(copy (fun k sk -> ", Neq"^sk))^", Ncoll.\n"
    else "")^
    "\nfun f(key, $input%$, $):output.\n\n"^
    (if (!front_end) = ProVerif then "" else 
"equiv("^name^"(f))
      k <-R key;
        (foreach i <= N do O($x%: input%$, $) := return(f(k, $x%$, $))"^(if is_large then " |
         foreach ieq <= Neq do Oeq($xeq%: input%$, $, req: output) := return(req = f(k, $xeq%$, $)) |
         foreach icoll <= Ncoll do Ocoll($y%: input%$, $, $z%: input%$, $) := 
                 return(f(k, $y%$, $) = f(k, $z%$, $))" else "")^")
       <=("^(sum (proba ncalls maxlength) proba_coll)^")=>
         foreach i <= N do O($x%: input%$, $) := 
	   find[unique] u <= N suchthat defined($x%[u]$, $, r[u]) && $x% = x%[u]$ && $ then return(r[u]) else
           r <-R output; return(r)"^(if is_large then " |
         foreach ieq <= Neq do Oeq($xeq%: input%$, $, req: output) := 
           find[unique] u <= N suchthat defined($x%[u]$, $, r[u]) && $xeq% = x%[u]$ && $ then return(req = r[u]) else
	   return(false) |
         foreach icoll <= Ncoll do Ocoll($y%: input%$, $, $z%: input%$, $) := 
                 return($y% = z%$ && $)" else "")^".

event ev_coll.

equiv("^name^"_partial(f))
      k <-R key;\n        ("
			  ^(odecl "" false)^(f_ret "")
			  ^osep^(odecl "cut" false)^(f_ret "cut")
			  ^(copy (fun k ocur -> 
			      osep^(odecl ocur false)^(f_ret ocur))) 
			  ^(if is_large then
			    osep^(odecl "eq" true)^(eq_f_ret "eq")
			    ^osep^(odecl "eqcut" true)^(eq_f_ret "eqcut")
			    ^(copy (fun k sk -> let ocur = "eq"^sk in
			    osep^(odecl ocur true)^(eq_f_ret ocur)))
^osep^"foreach icoll <= Ncoll do Ocoll($y%: input%$, $, $z%: input%$, $) := 
                 return(f(k, $y%$, $) = f(k, $z%$, $))" else "")^")
       <=("^(sum (proba ncalls_partial maxlength_partial) proba_coll_partial)^")=> [manual]
      k <-R key;\n        ("
			  ^(odecl "" false)
			  ^ (copy (fun k' other -> 
			  "\n          "^(find_pref k') ^ (collision "" other) ^(found_rand_ret other)))^
			  "\n          else "^(f_ret "")

			  ^osep^(odecl "cut" false)
			  ^(copy (fun k' other -> 
			  "\n          "^(find_pref k') ^ (collision "cut" other) ^ ev_ret))^
			  "\n          else "^(f_ret "cut")

			  ^(copy (fun k ocur -> 
			  osep^(odecl ocur false)
			  ^ (copy (fun k' other -> 
			  "\n          "^(find_pref k') ^ (collision ocur other) ^ (if k = k' then found_rand_ret other else ev_ret)))^
			  "\n          else find"^(collision_no_r ocur "cut")^ev_ret^
                          "\n          else find"^(collision_no_r ocur "")^(found_f_ret "")^
			  "\n          else "^(rand_ret ocur)))
			      
			  ^(if is_large then
			    osep^(odecl "eq" true)
			  ^(copy (fun k' other -> 
			  "\n          "^(find_pref k') ^ (collision "eq" other) ^ (eq_out_ret "eq" other)))^
			  "\n          else "^(eq_f_ret "eq")

			  ^osep^(odecl "eqcut" true)
			  ^(copy (fun k' other ->
			  "\n          "^(find_pref k') ^ (collision "eqcut" other) ^ev_ret))^
			  "\n          else "^(eq_f_ret "eqcut")
								       
			  ^ (copy (fun k sk -> let ocur = "eq"^sk in
			  osep^(odecl ocur true)
			  ^ (copy (fun k' other -> 
			  "\n          "^(find_pref k') ^ (collision ocur other) ^ (if k = k' then eq_out_ret ocur other else ev_ret)))^
			  "\n          else find"^(collision_no_r ocur "cut")^ev_ret^
			  "\n          else find"^(collision_no_r ocur "")^(eq_found_f_ret ocur "")^
			  "\n          else return(false)"))

^osep^"foreach icoll <= Ncoll do Ocoll($y%: input%$, $, $z%: input%$, $) := 
                 return($y% = z%$ && $)" else "")^").\n\n")


let call_f_oracle() =
  "\nparam qH [noninteractive].\n"^
  (if (!front_end) = Channels || (!front_end) = ProVerif then
"channel ch1, ch2.

let f_oracle(k: key) = 
        foreach iH <= qH do
	in(ch1, ($x%: input%$, $));
        out(ch2, f(k, $x%$, $))."
  else
"
let f_oracle(k: key) = 
        foreach iH <= qH do
	OH($x%: input%$, $) :=
        return(f(k, $x%$, $)).")

let key_ret_oracle() =     
  (if (!front_end) = Channels || (!front_end) = ProVerif then
"channel ch1, ch2.

let f_oracle(k: key) =
    in(ch1, ());
    out(ch2, k)."
  else
"let f_oracle(k: key) =
        OH() := return(k).")  
    
let rom_hash_prefix =
"(******************************* Hash functions (ROM) ****************************)

(* Hash function in the random oracle model
   key: type of the key of the hash function, which models the choice of the hash function, must be \"bounded\", typically \"fixed\"
   input%: type of the %-th input of the hash function
   output: type of the output of the hash function, must be \"bounded\" or \"nonuniform\" (typically \"fixed\").

   f: the hash function.
   WARNING: f is a keyed hash function.
   The key must be generated once and for all at the beginning of the game 
   and the hash oracle must be made available to the adversary,
   by including the process f_oracle(k) where k is the key.
   qH is the number of calls to f_oracle.

   The types key, input%, and output must be declared before
   this macro. The function f, the process f_oracle, and
   the parameter qH are defined by this macro. They must not
   be declared elsewhere, and they can be used only after expanding the
   macro.

 *)\n\n"

let rom_hash_large_prefix =
"(* ROM with large output.
    The only difference with ROM is that we eliminate collisions on the output.
    The interface is the same as for ROMs. *)\n\n"
  
    
let rom_hash_macro is_large =
  let large_st = if is_large then "_large" else "" in
  "def ROM_hash"^large_st^"_%(key, $input%$, $, output, f, f_oracle, qH) {\n\n"^
  (equiv_random_fun "rom" (fun _ _ -> "") is_large)^
  (call_f_oracle())^"\n\n}\n\n"


let rom_hash_suffix is_large =
  let large_st = if is_large then "_large" else "" in
"def ROM_hash"^large_st^"(key, input, output, f, f_oracle, qH) {
expand ROM_hash"^large_st^"_1(key, input, output, f, f_oracle, qH).
}\n\n"

let gen_rom is_large =
  var_arg_macro
    (if is_large then rom_hash_large_prefix else rom_hash_prefix)
    (rom_hash_macro is_large)
    (rom_hash_suffix is_large)
			   
(* Collision-resistant hash functions *)
    
let coll_hash_prefix =
"(* Collision resistant hash function 
   key: type of the key of the hash function, must be \"bounded\" or \"nonuniform\", typically \"fixed\"
   input%: type of the %-th input of the hash function
   output: type of the output of the hash function

   f: the hash function.
   Phash: probability of breaking collision resistance.
   WARNING: A collision resistant hash function is a keyed hash function.
   The key must be generated once and for all at the beginning of the game,
   and immediately made available to the adversary, for instance by
   including the process f_oracle(k), where k is the key.

   The types key, input%, output, and the probability Phash
   must be declared before this macro.  The function f and the
   process f_oracle are defined by this macro. They must not be
   declared elsewhere, and they can be used only after expanding the
   macro.

 *)\n\n"
      
let coll_hash_macro() =
"def CollisionResistant_hash_%(key, $input%$, $, output, f, f_oracle, Phash) {

fun f(key, $input%$, $):output.\n\n"
    ^(if (!front_end = ProVerif) then "" else 
      "collision k <-R key; forall $x%:input%$, $, $y%:input%$, $;
	return(f(k, $x%$, $) = f(k, $y%$, $)) <=(Phash(time))=> return($(x% = y%)$ && $).\n\n")	
    ^(key_ret_oracle())
    ^ "\n\n}\n\n"

let coll_hash_suffix =
"def CollisionResistant_hash(key, input, output, f, f_oracle, Phash) {
expand CollisionResistant_hash_1(key, input, output, f, f_oracle, Phash).
}\n\n"

let gen_coll() =
  var_arg_macro coll_hash_prefix (coll_hash_macro()) coll_hash_suffix

(* Hidden key collision-resistant hash functions *)

let hidden_key_coll_hash_prefix =
"(* Hidden-key collision resistant hash function
   The interface is similar to collision-resistant hash functions, except for the addition of qH.
   WARNING: A hidden-key collision resistant hash function is a keyed hash function.
   The key must be generated once and for all at the beginning of the game,
   and the hash oracle must be made available to the adversary,
   by including the process f_oracle(k) where k is the key.
   qH is the number of calls to f_oracle. 
   Phash(t,N): probability of breaking collision resistance 
   for an adversary that runs in time at most t 
   and calls the hash oracle at most N times. *)\n\n"
    
let hidden_key_coll_hash_macro() =
  "def HiddenKeyCollisionResistant_hash_%(key, $input%$, $, output, f, f_oracle, qH, Phash) {

fun f(key, $input%$, $):output.\n\n"
    ^(if (!front_end = ProVerif) then "" else
      "param N, Ncoll.

equiv(collision_res(f))
         k <-R key; 
          (foreach i <= N do O($x%:input%$, $) := return(f(k, $x%$, $)) |
           foreach i <= Ncoll do Ocoll($x%:input%$, $, $y%:input%$, $) [useful_change] := return(f(k, $x%$, $) = f(k, $y%$, $)))
       <=(Phash(time, N))=> [computational]
         k <-R key [unchanged]; 
          (foreach i <= N do O($x%:input%$, $) := return(f(k, $x%$, $)) |
           foreach i <= Ncoll do Ocoll($x%:input%$, $, $y%:input%$, $) := return($(x% = y%)$ && $)).\n\n")
    ^(call_f_oracle())
    ^ "\n\n}\n\n"

 let hidden_key_coll_hash_suffix =
"def HiddenKeyCollisionResistant_hash(key, input, output, f, f_oracle, qH, Phash) {
expand HiddenKeyCollisionResistant_hash_1(key, input, output, f, f_oracle, qH, Phash).
    }\n\n"

let gen_hidden_key_coll() =
  var_arg_macro hidden_key_coll_hash_prefix
    (hidden_key_coll_hash_macro())
    hidden_key_coll_hash_suffix
     
(* Second-preimage-resistant hash functions *)
     
let second_pre_hash_prefix =
"(* Second-preimage-resistant hash function 
    The interface is the same as for collision-resistant hash functions.
 *)\n\n"
      
let second_pre_hash_macro() =
"def SecondPreimageResistant_hash_%(key, $input%$, $, output, f, f_oracle, Phash) {

fun f(key, $input%$, $):output.\n\n"
    ^(if (!front_end = ProVerif) then "" else 
      "collision k <-R key; $x% <-R input%; $$ forall $y%:input%$, $;
	return(f(k, $x%$, $) = f(k, $y%$, $)) <=(Phash(time))=> return($(x% = y%)$ && $).\n\n")	
    ^(key_ret_oracle())
    ^ "\n\n}\n\n"

let second_pre_hash_suffix =
"def SecondPreimageResistant_hash(key, input, output, f, f_oracle, Phash) {
expand SecondPreimageResistant_hash_1(key, input, output, f, f_oracle, Phash).
}\n\n"

let gen_second_pre() =
  var_arg_macro second_pre_hash_prefix (second_pre_hash_macro()) second_pre_hash_suffix
    
(* Hidden-key second-preimage-resistant hash functions *)

let hidden_key_second_pre_hash_prefix =
"(* Hidden key second-preimage-resistant hash function 
    The interface is the same as for hidden-key collision-resistant hash functions.
 *)\n\n"

let hidden_key_second_pre_hash_macro() =
  "def HiddenKeySecondPreimageResistant_hash_%(key, $input%$, $, output, f, f_oracle, qH, Phash) {

fun f(key, $input%$, $):output.\n\n"
    ^(if (!front_end = ProVerif) then "" else
      "param N, Nx, Ncoll.

equiv(second_pre_res(f))
         k <-R key; 
          (foreach i <= N do O($z%:input%$, $) := return(f(k, $z%$, $)) |
           foreach i <= Nx do $x% <-R input%; $$ 
              ($Ox%() := return(x%) | $$
               foreach i <= Ncoll do Ocoll($y%:input%$, $) [useful_change] := return(f(k, $x%$, $) = f(k, $y%$, $))))
       <=(Nx * Phash(time, N))=> [computational]
         k <-R key [unchanged];
          (foreach i <= N do O($z%:input%$, $) := return(f(k, $z%$, $)) |
           foreach i <= Nx do $x% <-R input% [unchanged]; $$ 
              ($Ox%() := return(x%) | $$
               foreach i <= Ncoll do Ocoll($y%:input%$, $) :=  return($(x% = y%)$ && $))).\n\n")
    ^(call_f_oracle())
    ^ "\n\n}\n\n"

 let hidden_key_second_pre_hash_suffix =
"def HiddenKeySecondPreimageResistant_hash(key, input, output, f, f_oracle, qH, Phash) {
expand HiddenKeySecondPreimageResistant_hash_1(key, input, output, f, f_oracle, qH, Phash).
    }\n\n"

let gen_hidden_key_second_pre() = 
  var_arg_macro hidden_key_second_pre_hash_prefix
    (hidden_key_second_pre_hash_macro())
    hidden_key_second_pre_hash_suffix
      
(* Fixed hash second-preimage-resistant hash functions *)
     
let fixed_second_pre_hash_prefix =
"(* Fixed-hash second-preimage-resistant hash function 
   input%: type of the %-th input of the hash function
   output: type of the output of the hash function

   f(input...):output : the hash function. (It is not keyed.)
   Phash: probability of breaking second-preimage resistance.

   The types input%, output, and the probability Phash
   must be declared before this macro.  The function f 
   is defined by this macro. It must not be
   declared elsewhere, and it can be used only after expanding the
   macro.
 *)\n\n"
      
let fixed_second_pre_hash_macro() =
"def FixedSecondPreimageResistant_hash_%($input%$, $, output, f, Phash) {

fun f($input%$, $):output.\n\n"
    ^(if (!front_end = ProVerif) then "" else 
      "collision $x% <-R input%; $$ forall $y%:input%$, $;
	return(f($x%$, $) = f($y%$, $)) <=(Phash(time))=> return($(x% = y%)$ && $).\n\n")	
    ^ "}\n\n"

let fixed_second_pre_hash_suffix =
"def FixedSecondPreimageResistant_hash(input, output, f, Phash) {
expand FixedSecondPreimageResistant_hash_1(input, output, f, Phash).
}\n\n"

let gen_fixed_second_pre() =
  var_arg_macro fixed_second_pre_hash_prefix
    (fixed_second_pre_hash_macro())
    fixed_second_pre_hash_suffix

(* Preimage-resistant hash function *)

let pre_hash_prefix =
"(* preimage-resistant hash function 
    The interface is the same as for collision-resistant hash functions.
 *)\n\n"

let pre_hash_macro() = 
  "def PreimageResistant_hash_all_args_%(key, $input%$, $, output, f, f', f_oracle, Phash) {

fun f(key, $input%$, $):output.\n\n"
    ^(if (!front_end = ProVerif) then "" else
      "fun f'(key, $input%$, $):output.

param Nx, Neq.

equiv(preimage_res(f))
         k <-R key; 
          (Ok() := return(k) |
           foreach i <= Nx do $x% <-R input%; $$ 
              (Oim() := return(f(k, $x%$, $)) | 
               foreach i <= Neq do Oeq($y%: input%$, $) := return($(x% = y%)$ && $) |
               $Ox%() := return(x%)$ | $))
  <=(Nx * Phash(time))=> 
         k <-R key; 
          (Ok() := return(k) |
           foreach i <= Nx do $x% <-R input%; $$ 
              (Oim() := return(f'(k, $x%$, $)) | 
               foreach i <= Neq do Oeq($y%: input%$, $) := 
                        let r = $(x% = y%)$ && $ in 
                        find $suchthat defined(comp%) then return(r)$ orfind $ else return(false) |
               $Ox%() := let comp%: bool = true in return(x%)$ | $)).\n\n")
    ^(key_ret_oracle())
    ^ "\n\n}

def PreimageResistant_hash_%(key, $input%$, $, output, f, f_oracle, Phash) {
  expand PreimageResistant_hash_all_args_%(key, $input%$, $, output, f, f', f_oracle, Phash).
}\n\n"

let pre_hash_suffix =
"def PreimageResistant_hash(key, input, output, f, f_oracle, Phash) {
expand PreimageResistant_hash_1(key, input, output, f, f_oracle, Phash).
}

def PreimageResistant_hash_all_args(key, input, output, f, f', f_oracle, Phash) {
expand PreimageResistant_hash_all_args_1(key, input, output, f, f', f_oracle, Phash).
}\n\n"

let gen_pre() = 
  var_arg_macro pre_hash_prefix
    (pre_hash_macro())
    pre_hash_suffix

(* Hidden-key preimage-resistant hash function *)

let hidden_key_pre_hash_prefix =
"(* Hidden key preimage-resistant hash function 
    The interface is the same as for hidden-key collision-resistant hash functions.
 *)\n\n"

let hidden_key_pre_hash_macro() =
  "def HiddenKeyPreimageResistant_hash_all_args_%(key, $input%$, $, output, f, f', f_oracle, qH, Phash) {

fun f(key, $input%$, $):output.\n\n"
    ^(if (!front_end = ProVerif) then "" else
      "fun f'(key, $input%$, $):output.

param N, Nx, Neq.

equiv(preimage_res(f))
         k <-R key; 
          (foreach i <= N do O($z%:input%$, $) := return(f(k, $z%$, $)) |
           foreach i <= Nx do $x% <-R input%; $$ 
              (Oim() := return(f(k, $x%$, $)) | 
               foreach i <= Neq do Oeq($y%: input%$, $) := return($(x% = y%)$ && $) |
               $Ox%() := return(x%)$ | $))
  <=(Nx * Phash(time, N))=> 
         k <-R key; 
          (foreach i <= N do O($z%:input%$, $) := return(f(k, $z%$, $)) |
           foreach i <= Nx do $x% <-R input%; $$ 
              (Oim() := return(f'(k, $x%$, $)) | 
               foreach i <= Neq do Oeq($y%: input%$, $) := 
                        let r = $(x% = y%)$ && $ in 
                        find $suchthat defined(comp%) then return(r)$ orfind $ else return(false) |
               $Ox%() := let comp%: bool = true in return(x%)$ | $)).\n\n")
    ^(call_f_oracle())
    ^ "\n\n}

def HiddenKeyPreimageResistant_hash_%(key, $input%$, $, output, f, f_oracle, qH, Phash) {
  expand HiddenKeyPreimageResistant_hash_all_args_%(key, $input%$, $, output, f, f', f_oracle, qH, Phash).
}\n\n"
	
let hidden_key_pre_hash_suffix =
"def HiddenKeyPreimageResistant_hash(key, input, output, f, f_oracle, qH, Phash) {
expand HiddenKeyPreimageResistant_hash_1(key, input, output, f, f_oracle, qH, Phash).
}

def HiddenKeyPreimageResistant_hash_all_args(key, input, output, f, f', f_oracle, qH, Phash) {
expand HiddenKeyPreimageResistant_hash_all_args_1(key, input, output, f, f', f_oracle, qH, Phash).
}\n\n"

let gen_hidden_key_pre() = 
  var_arg_macro hidden_key_pre_hash_prefix
    (hidden_key_pre_hash_macro())
    hidden_key_pre_hash_suffix

(* Fixed preimage-resistant hash function *)

let fixed_pre_hash_prefix =
"(* Fixed-hash preimage-resistant hash function 
    The interface is the same as for fixed-hash second-preimage-resistant hash functions.
 *)\n\n"

let fixed_pre_hash_macro() =
"def FixedPreimageResistant_hash_all_args_%($input%$, $, output, f, f', Phash) {

fun f($input%$, $):output.\n\n"
    ^(if (!front_end = ProVerif) then "" else 
    "fun f'($input%$, $):output.

param Neq.

equiv(preimage_res(f))
  $x% <-R input%; $$(Oim() := return(f($x%$, $)) | 
                      foreach i <= Neq do Oeq($y%: input%$, $) := return($(x% = y%)$ && $) |
                      $Ox%() := return(x%)$ | $)
  <=(Phash(time))=> 
  $x% <-R input%; $$(Oim() := return(f'($x%$, $)) | 
                      foreach i <= Neq do Oeq($y%: input%$, $) := 
                        let r = $(x% = y%)$ && $ in 
                        find $suchthat defined(comp%) then return(r)$ orfind $ else return(false) |
		      $Ox%() := let comp%: bool = true in return(x%)$ | $).\n\n")
      ^ "}

def FixedPreimageResistant_hash_%($input%$, $, output, f, Phash) {
  expand FixedPreimageResistant_hash_all_args_%($input%$, $, output, f, f', Phash).
}\n\n"

let fixed_pre_hash_suffix =
"def FixedPreimageResistant_hash(input, output, f, Phash) {
expand FixedPreimageResistant_hash_1(input, output, f, Phash).
}

def FixedPreimageResistant_hash_all_args(input, output, f, f', Phash) {
expand FixedPreimageResistant_hash_all_args_1(input, output, f, f', Phash).
}\n\n"
	  
let gen_fixed_pre() =
  var_arg_macro fixed_pre_hash_prefix
    (fixed_pre_hash_macro())
    fixed_pre_hash_suffix
      
(* Pseudo random functions *)

let prf_prefix =
  "(* Pseudo random function (PRF) 
   key: type of keys, must be \"bounded\" (to be able to generate random numbers from it, and to talk about the runtime of f without mentioned the length of the key), typically \"fixed\" and \"large\".
   input%: type of the %-th input of the PRF.
   output: type of the output of the PRF, must be \"bounded\" or \"nonuniform\", typically \"fixed\".

   f: PRF function

   Pprf(t, N, l): probability of breaking the PRF property
   in time t, for one key, N queries to the PRF of length at most l.

   The types key, input, output and the probability Pprf must
   be declared before this macro is expanded. The function f
   is declared by this macro. It must not be declared elsewhere,
   and it can be used only after expanding the macro.

      *)\n\n"

let prf_large_prefix =
  "(* Pseudo random function (PRF) with large output.
   The only difference with PRF is that we eliminate collisions on the output.
   The interface is the same as for PRFs. *)\n\n"

let prf_macro is_large  =
  let large_st = if is_large then "_large" else "" in
  "def PRF"^large_st^"_%(key, $input%$, $, output, f, Pprf) {\n\n"^
  (equiv_random_fun "prf" (fun ncalls maxlength -> "Pprf(time, "^ncalls^", "^maxlength^")") is_large)^
  "\n\n}\n\n"

let prf_suffix is_large =
  let large_st = if is_large then "_large" else "" in
"def PRF"^large_st^"(key, input, output, f, Pprf) {
expand PRF"^large_st^"_1(key, input, output, f, Pprf).
}\n\n"

let gen_prf is_large =
  var_arg_macro
    (if is_large then prf_large_prefix else prf_prefix)
    (prf_macro is_large)
    (prf_suffix is_large)

(* Ideal cipher model *)

let icm() =
  if (!front_end) = ProVerif then
"def ICM_cipher(cipherkey, key, blocksize, enc, dec, enc_dec_oracle, qE, qD) {

fun enc(cipherkey, blocksize, key): blocksize.
fun dec(cipherkey, blocksize, key): blocksize.

equation forall ck:cipherkey, m:blocksize, k:key; 
	dec(ck, enc(ck, m, k), k) = m.
equation forall ck:cipherkey, m:blocksize, k:key; 
	enc(ck, dec(ck, m, k), k) = m.

param qE, qD [noninteractive].
channel chE1, chE2, chD1, chD2.
let enc_dec_oracle(ck: cipherkey) =
    (foreach iE <= qE do in(chE1, (x:blocksize, ke:key)); out(chE2, enc(ck,x,ke)))
  | (foreach iD <= qD do in(chD1, (m:blocksize, kd:key)); out(chD2, dec(ck,m,kd))). 

}\n\n"
  else
  "(* Ideal Cipher Model
   cipherkey: type of keys that correspond to the choice of the scheme, must be \"bounded\" or \"nonuniform\", typically \"fixed\".
   key: type of keys (typically \"large\")
   blocksize: type of the input and output of the cipher, must be \"bounded\" or \"nonuniform\" (to be able to generate random numbers from it; typically \"fixed\") and \"large\".
   (The modeling of the ideal cipher model is not perfect in that, in
   order to encrypt a new message, one chooses a fresh random number,
   not necessarily different from previously generated random
   numbers. Then CryptoVerif needs to eliminate collisions between
   those random numbers, so blocksize must really be \"large\".)

   enc: encryption function
   dec: decryption function
   WARNING: the encryption and decryption functions take 2 keys as
   input: the key of type cipherkey that corresponds to the choice of
   the scheme, and the normal encryption/decryption key. The cipherkey
   must be chosen once and for all at the beginning of the game and
   the encryption and decryption oracles must be made available to the
   adversary, by including a process enc_dec_oracle(ck) where
   ck is the cipherkey.
   qE is the number of calls of the encryption oracle
   qD is the number of calls of the decryption oracle
   
   The types cipherkey, key, blocksize must be declared before this
   macro is expanded. The functions enc, dec, the process
   enc_dec_oracle, and the parameters qE, qD are declared by this
   macro. They must not be declared elsewhere, and they can be used
   only after expanding the macro.

 *)

def ICM_cipher(cipherkey, key, blocksize, enc, dec, enc_dec_oracle, qE, qD) {

param Ne, Nd, Necoll, Ndcoll, Nck.

fun enc(cipherkey, blocksize, key): blocksize.
fun dec(cipherkey, blocksize, key): blocksize.

equation forall ck:cipherkey, m:blocksize, k:key; 
	dec(ck, enc(ck, m, k), k) = m.
equation forall ck:cipherkey, m:blocksize, k:key; 
	enc(ck, dec(ck, m, k), k) = m.
equation forall ck:cipherkey, m1:blocksize, m2:blocksize, k:key; 
	(dec(ck, m1, k) = dec(ck, m2, k)) = (m1 = m2).
equation forall ck:cipherkey, m1:blocksize, m2:blocksize, k:key; 
	(enc(ck, m1, k) = enc(ck, m2, k)) = (m1 = m2).

equiv(icm(enc))
       foreach ick <= Nck do ck <-R cipherkey;
         (foreach ie <= Ne do Oenc(me:blocksize, ke:key) := return(enc(ck, me, ke)) |
          foreach id <= Nd do Odec(md:blocksize, kd:key) := return(dec(ck, md, kd)) |
	  foreach iecoll <= Necoll do Oenccoll(me':blocksize, ke':key, re': blocksize) := return(enc(ck, me', ke') = re') |
	  foreach idcoll <= Ndcoll do Odeccoll(md':blocksize, kd':key, rd': blocksize) := return(dec(ck, md', kd') = rd'))
     <=((#Oenc+#Odec)*(#Oenc+#Odec-1)*Pcoll2rand(blocksize) + (#Oenccoll + #Odeccoll) * Pcoll1rand(blocksize))=>
       foreach ick <= Nck do 
         (foreach ie <= Ne do Oenc(me:blocksize, ke:key) :=
		find[unique] j<=Ne suchthat defined(me[j],ke[j],re[j]) && me = me[j] && ke = ke[j] then return(re[j]) 
		orfind k<=Nd suchthat defined(rd[k],md[k],kd[k]) && me = rd[k] && ke = kd[k] then return(md[k]) 
		else re <-R blocksize; return(re) |
          foreach id <= Nd do Odec(md:blocksize, kd:key) :=
		find[unique] j<=Ne suchthat defined(me[j],ke[j],re[j]) && md = re[j] && kd = ke[j] then return(me[j]) 
		orfind k<=Nd suchthat defined(rd[k],md[k],kd[k]) && md = md[k] && kd = kd[k] then return(rd[k]) 
		else rd <-R blocksize; return(rd) |
	  foreach iecoll <= Necoll do Oenccoll(me':blocksize, ke':key, re': blocksize) :=
		find[unique] j<=Ne suchthat defined(me[j],ke[j],re[j]) && me' = me[j] && ke' = ke[j] then return(re' = re[j]) 
		orfind k<=Nd suchthat defined(rd[k],md[k],kd[k]) && me' = rd[k] && ke' = kd[k] then return(re' = md[k]) 
		else return(false) |
          foreach idcoll <= Ndcoll do Odeccoll(md':blocksize, kd':key, rd': blocksize) :=
		find[unique] j<=Ne suchthat defined(me[j],ke[j],re[j]) && md' = re[j] && kd' = ke[j] then return(rd' = me[j]) 
		orfind k<=Nd suchthat defined(rd[k],md[k],kd[k]) && md' = md[k] && kd' = kd[k] then return(rd' = rd[k]) 
		else return(false)).

(* The difference of probability is the probability of collision between two
random numbers in blocksize among the N+N2 chosen random numbers. *)

  param qE, qD [noninteractive].\n\n"
^
(if (!front_end) = Channels then
"channel chE1, chE2, chD1, chD2.
let enc_dec_oracle(ck: cipherkey) =
    (foreach iE <= qE do in(chE1, (x:blocksize, ke:key)); out(chE2, enc(ck,x,ke)))
  | (foreach iD <= qD do in(chD1, (m:blocksize, kd:key)); out(chD2, dec(ck,m,kd)))."
else
"let enc_dec_oracle(ck: cipherkey) =
    (foreach iE <= qE do Oenc(x:blocksize, ke:key) := return(enc(ck,x,ke)))
  | (foreach iD <= qD do Odec(m:blocksize, kd:key) := return(dec(ck,m,kd))).")
^"\n\n}\n\n"

let gen_icm() =
  print_string (icm())
    
(* Split a value *)

let split_prefix() = "(* random_split_N defines functions to split a random value into N values.

  input_t: type of the input value
  part%_t: types of the output parts
  tuple_t: type of a tuple of the output parts
  tuple(part1_t, ..., partN_t): tuple_t builds a tuple from N parts.
  split(input_t): tuple_t splits the input into N parts and returns a tuple of these parts
  Usage: let tuple(x1, ..., xN) = split(y) in ...

  input_t, part%_t, and tuple_t must be defined before.
  tuple and split are defined by this macro. " ^
(if (!front_end) = ProVerif then
"\n\n  This macro does not model that each xi leaks a part of y.
  It is suitable to split the result of a hash function,
  when you do not use that result in other ways and do not
  prove strong secrecy properties on that result.
  Other usages may not be sound. "
else "") ^ 
"*)\n\n"

let split_macro() =
if (!front_end) = ProVerif then
  "def random_split_%(input_t, $part%_t$, $, tuple_t, tuple, split) {

  fun tuple($part%_t$, $): tuple_t [data].

  $fun get%(input_t): part%_t.$
  $

  letfun split(r: input_t) = tuple($get%(r)$, $).

  reduc forall x: input_t; concat($get%(x)$, $) = x.

}\n\n"
else
  "def random_split_%(input_t, $part%_t$, $, tuple_t, tuple, split) {

  fun tuple($part%_t$, $): tuple_t [data].

  $fun get%(input_t): part%_t.$
  $

  letfun split(r: input_t) = tuple($get%(r)$, $).

  equiv(splitter(split))
     r <-R input_t; 
       ($O%() := return(get%(r))$ | $)
    <=(0)=>
     $part% <-R part%_t;$ $
       ($O%() := return(part%)$ | $).

}\n\n"
    
let gen_split() =
  var_arg_macro (split_prefix()) (split_macro()) ""
    

let started = ref false
    
let gen s =
  started := true;
  match s with
  | "ROM_hash" -> gen_rom false
  | "ROM_hash_large" -> gen_rom true
  | "CollisionResistant_hash" -> gen_coll()
  | "HiddenKeyCollisionResistant_hash" -> gen_hidden_key_coll()
  | "SecondPreimageResistant_hash" -> gen_second_pre()
  | "HiddenKeySecondPreimageResistant_hash" -> gen_hidden_key_second_pre()
  | "FixedSecondPreimageResistant_hash" -> gen_fixed_second_pre()
  | "PreimageResistant_hash" -> gen_pre()
  | "HiddenKeyPreimageResistant_hash" -> gen_hidden_key_pre()
  | "FixedPreimageResistant_hash" -> gen_fixed_pre()
  | "PRF" -> gen_prf false
  | "PRF_large" -> gen_prf true
  | "ICM_cipher" -> gen_icm()
  | "random_split" -> gen_split()
  | "all" ->
      gen_rom false;
      gen_rom true;
      gen_coll();
      gen_hidden_key_coll();
      gen_second_pre();
      gen_hidden_key_second_pre();
      gen_fixed_second_pre();
      gen_pre();
      gen_hidden_key_pre();
      gen_fixed_pre();
      gen_prf false;
      gen_prf true;
      gen_icm();
      gen_split()
  | s ->
      prerr_string ("Unknown primitive " ^s);
      exit 2

      
let _ =
  Arg.parse
    [ "-out", Arg.String (function s ->
      if !started then
	begin
	  prerr_string "Cannot change the front-end after having printed some primitives.\n";
	  exit 2
	end;
      match s with
	"channels" -> front_end := Channels
      | "oracles" -> front_end := Oracles
      | "proverif" -> front_end := ProVerif
      | _ ->
          prerr_string "Command-line option -out expects argument either \"channels\", \"oracles\", or \"proverif\".\n";
          exit 2),
      "channels / -out oracles / -out proverif \tchoose the front-end";
      "-dist_oracles", Arg.Int (fun n ->
	if n < 2 || n > 100 then
	  begin
	    prerr_string "Argument of -dist_oracles should be between 2 and 100.\n";
	    exit 2
	  end;
	max_copy := n),
      "<n>\tset the number of distinct oracles in ROM, PRF, ...";
      "-args", Arg.Int (fun n ->
	if n < 0 || n > 100 then
	  begin
	    prerr_string "Argument of -args should be between 1 and 100.\n";
	    exit 2;
	  end;
	start := n; final := n),
      "<n>\tgenerate primitives with <n> arguments (for primitives that support a variable number of arguments)";
      "-args-from-to", Arg.Tuple
	[ Arg.Int (fun n ->
	  if n < 0 || n > 100 then
	    begin
	      prerr_string "Arguments of -args-from-to should be between 1 and 100.\n";
	      exit 2;
	    end;
	  start := n);
	  Arg.Int (fun n ->
	  if n < !start || n > 100 then
	    begin
	      prerr_string "Arguments of -args-from-to should be between 1 and 100,\nand the second argument should be larger than the first one.\n";
	      exit 2;
	    end;
	    final := n) ],
	  "<min> <max>\tgenerate primitives with from <min> to <max> arguments"
    ]
    gen ("Crypto library generator, by Bruno Blanchet\nCopyright ENS-CNRS-Inria, distributed under the CeCILL-B license\nUsage:\n  cryptogen [options] <primitive>\nto print macro for the primitive <primitive>.\n\nAllowed primitives:\n  ROM_hash\n  ROM_hash_large\n  CollisionResistant_hash\n  HiddenKeyCollisionResistant_hash\n  SecondPreimageResistant_hash\n  HiddenKeySecondPreimageResistant_hash\n  FixedSecondPreimageResistant_hash\n  PRF\n  PRF_large\n  ICM_cipher\n  random_split\n  all (to print macros for all primitives above)\n\nOptions:")

