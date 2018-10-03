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

 *)\n\n"

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


let rom_hash_suffix =
"def ROM_hash(key, hashinput, hashoutput, hash, hashoracle, qH) {
expand ROM_hash_1(key, hashinput, hashoutput, hash, hashoracle, qH).
}\n\n"

(* Collision-resistant hash functions *)
    
let coll_hash_prefix =
"(* Collision resistant hash function 
   key: type of the key of the hash function, must be \"bounded\" or \"nonuniform\", typically \"fixed\"
   hashinput%: type of the %-th input of the hash function
   hashoutput: type of the output of the hash function

   hash: the hash function.
   Phash: probability of breaking collision resistance.
   WARNING: A collision resistant hash function is a keyed hash function.
   The key must be generated once and for all at the beginning of the game,
   and immediately made available to the adversary, for instance by
   including the process hashoracle(k), where k is the key.

   The types key, hashinput%, hashoutput, and the probability Phash
   must be declared before this macro.  The function hash and the
   process hashoracle are defined by this macro. They must not be
   declared elsewhere, and they can be used only after expanding the
   macro.

 *)\n\n"
      
let coll_hash_macro() =
  if (!front_end) = ProVerif then
"def CollisionResistant_hash_%(key, $hashinput%$, $, hashoutput, hash, hashoracle, Phash) {
    
fun hash(key, $hashinput%$, $):hashoutput.

channel ch1, ch2.
let hashoracle(k: key) = 
	in(ch1, ());
        out(ch2, k)).

}

"	
  else
"def CollisionResistant_hash_%(key, $hashinput%$, $, hashoutput, hash, hashoracle, Phash) {

fun hash(key, $hashinput%$, $):hashoutput.

collision k <-R key; forall $x%:hashinput%$, $, $y%:hashinput%$, $;
  return(hash(k, $x%$, $) = hash(k, $y%$, $)) <=(Phash(time))=> return($(x% = y%)$ && $).\n\n"
  ^
  (if (!front_end) = Channels then
"channel ch1, ch2.
let hashoracle(k: key) =
    in(ch1, ());
    out(ch2, k)."
  else
"let hashoracle(k: key) =
        OH() := return(k).")
  ^ "\n\n}\n\n"

let coll_hash_suffix =
"def CollisionResistant_hash(key, hashinput, hashoutput, hash, hashoracle, Phash) {
expand CollisionResistant_hash_1(key, hashinput, hashoutput, hash, hashoracle, Phash).
}\n\n"


(* Ideal cipher model *)

let icm() =
  if (!front_end) = ProVerif then
"def ICM_cipher(cipherkey, key, blocksize, enc, dec, enc_dec_oracle, qE, qD) {

fun enc(cipherkey, blocksize, key): blocksize.
fun dec(cipherkey, blocksize, key): blocksize.

equation forall ck:cipherkey, m:blocksize, k:key; 
	dec(ck, enc(ck, m, k), k) = m.
equation forall ck:cipherkey, m:blocksize, r:keyseed; 
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
  print_string rom_hash_prefix;
  for n = !start to !final do
    print_macro (rom_hash_macro()) n
  done;
  print_string rom_hash_suffix;
  print_string coll_hash_prefix;
  for n = !start to !final do
    print_macro (coll_hash_macro()) n
  done;
  print_string coll_hash_suffix;
  print_string (icm())
  
    
