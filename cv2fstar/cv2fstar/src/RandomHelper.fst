module RandomHelper

module B = Lib.ByteSequence
open Lib.Sequence
open Lib.RandomSequence

noeq
type entropy = | Entropy : system_entropy: Lib.RandomSequence.entropy -> entropy

let initialize_entropy ent = Entropy ent

let finalize_entropy ent =
  let Entropy entropy = ent in
  entropy

val crypto_random_unbounded: Lib.RandomSequence.entropy -> len: nat
  -> Tot (Lib.RandomSequence.entropy * b: Lib.ByteSequence.bytes{Seq.length b = len})
      (decreases len)

let rec crypto_random_unbounded ent len =
  if len > Lib.IntTypes.max_size_t
  then
    let ent1, bytes1 = crypto_random ent Lib.IntTypes.max_size_t in
    let ent2, bytes2 = crypto_random_unbounded ent1 (len - Lib.IntTypes.max_size_t) in
    ent2, Seq.append bytes1 bytes2
  else
    let ent3, bytes3 = crypto_random ent len in
    ent3, bytes3

val log_2_lt (x: pos) : Lemma (FStar.Math.Lib.log_2 x < x)
let rec log_2_lt x =
  match x with
  | 1 -> ()
  | 2 -> ()
  | _ -> log_2_lt (x / 2)

let gen_nat accuracy max ent =
  let Entropy entropy1 = ent in
  log_2_lt max;
  let k_num_bits:nat = 1 + FStar.Math.Lib.log_2 max in
  let k_num_bytes:nat = k_num_bits / 8 + (if k_num_bits % 8 > 0 then 1 else 0) in
  assume (pow2 (op_Multiply 8 k_num_bytes) - 1 >= max);
  (* The accuracy is to reduce skew in the distribution. *)
  let num_bytes = k_num_bytes + accuracy in
  let entropy2, r = crypto_random_unbounded entropy1 num_bytes in
  let n_raw = Lib.ByteSequence.nat_from_bytes_le #Lib.IntTypes.SEC r in
  let n = n_raw % (max + 1) in
  (Entropy entropy2, n)

let gen_lbytes num ent =
  let Entropy entropy1 = ent in
  let entropy2, bytes = crypto_random entropy1 num in
  Entropy entropy2, bytes

let gen_bool ent =
  let Entropy entropy1 = ent in
  let entropy2, byte = crypto_random entropy1 1 in
  let n = Lib.ByteSequence.nat_from_bytes_le #Lib.IntTypes.SEC byte in
  Entropy entropy2, n % 2 <> 0
