module CVTypes

open Lib.IntTypes
module B = Lib.ByteSequence
open Lib.Sequence
open Lib.PrintSequence

open RandomHelper

type entropy = RandomHelper.entropy

type bytes = B.bytes

(* Random generation *)

let initialize_entropy ent = RandomHelper.initialize_entropy ent

let finalize_entropy ent = RandomHelper.finalize_entropy ent

let gen_nat max ent = RandomHelper.gen_nat 10 max ent

let gen_lbytes l ent = RandomHelper.gen_lbytes l ent

let gen_bool ent = RandomHelper.gen_bool ent

(* Equality *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let rec _eq_bytes (blocks_left blocks_right: FStar.Seq.seq uint8)
    : Pure bool
      (requires
        FStar.Seq.length blocks_left = FStar.Seq.length blocks_right /\
        FStar.Seq.length blocks_left >= Lib.IntTypes.max_size_t)
      (ensures fun b -> b = true <==> blocks_left == blocks_right)
      (decreases (FStar.Seq.length blocks_left)) =
  let block_left, rem_left = Lib.UpdateMulti.split_block Lib.IntTypes.max_size_t blocks_left 1 in
  let block_right, rem_right = Lib.UpdateMulti.split_block Lib.IntTypes.max_size_t blocks_right 1 in
  assert (FStar.Seq.length block_left = FStar.Seq.length block_right);
  assert (FStar.Seq.length rem_left = FStar.Seq.length rem_right);
  let front = B.lbytes_eq #(Seq.length block_left) block_left block_right in
  if (FStar.Seq.length rem_left <= Lib.IntTypes.max_size_t)
  then front && B.lbytes_eq #(Seq.length rem_left) rem_left rem_right
  else front && _eq_bytes rem_left rem_right
#pop-options

let eq_bytes b1 b2 =
  if not (Seq.length b1 = Seq.length b2)
  then false
  else
    if (Seq.length b1 <= Lib.IntTypes.max_size_t)
    then B.lbytes_eq #(Seq.length b1) b1 b2
    else _eq_bytes b1 b2

let eq_obytes ob1 ob2 =
  match ob1, ob2 with
  | None, None -> true
  | Some b1, Some b2 -> eq_bytes b1 b2
  | _ -> false

let eq_lbytes #l b1 b2 = B.lbytes_eq #l b1 b2

(* Lemmas for Equality *)

let rec lemma__eq_bytes_is_equal
      (b1: bytes)
      (b2: bytes{Seq.length b1 = Seq.length b2 /\ Seq.length b1 >= Lib.IntTypes.max_size_t})
    : Lemma (ensures _eq_bytes b1 b2 <==> b2 == b1) (decreases Seq.length b1) =
  let block_left, rem_left = Lib.UpdateMulti.split_block Lib.IntTypes.max_size_t b1 1 in
  let block_right, rem_right = Lib.UpdateMulti.split_block Lib.IntTypes.max_size_t b2 1 in
  assert (FStar.Seq.length block_left = FStar.Seq.length block_right);
  assert (FStar.Seq.length rem_left = FStar.Seq.length rem_right);
  if Seq.length rem_left <= Lib.IntTypes.max_size_t
  then
    (* in this case we rely on the property of lbytes_eq *)
    ()
  else lemma__eq_bytes_is_equal rem_left rem_right

let lemma_eq_bytes_equal b1 b2 =
  if not (Seq.length b1 = Seq.length b2)
  then ()
  else if (Seq.length b1 <= Lib.IntTypes.max_size_t) then () else lemma__eq_bytes_is_equal b1 b2

let lemma_eq_obytes_equal b1 b2 = ()

(* Serialization *)

let serialize_nat n =
  let len = if n > 0 then (FStar.Math.Lib.div (FStar.Math.Lib.log_2 n) 8) + 1 else 0 in
  assume (n < pow2 (op_Multiply 8 len));
  B.nat_to_intseq_be #U8 #SEC len n

let deserialize_nat b = Some (B.nat_from_intseq_be #U8 #SEC b)

let serialize_lbytes lb = lb
let deserialize_lbytes l b = if Seq.length b = l then Some b else None

let obytes_none:uint8 = u8 0x00
let obytes_some:uint8 = u8 0x01
let obytes_none_l:lbytes 1 = (Seq.createL [obytes_none])
let obytes_some_l:lbytes 1 = (Seq.createL [obytes_some])

let serialize_obytes ob =
  match ob with
  | None -> obytes_none_l
  | Some b ->
    let c = b in
    let c = Seq.append obytes_some_l c in
    c

let deserialize_obytes b =
  if Seq.length b < 1
  then None
  else
    let fst, rem = FStar.Seq.Properties.split b 1 in
    if Lib.ByteSequence.lbytes_eq #1 obytes_none_l fst
    then (if Seq.length rem = 0 then Some (None) else None)
    else if Lib.ByteSequence.lbytes_eq #1 obytes_some_l fst then Some (Some rem) else None

inline_for_extraction
let size_bytes_true:size_nat = 1
let bytes_true_list:l: list uint8 {List.Tot.length l == size_bytes_true} =
  [@@ inline_let ]let l = [u8 0xFF] in
  assert_norm (List.Tot.length l == size_bytes_true);
  l
let bytes_true:lbytes size_bytes_true = Seq.createL bytes_true_list

inline_for_extraction
let size_bytes_false:size_nat = 1
let bytes_false_list:l: list uint8 {List.Tot.length l == size_bytes_false} =
  [@@ inline_let ]let l = [u8 0x00] in
  assert_norm (List.Tot.length l == size_bytes_false);
  l
let bytes_false:lbytes size_bytes_false = Seq.createL bytes_false_list


let serialize_bool b =
  match b with
  | true -> bytes_true
  | false -> bytes_false

let deserialize_bool b =
  if Seq.length b = 1
  then
    (if B.lbytes_eq b bytes_true
      then Some true
      else if B.lbytes_eq b bytes_false then Some false else None)
  else None

let lemma_deser_nat_inner a = admit ()

let lemma_serde_nat_inner a = admit ()

let lemma_deser_lbytes_inner a = ()

let lemma_serde_lbytes_inner a = ()

let lemma_deser_obytes_inner a =
  match a with
  | Some b ->
    FStar.Seq.Properties.append_slices obytes_some_l b;
    ()
  | None -> ()

let lemma_serde_obytes_inner a =
  match deserialize_obytes a with
  | Some b ->
    (assert (Seq.length a >= 1);
      FStar.Seq.Properties.lemma_split a 1;
      match b with
      | None -> ()
      | Some c -> ())
  | None -> ()

let lemma_deser_bool_inner a = ()

let lemma_serde_bool_inner a = ()

(* Printing *)
let bool_to_str b =
  match b with
  | true -> "true"
  | false -> "false"


let print_bytes bytes = List.iter (fun a -> print_uint8_hex_pad a) (to_list bytes)

let print_nat n = print_bytes (serialize_nat n)

let print_bool b = IO.print_string (bool_to_str b)

let print_label_bytes l b separator =
  IO.print_string ("  " ^ l ^ ": ");
  print_bytes b;
  IO.print_string (if separator then "," else "");
  IO.print_newline ()

let print_label_nat l n separator = print_label_bytes l (serialize_nat n) separator

let print_label_bool l b separator =
  IO.print_string ("  " ^ l ^ ": ");
  IO.print_string (bool_to_str b);
  IO.print_string (if separator then "," else "");
  IO.print_newline ()

