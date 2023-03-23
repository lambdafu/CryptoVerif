module Helper

module List = FStar.List.Tot
module String = FStar.String
module Char = FStar.Char
module B = Lib.ByteSequence
module Seq = Lib.Sequence
open FStar.Mul
open Lib.IntTypes

#set-options "--z3rlimit 25"

val char4_of_int (n: uint32) : Tot (B.lbytes 4)
let char4_of_int n = B.uint_to_bytes_le n


val int_of_char4 (s: B.bytes) (i: uint32{Seq.length s >= (uint_v i) + 4}) : Tot (uint32)
let int_of_char4 s i =
  let length_bytes = FStar.Seq.slice s (uint_v i) ((uint_v i) + 4) in
  B.uint_from_bytes_le length_bytes

// generated: "__Failure__"
inline_for_extraction
let size_label_failure_bytes:size_nat = 11
let label_failure_bytes_list:l: list uint8 {List.Tot.length l == size_label_failure_bytes} =
  [@@ inline_let ]let l =
    [
      u8 0x5f; u8 0x5f; u8 0x46; u8 0x61; u8 0x69; u8 0x6c; u8 0x75; u8 0x72; u8 0x65; u8 0x5f;
      u8 0x5f
    ]
  in
  assert_norm (List.Tot.length l == size_label_failure_bytes);
  l
let failure_bytes:B.lbytes size_label_failure_bytes = Seq.createL label_failure_bytes_list

val sub_compos: list B.bytes -> option B.bytes

let rec sub_compos l' =
  match l' with
  | [] -> Some B.bytes_empty
  | e :: ql ->
    let len_e = Seq.length e in
    if len_e > maxint U32
    then None
    else
      let t = char4_of_int (u32 len_e) in
      match sub_compos ql with
      | None -> None
      | Some r ->
        let len_r = Seq.length r in
        if len_e + len_r + 4 > maxint U32
        then None
        else Some (FStar.Seq.append t (FStar.Seq.append e r))

let compos l =
  if List.length l <= maxint U32
  then
    let s = char4_of_int (u32 (List.length l)) in
    match sub_compos l with
    | None -> failure_bytes
    | Some r -> if Seq.length r + 4 <= maxint U32 then FStar.Seq.append s r else failure_bytes
  else failure_bytes

val sub_decompos: B.bytes -> nat -> uint32 -> option (l: list B.bytes {List.for_all length_restr l})

let rec sub_decompos b nb pos =
  if Seq.length b > uint_v pos + 4
  then
    if nb > 0
    then
      let len = int_of_char4 b pos in
      if uint_v pos + 4 > maxint U32
      then None
      else
        let i_s = add pos (u32 4) in
        let req = uint_v i_s + uint_v len in
        if Seq.length b >= req && req <= maxint U32
        then
          match sub_decompos b (nb - 1) (add len i_s) with
          | None -> None
          | Some r -> Some ((FStar.Seq.slice b (uint_v i_s) req) :: r)
        else None
    else if uint_v pos = Seq.length b then Some [] else None
  else None

let decompos b =
  if Seq.length b > 4
  then
    let nb = int_of_char4 b (u32 0) in
    sub_decompos b (uint_v nb) (u32 4)
  else None

