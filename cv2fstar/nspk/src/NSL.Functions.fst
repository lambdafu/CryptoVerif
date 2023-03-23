module NSL.Functions

friend CVTypes
friend NSL.Types
module Crypto = Crypto

open Lib.IntTypes
open Lib.ByteSequence

let nonce = lbytes 8

let msg1type:uint8 = u8 0x01
let msg2type:uint8 = u8 0x02
let msg3type:uint8 = u8 0x03
let msg1typel:lbytes 1 = (Seq.createL [msg1type])
let msg2typel:lbytes 1 = (Seq.createL [msg2type])
let msg3typel:lbytes 1 = (Seq.createL [msg3type])

(* Concatenation *)
(* We may want to have the lemmas stating that unconcat of concat is the identity
   and similar lemmas*)
// we could call this encode_msg1 and decode_msg1
let msg1_content (x: lbytes 8) (y: address) =
  let l = Lib.ByteSequence.nat_to_bytes_be #Lib.IntTypes.SEC 2 (Seq.length y) in
  let c = y in
  let c = Seq.append l c in
  let c = Seq.append x c in
  c

val _msg1: nonce -> address -> plaintext
let _msg1 n addr = Seq.append msg1typel (msg1_content n addr)


val _inv_msg1: bytes -> option (nonce * address)
let _inv_msg1 bytes =
  if Seq.length bytes < 1
  then None
  else
    let msgtype, bytes = FStar.Seq.Properties.split bytes 1 in
    if lbytes_eq #1 msgtype msg1typel
    then
      let len = Seq.length bytes in
      if len < size_nonce + 2
      then None
      else
        let n, bytes = FStar.Seq.Properties.split bytes size_nonce in
        let l_encoded, addr = FStar.Seq.Properties.split bytes 2 in
        let l = nat_from_bytes_be #SEC l_encoded in
        if len = (size_nonce + 2 + l) && l <= max_size_addr then Some (n, addr) else None
    else None

let msg2_content (x y: lbytes 8) (z: address) =
  let l = nat_to_bytes_be #SEC 2 (Seq.length z) in
  let c = z in
  let c = Seq.append l c in
  let c = Seq.append y c in
  let c = Seq.append x c in
  c

val _msg2: nonce -> nonce -> address -> plaintext
let _msg2 na nb addr =
  let c = msg2_content na nb addr in
  let c = Seq.append msg2typel c in
  c

val _inv_msg2: bytes -> option (nonce * nonce * address)
let _inv_msg2 bytes =
  if Seq.length bytes < 1
  then None
  else
    let msgtype, bytes = FStar.Seq.Properties.split bytes 1 in
    if lbytes_eq #1 msgtype msg2typel
    then
      let two_size_nonce = size_nonce + size_nonce in
      let len = Seq.length bytes in
      if len < two_size_nonce + 2
      then None
      else
        let na, bytes = FStar.Seq.Properties.split bytes size_nonce in
        let nb, bytes = FStar.Seq.Properties.split bytes size_nonce in
        let l_encoded, addr = FStar.Seq.Properties.split bytes 2 in
        let l = nat_from_bytes_be #SEC l_encoded in
        if len = (two_size_nonce + 2 + l) && l <= max_size_addr then Some (na, nb, addr) else None
    else None

val _msg3: nonce -> plaintext
let _msg3 nb = Seq.append msg3typel nb

val _inv_msg3: bytes -> option (nonce)
let _inv_msg3 bytes =
  if Seq.length bytes < 1
  then None
  else
    let msgtype, n = FStar.Seq.Properties.split_eq bytes 1 in
    if lbytes_eq #1 msgtype msg3typel
    then
      let len = Seq.length n in
      if len = size_nonce then Some n else None
    else None

let skgen sk = sk

let pkgen sk = Crypto.get_pk sk

let enc pt pk sk = Crypto.enc pt pk sk

let ciphertext_bottom = None

let msg1fail = None

let msg1succ sk pk trust n ct = Some (sk, pk, trust, n, ct)

let inv_msg1succ o =
  match o with
  | Some (sk, pk, trust, n, ct) -> Some (sk, pk, trust, n, ct)
  | None -> None

let msg3 nb = _msg3 nb

let inv_msg3 m = _inv_msg3 m

let msg2 na nb addrB = _msg2 na nb addrB

let inv_msg2 m = _inv_msg2 m

let ciphertext_some ct = Some (ct)

let inv_ciphertext_some oct = oct

let dec ct sk = Crypto.dec ct sk

let msg1 na addrA = _msg1 na addrA

let inv_msg1 m = _inv_msg1 m

let injbot pt = Some (pt)

let inv_injbot ob =
  match ob with
  | None -> None
  | Some b ->
    if Seq.length b <= Spec.Agile.AEAD.max_length Spec.Agile.AEAD.CHACHA20_POLY1305
    then Some b
    else None

let kp pk sk = pk, sk

let inv_kp kp =
  match kp with
  | pk, sk -> Some (pk, sk)
  | _ -> None

