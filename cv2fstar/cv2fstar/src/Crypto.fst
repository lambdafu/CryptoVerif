module Crypto

module HPKE = Spec.Agile.HPKE
module DH = Spec.Agile.DH
module AEAD = Spec.Agile.AEAD
module Hash = Spec.Agile.Hash
module HKDF = Spec.Agile.HKDF
open Lib.IntTypes
module B = Lib.ByteSequence
open Lib.Sequence
open Lib.PrintSequence
open FStar.All

friend CVTypes

#set-options "--z3rlimit 75"

(* Asymmetric encryption / decryption *)

let get_pk sk = match DH.secret_to_public DH.DH_Curve25519 sk with | Some pk -> pk

let enc plain pk skE =
  match HPKE.sealBase cs skE pk B.lbytes_empty B.lbytes_empty plain with
  | None -> None
  | Some (pkE, c) -> Some (pkE, c)

let dec ciphertext sk =
  let enc, c = ciphertext in
  match HPKE.openBase cs enc sk B.lbytes_empty B.lbytes_empty c with
  | None -> None
  | Some p -> Some p
