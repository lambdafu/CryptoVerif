module NSL.Types

open CVTypes
friend CVTypes

module HPKE = Spec.Agile.HPKE
module DH = Spec.Agile.DH
module AEAD = Spec.Agile.AEAD
module Hash = Spec.Agile.Hash
module HKDF = Spec.Agile.HKDF

let aead_alg = AEAD.CHACHA20_POLY1305
let cs:HPKE.ciphersuite = (DH.DH_Curve25519, Hash.SHA2_256, HPKE.Seal aead_alg, Hash.SHA2_256)

let size_nonce = 8

let _pkey = HPKE.key_dh_secret_s cs
let _skey = HPKE.key_dh_public_s cs
let _ciphertext = HPKE.key_dh_public_s cs * AEAD.cipher aead_alg

let msg1res = option (_skey * _pkey * bool * lbytes 8 * _ciphertext)

let ciphertext_opt = option _ciphertext

let plaintext = AEAD.plain aead_alg
let ciphertext = _ciphertext

let skey = _skey
let keypair = _pkey * _skey
let pkey = _pkey

// maximum POSIX user name length seems to be 32 byte
// maximum DNS hostname length seems to be 253 byte
let max_size_addr = 32 + 1 + 253
type address = b: bytes{Seq.length b <= max_size_addr}

let _eq_skey sk1 sk2 = eq_lbytes #(HPKE.size_dh_key cs) sk1 sk2

let _eq_pkey pk1 pk2 = eq_lbytes #(HPKE.size_dh_public cs) pk1 pk2

let _eq_nonce n1 n2 = eq_lbytes #size_nonce n1 n2

let _eq_ct ct1 ct2 = eq_bytes ct1 ct2

let _eq_ciphertext (c1 c2: ciphertext) =
  let (pk1, ct1), (pk2, ct2) = c1, c2 in
  _eq_pkey pk1 pk2 && _eq_ct ct1 ct2

let eq_msg1res m1 m2 =
  match m1, m2 with
  | Some (sk1, pk1, trust1, n1, c1), Some (sk2, pk2, trust2, n2, c2) ->
    _eq_skey sk1 sk2 && _eq_pkey pk1 pk2 && trust1 = trust2 && _eq_nonce n1 n2 &&
    _eq_ciphertext c1 c2
  | _, _ -> false

let eq_ciphertext_opt oc1 oc2 =
  match oc1, oc2 with
  | Some c1, Some c2 -> _eq_ciphertext c1 c2
  | _, _ -> false

let eq_plaintext p1 p2 = eq_bytes p1 p2

let eq_ciphertext (c1 c2: ciphertext) = _eq_ciphertext c1 c2

let eq_skey sk1 sk2 = _eq_skey sk1 sk2

let eq_pkey pk1 pk2 = _eq_pkey pk1 pk2

let eq_keypair kp1 kp2 =
  match kp1, kp2 with | (pk1, sk1), (pk2, sk2) -> _eq_skey sk1 sk2 && _eq_pkey pk1 pk2

let eq_addr adr1 adr2 = eq_bytes adr1 adr2


let _serialize_pkey p = p
let _deserialize_pkey (b: bytes) : option pkey =
  if Seq.length b = HPKE.size_dh_public cs then Some b else None

let serialize_ciphertext c = match c with | e, ct -> Seq.append (_serialize_pkey e) ct

let deserialize_ciphertext b =
  if
    (Seq.length b >= (HPKE.size_dh_public cs) + AEAD.tag_length aead_alg) &&
    (Seq.length b - (HPKE.size_dh_public cs) <= AEAD.cipher_max_length aead_alg)
  then
    (let e, ct = FStar.Seq.Properties.split b (HPKE.size_dh_public cs) in
      match _deserialize_pkey e with
      | None -> None
      | Some pk -> Some (pk, ct))
  else None

let serialize_skey s = s
let deserialize_skey b = if Seq.length b = HPKE.size_dh_key cs then Some b else None

let serialize_pkey p = _serialize_pkey p
let deserialize_pkey b = _deserialize_pkey b

let serialize_address a = a
let deserialize_address b = if Seq.length b <= max_size_addr then Some b else None

