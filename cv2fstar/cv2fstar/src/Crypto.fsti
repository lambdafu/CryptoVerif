module Crypto

open CVTypes

module HPKE = Spec.Agile.HPKE
module DH = Spec.Agile.DH
module AEAD = Spec.Agile.AEAD
module Hash = Spec.Agile.Hash
module HKDF = Spec.Agile.HKDF

let aead_alg = AEAD.CHACHA20_POLY1305
let cs:HPKE.ciphersuite = (DH.DH_Curve25519, Hash.SHA2_256, HPKE.Seal aead_alg, Hash.SHA2_256)

let plaintext = AEAD.plain aead_alg
let pkey = HPKE.key_dh_secret_s cs
let skey = HPKE.key_dh_public_s cs
let ciphertext = HPKE.key_dh_public_s cs * AEAD.cipher aead_alg
let keypair = pkey * skey

val get_pk: skey -> pkey

val enc: plaintext -> pkey -> skey -> option ciphertext
val dec: ciphertext -> skey -> option bytes

