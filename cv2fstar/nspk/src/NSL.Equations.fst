module NSL.Equations

open CVTypes
open NSL.Types
open NSL.Functions
friend CVTypes
friend NSL.Types
friend NSL.Functions

module SP = FStar.Seq.Properties
module I = Lib.IntTypes
module B = Lib.ByteSequence
module HPKE = Spec.Agile.HPKE

let lemma_0 () = ()

let lemma_1 () = ()

let lemma_2 () = ()

let msg1_min_length:nat = 11
let msg1_has_min_length (x: lbytes 8) (y: address)
    : Lemma (ensures Seq.length (msg1 x y) >= msg1_min_length) = ()
let msg2_min_length:nat = 19
let msg2_has_min_length (x y: lbytes 8) (z: address)
    : Lemma (ensures Seq.length (msg2 x y z) >= msg2_min_length) = ()
let msg3_length:nat = 9
let msg3_has_length (x: lbytes 8) : Lemma (ensures Seq.length (msg3 x) = msg3_length) = ()

let has_msg1_beginning (msg: bytes{Seq.length msg >= msg1_min_length}) : bool =
  let t = FStar.Seq.index msg 0 in
  B.lbytes_eq #1 (Seq.createL [t]) msg1typel

let msg1_begins_with_typebyte (x: lbytes 8) (y: address)
    : Lemma (ensures has_msg1_beginning (msg1 x y)) =
  ()


let has_msg2_beginning (msg: bytes{Seq.length msg >= msg2_min_length}) : bool =
  let t = FStar.Seq.index msg 0 in
  B.lbytes_eq #1 (Seq.createL [t]) msg2typel

let msg2_begins_with_typebyte (x y: lbytes 8) (z: address)
    : Lemma (ensures has_msg2_beginning (msg2 x y z)) =
  ()

let has_msg3_beginning (msg: bytes{Seq.length msg = msg3_length}) : bool =
  let t = FStar.Seq.index msg 0 in
  B.lbytes_eq #1 (Seq.createL [t]) msg3typel

let msg3_begins_with_typebyte (x: lbytes 8) : Lemma (ensures has_msg3_beginning (msg3 x)) =
  ()

let lemma_3 () =
  let lem3 (x y: lbytes 8) (z: address) (a: lbytes 8) (b: address)
      : Lemma (ensures not (eq_plaintext (msg2 x y z) (msg1 a b)))
        [SMTPat (eq_plaintext (msg2 x y z) (msg1 a b))] =
    msg1_begins_with_typebyte a b;
    msg2_begins_with_typebyte x y z
  in
  assert (forall (x: lbytes 8) (y: lbytes 8) (z: address) (a: lbytes 8) (b: address).
        (not (eq_plaintext (msg2 x y z) (msg1 a b))))

let lemma_4 () = ()

let lemma_5 () = ()

let lemma_6 () = ()

let lemma_7 () = ()

let lemma_8 () = ()

let lemma_9 () = ()

let lemma_10 () = ()

let lemma_11 () = ()

let lemma_12 () = ()

let lemma_13 () = ()

let lemma_14 () = ()

let msg2_length (x0 x1: lbytes 8) (x2: address) : nat =
  1 + size_nonce + size_nonce + 2 + Seq.length x2

let msg2_has_expected_length (x0 x1: lbytes 8) (x2: address)
    : Lemma (ensures Seq.length (msg2 x0 x1 x2) = msg2_length x0 x1 x2) = ()

let lemma_15_inner (x0 x1: lbytes 8) (x2: address) =
  (* the lengths match *)
  msg2_has_expected_length x0 x1 x2;
  (* slice and append are inverses with the right parameters *)
  SP.append_slices (B.nat_to_bytes_be #I.SEC 2 (Seq.length x2)) x2;
  SP.append_slices x1 (Seq.append (B.nat_to_bytes_be #I.SEC 2 (Seq.length x2)) x2);
  SP.append_slices x0 (Seq.append x1 (Seq.append (B.nat_to_bytes_be #I.SEC 2 (Seq.length x2)) x2));
  SP.append_slices msg2typel
    (Seq.append x0 (Seq.append x1 (Seq.append (B.nat_to_bytes_be #I.SEC 2 (Seq.length x2)) x2)));
  match inv_msg2 (msg2 x0 x1 x2) with
  | Some (y0, y1, y2) ->
    assert (eq_lbytes x0 y0);
    assert (eq_lbytes x1 y1);
    assert (eq_addr x2 y2)
  | None -> ()

#push-options "--z3rlimit 50"
let lemma_16_inner (x: plaintext) =
  match inv_msg2 x with
  | Some (y0, y1, y2) ->
    msg2_has_expected_length y0 y1 y2;
    SP.lemma_split x 1;
    let msgtype, bytes1 = SP.split x 1 in
    SP.lemma_split bytes1 size_nonce;
    let na, bytes2 = SP.split bytes1 size_nonce in
    SP.lemma_split bytes2 size_nonce;
    let nb, bytes3 = SP.split bytes2 size_nonce in
    SP.lemma_split bytes3 2;
    let lenc, addr = SP.split bytes3 2 in
    B.lemma_nat_from_to_bytes_be_preserves_value #I.SEC lenc 2
  | None -> ()
#pop-options

let lemma_17_inner sk pk trust n ct = ()

let lemma_18_inner x = ()

let msg3_has_expected_length (x: lbytes 8) : Lemma (ensures Seq.length (msg3 x) = msg3_length) = ()

let lemma_19_inner n =
  msg3_has_expected_length n;
  SP.append_slices msg3typel n;
  ()

let lemma_20_inner x =
  match inv_msg3 x with
  | Some y ->
    msg3_has_expected_length y;
    SP.lemma_split x 1;
    ()
  | None -> ()

let lemma_21_inner x = ()

let lemma_22_inner x = ()

let msg1_length (x0: lbytes 8) (x1: address) : nat = 1 + size_nonce + 2 + Seq.length x1

let msg1_has_expected_length (x0: lbytes 8) (x1: address)
    : Lemma (ensures Seq.length (msg1 x0 x1) = msg1_length x0 x1) = ()

let lemma_23_inner x0 x1 =
  msg1_has_expected_length x0 x1;
  SP.append_slices (B.nat_to_bytes_be #I.SEC 2 (Seq.length x1)) x1;
  SP.append_slices x0 (Seq.append (B.nat_to_bytes_be #I.SEC 2 (Seq.length x1)) x1);
  SP.append_slices msg1typel
    (Seq.append x0 (Seq.append (B.nat_to_bytes_be #I.SEC 2 (Seq.length x1)) x1))

let lemma_24_inner x =
  match inv_msg1 x with
  | Some (y0, y1) ->
    msg1_has_expected_length y0 y1;
    SP.lemma_split x 1;
    let msgtype, bytes1 = SP.split x 1 in
    SP.lemma_split bytes1 size_nonce;
    let na, bytes2 = SP.split bytes1 size_nonce in
    SP.lemma_split bytes2 2;
    let lenc, addr = SP.split bytes2 2 in
    B.lemma_nat_from_to_bytes_be_preserves_value #I.SEC lenc 2
  | None -> ()

let lemma_25_inner x = ()

let lemma_26_inner x = ()

let lemma_27_inner x0 x1 = ()

let lemma_28_inner x = ()

let lemma_29_inner ct =
  let pk, c = ct in
  let ser = serialize_ciphertext ct in
  SP.lemma_split ser (HPKE.size_dh_public cs);
  SP.append_slices (serialize_pkey pk) c;
  match deserialize_ciphertext ser with
  | Some (pk', c') ->
    assert (eq_pkey pk pk');
    assert (eq_bytes c c')
  | None -> ()

let lemma_30_inner b =
  match deserialize_ciphertext b with
  | Some _ -> SP.lemma_split b (HPKE.size_dh_public cs)
  | None -> ()

let lemma_31_inner sk = ()

let lemma_32_inner b = ()

let lemma_33_inner a = ()

let lemma_34_inner b = ()

let lemma_35_inner b = ()

let lemma_36_inner b = ()

let lemma_37 () = ()

let lemma_38 () = ()

let lemma_39 () = ()

let lemma_40 () = ()

let lemma_41 () = ()

let lemma_42 () = ()

let lemma_43 () = ()

let lemma_44 () = ()

let lemma_45 () = ()

let lemma_46 () = ()

let lemma_47 () = ()

let lemma_48 () = ()

let lemma_49 () = ()

let lemma_50 () = ()

let lemma_51 () =
  let lem51 (a b: msg1res)
      : Lemma (ensures eq_msg1res a b = eq_msg1res b a) [SMTPat (eq_msg1res a b)] =
    match a, b with
    | Some (sk1, pk1, trust1, n1, c1), Some (sk2, pk2, trust2, n2, c2) ->
      assert (eq_skey sk1 sk2 = eq_skey sk2 sk1);
      assert (eq_pkey pk1 pk2 = eq_pkey pk2 pk1);
      lemma_eq_bytes_equal n1 n2;
      assert (eq_ciphertext c1 c2 = eq_ciphertext c2 c1)
    | _, _ -> ()
  in
  assert (forall (a: msg1res) (b: msg1res). (not (eq_msg1res a b)) = (not (eq_msg1res b a)))

