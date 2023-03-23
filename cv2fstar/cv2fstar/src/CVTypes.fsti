module CVTypes

val entropy:Type0

val bytes:Type0
let lbytes (l: Lib.IntTypes.size_nat) = Lib.ByteSequence.lbytes l

(* Random generation *)

val initialize_entropy: Lib.RandomSequence.entropy -> entropy
val finalize_entropy: entropy -> Lib.RandomSequence.entropy
val gen_nat: max: nat{max > 0} -> entropy -> entropy * n: nat{n <= max}
val gen_lbytes: l: Lib.IntTypes.size_nat -> entropy -> entropy * lbytes l
val gen_bool: entropy -> entropy * bool

(* Equality *)

val eq_bytes: bytes -> bytes -> bool
val eq_obytes: option bytes -> option bytes -> bool
val eq_lbytes: #l: Lib.IntTypes.size_nat -> lbytes l -> lbytes l -> bool

(* Lemmas for Equality *)

val lemma_eq_bytes_equal (b1 b2: bytes)
    : Lemma (eq_bytes b1 b2 <==> b1 == b2) [SMTPat (eq_bytes b1 b2)]

val lemma_eq_obytes_equal (b1 b2: option bytes)
    : Lemma (eq_obytes b1 b2 <==> b1 == b2) [SMTPat (eq_obytes b1 b2)]

(* Serialization *)

(* for replication indices *)
val serialize_nat: nat -> bytes
val deserialize_nat: bytes -> option nat

val serialize_lbytes: #l: Lib.IntTypes.size_nat -> lbytes l -> bytes
val deserialize_lbytes: l: Lib.IntTypes.size_nat -> bytes -> option (lbytes l)

val serialize_obytes: option bytes -> bytes
val deserialize_obytes: bytes -> option (option bytes)

val serialize_bool: bool -> bytes
val deserialize_bool: bytes -> option (bool)

(* Lemmas for (de)serialization *)

val lemma_deser_nat_inner (a: nat)
    : Lemma
      (match deserialize_nat (serialize_nat a) with
        | Some b -> a = b
        | None -> False) [SMTPat (deserialize_nat (serialize_nat a))]

let lemma_deser_nat ()
    : Lemma
    (forall (a: nat).
        match deserialize_nat (serialize_nat a) with
        | Some b -> a = b
        | None -> False) = ()

val lemma_serde_nat_inner (a: bytes)
    : Lemma
      (match deserialize_nat a with
        | Some b -> eq_bytes (serialize_nat b) a
        | None -> ~(exists (b: nat). eq_bytes (serialize_nat b) a)) [SMTPat (deserialize_nat a)]

let lemma_serde_nat ()
    : Lemma
    (forall (a: bytes).
        match deserialize_nat a with
        | Some b -> eq_bytes (serialize_nat b) a
        | None -> ~(exists (b: nat). eq_bytes (serialize_nat b) a)) = ()

val lemma_deser_lbytes_inner (#l: Lib.IntTypes.size_nat) (a: lbytes l)
    : Lemma
      (match deserialize_lbytes l (serialize_lbytes a) with
        | Some b -> eq_lbytes a b
        | None -> False) [SMTPat (deserialize_lbytes l (serialize_lbytes a))]

let lemma_deser_lbytes ()
    : Lemma
    (forall (#l: Lib.IntTypes.size_nat) (a: lbytes l).
        match deserialize_lbytes l (serialize_lbytes a) with
        | Some b -> eq_lbytes a b
        | None -> False) = ()

val lemma_serde_lbytes_inner (#l: Lib.IntTypes.size_nat) (a: bytes)
    : Lemma
      (match deserialize_lbytes l a with
        | Some b -> eq_bytes (serialize_lbytes b) a
        | None -> ~(exists (b: lbytes l). eq_bytes (serialize_lbytes b) a))
      [SMTPat (deserialize_lbytes l a)]

let lemma_serde_lbytes ()
    : Lemma
    (forall (#l: Lib.IntTypes.size_nat) (a: bytes).
        match deserialize_lbytes l a with
        | Some b -> eq_bytes (serialize_lbytes b) a
        | None -> ~(exists (b: lbytes l). eq_bytes (serialize_lbytes b) a)) = ()

val lemma_deser_obytes_inner (a: option bytes)
    : Lemma
      (match deserialize_obytes (serialize_obytes a) with
        | Some b -> eq_obytes a b
        | None -> False) [SMTPat (deserialize_obytes (serialize_obytes a))]

let lemma_deser_obytes ()
    : Lemma
    (forall (a: option bytes).
        match deserialize_obytes (serialize_obytes a) with
        | Some b -> eq_obytes a b
        | None -> False) = ()

val lemma_serde_obytes_inner (a: bytes)
    : Lemma
      (match deserialize_obytes a with
        | Some b -> eq_bytes (serialize_obytes b) a
        | None -> ~(exists (b: option bytes). eq_bytes (serialize_obytes b) a))
      [SMTPat (deserialize_obytes a)]

let lemma_serde_obytes ()
    : Lemma
    (forall (a: bytes).
        match deserialize_obytes a with
        | Some b -> eq_bytes (serialize_obytes b) a
        | None -> ~(exists (b: option bytes). eq_bytes (serialize_obytes b) a)) = ()

val lemma_deser_bool_inner (a: bool)
    : Lemma
      (match deserialize_bool (serialize_bool a) with
        | Some b -> a = b
        | None -> False) [SMTPat (deserialize_bool (serialize_bool a))]

let lemma_deser_bool ()
    : Lemma
    (forall (a: bool).
        match deserialize_bool (serialize_bool a) with
        | Some b -> a = b
        | None -> False) = ()

val lemma_serde_bool_inner (a: bytes)
    : Lemma
      (match deserialize_bool a with
        | Some b -> eq_bytes (serialize_bool b) a
        | None -> ~(exists (b: bool). eq_bytes (serialize_bool b) a)) [SMTPat (deserialize_bool a)]

let lemma_serde_bool ()
    : Lemma
    (forall (a: bytes).
        match deserialize_bool a with
        | Some b -> eq_bytes (serialize_bool b) a
        | None -> ~(exists (b: bool). eq_bytes (serialize_bool b) a)) = ()

(* Printing *)

val bool_to_str: bool -> string

val print_bytes: bytes -> FStar.All.ML unit
val print_nat: nat -> FStar.All.ML unit
val print_bool: bool -> FStar.All.ML unit

(* label, value, boolean indicating if separator should be printed *)
val print_label_bytes: string -> bytes -> bool -> FStar.All.ML unit
val print_label_nat: string -> nat -> bool -> FStar.All.ML unit
val print_label_bool: string -> bool -> bool -> FStar.All.ML unit

