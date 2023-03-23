module NatMap

module Map = FStar.Map
module S = FStar.Set

(* Map.t key value: The main type provided by this module *)
val t (value: Type u#a) : Type u#a

(* sel m k : Look up key `k` in map `m` *)
val sel: #value: Type -> t value -> nat -> Tot value

(* upd m k v : A map identical to `m` except mapping `k` to `v` *)
val upd: #value: Type -> t value -> nat -> value -> Tot (t value)

(* empty v : A map with empty domain. v is needed as a dummy value. *)
val empty: #value: Type -> value -> Tot (t value)

(* domain m : The set of keys on which this partial map is defined *)
val domain: #value: Type -> t value -> Tot (S.set nat)

(* contains m k: Decides if key `k` is in the map `m` *)
val contains: #value: Type -> t value -> nat -> Tot bool

val reserve: #value: Type -> t value -> Tot (nat * t value)

val add: #value: Type -> t value -> value -> Tot (nat * t value)

val remove: #value: Type -> t value -> nat -> Tot (t value)

val get: #value: Type -> t value -> nat -> Tot (option (value))

