open Types

(* [is_success state] tries to prove queries that still need to be
   proved in [state]. It updates the proofs of the queries inside
   [state] and returns the list of newly proved queries (with the
   associated probability of success of an attack) as well as boolean
   which is true when all queries are proved. *)

val is_success : known_when_adv_wins ref option -> state -> ((query * game) * probaf) list * bool
