open Types

(* [check_corresp event_accu corresp g] returns true when the
   correspondence [corresp] is proved (up to negligible probability).
   It is called from success.ml. [g] is the full game. In addition to the
   boolean result, when it is true, it also returns the probability of
   collisions eliminated to reach that result. *)
val check_corresp : 
    known_when_adv_wins ref option -> (term * program_point) list -> 
    (bool * term) list * qterm * binder list -> game -> bool * setf list

(* [remove_inj event_accu g q] returns
   - [Some(q',proba)] when [q] is an injective correspondence and 
   it managed to prove injectivity; [q'] is the non-injective
   query still proba and [proba] is the probability of breaking injectivity.
   - [None] otherwise. *)
val remove_inj : (term * program_point) list -> game -> query ->
  (query * setf list) option

(* [well_formed q] checks that [q] is well-formed, that is,
   for correspondence queries psi => phi, psi = psi{x'/x} => phi = phi{x'/x}
   where x represents the tuple of variables of psi, and x' is a tuple of fresh
   variables. 
   It displays a warning message when the proof of well-formedness fails. *)
val well_formed : query -> unit
