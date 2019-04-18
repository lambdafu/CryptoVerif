open Types

(* [check_corresp event_accu corresp g] returns true when the
   correspondence [corresp] is proved (up to negligible probability).
   It is called from success.ml. [g] is the full game. In addition to the
   boolean result, when it is true, it also returns the probability of
   collisions eliminated to reach that result. *)
val check_corresp : 
     (* TO DO 'a *) 'a list ref option -> (term * program_point) list -> 
    (bool * term) list * qterm * binder list -> game -> bool * setf list

