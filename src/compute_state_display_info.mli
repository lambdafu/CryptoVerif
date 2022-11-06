open Types

(* [update_full_proof state] updates the proved status of queries inside
   [state]: it transfers proved queries from one game to the previous
   game. *)
val update_full_proof : state -> unit

val compute_state_display_info : state -> state_display_info
