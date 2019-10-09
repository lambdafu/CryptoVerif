open Types

val check_def_process_main : inputprocess -> unit
val check_def_eqstatement : equiv -> unit

(* [check_equiv normalize equiv] checks the equivalence [equiv] and 
   computes the mapping between random numbers.
   When [normalize] is true, introduces lets for arguments in the RHS
   and adds replications when they are not present at the root. *)
val check_equiv : bool -> equiv -> equiv_nm
