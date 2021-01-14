open Types

val build_def_process : (term * program_point) list ref option -> inputprocess -> unit
val build_def_member : eqmember -> unit
    
val empty_def_process : inputprocess -> unit
val empty_def_member : eqmember -> unit
