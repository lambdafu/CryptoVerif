open Types

(*** [improved_def_process event_accu compatible_needed p]
     Improved version of [Terms.build_def_process] that infers facts from 
     variables being defined at a program point, variables being simultaneously
     defined, and elsefind facts.
     Reverts to [Terms.build_def_process] when [Settings.improved_fact_collection = false].
     When [compatible_needed] is true, always initializes the [incompatible] field.
 ***)
val improved_def_process : (term * program_point) list ref option -> bool -> inputprocess -> unit

val empty_improved_def_process : bool -> inputprocess -> unit
