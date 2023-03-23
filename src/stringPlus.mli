(* String helper functions *)

(* [starts_with s sub] is true when the string [s] starts with
   [sub]. *)
val starts_with : string -> string -> bool

(* [ends_with s sub] is true when the string [s] ends with
   [sub]. *)
val ends_with : string -> string -> bool

(* [contains s sub] is true when [s] contains [sub] *)
val contains : string -> string -> bool

(* [pos s sub] returns [Some n'] when [s] contains [sub] at 
   position [n'], and [None] when [s] does not contain [sub]. *)
val pos : string -> string -> int option

(* [case_insensitive_ends_with s sub] is true when the string [s] ends with
   [sub]. Comparison is case insensitive. *)
val case_insensitive_ends_with : string -> string -> bool

(* [case_insensitive_contains s sub] is true when [s] contains [sub]. 
   Comparison is case insensitive. *)
val case_insensitive_contains : string -> string -> bool

(* [alphabetize_string] converts any string into a string that contains
   only alphanumeric characters (A..Z,a..z,0..9) and underscore.
   This function is injective. This is required to avoid clashes
   between OCaml/F* identifiers generated from CryptoVerif identifiers. *)
val alphabetize_string : string -> string
