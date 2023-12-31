(* Exception Bad_call is raised when one tries to call several times
   an oracle that can be called only once, or one calls an oracle
   with data that are not of the right types. *)
exception Bad_call

(* Exception Match_fail is raised when a pattern-matching fails
   or one executes "yield" (channel front-end) / "end" 
   (oracles front-end) *)
exception Match_fail

(* Exception Abort is raised when executing "abort".
   The system should stop whole the protocol *) 
exception Abort

(* Exception Bad_file is raised when reading/writing a file leads to an
   error. The argument is the name of the file. *)
exception Bad_file of string

(* Reading from and writing to a file *)

val input_string_from_file : string -> string
val output_string_to_file : string -> string -> unit

(* [exc_bad_file fname f v] calls [f v]; if it raises [Match_fail], 
   raises [Bad_file fname] instead. This function is useful because
   when deserialization fails, it raises [Match_fail]. When we use
   deserialization for reading a file, we want to raise [Bad_file]
   instead. *)

val exc_bad_file : string -> ('a -> 'b) -> 'a -> 'b

(* Random number generation. *)

val rng : unit -> Cryptokit.Random.rng

val rand_string : int -> unit -> string
val rand_bool : unit -> bool
(* [rand_list l] returns a random element of [l].
   It is used for implementing "get": when several elements satisfy
   the desired condition, one of them is chosen randomly. *)
val rand_list : 'a list -> 'a

(* [char4_of_int s pos val] writes the integer [val] at position
   [pos] in the string [s]. The integer takes 4 bytes. 
   [int_of_char4 s pos] reads the integer at position [pos]
   in the string [s]. *)
val char4_of_int : bytes -> int -> int -> unit
val int_of_char4 : string -> int -> int

(* [compos] concatenates bitstrings, with length indications,
   so that the initial bitstrings can be recovered. 
   [decompos] recovers the initial bitstrings. 
   These functions are used for building and breaking tuples. 
   When [decompos] fails, raises [Match_fail] *)

val compos : string list -> string
val decompos : string -> string list

(* Read from and write to a table
   [get_from_table], [get_one_from_table] and [exists_in_table] 
   are used for implementing "get"
   ([get_one_from_table] implements get[unique].
   [exists_in_table] optimizes the case in which "get" is used only to
   test for the existence of an element in the table satisfying certain
   conditions)
   [insert_in_table] is used for implementing "insert"

   [get_from_table file filter] reads the table in file [file]
   and returns the image of entries by [filter]. Entries
   [e] such that [filter e] raises [Match_fail] are removed.

   [get_one_from_table file filter] reads the table in file [file]
   and returns [Some] of the image by [filter] of the first entry for which [filter]
   does not raise [Match_fail]. If [filter] raises [Match_fail]
   for all entries, it returns [None].

   [exists_in_table file filter] reads the table in file [file]
   and returns true if there exists an entry in the table for which
   [filter] does not raise [Match_fail] *)

val get_from_table : string -> (string list -> 'a) -> 'a list
val get_one_from_table : string -> (string list -> 'a) -> 'a option
val exists_in_table : string -> (string list -> 'a) -> bool
val insert_in_table : string -> string list -> unit

(* Predicates, to test whether a value belongs to a type.
   * [always_true] is always true; this predicate can be used
   for types such that the Caml representation always 
   corresponds to a valid CryptoVerif value 
   * [sizep n] is true for strings of [n] bits ([n] multiple of 8).
   It is used for fixed-length types. *)

val always_true : 'a -> bool
val sizep : int -> string -> bool

(* Function if_fun *)

val if_fun : bool -> 'a -> 'a -> 'a
    
(* Serialization and deserialization functions for the default types:
   bitstring, bool, bitstrings having a fixed size, bitstringbot
   When deserialization fails, raises Match_fail *)

val id : 'a -> 'a
val bool_from : string -> bool
val bool_to : bool -> string
val size_from : int -> string -> string
val stringbot_from : string -> string option
val stringbot_to : string option -> string



(* Utilities *)

(* [ceildiv] is the function that returns the lowest integer that is
   greater or equal to [n]/[d]. [n] and [d] must be positive or equal
   to zero *)
val ceildiv : int -> int -> int

(* [i2osp] is the function that returns the representation of the number 
   [x] in a string of size [l]. *)
val i2osp : int -> int -> string
val osp2i : string -> int -> int -> int
