
val resolve : string -> Unix.inet_addr
val input_packet : in_channel -> string
val output_packet : out_channel -> string -> unit
val chop : string -> string
val input_blocks : in_channel -> int -> string
val input_block : in_channel -> string
val input_mac : in_channel -> string
(* this function takes as input the input and output channel, the closure corresponding to the initialization of the tunnel, and returns two functions, read and write *)
val create_tunnel : (in_channel * out_channel) -> (unit -> ((string * string * int -> unit * string) * (string * string -> (string * string * string * int -> unit * string) * int)) * string * string * string) -> (unit -> string) * (string -> unit) * string
val string_of_char : char -> string

(*message parsing*)
val parse_message_tag : string -> int -> char * int
val parse_int : string -> int -> int * int
val parse_string : string -> int -> string * int
val parse_bool : string -> int -> bool * int

