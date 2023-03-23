
type pkey
type skey

(* Tags *)

val tag_disconnect                : char
val tag_ignore                    : char
val tag_unimplemented             : char
val tag_debug                     : char
val tag_service_request           : char
val tag_service_accept            : char
val tag_kex_init                  : char
val tag_newkeys                   : char
val tag_kexdh_init                : char
val tag_kexdh_reply               : char
val tag_userauth_request          : char
val tag_userauth_failure          : char
val tag_userauth_success          : char
val tag_userauth_banner           : char
val tag_userauth_pk_ok            : char
val tag_global_request            : char
val tag_request_success           : char
val tag_request_failure           : char
val tag_channel_open              : char
val tag_channel_open_confirmation : char
val tag_channel_open_failure      : char
val tag_channel_window_adjust     : char
val tag_channel_data              : char
val tag_channel_extended_data     : char
val tag_channel_eof               : char
val tag_channel_close             : char
val tag_channel_request           : char
val tag_channel_success           : char
val tag_channel_failure           : char



(* Functions to get public and private ssh-rsa keys*)
val pkey_to : pkey -> string
val skey_to : skey -> string
val pkey_from : string -> pkey
val skey_from : string -> skey
val pkey_to_file : pkey -> string
val pkey_from_file : string -> pkey

val kgen : ?e:int -> int -> unit -> (pkey * skey)

(* Function to create a packet from a payload *)
val ssh_pad : int (* block size *) -> string -> string
val ssh_unpad : string -> string option

(*concatenates tag and payload for the tag*)
val concatm : char -> string -> string
val unconcatm : string -> char * string

(* utilities *)
val ssh_string : string -> string
val strings_of_ssh_string_ind : string -> int -> int -> string list 
val signature_from_ind : string -> int -> string
val skey_to_pkey : skey -> pkey

(*concatenates the values for the negotiation*)
val negotiation_string : string
val concatn : string -> string -> string
val unconcatn : string -> (string * string)
val check_algorithms : string -> bool

(*concatenates both parts of a message *)
val concatmsm : string -> string -> string

(* hash function : sha1 *)
val hash : unit -> string -> string

val g_of_mpint : string -> string
val mpint_of_g : string -> string

val signature_to : string -> string
val signature_from : string -> string

(* concatenation for KEXDH_REPLY (pk,g,sig) *)
val concat3 : pkey -> string -> string -> string
val unconcat3 : string -> (pkey * string * string)

(* concatenation to get the value to hash to get the shared hash *)
val concat8 : string -> string -> string -> string -> pkey -> string ->  string -> string -> string


val sign : string -> skey -> string
val check : string -> pkey -> string -> bool

(* creation of IV, symmetric keys, mac keys from shared secrets *)
val construct : int -> string -> unit -> string -> string -> string -> string

(* symmetric encryption/decryption, with IV *)
val symenc : string -> string -> string -> string
val symdec : string -> string -> string -> string option

val mac : string -> string -> string
val check_mac : string -> string -> string -> bool

(* concatenation of the message number and the payload *)
val concatnm : int -> string -> string

(* get the size of the packet from the first block *)
val get_size : string -> int

(* concatenation of the encrypted message and the MAC *)
val concatem : string -> string -> string

(* ssh-userauth string *)
val ssh_userauth : string
(* ssh-connection string *)
val ssh_connection : string
