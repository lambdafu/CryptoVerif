open Types

(* Encodes query secret .. [reachability] as a correspondence query *)
val encode_queries : query list -> inputprocess -> query list * inputprocess
