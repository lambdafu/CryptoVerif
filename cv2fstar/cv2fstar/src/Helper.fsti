module Helper

module B = Lib.ByteSequence
module List = FStar.List.Tot
module Seq = Lib.Sequence
open Lib.IntTypes


val compos: list B.bytes -> b: B.bytes{Seq.length b <= maxint U32}

let length_restr (b: B.bytes) = Seq.length b <= maxint U32

val decompos: B.bytes -> option (l: list B.bytes {List.for_all length_restr l})

