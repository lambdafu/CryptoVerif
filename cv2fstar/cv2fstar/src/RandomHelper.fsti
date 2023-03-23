module RandomHelper

val entropy:Type0

val initialize_entropy: Lib.RandomSequence.entropy -> entropy
val finalize_entropy: entropy -> Lib.RandomSequence.entropy

val gen_nat: accuracy: nat -> max: nat{max > 0} -> entropy -> entropy * n: nat{n <= max}

val gen_lbytes: len: Lib.IntTypes.size_nat -> entropy -> entropy * Lib.ByteSequence.lbytes len

val gen_bool: entropy -> entropy * bool
