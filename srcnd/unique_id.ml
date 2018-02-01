type t = int

let count = ref 0

let get() =
  incr count;
  !count

