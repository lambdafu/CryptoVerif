open Types

type trans_res =
    CSuccess of state
  | CFailure of (equiv_nm * binder list * instruct list) list

val execute_any_crypto : Ptree.ident list list option -> state -> trans_res
