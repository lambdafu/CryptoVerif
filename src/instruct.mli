open Types

type trans_res =
    CSuccess of state
  | CFailure of (equiv_nm * crypto_transf_user_info * instruct list) list

val execute_any_crypto : Ptree.ident list list option -> state -> trans_res
