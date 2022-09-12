open Types

(* [check_secrecy g collector b pub_vars one_session] shows that [b] is secret or
   one-session secret in game [g] with public variables [pub_vars].
   It returns [(one_session_res, multi_session_opt)] where
   [one_session_res] is the result for one-session secrecy and
   [multi_session_opt] is
     [None] when [one_session = true] and
     [Some multi_session_res] when [one_session = false], where
     [multi_session_res] is the result for secrecy.
   [one_session_res] and [multi_session_res] are pairs [(result, proba)]
   where [result = true] when the property holds up to probability [proba],
   and [result = false] when the property is not proved.
*)
val check_secrecy : game -> known_when_adv_wins ref option ->
  binder -> binder list -> bool -> (bool * setf list) * (bool * setf list) option
