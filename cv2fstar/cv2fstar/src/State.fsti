module State

open CVTypes

val table (#tns: eqtype) (te: (tns -> Type0)) (tn: tns) : Type0

val table_empty (#tns: eqtype) (te: (tns -> Type0)) (tn: tns) : table #tns te tn

noeq
type table_type =
  (* table names *)
  (* table entries *)
  (* record *)
  (* init *)
  (* return table *)
  (* update tables *)
  | TableType :
      tns: eqtype ->
      te: (tns -> Type0) ->
      r: Type0 ->
      init: r ->
      rt: (r -> tn: tns -> table te tn) ->
      ut: (r -> tn: tns -> table te tn -> r)
    -> table_type

let table_name (tt: table_type) = match tt with | TableType tns _ _ _ _ _ -> tns

let table_entry (#tt: table_type) (tn: table_name tt) =
  match tt with | TableType _ te _ _ _ _ -> te tn

noeq
type session_type =
  (* oracle name *)
  (* session state entry *)
  (* following_oracles *)
  (* session_entry_to_name *)
  | SessionType : on: eqtype -> se: Type0 -> fo: (on -> list on) -> se2on: (se -> on)
    -> session_type

let oracle_name (st: session_type) = match st with | SessionType on _ _ _ -> on

let session_entry (st: session_type) = match st with | SessionType _ se _ _ -> se

let is_valid_entry (#st: session_type) (on: oracle_name st) (se: session_entry st) =
  match st with | SessionType _ _ _ se2on -> (se2on se = on)

let is_valid_next_entry (#st: session_type) (on: oracle_name st) (se: session_entry st) =
  match st with
  | SessionType _ _ fo se2on ->
    let nsn = se2on se in
    FStar.List.Tot.Base.mem nsn (fo on)

let session_entry_to_name (#st: session_type) (se: session_entry st) : oracle_name st =
  match st with | SessionType _ _ _ se2on -> se2on se


val sessions (st: session_type) : Type0

// each protocol instantiates this type and uses it with state
noeq
type state_type =
  | StateType : tt: table_type -> st: session_type -> event_type: Type0 -> state_type

let tt_of (stt: state_type) : table_type = match stt with | StateType tt _ _ -> tt

let st_of (stt: state_type) : session_type = match stt with | StateType _ st _ -> st

let et_of (stt: state_type) = match stt with | StateType _ _ et -> et

val state (stt: state_type) : Type0

(**
 * There are a couple of predicates related to sessions that we did not describe
 * in the thesis manuscript because they are ongoing work. We mention in the
 * section on future work that we would like to prove that oracle functions
 * add correct session entries. These predicates are a step in this direction.
**)
val is_existing_sess_id: #stt: state_type -> state stt -> id: nat -> bool

val is_matching_sess_id_entry
      (#stt: state_type)
      (st: state stt)
      (on: oracle_name (st_of stt))
      (id: nat)
    : Pure (bool)
      (requires True)
      (ensures
        fun b ->
          match b with
          | false -> True
          | true -> is_existing_sess_id st id)

let same_sessions (#stt: state_type) (st0 st1: state stt) =
  (forall (id: nat) (on: oracle_name (st_of stt)).
      is_matching_sess_id_entry st0 on id ==> is_matching_sess_id_entry st1 on id)

val call_with_entropy: #stt: state_type -> #a: Type -> st0: state stt -> (entropy -> entropy * a)
  -> Pure (state stt * a) (requires True) (ensures fun (st1, _) -> same_sessions st0 st1)


type table_filter_type =
  | TableFilterSimple
  | TableFilterFull

let table_filter
      (#stt: state_type)
      (tft: table_filter_type)
      (rt: Type0)
      (tn: table_name (tt_of stt))
     =
  match tft with
  | TableFilterSimple -> (table_entry #(tt_of stt) tn -> option rt)
  | TableFilterFull ->
    (* we could also formalize (as a lemma), that a filter function cannot add events (although that is supposed to be ensured by CryptoVerif already) *)
    (st0: state stt -> table_entry #(tt_of stt) tn
        -> st1: state stt {same_sessions st0 st1} * option rt)

val insert:
    #stt: state_type ->
    st0: state stt ->
    tn: table_name (tt_of stt) ->
    table_entry #(tt_of stt) tn
  -> Pure (state stt) (requires True) (ensures fun st1 -> same_sessions st0 st1)

val get:
    #stt: state_type ->
    #tft: table_filter_type ->
    #rt: Type0 ->
    st0: state stt ->
    tn: table_name (tt_of stt) ->
    table_filter #stt tft rt tn
  -> Pure (state stt * option rt) (requires True) (ensures fun (st1, _) -> same_sessions st0 st1)

val get_unique_full:
    #stt: state_type ->
    #rt: Type0 ->
    st0: state stt ->
    tn: table_name (tt_of stt) ->
    table_filter #stt TableFilterFull rt tn
  -> Pure (state stt * option rt) (requires True) (ensures fun (st1, _) -> same_sessions st0 st1)

(* get[unique] with a simple filter does not use randomness and thus does not need entropy. *)
val get_unique:
    #stt: state_type ->
    #rt: Type0 ->
    st0: state stt ->
    tn: table_name (tt_of stt) ->
    table_filter #stt TableFilterSimple rt tn
  -> option rt

(* if on the CV side we do not use the entry but only its existence *)
val entry_exists_full:
    #stt: state_type ->
    #rt: Type0 ->
    st0: state stt ->
    tn: table_name (tt_of stt) ->
    table_filter #stt TableFilterFull rt tn
  -> Pure (state stt * bool) (requires True) (ensures fun (st1, _) -> same_sessions st0 st1)

val entry_exists:
    #stt: state_type ->
    #rt: Type0 ->
    state stt ->
    tn: table_name (tt_of stt) ->
    table_filter #stt TableFilterSimple rt tn
  -> bool

val print_table:
    #stt: state_type ->
    state stt ->
    tn: table_name (tt_of stt) ->
    tns: string ->
    (table_entry tn -> FStar.All.ML unit)
  -> FStar.All.ML unit


val print_session
      (#stt: state_type)
      (st: state stt)
      (pe: (session_entry (st_of stt) -> FStar.All.ML unit))
      (id: nat)
    : FStar.All.ML unit

val print_events (#stt: state_type) (st: state stt) (pe: (et_of (stt) -> FStar.All.ML unit))
    : FStar.All.ML unit


val init_state: stt: state_type -> Lib.RandomSequence.entropy -> state stt
val finalize_state: #stt: state_type -> state stt -> Lib.RandomSequence.entropy

val get_session_entry (#stt: state_type) (st: state stt) (on: oracle_name (st_of stt)) (id: nat)
    : Tot (option (s: (session_entry (st_of stt)){is_valid_entry on s}))

val get_and_remove_session_entry
      (#stt: state_type)
      (st: state stt)
      (on: oracle_name (st_of stt))
      (id: nat)
    : Tot (state stt * option (s: (session_entry (st_of stt)){is_valid_entry on s}))

// Adds a new session with a list of session states
val state_reserve_session_id (#stt: state_type) (st0: state stt) : Tot (state stt * nat)

val state_add_to_session
      (#stt: state_type)
      (st0: state stt)
      (id: nat)
      (ses: list (session_entry (st_of stt)))
    : Tot (state stt)


val state_add_event (#stt: state_type) (st: state stt) (ev: et_of stt) : Tot (state stt)

(* three more predicates on our way to more guarantees on session entries *)
let sessions_of_other_modules_unchanged (#stt: state_type) (st0 st1: state stt) =
  (forall (id: nat) (on: oracle_name (st_of stt)).
      is_matching_sess_id_entry st0 on id ==> is_matching_sess_id_entry st1 on id)

let sessions_other_of_module_unchanged (#stt: state_type) (st0 st1: state stt) (id: nat) =
  (forall (other_id: nat{other_id <> id}) (on: oracle_name (st_of stt)).
      is_matching_sess_id_entry st0 on other_id ==> is_matching_sess_id_entry st1 on other_id)

let sessions_unaffected (#stt: state_type) (st0 st1: state stt) (id: nat) =
  sessions_of_other_modules_unchanged st0 st1 /\ sessions_other_of_module_unchanged st0 st1 id

