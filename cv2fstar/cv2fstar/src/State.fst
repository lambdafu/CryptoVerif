module State

open CVTypes

module Map = NatMap
module Set = FStar.Set

// Abbreviations:
// tt: table type
// tn: table name
// tns: table names
// te: table entry

let table #tns te tn = Seq.seq (te tn)
let table_empty #tns te tn = Seq.empty

let table' (#tt: table_type) (tn: table_name tt) = table #(table_name tt) (table_entry #tt) tn

let tables tt = match tt with | TableType _ _ r _ _ _ -> r

val init_tables (tt: table_type) : tables tt
let init_tables tt = match tt with | TableType _ _ _ i _ _ -> i


let sessions (st: session_type) = Map.t (list (session_entry st))

val init_sessions (st: session_type) : sessions st
let init_sessions st = Map.empty []

noeq
type state (stt: state_type) =
  | State :
      ent: entropy ->
      tabs: tables (tt_of stt) ->
      s: sessions (st_of stt) ->
      evs: list (et_of stt)
    -> state stt

val entropy_of: #stt: state_type -> state stt -> entropy
let entropy_of st =
  let State ent _ _ _ = st in
  ent

val tables_of: #stt: state_type -> state stt -> tables (tt_of stt)
let tables_of st =
  let State _ tabs _ _ = st in
  tabs

val sessions_of: #stt: state_type -> state stt -> sessions (st_of stt)
let sessions_of st =
  let State _ _ sessions _ = st in
  sessions

val events_of: #stt: state_type -> state stt -> list (et_of stt)
let events_of st =
  let State _ _ _ events = st in
  events

let is_existing_sess_id #stt st id = Map.contains (sessions_of st) id

let is_matching_sess_id_entry #stt st sn id =
  if is_existing_sess_id st id
  then
    (let seo = Map.get (sessions_of st) id in
      match seo with
      | None -> false // being in the true branch of is_existing, we know it is not None
      | Some se -> not (List.Tot.existsb (fun sess -> not (is_valid_entry sn sess)) se))
  else false


val state_upd_entropy (#stt: state_type) (st0: state stt) (e: entropy)
    : Pure (state stt) (requires True) (ensures fun st1 -> same_sessions st0 st1)
let state_upd_entropy st ent =
  let State _ tabs sessions evs = st in
  State ent tabs sessions evs

val state_upd_tables (#stt: state_type) (st0: state stt) (tabs: tables (tt_of stt))
    : Pure (state stt) (requires True) (ensures fun st1 -> same_sessions st0 st1)
let state_upd_tables st tabs =
  let State ent _ sessions evs = st in
  State ent tabs sessions evs

val state_upd_sessions (#stt: state_type) (st0: state stt) (s: sessions (st_of stt)) : state stt
let state_upd_sessions st sessions =
  let State ent tabs _ evs = st in
  State ent tabs sessions evs

val state_upd_events (#stt: state_type) (st: state stt) (evs: list (et_of stt)) : state stt
let state_upd_events st evs =
  let State ent tabs sess _ = st in
  State ent tabs sess evs


let call_with_entropy st0 f =
  let ent0 = entropy_of st0 in
  let ent1, res = f ent0 in
  let st1 = state_upd_entropy st0 ent1 in
  st1, res

let return_table (#stt: state_type) (st: state stt) (tn: table_name (tt_of stt)) : table' tn =
  let tabs = tables_of st in
  match tt_of stt with | TableType _ _ _ _ rt _ -> rt tabs tn

let update_tables
      (#stt: state_type)
      (st: state stt)
      (tn: table_name (tt_of stt))
      (new_tab: table' tn)
    : tables (tt_of stt) =
  let tabs = tables_of st in
  match tt_of stt with | TableType _ _ _ _ _ ut -> ut tabs tn new_tab


let insert #stt st tn te =
  let tab = return_table st tn in
  let new_tab = Seq.snoc tab te in
  let new_tabs = update_tables st tn new_tab in
  state_upd_tables st new_tabs

val get_inner_simple
      (#stt: state_type)
      (#rt: Type0)
      (#tn: table_name (tt_of stt))
      (matches: Seq.seq rt)
      (tab: table' tn)
      (filter: table_filter TableFilterSimple rt tn)
    : Tot (Seq.seq rt) (decreases (Seq.length tab))

let rec get_inner_simple matches tab f =
  if Seq.length tab = 0
  then matches
  else
    match f (Seq.head tab) with
    | Some e -> get_inner_simple (Seq.cons e matches) (Seq.tail tab) f
    | None -> get_inner_simple matches (Seq.tail tab) f

val get_inner_full
      (#stt: state_type)
      (#rt: Type0)
      (#tn: table_name (tt_of stt))
      (st0: state stt)
      (matches: Seq.seq rt)
      (tab: table' tn)
      (filter: table_filter TableFilterFull rt tn)
    : Pure (state stt * Seq.seq rt)
      (decreases (Seq.length tab))
      (requires True)
      (ensures fun (st1, _) -> same_sessions st0 st1)

let rec get_inner_full st matches tab f =
  if Seq.length tab = 0
  then st, matches
  else
    match f st (Seq.head tab) with
    | st, Some e -> get_inner_full st (Seq.cons e matches) (Seq.tail tab) f
    | st, None -> get_inner_full st matches (Seq.tail tab) f

let get #stt #tft st tn f =
  let tab = return_table st tn in
  let st, matches =
    (match tft with
      | TableFilterSimple -> st, get_inner_simple Seq.empty tab f
      | TableFilterFull -> get_inner_full st Seq.empty tab f)
  in
  match Seq.length matches with
  | 0 -> st, None
  | 1 -> st, Some (Seq.head matches)
  | _ ->
    let st, rand_i = call_with_entropy st (gen_nat (Seq.length matches - 1)) in
    st, Some (Seq.index matches rand_i)

val get_unique_inner_simple
      (#stt: state_type)
      (#rt: Type0)
      (#tn: table_name (tt_of stt))
      (tab: table' tn)
      (filter: table_filter TableFilterSimple rt tn)
    : Tot (option rt) (decreases (Seq.length tab))

let rec get_unique_inner_simple tab f =
  if Seq.length tab = 0
  then None
  else
    match f (Seq.head tab) with
    | Some e -> Some e
    | None -> get_unique_inner_simple (Seq.tail tab) f

val get_unique_inner_full
      (#stt: state_type)
      (#rt: Type0)
      (#tn: table_name (tt_of stt))
      (st0: state stt)
      (tab: table' tn)
      (filter: table_filter TableFilterFull rt tn)
    : Pure (state stt * option rt)
      (decreases (Seq.length tab))
      (requires True)
      (ensures fun (st1, _) -> same_sessions st0 st1)

let rec get_unique_inner_full st tab f =
  if Seq.length tab = 0
  then st, None
  else
    match f st (Seq.head tab) with
    | st, Some e -> st, Some e
    | st, None -> get_unique_inner_full st (Seq.tail tab) f

let get_unique_full #stt st tn f =
  let tab = return_table st tn in
  (* CryptoVerif proves that it is not possible to have multiple matches, so we
     can return after finding a first (and thus the only) match. *)
  get_unique_inner_full st tab f

let get_unique #stt st tn f =
  let tab = return_table st tn in
  (* CryptoVerif proves that it is not possible to have multiple matches, so we
     can return after finding a first (and thus the only) match. *)
  get_unique_inner_simple tab f

let entry_exists_full st tn f =
  match get_unique_full st tn f with
  | st, None -> st, false
  | st, Some _ -> st, true

let entry_exists st tn f =
  match get_unique st tn f with
  | None -> false
  | Some _ -> true

let print_table #stt st tn tns print_entry =
  let tab = return_table st tn in
  IO.print_string (tns ^ " [");
  IO.print_newline ();
  List.iter (fun te -> print_entry te) (Lib.Sequence.to_list tab);
  IO.print_string "]";
  IO.print_newline ();
  IO.print_newline ()

(* There is no way to iterate over all keys on which the map is defined,
   so we require the caller to tell us which session id they want. *)
let print_session st print_entry id =
  IO.print_string (string_of_int id);
  IO.print_string ".";
  let seso = Map.get (sessions_of st) id in
  match seso with
  | None
  | Some [] ->
    IO.print_string "session does not exist";
    IO.print_newline ()
  | Some ses -> List.iter (fun se -> print_entry se) ses

let print_events st print_event =
  IO.print_string "Events: [\n";
  let evl = events_of st in
  List.iter (fun e -> print_event e) evl;
  IO.print_string "]"

let init_state stt ent =
  let entropy = initialize_entropy ent in
  let tabs = init_tables (tt_of stt) in
  let sess = init_sessions (st_of stt) in
  let evs = [] in
  State entropy tabs sess evs

let finalize_state state = finalize_entropy (entropy_of state)

let _get_remove_session_entry #stt st sn id rm_flag =
  let seso = Map.get (sessions_of st) id in
  match seso with
  | None -> st, None
  | Some ses ->
    let seo = List.Tot.find (fun se -> is_valid_entry sn se) ses in
    if rm_flag
    then
      // construct a list without the entry
      (let ses_new = List.Tot.filter (fun se -> not (is_valid_entry sn se)) ses in
        (let m = Map.upd (sessions_of st) id ses_new in
          state_upd_sessions #stt st m, seo))
    else (st, seo)

let get_session_entry #stt st sn id =
  let _, seo = _get_remove_session_entry #stt st sn id false in
  seo

let get_and_remove_session_entry #stt st sn id = _get_remove_session_entry #stt st sn id true


let state_reserve_session_id st0 =
  let m = sessions_of st0 in
  let id, m = Map.reserve m in
  state_upd_sessions st0 m, id

let state_add_to_session st id ses =
  let m = sessions_of st in
  match Map.get m id with
  | None ->
    let m = Map.upd m id ses in
    state_upd_sessions st m
  | Some old_ses ->
    let new_ses = List.Tot.append old_ses ses in
    let m = Map.upd m id new_ses in
    state_upd_sessions st m

let state_add_event st ev = state_upd_events st (List.append (events_of st) [ev])

