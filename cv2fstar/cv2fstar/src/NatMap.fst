module NatMap

module Map = FStar.Map

type t value = nat * Map.t nat value

let next_id (#value: Type) (m: t value) = match m with | nid, m -> nid
let map (#value: Type) (m: t value) = match m with | nid, m -> m

let sel t n = Map.sel (map t) n

let upd t n v = next_id t, Map.upd (map t) n v

let empty v =
  let m = Map.const v in
  0, Map.restrict Set.empty m

let domain t = Map.domain (map t)

let contains t id = Map.contains (map t) id

let reserve t = match t with | nid, m -> nid, ((nid + 1), m)

let add t v = match t with | nid, m -> nid, ((nid + 1), Map.upd m nid v)

let remove t id =
  match t with
  | nid, m ->
    let new_dom = Set.complement #nat (Set.singleton #nat id) in
    nid, Map.restrict #nat new_dom m

let get m id = match m with | nid, m -> if Map.contains m id then Some (Map.sel m id) else None

