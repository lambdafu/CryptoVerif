open Types
module StringMap = Map.Make (String)

let alphabetize_string = StringPlus.alphabetize_string

let get_oracle_function_name name = "oracle_" ^ alphabetize_string name

let get_binder_name b =
  "var_" ^ alphabetize_string b.sname ^ "_" ^ string_of_int b.vname

let get_letfun_name f = "fun_" ^ alphabetize_string f.f_name

let get_oracle_name o = "Oracle_" ^ alphabetize_string o

module Binder =
  struct
    type t = binder
    let compare b1 b2 = compare (get_binder_name b1) (get_binder_name b2)
  end

module BinderSet = Set.Make (Binder)

(*informations to the user*)
let info mess = print_string ("Information: " ^ mess ^ " (implementation)\n")

let error mess =
  Parsing_helper.user_error ("Error: " ^ mess ^ " (implementation)\n")

let activate_debug_comments = false

let debug_comment str =
  if activate_debug_comments then " (* " ^ str ^ " *) " else ""

let protocol_name = ref "nsl"
let protocol_name_allcaps = ref "NSL"

let set_protocol_name filename = 
  let suffix = 
    try 
      List.find (fun suffix -> StringPlus.case_insensitive_ends_with filename suffix) [".pcv"; ".cv"; ".ocv" ]
    with Not_found -> 
      "" 
  in
  let basename = String.sub filename 0 (String.length filename - String.length suffix) in
  let alph_basename = alphabetize_string basename in
  protocol_name := String.lowercase_ascii alph_basename;
  protocol_name_allcaps := String.uppercase_ascii alph_basename

let letfun_module = "Letfun"

let letfun_prefix = ref ""

let string_list_sep = String.concat

let list_args l =
  if l = [] then
    "()"
  else
    String.concat " " l

let state_type () = !protocol_name ^ "_state"

let state_variable = "state"

let state_declaration () = state_variable ^ ":" ^ (state_type ())

let table_entry_type = ref "table_entry"

let table_entry_exists = "entry_exists"
let table_entry_exists_full = "entry_exists_full"

let table_get = "get"

let table_get_unique = "get_unique"
let table_get_unique_full = "get_unique_full"

let table_insert = "insert"

let call_with_entropy = "call_with_entropy"

let session_id_variable = "sid"

let in_parens str = "(" ^ str ^ ")"

let in_parens_if_needed code_str =
  let trimmed = String.trim code_str in
  (* We do not produce \r, nor form feed characters, nor other whitespace, so these should suffice: *)
  if String.contains trimmed '\n' || String.contains trimmed ' ' || String.contains trimmed '\t' then
    in_parens code_str
  else code_str

let is_complicated code_str =
  let trimmed = String.trim code_str in
  String.contains trimmed '\n' || String.length trimmed > 15

(* Add ind in front of every line *)
let code_block_add_line_prefix code_str ind =
  ind ^ String.concat ("\n" ^ ind) (String.split_on_char '\n' code_str)

let code_block code ind print_right_separator =
  (* We reuse code_str to make sure to evaluate `code` only once. *)
  let code_str = code "" in
  if is_complicated code_str then
    "\n" ^
    ind ^ "  begin\n" ^
    (code_block_add_line_prefix code_str (ind ^ "    ")) ^ "\n" ^
    ind ^ "  end" ^
    if print_right_separator then "\n" ^ ind else ""
  else
    " " ^ String.trim code_str ^
    if print_right_separator then " " else ""

let term_needs_entropy t =
  match t.t_desc with
  | FunApp(f, _) -> f.f_impl_ent
  | _ -> false

(* returns set of free and set of bound variables
  get_iprocess_bv returns the set of variables bound not under a replication
  The set of variables bound under a replication is stored in
  bound_vars_under_repl.
  The set of variables bound inside a term is stored in bound_vars_terms.
  The set of free variables is stored in free_vars.
*)

let empty_bv = BinderSet.empty

let bound_bv = BinderSet.singleton

let add_bv = BinderSet.union

let add_list_bv f l = List.fold_left (fun x y -> add_bv x (f y)) empty_bv l

let get_binderref_binder ext (b, l) =
  if Terms.is_args_at_creation b l then b
  else
    Parsing_helper.input_error
      "There should not be any find variable (implementation)" ext

let free_vars = ref BinderSet.empty

(* Contains all free variables; may contain some variables that are also bound *)

let bound_vars_under_repl = ref BinderSet.empty

let bound_vars_terms = ref BinderSet.empty


type oracle_def =
| Top of inputprocess
  (* nb_of_return, free variables, input process *)
| NonTop of (int * binder list * inputprocess) list

type oracle_data = {
  oracle_name: string;
  under_repl: bool;
  previous_oracle: string option;
  input_type: typet list;
  mutable output_type: typet list option;
  mutable following_oracles: string list option;
  mutable list_of_returns: (int * (string * binder list) list * process) list;
  mutable list_of_defs: oracle_def;
  mutable seen_returns: int
}

let oracle_only_yields od =
  match od.output_type with
  (* this is if all branches yield *)
  | None -> true
  (* this is if at least one other branch returns/has an output *)
  | Some _ -> false

let oracles = ref (StringMap.empty:oracle_data StringMap.t)

let tables = ref []

let events = ref []

let built_in_types = [Settings.t_bitstring; Settings.t_bitstringbot;
                      Settings.t_bool; Settings.t_unit; Settings.t_interv]

let types = ref []
let eq_types = ref []
let serde_types = ref []
let random_types = ref []

let built_in_constants = [Settings.c_true; Settings.c_false]
let built_in_functions = [Settings.f_and; Settings.f_or; Settings.f_not;
  Settings.f_plus; Settings.f_mul; Settings.f_comp Equal Settings.t_bool Settings.t_bool;
  Settings.f_comp Diff Settings.t_bool Settings.t_bool;
  Settings.f_comp Equal Settings.t_bitstring Settings.t_bitstring;
  Settings.f_comp Diff Settings.t_bitstring Settings.t_bitstring;
  Settings.f_comp Equal Settings.t_bitstringbot Settings.t_bitstringbot;
  Settings.f_comp Diff Settings.t_bitstringbot Settings.t_bitstringbot]
let functions = ref []
let inv_functions = ref []

let add_bv_term bs = bound_vars_terms := BinderSet.union bs !bound_vars_terms

let free_var b =
  free_vars := BinderSet.add b !free_vars;
  BinderSet.empty

let rec get_pattern_bv = function
  | PatVar b -> bound_bv b
  | PatTuple (fs, pl) -> add_list_bv get_pattern_bv pl
  | PatEqual t ->
      add_bv_term (get_term_bv t);
      empty_bv

and get_iprocess_bv p =
  match p.i_desc with
  | Nil -> empty_bv
  | Input ((c, tl), pat, p) -> add_bv (get_pattern_bv pat) (get_oprocess_bv p)
  | Par (p1, p2) -> add_bv (get_iprocess_bv p1) (get_iprocess_bv p2)
  | Repl (b, p1) ->
      let bv = get_iprocess_bv p1 in
      bound_vars_under_repl := BinderSet.union !bound_vars_under_repl bv;
      empty_bv

and get_term_bv t =
  match t.t_desc with
  | Var (b, tl) -> free_var (get_binderref_binder t.t_loc (b, tl))
  | FunApp (fs, tl) -> add_list_bv get_term_bv tl
  | TestE (t1, t2, t3) ->
      add_bv (add_bv (get_term_bv t1) (get_term_bv t2)) (get_term_bv t3)
  | LetE (pat, t1, t2, t3) ->
      add_bv (get_pattern_bv pat)
        (add_bv (get_term_bv t1)
           (add_bv (get_term_bv t2)
              (match t3 with None -> empty_bv | Some t -> get_term_bv t)))
  | ResE (b, t) -> add_bv (bound_bv b) (get_term_bv t)
  | ReplIndex _ -> empty_bv
      (* Replication indices may occur in events and variables *)
  | EventAbortE _ -> empty_bv
  | EventE (t, p) -> add_bv (get_term_bv t) (get_term_bv p)
  | FindE _ ->
      Parsing_helper.input_error "Find not supported (implementation)" t.t_loc
  | GetE (tbl, patl, topt, p1, p2, _) ->
      List.fold_right add_bv
        (List.map get_pattern_bv patl)
        (add_bv
           (match topt with Some t -> get_term_bv t | None -> empty_bv)
           (add_bv (get_term_bv p1) (get_term_bv p2)))
  | InsertE (tbl, tl, p) ->
      List.fold_right add_bv (List.map get_term_bv tl) (get_term_bv p)

and get_oprocess_bv p =
  match p.p_desc with
  | Yield | EventAbort _ -> empty_bv
  | Restr (b, p) -> add_bv (bound_bv b) (get_oprocess_bv p)
  | Test (t, p1, p2) ->
      add_bv_term (get_term_bv t);
      add_bv (get_oprocess_bv p1) (get_oprocess_bv p2)
  | Output ((c, tl), t, p) ->
      add_bv_term (get_term_bv t);
      get_iprocess_bv p
  | Let (pat, t, p1, p2) ->
      add_bv_term (get_term_bv t);
      add_bv (get_pattern_bv pat)
        (add_bv (get_oprocess_bv p1) (get_oprocess_bv p2))
  | EventP (t, p) ->
      add_bv_term (get_term_bv t);
      get_oprocess_bv p
  | Find (fl, ep, _) -> error "Find not supported"
  | Get (tbl, patl, topt, p1, p2, _) ->
      (match topt with Some t -> add_bv_term (get_term_bv t) | None -> ());
      List.fold_right add_bv
        (List.map get_pattern_bv patl)
        (add_bv (get_oprocess_bv p1) (get_oprocess_bv p2))
  | Insert (tbl, tl, p) ->
      List.iter (fun t -> add_bv_term (get_term_bv t)) tl;
      get_oprocess_bv p

let display_vars (a, b) =
  print_string "Free vars : ";
  BinderSet.iter (fun x -> print_string ((get_binder_name x) ^ " ")) a;
  print_newline ();
  print_string "Bound vars : ";
  BinderSet.iter (fun x -> print_string ((get_binder_name x) ^ " ")) b;
  print_newline ()

let impl_get_vars p =
  free_vars := BinderSet.empty;
  bound_vars_under_repl := BinderSet.empty;
  bound_vars_terms := BinderSet.empty;
  let bv_no_repl = get_iprocess_bv p in
  let bv_repl = !bound_vars_under_repl in
  let bv_terms = !bound_vars_terms in
  (* This way of computing free variables is ok because the variables
     are renamed to distinct names *)
  let fv =
    BinderSet.diff !free_vars
      (BinderSet.union bv_no_repl (BinderSet.union bv_repl bv_terms))
  in
  free_vars := BinderSet.empty;
  bound_vars_under_repl := BinderSet.empty;
  bound_vars_terms := BinderSet.empty;
  (fv, bv_no_repl, bv_repl, bv_terms)

let rt = ref 0

let create_fresh_number () =
  rt := !rt + 1;
  !rt

let create_fresh_name prefix = prefix ^ string_of_int (create_fresh_number ())

let rec create_fresh_names prefix = function
  | 0 -> []
  | i -> create_fresh_name prefix :: create_fresh_names prefix (i - 1)

let create_local_name prefix i = prefix ^ string_of_int i

let rec create_local_names prefix curr = function
  | 0 -> []
  | i -> create_local_name prefix curr :: create_local_names prefix (curr + 1) (i - 1)

let check_oracle_compatibility name (rt, o) (rt', o') =
  if rt <> rt' then
    match !Settings.front_end with
    | Settings.Channels ->
        error
          ( "The outputs following inputs on channel " ^ name
            ^ " do not have the same type" )
    | Settings.Oracles ->
        error
          ( "The oracle " ^ name
            ^ " does not have the same return types everywhere" )
  else if o <> o' then
    match !Settings.front_end with
    | Settings.Channels ->
        error
          ( "The input channels after outputs after inputs on channel " ^ name
            ^ " are not the same everywhere" )
    | Settings.Oracles ->
        error
          ( "The oracle " ^ name
            ^ " does not have the same next oracles everywhere" )

let check_argument_type_compatibility name at at' =
  if at <> at' then
    match !Settings.front_end with
    | Settings.Channels ->
        error
          ( "The messages of inputs on channel " ^ name
            ^ " do not have the same types everywhere" )
    | Settings.Oracles ->
        error
          ( "The arguments of oracle " ^ name
            ^ " do not have the same types everywhere" )

let type_append =
  StringMap.fold (fun name (s, at) acc ->
      try
        let s', at' = StringMap.find name acc in
        check_argument_type_compatibility name at at';
        match (s, s') with
        | Some (rt, o), Some (rt', o') ->
            check_oracle_compatibility name (rt, o) (rt', o');
            acc
        | None, Some (rt, o) -> acc
        | Some (rt, o), None ->
            StringMap.add name (Some (rt, o), at) (StringMap.remove name acc)
        | None, None -> acc
      with Not_found -> StringMap.add name (s, at) acc)

(** Returns the next oracles.
 *  b represents if the oracle is under replication (false) or not (true)
**)
let rec get_next_oracles b p =
  match p.i_desc with
  | Nil -> []
  | Input ((c, tl), pat, p) -> [ (b, c.cname, pat, p) ]
  | Par (p1, p2) -> get_next_oracles b p1 @ get_next_oracles b p2
  | Repl (b, p) -> get_next_oracles false p

let term_tuple_types t =
  match !Settings.front_end with
  | Settings.Oracles -> (
      match t.t_desc with
      | FunApp (f, tl) when f.f_name = "" -> List.map (fun t -> t.t_type) tl
      | _ ->
          Parsing_helper.internal_error
            "The output term must be a call to the function \"\"" )
  | Settings.Channels -> (
      match t.t_desc with
      | FunApp (f, tl) when f.f_name = "" ->
          (* decompose if tuple *)
          List.map (fun t -> t.t_type) tl
      | _ -> [ t.t_type ] )

let pat_tuple_types pat =
  match !Settings.front_end with
  | Settings.Oracles -> (
      match pat with
      | PatTuple (f, pl) when f.f_name = "" ->
          List.map Terms.get_type_for_pattern pl
      | _ ->
          Parsing_helper.internal_error
            "An oracle argument must be a pattern with a function tuple" )
  | Settings.Channels -> (
      match pat with
      | PatTuple (f, pl) when f.f_name = "" ->
          (* if we are given a tuple, decompose it *)
          List.map Terms.get_type_for_pattern pl
      | _ -> [ Terms.get_type_for_pattern pat ] )

let rec get_oracle_types_oprocess name args_types p =
  match p.p_desc with
  | Yield | EventAbort _ ->
      StringMap.add name (None, args_types) StringMap.empty
  | Restr (b, p) -> get_oracle_types_oprocess name args_types p
  | Test (t, p1, p2) ->
      type_append
        (get_oracle_types_oprocess name args_types p1)
        (get_oracle_types_oprocess name args_types p2)
  | Output ((c, tl), t, p) -> (
      let r = get_oracle_types_process p in
      let o = List.map (fun (b, n, _, _) -> (b, n)) (get_next_oracles true p) in
      let ra = term_tuple_types t in
      try
        let s, a' = StringMap.find name r in
        check_argument_type_compatibility name a' args_types;
        match s with
        | Some (ra', o') ->
            check_oracle_compatibility name (ra, o) (ra', o');
            r
        | None ->
            type_append
              (StringMap.add name (Some (ra, o), args_types) StringMap.empty)
              r
      with Not_found -> StringMap.add name (Some (ra, o), args_types) r )
  | Let (pat, t, p1, p2) ->
      type_append
        (get_oracle_types_oprocess name args_types p1)
        (get_oracle_types_oprocess name args_types p2)
  | EventP (t, p) -> get_oracle_types_oprocess name args_types p
  | Find (_, _, _) -> error "Find not supported"
  | Get (tbl, patl, topt, p1, p2, _) ->
      type_append
        (get_oracle_types_oprocess name args_types p1)
        (get_oracle_types_oprocess name args_types p2)
  | Insert (tbl, tl, p) -> get_oracle_types_oprocess name args_types p

and get_oracle_types_process p =
  match p.i_desc with
  | Nil -> StringMap.empty
  | Input ((c, tl), pat, p) ->
      get_oracle_types_oprocess c.cname (pat_tuple_types pat) p
  | Par (p1, p2) ->
      type_append (get_oracle_types_process p1) (get_oracle_types_process p2)
  | Repl (b, p) -> get_oracle_types_process p

let get_type_name t =
  match t.timplname with
  | Some s -> s
  | None ->
      match t.tcat with
      | Interv _ ->
          (* translate replication indices *)
          "nat"
      | _ -> error ("Type name required for type " ^ t.tname)

let preamble module_name =
  "module " ^ !protocol_name_allcaps ^ "." ^ module_name ^ "\n\n" ^
  "open CVTypes\n" ^
  "open State\n" ^
  "open Helper\n" ^
  "open " ^ !protocol_name_allcaps ^ ".Types\n" ^
  "open " ^ !protocol_name_allcaps ^ ".Functions\n" ^
  "open " ^ !protocol_name_allcaps ^ ".Tables\n" ^
  "open " ^ !protocol_name_allcaps ^ ".Sessions\n" ^
  "open " ^ !protocol_name_allcaps ^ ".Events\n" ^
  "open " ^ !protocol_name_allcaps ^ ".Protocol\n\n"

let get_table_name str = "Table_" ^ alphabetize_string str
let get_table_name_lowercase str = "table_" ^ alphabetize_string str

let get_table_entry_name str = "TableEntry_" ^ alphabetize_string str

let get_type_predicate t =
  match t.tpredicate with
  | Some x -> x
  | None -> error ("Predicate for type " ^ t.tname ^ " required!")

let get_table_file tbl =
  match tbl.tblfile with None -> tbl.tblname | Some f -> f

let get_read_serial ty =
  match ty.tserial with
  | Some (_, s) -> s
  | None ->
      match ty.tcat with
      | Interv _ -> "deserialize_nat"
      | _ -> error ("Deserialization for type " ^ ty.tname ^ " required")

let get_write_serial ty =
  match ty.tserial with
  | Some (s, _) -> s
  | None ->
      match ty.tcat with
      | Interv _ -> "serialize_nat"
      | _ -> error ("Serialization for type " ^ ty.tname ^ " required")

let get_random t =
  match t.trandom with
  | Some r -> r
  | None ->
      error
        ( "Random generation function required for type " ^ t.tname ^ "." )

let random b ind =
  let rand = get_random b.btype in
  "\n" ^
  (* rand already is in parentheses if needed *)
  ind ^ "let " ^ state_variable ^ ", " ^ get_binder_name b ^ " = " ^ call_with_entropy ^ " " ^ state_variable ^ " " ^ rand ^ " in\n"

let equal t =
  match t.tequal with
  | Some eq ->
      eq
  | None ->
      error
        ( "Equality test function required for type " ^ t.tname ^ "." )

let yield_transl od ind =
  if oracle_only_yields od then "\n" ^ ind ^ state_variable
  else "\n" ^ ind ^ state_variable ^ ", None"

let rec needs_state t =
  match t.t_desc with
  | Var _ -> false (* indices are always the current indices, and not encoded *)
  | FunApp(f, tl) -> f.f_impl_ent || f.f_impl_needs_state || List.exists needs_state tl
  | TestE(t1,t2,t3) -> needs_state t1 || needs_state t2 || needs_state t3
  | ReplIndex _ -> false
  | EventAbortE _ -> Parsing_helper.input_error "event_abort not supported in F* implementation" t.t_loc
  | EventE _ | GetE _ | InsertE _ | ResE _ -> true
  | FindE _ -> Parsing_helper.input_error "Find not supported (implementation)" t.t_loc
  | LetE (pat, t1, t2, topt) ->
      needs_state_pat pat || 
      needs_state t1 || needs_state t2 ||
      (match topt with
         None -> false
       | Some t3 -> needs_state t3)

and needs_state_pat = function
  | PatVar _ -> false
  | PatEqual(t) -> needs_state t
  | PatTuple(f, pl) -> List.exists needs_state_pat pl


let rec translate_termlist_ns sep tl ind = match tl with
  | [] -> "()"
  | [a] -> translate_term_ns a ind
  | a::b -> (translate_term_ns a ind) ^ sep ^ (translate_termlist_ns sep b ind)

(* ns = no state *)
and translate_term_ns t ind =
  (* This wraps everything except Var into parentheses, so everything that might contain spaces.
     This is important because translate_termlist_ns is used for event and function parameters. *)
  match t.t_desc with
  | Var(b, tl) -> debug_comment "translate_term_ns Var" ^ get_binder_name (get_binderref_binder t.t_loc (b, tl))
  | FunApp(f, tl) ->
      if f.f_name = "" then
        "(compos [" ^
        (string_list_sep
          ";"
          (List.map
            (fun t -> (get_write_serial t.t_type) ^ " " ^(translate_term_ns t ind))
            tl)) ^
        "])"
      else
        (match f.f_impl with
         | Func x ->
             assert (not f.f_impl_ent);
             "(" ^ debug_comment "translate_term_ns FunApp/Func" ^
             x ^ " " ^ (translate_termlist_ns " " tl ind) ^ ")"
         | Const x ->
             debug_comment "translate_term_ns FunApp/Const" ^
             x
         | SepFun ->
             assert (not f.f_impl_needs_state);
             "(" ^ (!letfun_prefix) ^ (get_letfun_name f) ^ " " ^ (translate_termlist_ns " " tl ind) ^ ")"
         | FuncEqual ->
             let eq = equal (List.hd tl).t_type in
             "(" ^ debug_comment "translate_term_ns FunApp/FuncEqual" ^
             eq ^ " " ^ (translate_termlist_ns " " tl ind) ^ ")"
         | FuncDiff ->
             let eq = equal (List.hd tl).t_type in
             "(" ^ debug_comment "translate_term_ns FunApp/FuncDiff" ^
             "not (" ^ eq ^ " " ^ (translate_termlist_ns " " tl ind) ^ "))"
         | No_impl -> error ("Function not registered:" ^ f.f_name)
        )
  | TestE(t1,t2,t3) ->
      "(if " ^ (translate_term_ns t1 ind) ^
      debug_comment "translate_term_ns TestE" ^
      " then " ^
      (translate_term_ns t2 ind) ^
      " else " ^
      (translate_term_ns t3 ind) ^ " )"
  | ReplIndex _ ->
      (* if we end up here, this means that the CV model contains
         not all replication indices, or not in the right order. *)
      Parsing_helper.input_error "Replication indices should occur only inside variables and events, and only as tuple of all replication indices leading to this program point (implementation)" t.t_loc
  | EventAbortE _ ->
      Parsing_helper.input_error "event_abort not supported in F* implementation" t.t_loc
  | EventE _ -> assert false  (* These need state and if we end up here *)
  | GetE _ -> assert false    (* it is an error in the code and so *)
  | InsertE _ -> assert false (* we assert it does not happen. *)
  | ResE _ -> assert false
  | FindE _ ->
      Parsing_helper.input_error "Find not supported (implementation)" t.t_loc
  | LetE (pat, t1, t2, topt) ->
      "(" ^ debug_comment "translate_term_ns LetE" ^
      (match_pattern_ns [] pat (translate_term_ns t1 ind) (translate_term_ns t2)
         (match topt with
            Some t3 ->
              translate_term_ns t3
          | None ->
              (fun ind ->
                Parsing_helper.internal_error "else branch of let called but not defined"))
         true ind) ^
      ")"

and match_pattern_complex_ns opt pat s p1 p2 in_term ind =
  (* decomposition of every function *)
  let rec decompos = function
    (* On the first layer, we will not find PatVar or PatEqual -- it will have been captured
       by match_pattern_ns, already. *)
    | PatVar(b) ->
        let bname = get_binder_name b in
        ([], bname, [], [bname])
    | PatEqual(t) ->
        let n = create_fresh_name "bvar_" in
        let eq = equal t.t_type in
        ([], n, [(eq, n, translate_term_ns t ind)], [])
    | PatTuple(f, pl) ->
        let n = create_fresh_name "bvar_" in
        let func =
          if f.f_name = "" then
            let n  = create_fresh_name "cvar_" in
            let nl = create_fresh_names "cvar_" (List.length pl) in
            let return_vars = create_fresh_names "cvar_" (List.length pl) in
            let return_vars_list = (string_list_sep "," return_vars) in
            (* decompos cuts into substrings according to the encoded length indications *)
            "(fun " ^ n ^ " -> match decompos " ^ n ^ " with\n" ^
            ind ^ "    | Some [" ^ (string_list_sep ";" nl) ^ "] -> (\n" ^
            ind ^ "        match (" ^
            (* then we deserialize according to the expected type *)
            (string_list_sep ","
               (List.map2 (fun p n -> (get_read_serial (Terms.get_type_for_pattern p)) ^ " " ^ n) pl nl)) ^ ") with\n" ^
            ind ^ "        | (" ^ (string_list_sep "," (List.map (fun rv -> "Some " ^ rv) return_vars)) ^ ") -> Some (" ^ return_vars_list ^ ")\n" ^
            ind ^ "        | _ -> None)\n" ^
            ind ^ "    | _ -> None\n" ^
            ")"
          else
            (
              match (f.f_impl_inv) with
                Some(f) -> f
              | _ -> error ("Inverse function of " ^ f.f_name ^ " not registered. Add a line 'implementation fun " ^ f.f_name ^ "=\"f1\" [inverse = \"f2\"].' in the source.")
            )
        in (* end let func *)
        let decompos_list = List.map decompos pl in
        (
          (* func: (parameter n, func, variable list) *) (n, func, List.map (fun (_, y, _, _) -> y) decompos_list)::
            (List.concat (List.map (fun (x, _, _, _) -> x) decompos_list)),
          (* name *) n,
          (* tests *) List.concat (List.map (fun (_, _, z, _) -> z) decompos_list),
          (* all_binders *) List.concat (List.map (fun (_, _, _, t) -> t) decompos_list)
        )
  in
  let rec andlist = function
    | [] -> "true"
    | [x] -> x
    | x::y -> x ^ " && " ^ (andlist y)
  in
  let (func, name, tests, all_binders) = decompos pat in
  let aux ovar p1 p2_str =
    let p2_block = code_block (fun _ -> p2_str) (ind ^ "  ") false in
    ind ^ "  let " ^ name ^ " = " ^ s ^ " in" ^
    (* decompos functions *)
    (match ovar with Some m -> "\n" ^ "let " ^ m ^ " = " | _ -> "") ^
    (List.fold_left (^) ""
       (List.map
          (fun (n, f, vl) -> "\n" ^
                             ind ^ "  match " ^ f ^ " " ^ n ^ " with\n" ^
                             ind ^ "  | None ->" ^ code_block_add_line_prefix p2_block "  " ^ "\n" ^
                             ind ^ "  | Some (" ^ (string_list_sep "," vl) ^ ") ->") func)
    ) ^
    (* tests *)
    "\n"^
    (if tests == [] then (code_block p1 (ind ^ "  ") true)
    else
      ind ^ "  if " ^ (andlist (List.map (fun (eq, n, s) -> eq ^ " " ^ n ^ " " ^ s) tests)) ^ " then" ^
      (code_block p1 (ind ^ "  ") true) ^
      "else" ^
      p2_block ^ "\n") ^ (match ovar with Some m -> ind ^ "in\n" | _ -> "")
  in
  (* We reuse p2_str to make sure p2 is only evaluated once. p1 is evaluated only once anyway. *)
  let p2_str = p2 "" in
  if is_complicated p2_str then
    (*the result of the match needs to be assigned to a new variable.*)
    let m = create_fresh_name "bvar_" in
    debug_comment "match_pattern_complex_ns" ^
    (aux (Some m) (fun s -> "Some (" ^ (string_list_sep "," all_binders) ^ ")") "None") ^ "\n" ^
    ind ^ "match " ^ m ^ " with\n" ^
    ind ^ "| None ->\n" ^
    ind ^ "  " ^ (code_block_add_line_prefix p2_str (ind ^ "      ")) ^ "\n" ^
    ind ^ "| Some (" ^ (string_list_sep "," all_binders) ^ ") ->\n" ^
    ind ^ "  " ^ (p1 (ind ^ "      "))
  else
    debug_comment "match_pattern_complex_ns" ^
    aux None p1 p2_str

(*
  The meaning of the parameters is the following:
  let pat = var in ( p1 ) else ( p2 )
*)
and match_pattern_ns opt (pat:Types.pattern) (var:string) (p1:string -> string) (p2: string -> string) (in_term:bool) ind =
  match pat with
  | PatVar(b) ->
      ind ^
      "let " ^ (get_binder_name b) ^ " = " ^ var ^
      debug_comment "match_pattern_ns PatVar" ^
      " in\n" ^
      (p1 ind)
  | PatEqual(t) ->
      let eq = equal t.t_type in
      ind ^
      "if " ^ eq ^ " " ^ (translate_term_ns t ind) ^ " " ^ var ^ " then" ^
      debug_comment "match_pattern_ns PatEqual" ^
      (code_block p1 ind true) ^
      "else" ^
      (code_block p2 ind true)
  | _ -> match_pattern_complex_ns opt pat var p1 p2 in_term ind

let rec translate_oprocess od p ind =
  match p.p_desc with
  | Yield -> yield_transl od ind
  | EventAbort _ ->
      Parsing_helper.input_error "event_abort not supported in F* implementation" p.p_loc
  | Restr(b, p) ->
      (random b ind) ^
      (translate_oprocess od p ind)
  | Test(t, p1, p2) ->
      let (prefix, valt) = translate_term_get_val t ind in
      "\n" ^
      prefix ^ "\n" ^
      ind ^ "if " ^ valt ^ " then\n" ^
      ind ^ "begin" ^
      (translate_oprocess od p1 (ind ^ "  ")) ^ "\n" ^
      ind ^ "end\n" ^
      ind ^ "else\n" ^
      ind ^ "begin" ^
      (translate_oprocess od p2 (ind ^ "  ")) ^ "\n" ^
      ind ^ "end"
  | Output((_,_),t,p1) ->
      (try
        let (nr, fol, _) = List.find (fun (_, _, pr) -> pr == p) od.list_of_returns in
        (if fol == [] then ""
        else
          "let sel = [" ^
          String.concat "; "
            (List.map
              (fun (fon, bl) ->
                "R" ^ string_of_int nr ^ "_" ^ alphabetize_string fon ^
                List.fold_left
                  (fun s b -> s ^ " " ^ get_binder_name b)
                  ""
                  bl
              )
              fol) ^ "] in\n" ^
        "let " ^ state_variable ^ " = state_add_to_session " ^ state_variable ^ " " ^ session_id_variable ^ " sel in\n") ^
        let (prefix, valt) = translate_term_to_output t ind in
        "\n" ^ prefix ^ "(" ^
        state_variable ^ ", Some (" ^
        (if not (fol == []) && od.under_repl then session_id_variable ^ ", " else "") ^
        valt ^ "))\n"
      with Not_found ->
        Parsing_helper.internal_error ("Expected exactly one list entry corresponding to the process, when treating an output of oracle " ^ od.oracle_name)
      )
  | Let(pat,t,p1,p2) ->
      let (prefix, valt) = translate_term_get_val t ind in
      let (prefixpat, valpat) = match_pattern [] pat valt (translate_oprocess od p1) (translate_oprocess od p2) false ind in
      "\n" ^ prefix ^ prefixpat ^
      "\n" ^ ind ^ valpat
  | EventP(t,p)->
      "\n"^ind^(translate_event t ind)^
      (translate_oprocess od p ind)
  | Find(_,_,_) ->
      Parsing_helper.input_error "Find not supported (implementation)" p.p_loc
  | Get(tbl,patl,topt,p1,p2,find_info) ->
      translate_get (fun b -> Terms.refers_to_oprocess b p1) [] tbl patl topt (translate_oprocess od p1) (translate_oprocess od p2) find_info ind
  | Insert(tbl,tl,p) ->
      let (prefixtl, valtl) = translate_termlist tl ind in
      let tfile = get_table_file tbl in
      prefixtl ^ "let state = " ^ table_insert ^ " " ^ state_variable ^ " " ^ get_table_name tfile ^ " (" ^
      get_table_entry_name tfile ^ " #" ^ get_table_name tfile ^ " " ^
      (string_list_sep " "
         (List.map in_parens_if_needed valtl)
      ) ^ ") in\n" ^
      (translate_oprocess od p ind)

(* p1 and p2 are functions that take the indentation level
   and return the string corresponding to the program.
   Meaning of parameters: get tbl(patl) suchthat topt (p1) else (p2)
*)
and translate_get used opt tbl patl topt p1 p2 find_info ind =
  let pat_vars = Terms.vars_from_pat_list [] patl in
  let used_vars = List.filter used pat_vars in
  let match_res = "("^(string_list_sep "," (List.map get_binder_name used_vars))^")" in
  let tfile = get_table_file tbl in
  let tvars = create_fresh_names "tvar_" (List.length tbl.tbltype) in
  let filter_needs_state = match topt with | Some t -> needs_state t | None -> false in
  let (prefix, matchfilt) =
    match_pattern_list
      opt patl tvars
      (fun ind -> (* p1 *)
        match topt with
           | Some t ->
               if filter_needs_state then
                 let prefixf, valf = translate_term_get_val t ind in
                 ind ^ prefixf ^ "if (" ^ valf ^ ") then " ^ state_variable ^ ", Some " ^ match_res ^ " else " ^ state_variable ^ ", None"
               else
                 ind ^ "if (" ^ (translate_term_ns t ind) ^ ") then Some " ^ match_res ^ " else None"
           | None -> ind ^ "Some " ^ match_res)
      (fun ind -> "None") (* p2 *)
      false
      (ind ^ "      ")
  in
  let filterfun =
    ind ^ "  (fun " ^ (if filter_needs_state then "(" ^ state_variable ^ ":"  ^ (state_type ()) ^ ") " else "") ^ "(te:" ^ (!protocol_name ^ "_" ^ !table_entry_type) ^ " " ^ get_table_name tfile ^ ") -> " ^
    ind ^ "let " ^ get_table_entry_name tfile ^ " " ^ (string_list_sep " " tvars) ^ " = te in\n" ^
    ind ^ "    begin\n" ^
    (*  *)
    matchfilt ^ "\n" ^
    ind ^ "    end\n" ^
    ind ^ "  )"
  in
  if used_vars = [] then
    "\n" ^
    ind^"begin\n"^
    prefix ^
    (if filter_needs_state then
      ind ^ "let " ^ state_variable ^ ", b = " ^ table_entry_exists_full ^ " " ^ state_variable ^ " " ^ get_table_name tfile ^ "\n" ^ filterfun ^ " in\n" ^
      ind ^ "if b then"
    else
      ind ^ "if " ^ table_entry_exists ^ " " ^ state_variable ^ " " ^ get_table_name tfile ^ "\n" ^ filterfun ^
      ind ^ "then") ^
    (code_block p1 ind true) ^
    "else" ^
    (code_block p2 ind true) ^
    "end"
  else if find_info = Unique then
    "\n" ^
    ind ^ "begin\n"^
    prefix ^
    ind ^ "match " ^ (if filter_needs_state then table_get_unique_full else table_get_unique) ^ " " ^ state_variable ^ " " ^ get_table_name tfile ^ "\n" ^
    filterfun ^ "\n" ^
    ind ^ "with\n"^
    ind ^ "| " ^ (if filter_needs_state then state_variable ^ ", " else "") ^ "None ->" ^
    (code_block p2 ind false) ^ "\n" ^
    ind ^ "| " ^ (if filter_needs_state then state_variable ^ ", " else "") ^ "Some " ^ match_res ^ " ->" ^
    (code_block p1 ind true) ^
    "end"
  else
    "\n" ^
    ind ^ "begin\n"^
    prefix ^
    ind ^ "match " ^ table_get ^ " " ^ state_variable ^ " " ^ get_table_name tfile ^ "\n" ^
    filterfun ^ "\n" ^
    ind ^ "with\n"^
    ind ^ "| " ^ state_variable ^ ", None ->" ^
    (code_block p2 ind false) ^ "\n" ^
    ind ^ "| " ^ state_variable ^ ", Some " ^ match_res ^ " ->" ^
    (code_block p1 ind true) ^
    "end"

and translate_event t ind =
  match t.t_desc with
  | FunApp (event_function, repl_indices :: paraml) ->
      let is_session_id = match repl_indices.t_desc with
        (* first boolean: if it matches, second boolean: if we need serialization.
           We need serialization if the event was declared bitstring as type for
           a tuple of replication indices. *)
        | FunApp (_, []) -> (fun t -> false, false)
        | FunApp (_, [repl_index]) -> (fun t -> Terms.equal_terms t repl_index, false)
        | FunApp (_, _) -> (fun t -> Terms.equal_terms t repl_indices, true)
        | _ -> Parsing_helper.internal_error "Expected FunApp for event replication index list (translate_event)"
      in
      let translate_term_get_val_event t ind =
        match is_session_id t with
        | true, true -> ("", "(serialize_nat " ^ session_id_variable ^ ")")
        | true, false -> ("", session_id_variable)
        (* if the model uses only _some_ replication indices, or in the wrong order,
           or not as top-level parameter of the event but nested inside a parameter,
           we will end up in this last case, and then translate_term_get_val will
           complain about any replication indices. *)
        | _ -> translate_term_get_val t ind
      in
      let rec translate_termlist_event l ind =
        match l with
          [] -> ("", [])
        | [a] -> let (prefix, vala) = translate_term_get_val_event a ind in (prefix, [vala])
        | a::l ->
            let (prefixa, vala) = translate_term_get_val_event a ind in
            let (prefixl, vall) = translate_termlist_event l ind in
            prefixa ^ prefixl, vala :: vall
      in
      let prefix, vall = translate_termlist_event paraml "  " in
      prefix ^
      "let ev = Event_" ^ event_function.f_name ^ " " ^ (String.concat " " vall) ^ " in\n" ^
      "let " ^ state_variable ^ " = state_add_event " ^ state_variable ^ " ev in\n"
  | _ -> Parsing_helper.internal_error "Expected FunApp for event (translate_event)"

and translate_termlist l ind = 
  match l with
    [] -> ("", [])
  | [a] -> let (prefix, vala) = translate_term_get_val a ind in (prefix, [vala])
  | a::l ->
      let (prefixa, vala) = translate_term_get_val a ind in
      let (prefixl, vall) = translate_termlist l ind in
      prefixa ^ prefixl, vala :: vall

and translate_term_get_val t ind =
  if not (needs_state t) then
    ("", translate_term_ns t ind)
  else
    begin
      match t.t_desc with
      | Var _ | ReplIndex _ -> assert false (* should be translated by the version without state *)
      | FunApp(f, tl) when not f.f_impl_ent ->
          let prefix, valtl = translate_termlist tl ind in
          if f.f_name = "" then
            prefix,
            "(compos [" ^
            (string_list_sep
              ";"
              (List.map2
                (fun t valt -> (get_write_serial t.t_type) ^ " " ^ valt)
                tl
                valtl)) ^
            "])"
          else
            (match f.f_impl with
             | Func x ->
                 prefix,
                 "(" ^ debug_comment "translate_term_get_val FunApp/Func" ^
                 x ^ " " ^ (list_args valtl) ^ ")" 
             | Const x -> assert false (* should be translated by the version without state *)
             | SepFun ->
                 let v = create_fresh_name "v" in
                 prefix ^
                 "let " ^
                 (if f.f_impl_needs_state then state_variable ^ ", " else "") ^ v ^
                 " = " ^
                 (!letfun_prefix) ^ (get_letfun_name f) ^ " " ^
                 (if f.f_impl_needs_state then state_variable ^ " " else "") ^
                 (if f.f_impl_needs_state && valtl = [] then "" else (list_args valtl)) ^ " in\n", v
             | FuncEqual ->
                 let eq = equal (List.hd tl).t_type in
                 prefix,
                 "(" ^ debug_comment "translate_term_get_val FunApp/FuncEqual" ^
                 eq ^ " " ^ (list_args valtl) ^ ")"
             | FuncDiff ->
                 let eq = equal (List.hd tl).t_type in
                 prefix,
                 "(" ^ debug_comment "translate_term_get_val FunApp/FuncDiff" ^
                 "not (" ^ eq ^ " " ^ (list_args valtl) ^ "))"
             | No_impl -> error ("Function not registered:" ^ f.f_name)
            )
      | EventAbortE _ ->
          Parsing_helper.input_error "event_abort not supported in F* implementation" t.t_loc
      | FindE _ ->
          Parsing_helper.input_error "Find not supported (implementation)" t.t_loc
      | EventE(t,p)->
          let (prefix, valp) = translate_term_get_val p ind in
          (translate_event t ind) ^ prefix, valp
      | InsertE(tbl, tl, p) ->
          let (prefixtl, valtl) = translate_termlist tl ind in
          let (prefix, valp) = translate_term_get_val p ind in
          let tfile = get_table_file tbl in
          prefixtl ^ "let state = " ^ table_insert ^ " " ^ state_variable ^ " " ^ get_table_name tfile ^ " (" ^
          get_table_entry_name tfile ^ " #" ^ get_table_name tfile ^ " " ^
          (string_list_sep " "
             (List.map in_parens_if_needed valtl)
          ) ^ ") in\n" ^ prefix, valp
      | ResE (b, p) ->
          let (prefix, valp) = translate_term_get_val p ind in
          (* random is producing prefix-like code. *)
          debug_comment "translate_term_get_val ResE" ^
          (random b ind) ^ prefix, valp
      | TestE(t1,t2,t3) when not(needs_state t2 || needs_state t3) ->
          let (prefix1, v1) = translate_term_get_val t1 ind in
          prefix1,
          "(if " ^ v1 ^
          debug_comment "translate_term_get_val TestE" ^
          " then " ^ (translate_term_ns t2 ind) ^
          " else " ^ (translate_term_ns t3 ind) ^ ")"
      | _ ->
          let v = create_fresh_name "v" in
          "let " ^ state_variable ^ ", " ^ v ^ " = " ^ (translate_term_get_pair t ind) ^ " in\n", v
    end

and  translate_term_get_pair t ind =
  if not (needs_state t) then
    "("^ state_variable ^ ", " ^ (translate_term_ns t ind) ^ ")"
  else
    begin
      match t.t_desc with
      | Var _ | ReplIndex _ -> assert false (* should be translated by the version without state *)
      | FunApp(f, tl) when f.f_impl_ent ->
          let prefix, valtl = translate_termlist tl ind in
          assert (f.f_name <> ""); (* tuples should not need entropy *)
          (match f.f_impl with
           | Func x ->
               let f_code =
                 "(" ^
                 debug_comment "translate_term_get_pair FunApp/Func" ^
                 x ^
                 (if List.length valtl > 0 then " " ^ (list_args valtl) else "") ^
                 ")" in
               prefix ^ call_with_entropy ^ " " ^ state_variable ^ " " ^ f_code
           | Const x -> assert false (* should be translated by the version without state *)
           | SepFun | FuncEqual | FuncDiff -> assert false (* should not need entropy *)
           | No_impl -> error ("Function not registered:" ^ f.f_name)
          )
      | TestE(t1,t2,t3) when needs_state t2 || needs_state t3 ->
          let (prefix1, v1) = translate_term_get_val t1 ind in
          "(" ^ prefix1 ^
          " if " ^ v1 ^
          debug_comment "translate_term_get_pair TestE" ^
          " then " ^ (translate_term_get_pair t2 ind) ^
          " else " ^ (translate_term_get_pair t3 ind) ^ " )"
      | EventAbortE _ ->
          Parsing_helper.input_error "event_abort not supported in F* implementation" t.t_loc
      | EventE(t,p)->
          "(" ^ (translate_event t ind) ^
          (translate_term_get_pair p ind) ^ ")"
      | GetE(tbl,patl,topt,p1,p2, find_info) ->
          translate_get (fun b -> Terms.refers_to b p1) [] tbl patl topt (translate_term_get_pair p1) (translate_term_get_pair p2) find_info ind
      | InsertE(tbl, tl, p) ->
          let (prefixtl, valtl) = translate_termlist tl ind in
          let tfile = get_table_file tbl in
          prefixtl ^ "(let state = " ^ table_insert ^ " " ^ state_variable ^ " " ^ get_table_name tfile ^ " (" ^
          get_table_entry_name tfile ^ " " ^
          (string_list_sep " "
             (List.map in_parens_if_needed valtl)
          ) ^ ") in\n" ^
          (translate_term_get_pair p ind) ^ ")"
      | FindE _ -> Parsing_helper.input_error "Find not supported (implementation)" t.t_loc
      | ResE (b, t) ->
          "(" ^ debug_comment "translate_term_get_pair ResE" ^
          (random b ind) ^ (translate_term_get_pair t ind) ^ ")"
      | LetE (pat, t1, t2, topt) ->
          let (prefix1, val1) = translate_term_get_val t1 ind in
          let (prefixpat, valpat) =
          match_pattern [] pat val1 (translate_term_get_pair t2)
                       (match topt with
                          Some t3 -> translate_term_get_pair t3
                        | None -> (fun ind -> Parsing_helper.internal_error "else branch of let called but not defined"))
              true ind
          in
          "(" ^ debug_comment "translate_term_get_pair LetE" ^
          prefix1 ^ prefixpat ^ valpat ^
          ")"
      | _ ->
          let (prefix, valt) = translate_term_get_val t ind in
          prefix ^ "(" ^ state_variable ^ ", " ^ valt ^ ")"
    end

and translate_term_to_output t ind =
  match !Settings.front_end with
  | Settings.Oracles ->
      (
        match t.t_desc with
        | FunApp(f,tl) when f.f_name="" ->
            let prefix, valtl = translate_termlist tl ind in
            prefix, (string_list_sep "," valtl)
        | _ -> Parsing_helper.internal_error "output term not of the form \"\"()"
      )
  | Settings.Channels ->
      (
        match t.t_desc with
        | FunApp(f,tl) when f.f_name="" ->
            let prefix, valtl = translate_termlist tl ind in
            prefix, (string_list_sep "," valtl)
        | _ -> translate_term_get_val t ind
      )

and match_pattern_complex opt patl sl p1 p2 in_term ind =
  (* decomposition of every function *)
  let rec decompos = function
    | PatVar(b) ->
        let bname = get_binder_name b in
        ([], bname, [], [bname])
    | PatEqual(t) ->
        let n = create_fresh_name "bvar_" in
        let eq = equal t.t_type in
        ([], n, [(eq, n, translate_term_get_val t ind)], [])
    | PatTuple(f, pl) ->
        let n = create_fresh_name "bvar_" in
        let func =
          if f.f_name = "" then
            let n  = create_fresh_name "cvar_" in
            let nl = create_fresh_names "cvar_" (List.length pl) in
            let return_vars = create_fresh_names "cvar_" (List.length pl) in
            let return_vars_list = (string_list_sep "," return_vars) in
            "(fun " ^ n ^ " -> match decompos " ^ n ^ " with\n" ^
            ind ^ "    | Some [" ^ (string_list_sep ";" nl) ^ "] -> (\n" ^
            ind ^ "        match (" ^
            (string_list_sep ","
               (List.map2 (fun p n -> (get_read_serial (Terms.get_type_for_pattern p)) ^ " " ^ n) pl nl)) ^ ") with\n" ^
            ind ^ "        | (" ^ (string_list_sep "," (List.map (fun rv -> "Some " ^ rv) return_vars)) ^ ") -> Some (" ^ return_vars_list ^ ")\n" ^
            ind ^ "        | _ -> None)\n" ^
            ind ^ "    | _ -> None\n" ^
            ")"
          else
            (
              match (f.f_impl_inv) with
                Some(f) -> f
              | _ -> error ("Inverse function of "^f.f_name^" not registered. Add a line 'implementation fun "^f.f_name^"=\"f1\" [inverse = \"f2\"].' in the source.")
            )
        in
        let decompos_list = List.map decompos pl in
        (
          (n,func,List.map (fun (x,y,z,_)->y) decompos_list)::
            (List.concat (List.map (fun (x,y,z,_)->x) decompos_list)),
          n,
          List.concat (List.map (fun (x,y,z,_)->z) decompos_list),
          List.concat (List.map (fun (_,_,_,t)->t) decompos_list)
        )
  in
  let rec andlist = function
    | [] -> "true"
    | [x] -> x
    | x::y -> x^" && "^(andlist y)
  in
  let decompos_list = List.map decompos patl in
  let func = List.concat (List.map (fun (x,y,z,t)->x) decompos_list) in
  let assign = List.map2 (fun (x,y,z,t) s -> (y,s)) decompos_list sl in
  let tests = List.concat (List.map (fun (x,y,z,t)-> z) decompos_list) in
  let all_binders = List.concat (List.map (fun (_,_,_,t)->t) decompos_list) in
  let prefix = String.concat "" (List.map (fun (eq, n, (prefix, s)) -> prefix) tests) in
  let aux ovar p1 p2_str =
    let p2_block = code_block (fun _ -> p2_str) (ind ^ "  ") false in
    (String.concat
      ""
      (List.map
        (fun (name, s) ->
          "\n" ^
          ind ^ "let " ^ name ^ " = " ^ s ^ " in") assign)) ^
    (* decompos functions *)
    (match ovar with Some m -> "\n" ^ "let " ^ m ^ " = " | _ -> "") ^
    (List.fold_left (^) ""
       (List.map
          (fun (n, f, vl) -> "\n" ^
                             ind ^ "  match " ^ f ^ " " ^ n ^ " with\n" ^
                             ind ^ "  | None ->" ^ code_block_add_line_prefix p2_block "  " ^ "\n" ^
                             ind ^ "  | Some (" ^ (string_list_sep "," vl) ^ ") ->") func)
    ) ^
    (* tests *)
    "\n"^
    (if tests == [] then code_block p1 (ind ^ "  ") true
     else
      ind ^ "  if " ^ (andlist (List.map (fun (eq, n, (prefix, s)) -> eq ^ " " ^ n ^ " " ^ s) tests)) ^ " then" ^
      (code_block p1 (ind ^ "  ") true) ^
      "else" ^
      p2_block ^ "\n") ^ (match ovar with Some m -> ind ^ "in\n" | _ -> "") ^
    ind ^ ""
  in
  (* We reuse p2_str to make sure p2 is only evaluated once. p1 is evaluated only once anyway. *)
  let p2_str = p2 "" in
  if is_complicated p2_str then
    (* the result of the match needs to be assigned to a new variable. *)
    let m = create_fresh_name "bvar_" in
    prefix,
    debug_comment "match_pattern_complex" ^
    (aux (Some m) (fun s -> "Some (" ^ (string_list_sep "," all_binders) ^ ")") "None") ^ "\n" ^
    (* the new variable needs to be used here. *)
    ind ^ "match " ^ m ^ " with\n" ^
    ind ^ "| None ->\n" ^
    ind ^ "  " ^ (code_block_add_line_prefix p2_str (ind ^ "      ")) ^ "\n" ^
    ind ^ "| Some (" ^ (string_list_sep "," all_binders) ^ ") ->\n" ^
    ind ^ "  " ^ (p1 (ind ^ "      "))
  else
    prefix,
    debug_comment "match_pattern_complex" ^
    aux None p1 p2_str

and match_pattern opt (pat:Types.pattern) (var:string) (p1:string -> string) (p2: string -> string) (in_term:bool) ind =
  match pat with
  | PatVar(b) ->
      "",
      debug_comment "match_pattern PatVar" ^ "\n" ^
      ind ^ "let " ^ (get_binder_name b) ^ " = " ^ var ^ " in\n" ^
      (p1 ind)
  | PatEqual(t) ->
      let (prefixt, valt) = translate_term_get_val t ind in
      let eq = equal t.t_type in
      prefixt,
      ind ^ "if " ^ eq ^ " " ^ valt ^ " " ^ var ^ " then" ^
      debug_comment "match_pattern PatEqual" ^
      (code_block p1 ind true) ^
      "else" ^
      (code_block p2 ind true)
  | _ -> match_pattern_complex opt [pat] [var] p1 p2 in_term ind

and match_pattern_list opt patl vars (p1:string -> string) (p2:string -> string) in_term ind =
  match patl, vars with
  | [pat], [var] ->
      match_pattern opt pat var p1 p2 in_term ind
  | _ ->
      match_pattern_complex opt patl vars p1 p2 in_term ind

and match_pattern_from_input opt pat (vars:string list) (next:string -> string) od ind =
  match !Settings.front_end with
  | Settings.Oracles ->
      (
        match pat with
        | PatTuple (f,pl) when f.f_name = "" ->
            let (prefix, matchfilt) = match_pattern_list opt pl vars next (yield_transl od) false ind in
            prefix ^ matchfilt
        | _ -> Parsing_helper.internal_error "oracle must begin with pattern \"\"(...)"
      )
  | Settings.Channels ->
      (
        match pat with
        | PatTuple (f,pl) when f.f_name = "" ->
            let (prefix, matchfilt) = match_pattern_list opt pl vars next (yield_transl od) false ind in
            prefix ^ matchfilt
        | _ ->
            match vars with
              [var] ->
                let (prefix, matchfilt) = match_pattern opt pat var next (yield_transl od) false ind in
		prefix ^ matchfilt
            | _ -> Parsing_helper.internal_error "var in match_pattern_from_input"
      )

let get_interface module_name opt oracles =
  preamble module_name ^
  StringMap.fold
    (fun on od s -> s ^
       "val " ^ get_oracle_function_name on ^ ": " ^
       (state_type ()) ^ " -> " ^
       (match od.list_of_defs with
        | Top _ -> ""
        | NonTop _ -> "nat -> ") ^
       (List.fold_left
         (fun s t -> s ^ get_type_name t ^ " -> ")
         ""
         od.input_type) ^
       "Tot (" ^
       (state_type ()) ^ " " ^
       (match od.output_type with
        | None -> "" (* We come here if all branches yield *)
        | Some tl -> "* option (" ^
            (* return session id if needed *)
            (match od.following_oracles with
            | None -> Parsing_helper.internal_error "If output_type is not None, following_oracles should not be None"
            | Some [] -> ""
            | Some fol -> if od.under_repl then "nat * " else "") ^
            (* output types *)
            (match tl with
             | [] -> "unit"
             | _ -> String.concat " * " (List.map get_type_name tl)) ^
            ")"
       ) ^
       ")\n\n"
    )
    oracles
    ""

let get_implementation module_name opt oracles =
  preamble module_name ^
  StringMap.fold
    (fun on od s ->
       let args = create_fresh_names "input_" (List.length od.input_type) in
       let takes_id = (match od.list_of_defs with
        | Top _ -> false
        | NonTop _ -> true) in
       s ^ "\n\n" ^
       (* name of the function *)
       "let " ^ get_oracle_function_name on ^ " " ^
       (* we always take the current state as input *)
       state_variable ^ " " ^
       (* we take a session id as input in some cases *)
       (if takes_id then session_id_variable ^ " " else "") ^
       (* names for the explicit oracle parameters *)
       (string_list_sep " " args) ^
       (* first line ends here *)
       " =\n" ^
       (* if this continues a session, retrieve the entry *)
       (match od.list_of_defs with
        | Top p ->
            (match p.i_desc with
            | Input (_, pat, p1) ->
              (if od.following_oracles <> None && od.following_oracles <> (Some []) then
                 "let " ^ state_variable ^ ", " ^ session_id_variable ^ " = state_reserve_session_id " ^ state_variable ^ " in\n"
              else "") ^
              match_pattern_from_input opt pat args (translate_oprocess od p1) od ("      ")
            | _ -> Parsing_helper.internal_error "expected input process"
            )
        | NonTop dl ->
            "match " ^
            (if od.under_repl then "get_session_entry "
            else "get_and_remove_session_entry ") ^
            state_variable ^ " " ^
            get_oracle_name od.oracle_name ^ " " ^ session_id_variable ^ " with\n" ^
            "| " ^ state_variable ^ ", None -> " ^ state_variable ^ ", None\n" ^
            "| " ^ state_variable ^ ", Some (se:" ^ !protocol_name ^ "_session_entry) ->\n" ^
            (if od.under_repl && od.following_oracles <> None && od.following_oracles <> (Some []) then
              "  let " ^ state_variable ^ ", " ^ session_id_variable ^ " = state_reserve_session_id " ^ state_variable ^ " in\n"
            else "") ^
            "  match se with\n" ^
            (* And now we treat all definitions of the oracle/returns of the previous oracle.
                We know that we are in a NonTop case because we are in takes_id. *)
            (List.fold_left
              (fun s (nr, bl, p) -> s ^
                "    | R" ^ string_of_int nr ^ "_" ^ alphabetize_string od.oracle_name ^
                (List.fold_left
                  (fun s b ->
                    s ^ " " ^ get_binder_name b)
                  ""
                  bl
                ) ^ " ->\n" ^
                (match p.i_desc with
                | Input (_, pat, p1) ->
                  match_pattern_from_input opt pat args (translate_oprocess od p1) od ("      ")
                | _ -> Parsing_helper.internal_error "expected input process"
                )
              )
              ""
              dl
            )

       )
    )
    oracles
    ""

let get_letfun_interface module_name letfuns =
  preamble module_name ^
  (string_list_sep "\n"
     (List.map
        (fun (f, bl, res) ->
           f.f_impl_needs_state <- needs_state res;
           "val " ^ (get_letfun_name f) ^ " : " ^
           (if f.f_impl_needs_state then (state_type ()) ^ " -> " else "") ^
           (if bl = [] then
              if (not f.f_impl_needs_state) then "unit -> " else ""
            else
              (string_list_sep " -> " (List.map (fun b -> get_type_name b.btype) bl)) ^ " -> "
           ) ^
           (if f.f_impl_needs_state then (state_type ()) ^ " * " else "") ^
           (get_type_name res.t_type) ^ "\n"
        )
        letfuns
     )
  )

let get_letfun_implementation module_name letfuns =
  preamble module_name ^
  (string_list_sep "\n"
     (List.map
        (fun (f,bl,res) ->
           f.f_impl_needs_state <- needs_state res;
           "let " ^ (get_letfun_name f) ^ " " ^
           (if f.f_impl_needs_state then in_parens (state_declaration ()) ^ " " else "") ^
           (if bl = [] then
              if (not f.f_impl_needs_state) then "()" else ""
            else
              (string_list_sep " "
                 (List.map
                    (fun b -> ("(" ^ (get_binder_name b) ^ " : " ^ (get_type_name b.btype) ^ ")")) bl)
              )
           ) ^
           " =\n" ^
           (if f.f_impl_needs_state then
             translate_term_get_pair res "  "
           else
             translate_term_ns res "  ") ^
          "\n"
        )
        letfuns
     )
  )

let check_no_module_name_clash (impl_letfuns, impl_processes) =
  let basic_modules = [
    "Helper"; "NatMap"; "RandomHelper"; "Types"; "Crypto"; "State";
    "Functions"; "Tables"; "Sessions"; "Events"; "Protocol" ] in
  let reserved_modules =
    if impl_letfuns <> [] then letfun_module :: basic_modules else basic_modules
  in
  let rec check_clash = function
    | [] -> ()
    | (x, _, _) :: rest ->
        List.iter
          (fun m ->
             if x = m then error ("Module " ^ x ^ " clashes with reserved module");
             if String.uppercase_ascii x = String.uppercase_ascii m then
               error
                 ( "Module " ^ x ^ " clashes with reserved module " ^ m
                   ^ " (filenames are case-insensitive on Windows)" ))
          reserved_modules;
        List.iter
          (fun (x', _, _) ->
             if String.uppercase_ascii x = String.uppercase_ascii x' then
               error
                 ( "Module " ^ x ^ " clashes with module " ^ x'
                   ^ " (filenames are case-insensitive on Windows)" ))
          rest;
        check_clash rest
  in
  check_clash impl_processes

let input_types pat =
  match !Settings.front_end, pat with
  | _, PatTuple (f, pl) when f.f_name = "" ->
      List.map Terms.get_type_for_pattern pl
  | Settings.Oracles, _ ->
      Parsing_helper.internal_error "oracle must begin with pattern \"\"(...)"
  | Settings.Channels, _ ->
      [Terms.get_type_for_pattern pat]

let output_types t =
  match !Settings.front_end, t.t_desc with
  | _, FunApp(f,tl) when f.f_name="" ->
      List.map (fun t -> t.t_type) tl
  | Settings.Oracles, _ -> Parsing_helper.internal_error "output term not of the form \"\"()"
  | Settings.Channels, _ ->
      [t.t_type]

let user_defined_type t =
  (not (List.memq t built_in_types)) &&
  (match t.tcat with | Interv _ -> false | _ -> true)
let user_defined_function f =
  (not (List.memq f built_in_functions)) &&
  (not (List.memq f built_in_constants))
let in_scope_function f =
  match f.f_impl with
  | No_impl -> false
  | _ -> true

let add_type t =
  if user_defined_type t && not (List.memq t !types) then types := t::!types
let add_eq_type t =
  if user_defined_type t && not (List.memq t !eq_types) then eq_types := t::!eq_types
let add_serde_type t =
  if user_defined_type t && not (List.memq t !serde_types) then serde_types := t::!serde_types
let add_random_type t =
  if user_defined_type t && not (List.memq t !random_types) then random_types := t::!random_types

let add_table tab =
  if not (List.memq tab !tables) then tables := tab::!tables

let add_event e =
  if not (List.memq e !events) then events := e::!events

let add_function f =
  if user_defined_function f && not (List.memq f !functions) then functions := f::!functions

let add_inv_function f =
  if user_defined_function f && not (List.memq f !inv_functions) then inv_functions := f::!inv_functions

let rec get_iprocess_oracles p under_repl previous_oracle nb_of_return =
  match p.i_desc with
  | Nil -> []
  | Input ((c, tl), pat, p1) ->
     List.iter get_term_types tl;
     get_pattern_types pat;
     let (fv, _, _, _) = impl_get_vars p in
     let fv = BinderSet.elements fv in
     (try
       let oracle = StringMap.find c.cname !oracles in
       if oracle.oracle_name <> c.cname then
         error ("Oracle name " ^ oracle.oracle_name ^
           " expected to be " ^ c.cname ^
           " at occ " ^ string_of_int p.i_occ ^ ".")
       else if oracle.under_repl <> under_repl then
         error ("Oracle " ^ oracle.oracle_name ^
           " expected to be "^ (if under_repl then "" else "not ") ^
           " under replication at occ " ^ string_of_int p.i_occ ^ ".")
       else if oracle.previous_oracle <> previous_oracle then
         error ("Oracle " ^ oracle.oracle_name ^
           " does not have the expected same previous oracle as " ^
           "other occurrences of this oracle, at occ " ^
           string_of_int p.i_occ ^ ".")
       else
         let input_type = input_types pat in
         if not (Terms.equal_lists (==) oracle.input_type input_type) then
           error ("Oracle " ^ oracle.oracle_name ^
           " has different input type than other occurrences of this oracle" ^
           ", at occ " ^ string_of_int p.i_occ ^ ".")
       else
         match oracle.list_of_defs with
         | Top p2 ->
             error ("Oracle " ^ oracle.oracle_name ^
               " is a top-level oracle and should not occur multiple times, " ^
               "but does so at occ " ^ string_of_int p.i_occ ^ ".")
         | NonTop l ->
             match previous_oracle with
             | None ->
                 error ("Oracle " ^ oracle.oracle_name ^
                   " is not a top-level oracle but does not have a previous oracle," ^
                   " at occ " ^ string_of_int p.i_occ ^ ".")
             | Some _ -> (
                 oracle.list_of_defs <- NonTop ((nb_of_return, fv, p)::l);
                 get_oprocess_oracles p1 oracle)
     with Not_found ->
       let defl = match previous_oracle with
         | None -> Top p
         | Some prev -> NonTop [(nb_of_return, fv, p)] in
       let oracle = {
         oracle_name = c.cname;
         under_repl = under_repl;
         previous_oracle = previous_oracle;
         input_type = input_types pat;
         output_type = None;
         following_oracles = None;
         list_of_returns = [];
         list_of_defs = defl;
         seen_returns = 0
       } in
     oracles := StringMap.add c.cname oracle !oracles;
     get_oprocess_oracles p1 oracle
	 );
      [c.cname, fv]
  | Par (p1, p2) ->
     (get_iprocess_oracles p1 under_repl previous_oracle nb_of_return) @
     (get_iprocess_oracles p2 under_repl previous_oracle nb_of_return)
  | Repl (_, p1) ->
      get_iprocess_oracles p1 true previous_oracle nb_of_return

and get_oprocess_oracles p0 oracle =
  match p0.p_desc with
  | Yield | EventAbort _ -> ()
  | EventP (e, p) -> get_event_types e; get_oprocess_oracles p oracle
  | Restr (b, p) ->
      add_type b.btype;
      add_random_type b.btype;
      get_oprocess_oracles p oracle
  | Let (pat, t, p1, p2) ->
      get_pattern_types pat;
      get_term_types t;
      get_oprocess_oracles p1 oracle; get_oprocess_oracles p2 oracle
  | Test (t, p1, p2) ->
      get_term_types t;
      get_oprocess_oracles p1 oracle; get_oprocess_oracles p2 oracle
  | Get (tab, patl, topt, p1, p2, _) ->
      add_table tab;
      List.iter add_serde_type tab.tbltype;
      List.iter get_pattern_types patl;
      (match topt with
      | Some t -> get_term_types t
      | None -> ());
      get_oprocess_oracles p1 oracle; get_oprocess_oracles p2 oracle
  | Insert (tab, tl, p) ->
      add_table tab;
      List.iter add_serde_type tab.tbltype;
      List.iter get_term_types tl;
      get_oprocess_oracles p oracle
  | Find (fl, ep, _) -> error "Find not supported"
  | Output ((c, tl), t, p) ->
      List.iter get_term_types tl;
      get_term_types t;
      oracle.seen_returns <- oracle.seen_returns + 1;
      let ot = output_types t in
      (match oracle.output_type with
      | None -> oracle.output_type <- Some ot
      | Some l ->
         if not (Terms.equal_lists (==) l ot) then
           error ("Oracle " ^ oracle.oracle_name ^
           " has different output type than other occurrences of this oracle" ^
           ", at occ " ^ string_of_int p.i_occ ^ ".") );

      let fo = get_iprocess_oracles p false (Some oracle.oracle_name) oracle.seen_returns in
      (match oracle.following_oracles with
      | None -> oracle.following_oracles <- Some (List.map fst fo)
      | Some l ->
      	  if l <> (List.map fst fo) then
            error ("Oracle " ^ oracle.oracle_name ^
              " has different following oracles than other occurrences of this oracle" ^
              ", at occ " ^ string_of_int p.i_occ ^ ".") );
      oracle.list_of_returns <- (oracle.seen_returns, fo, p0) :: oracle.list_of_returns

and get_term_types t =
  match t.t_desc with
  | Var (b, tl) -> add_type b.btype; List.iter get_term_types tl
  | ReplIndex _ -> ()
  | FunApp (f, tl) ->
      (if f.f_name = "" then
        List.iter (fun t -> add_serde_type t.t_type) tl
      else (
        add_function f;
        (* return type *)
        add_type (snd f.f_type);
        (* input types *)
        List.iter add_type (fst f.f_type);
        (match f.f_impl with | FuncEqual | FuncDiff -> add_eq_type (List.hd tl).t_type | _ -> ())
      ));
      List.iter get_term_types tl;
  | TestE (t1, t2, t3) ->
      get_term_types t1;
      get_term_types t2;
      get_term_types t3;
  | FindE _ -> Parsing_helper.input_error "Find not supported (implementation)" t.t_loc
  | LetE (pat, t1, t2, topt) ->
      get_pattern_types pat;
      get_term_types t1;
      get_term_types t2;
      (match topt with
      | Some t3 -> get_term_types t3;
      | None -> ())
  | ResE (b, t) ->
      add_type b.btype;
      add_random_type b.btype;
      get_term_types t
  | EventAbortE _ -> Parsing_helper.input_error "event_abort not supported in F* implementation" t.t_loc
  | EventE (t, p) ->
      get_event_types t;
      get_term_types p
  | InsertE (tbl, tl, t) ->
      add_table tbl;
      List.iter add_serde_type tbl.tbltype;
      List.iter get_term_types tl;
      get_term_types t
  | GetE (tbl, patl, topt, t1, t2, _) ->
      add_table tbl;
      List.iter add_serde_type tbl.tbltype;
      List.iter get_pattern_types patl;
      (match topt with
      | Some t -> get_term_types t
      | None -> ());
      get_term_types t1;
      get_term_types t2

and get_event_types e =
  add_event e;
  match e.t_desc with
  | FunApp (ef, repl_indices :: param_list) ->
      List.iter add_serde_type (List.tl (fst ef.f_type));
      List.iter get_term_types param_list
  | _ -> Parsing_helper.internal_error "Expected FunApp for event (do_implementation)"

and get_pattern_types pat =
  match pat with
  | PatVar b -> add_type b.btype
  | PatTuple (f, pl) ->
      (* As we are in a pattern, it is actually the inverse function that we need. *)
      (if f.f_name = "" then
        List.iter (fun p -> add_serde_type (Terms.get_type_for_pattern p)) pl
      else
        add_function f;
        add_inv_function f;
        add_type (snd f.f_type);
        List.iter add_type (fst f.f_type);
        (* We are generating lemmas for inverse functions, so we need equality test. *)
        add_eq_type (snd f.f_type);
        List.iter add_eq_type (fst f.f_type);
      );
      List.iter get_pattern_types pl
  | PatEqual t -> add_eq_type t.t_type; get_term_types t

let rec descend l =
  let foldfun s t = s && term_contains_no_library_defs t in
  List.fold_left foldfun true l

and descend_pattern l =
  let foldfun s t = s && pattern_contains_no_library_defs t in
  List.fold_left foldfun true l

and term_contains_no_library_defs t =
  match t.t_desc with
  | Var (b, tl) -> descend tl
  | ReplIndex _ -> true
  | FunApp (f, tl) ->
      if f.f_name = "" then
        descend tl
      else
        if not (in_scope_function f)
        then (info ("1 equation will not be translated because there is no implementation for " ^ f.f_name); false)
        else descend tl
  | TestE (t1, t2, t3) ->
      term_contains_no_library_defs t1 &&
      term_contains_no_library_defs t2 &&
      term_contains_no_library_defs t3
  | FindE _ -> Parsing_helper.input_error "Find not supported (implementation)" t.t_loc
  | LetE (pat, t1, t2, topt) ->
      pattern_contains_no_library_defs pat &&
      term_contains_no_library_defs t1 &&
      term_contains_no_library_defs t2 &&
      (match topt with
      | Some t3 -> term_contains_no_library_defs t3
      | None -> true)
  | ResE (b, t) ->
      term_contains_no_library_defs t
  | EventAbortE _ -> Parsing_helper.input_error "event_abort not supported in F* implementation" t.t_loc
  | EventE (t, p) ->
      event_contains_no_library_defs t &&
      term_contains_no_library_defs p
  | InsertE (tbl, tl, t) ->
      descend tl &&
      term_contains_no_library_defs t
  | GetE (tbl, patl, topt, t1, t2, _) ->
      descend_pattern patl &&
      (match topt with
      | Some t -> term_contains_no_library_defs t
      | None -> true) &&
      term_contains_no_library_defs t1 &&
      term_contains_no_library_defs t2

and event_contains_no_library_defs e =
  match e.t_desc with
  | FunApp (ef, repl_indices :: param_list) ->
      descend param_list
  | _ -> Parsing_helper.internal_error "Expected FunApp for event (do_implementation)"

and pattern_contains_no_library_defs p =
  match p with
  | PatVar b -> true
  | PatTuple (f, pl) ->
      if f.f_name = "" then
        descend_pattern pl
      else
        if not (in_scope_function f) then false else
        descend_pattern pl
  | PatEqual t -> term_contains_no_library_defs t

(* translate built-in equational theories *)
let get_fun_equations first_nr =

  let header i =
    "val lemma_" ^ string_of_int i ^ ": " ^
    "unit -> Lemma (\n" in

  (* f is always a binary function with both inputs of the same type
     in the currently supported builtin equational theories. *)
  let typename f =
    (get_type_name (List.hd (fst f.f_type))) in

  let eq_result f =
    equal (snd f.f_type) in

  (* commut is the only equation that supports "not (eq ())" as a function:
     This requires closing an extra ) at the end which we do via the xend parameter. *)
  let commut f x xend =
    "  forall " ^
    "(a:" ^ typename f ^ ") " ^
    "(b:" ^ typename f ^ ") " ^
    ". " ^
    eq_result f ^ " (" ^ x ^ " a b" ^ xend ^ ") (" ^ x ^ " b a" ^ xend ^ "))\n\n" in
    (* the last closing ) is closing the header *)

  let assoc f x =
    "  forall " ^
    "(a:" ^ typename f ^ ") " ^
    "(b:" ^ typename f ^ ") " ^
    "(c:" ^ typename f ^ ") " ^
    ". " ^
    eq_result f ^ " (" ^ x ^ " a (" ^ x ^ " b c)) (" ^ x ^ " (" ^ x ^ " a b) c))\n\n" in

  let neutral f x n =
    "  forall " ^
    "(a:" ^ typename f ^ ") " ^
    ". (" ^
    eq_result f ^ " (" ^ x ^ " a " ^ n ^ ") a) /\\ (" ^
    eq_result f ^ "(" ^ x ^ " " ^ n ^ " a) a))\n\n" in

  let cancel f x n =
    "  forall " ^
    "(a:" ^ typename f ^ ") " ^
    ". " ^
    eq_result f ^ " (" ^ x ^ " a a) " ^ n ^ ")\n\n" in

  let inverse f x n inv =
    "  forall " ^
    "(a:" ^ typename f ^ ") " ^
    ". " ^
    eq_result f ^ " (" ^ x ^ " a (" ^ inv ^ " a)) " ^ n ^ " /\\ " ^
    eq_result f ^ " (" ^ x ^ " (" ^ inv ^ " a) a) " ^ n ^ ")\n\n" in

  let translate_eq_th f x xend s i =
    (match f.f_eq_theories with
    | NoEq -> s, i
    | Commut ->
        s ^ debug_comment "Commut" ^
        header i ^
        commut f x xend
        , i + 1
    | Assoc ->
        s ^ debug_comment "Assoc" ^
        header i ^
        assoc f x
        , i + 1
    | AssocCommut ->
        s ^ debug_comment "AssocCommut" ^
        header i ^
        commut f x xend ^
        header (i + 1) ^
        assoc f x
        , i + 2
    | AssocN (_, n) ->
        (match n.f_impl with
          | Const const ->
              s ^ debug_comment "AssocN" ^
              header i ^
              assoc f x ^
              header (i + 1) ^
              neutral f x const
              , i + 2
          | SepFun | Func _ | FuncEqual | FuncDiff ->
              Parsing_helper.internal_error "Expected a constant as second parameter to assocU."
          | No_impl ->
              info ("  1 builtin equation will not be translated because there is no implementation for " ^ n.f_name);
              s, i)
    | AssocCommutN (_, n) ->
        (match n.f_impl with
          | Const const ->
              s ^ debug_comment "AssocCommutN" ^
              header i ^
              commut f x xend ^
              header (i + 1) ^
              assoc f x ^
              header (i + 2) ^
              neutral f x const
              , i + 3
          | SepFun | Func _ | FuncEqual | FuncDiff ->
              Parsing_helper.internal_error "Expected a constant as second parameter to ACU."
          | No_impl ->
              info ("  1 builtin equation will not be translated because there is no implementation for " ^ n.f_name);
              s, i)
    | Group (_, inv, n) ->
        (match n.f_impl with
          | Const const ->
              (match inv.f_impl with
                | Func invx ->
                    s ^ debug_comment "Group" ^
                    header i ^
                    assoc f x ^
                    header (i + 1) ^
                    neutral f x const ^
                    header (i + 2) ^
                    inverse f x const invx
                    , i + 3
                | Const _ | SepFun | FuncEqual | FuncDiff -> Parsing_helper.internal_error "Expected a non-constant function as second parameter to group."
                | No_impl ->
                    info ("  1 builtin equation will not be translated because there is no implementation for " ^ inv.f_name);
                    s, i)
          | SepFun | Func _ | FuncEqual | FuncDiff ->
              Parsing_helper.internal_error "Expected a constant as third parameter to group."
          | No_impl ->
              info ("  1 builtin equation will not be translated because there is no implementation for " ^ n.f_name);
              s, i)
    | CommutGroup (_, inv, n) ->
        (match n.f_impl with
          | Const const ->
              (match inv.f_impl with
                | Func invx ->
                    s ^ debug_comment "CommutGroup" ^
                    header i ^
                    assoc f x ^
                    header (i + 1) ^
                    commut f x xend ^
                    header (i + 2) ^
                    neutral f x const ^
                    header (i + 3) ^
                    inverse f x const invx
                    , i + 4
                | Const _ | SepFun | FuncEqual | FuncDiff -> Parsing_helper.internal_error "Expected a non-constant function as second parameter to commut_group."
                | No_impl ->
                    info ("  1 builtin equation will not be translated because there is no implementation for " ^ inv.f_name);
                    s, i)
          | SepFun | Func _ | FuncEqual | FuncDiff ->
              Parsing_helper.internal_error "Expected a constant as third parameter to commut_group."
          | No_impl ->
              info ("  1 builtin equation will not be translated because there is no implementation for " ^ n.f_name);
              s, i)
    | ACUN (_, n) ->
        (match n.f_impl with
          | Const const ->
              s ^ debug_comment "ACUN" ^
              header i ^
              commut f x xend ^
              header (i + 1) ^
              assoc f x ^
              header (i + 2) ^
              neutral f x const ^
              header (i + 3) ^
              cancel f x const
              , i + 4
          | SepFun | Func _ | FuncEqual | FuncDiff ->
              Parsing_helper.internal_error "Expected a constant as second parameter to ACUN."
          | No_impl ->
              info ("  1 builtin equation will not be translated because there is no implementation for " ^ n.f_name);
              s, i)
    ) in

  List.fold_left
    (fun (s, i) f ->
      (* We ignore f_plus and f_mul explicitly because they cannot have an implementation
         and we do not want a useless warning about that. *)
      if f.f_eq_theories <> NoEq && f <> Settings.f_plus && f <> Settings.f_mul then (
        match f.f_impl with
        | Func x -> translate_eq_th f x "" s i
        | Const _ | SepFun -> Parsing_helper.internal_error "Expected a non-constant non-letfun function as subject of a builtin equation."
        | FuncEqual ->
          let eq = equal (List.hd (fst f.f_type)) in
          translate_eq_th f eq "" s i
        | FuncDiff ->
          let eq = equal (List.hd (fst f.f_type)) in
          translate_eq_th f ("not (" ^ eq) ")" s i
        | No_impl ->
            info ("  1 builtin equation will not be translated because there is no implementation for " ^ f.f_name);
            s, i)
      else s, i)
    ("", first_nr)
    (List.append built_in_functions !functions)

let rec fold_enum l s f i =
  match l with
  | [] -> Parsing_helper.internal_error "Table without entries."
  | [t] -> f t i
  | t::r -> f t i ^ s ^ fold_enum r s f (i+1)


let gen_str_tables_interface () =

  let str_table_name = "type " ^ !protocol_name ^ "_table_name: eqtype =\n" ^
    List.fold_left
      (fun s t -> s ^ "  | " ^ get_table_name t.tblname ^ "\n")
      ""
      !tables in

  let rec fold_last l tn =
    match l with
    | [] -> error "Table without entries."
    | [t] -> "_:" ^ get_type_name t ^ "{tn == " ^ get_table_name tn ^ "} -> "
    | t::r -> get_type_name t ^ " -> " ^ fold_last r tn in

  let str_table_entry = "noeq type " ^ !protocol_name ^ "_table_entry (tn:" ^ !protocol_name ^ "_table_name) =\n" ^
    List.fold_left
      (fun s t -> s ^ "  | " ^ get_table_entry_name t.tblname ^ ": " ^
        fold_last t.tbltype t.tblname ^
        !protocol_name ^ "_table_entry tn\n"
      )
      ""
      !tables in

  let str_table_static =
    "let " ^ !protocol_name ^ "_table (tn: " ^ !protocol_name ^ "_table_name) = table " ^ !protocol_name ^ "_table_entry tn\n\n" ^
    "let " ^ !protocol_name ^ "_table_empty (tn: " ^ !protocol_name ^ "_table_name) = table_empty " ^ !protocol_name ^ "_table_entry tn\n\n" ^
    "val " ^ !protocol_name ^ "_tables:Type0\n\n" ^
    "val " ^ !protocol_name ^ "_init_tables:" ^ !protocol_name ^ "_tables\n\n" ^
    "val " ^ !protocol_name ^ "_return_table (tabs: " ^ !protocol_name ^ "_tables) (tn: " ^ !protocol_name ^ "_table_name) : " ^ !protocol_name ^ "_table tn\n\n" ^
    "val " ^ !protocol_name ^ "_update_tables (tabs: " ^ !protocol_name ^ "_tables) (tn: " ^ !protocol_name ^ "_table_name) (tab: " ^ !protocol_name ^ "_table tn) : " ^ !protocol_name ^ "_tables\n\n" ^
    "let " ^ !protocol_name ^ "_table_type = TableType (" ^ !protocol_name ^ "_table_name) (" ^ !protocol_name ^ "_table_entry) (" ^ !protocol_name ^ "_tables) (" ^ !protocol_name ^ "_init_tables) (" ^ !protocol_name ^ "_return_table) (" ^ !protocol_name ^ "_update_tables)\n\n" ^
    "val " ^ !protocol_name ^ "_print_table_entry: #tn:" ^ !protocol_name ^ "_table_name -> " ^ !protocol_name ^ "_table_entry tn -> FStar.All.ML unit\n\n" ^
    "val " ^ !protocol_name ^ "_tablename_to_str: " ^ !protocol_name ^ "_table_name -> string\n\n" ^
    "val " ^ !protocol_name ^ "_print_tables: #stt:state_type{tt_of stt == " ^ !protocol_name ^ "_table_type} -> state stt -> FStar.All.ML unit\n\n" in

  "module " ^ !protocol_name_allcaps ^ ".Tables\n\n" ^
  "open CVTypes\n" ^
  "open " ^ !protocol_name_allcaps ^ ".Types\n" ^
  "open State\n\n" ^
  str_table_name ^ "\n" ^
  str_table_entry ^ "\n" ^
  str_table_static ^ "\n"


let gen_str_tables_impl () =

  let str_table_record = "noeq type " ^ !protocol_name ^ "_tables = {\n" ^
    (List.fold_left
      (fun s t -> s ^ "  " ^ get_table_name_lowercase t.tblname ^ ":" ^ !protocol_name ^ "_table " ^ get_table_name t.tblname ^ ";\n")
      ""
      !tables) ^
    "}"
  in

  let str_table_init = "let " ^ !protocol_name ^ "_init_tables =\n" ^
    "  {\n" ^
    (List.fold_left
      (fun s t -> s ^ "    " ^ get_table_name_lowercase t.tblname ^ " = " ^ !protocol_name ^ "_table_empty " ^ get_table_name t.tblname ^ ";\n")
      ""
      !tables) ^
    "  }"
  in

  let str_table_return = "let " ^ !protocol_name ^ "_return_table (tabs: " ^ !protocol_name ^ "_tables) (tn: " ^ !protocol_name ^ "_table_name) : " ^ !protocol_name ^ "_table tn =\n" ^
    "  match tn with\n" ^
    (List.fold_left
      (fun s t -> s ^ "  | " ^ get_table_name t.tblname ^ " -> tabs." ^ get_table_name_lowercase t.tblname ^ "\n")
      ""
      !tables)
  in

  let str_table_update = "let " ^ !protocol_name ^ "_update_tables (tabs: " ^ !protocol_name ^ "_tables) (tn: " ^ !protocol_name ^ "_table_name) (tab: " ^ !protocol_name ^ "_table tn) : " ^ !protocol_name ^ "_tables =\n" ^
    "  match tn with\n" ^
    (List.fold_left
      (fun s t -> s ^ "  | " ^ get_table_name t.tblname ^ " -> { tabs with " ^ get_table_name_lowercase t.tblname ^ " = tab }\n")
      ""
      !tables)
  in

  let str_table_print_entry = "let " ^ !protocol_name ^ "_print_table_entry e =\n" ^
    "  IO.print_string \"{\"; IO.print_newline ();\n" ^
    "  match e with\n" ^
    List.fold_left
      (fun s t -> s ^ "  | " ^ get_table_entry_name t.tblname ^ " " ^
        fold_enum t.tbltype " " (fun t i -> "var" ^ string_of_int i) 0 ^ " ->\n" ^
        fold_enum t.tbltype "" (fun t i -> "    print_label_bytes " ^ "\"" ^ get_type_name t ^ "\" (" ^ get_write_serial t ^ " var" ^ string_of_int i ^ ") true;\n") 0 ^
        "    IO.print_string \"}\"; IO.print_newline ()\n"
      )
      ""
      !tables in

  let str_table_to_string = "let " ^ !protocol_name ^ "_tablename_to_str t = match t with\n" ^
    List.fold_left
      (fun s t -> s ^ "  | " ^ get_table_name t.tblname ^ " -> \"" ^ t.tblname ^ "\"\n")
      ""
      !tables in

  let str_table_print = "let " ^ !protocol_name ^ "_print_tables st =\n" ^
    "  List.iter (fun e -> print_table st e (" ^ !protocol_name ^ "_tablename_to_str e) (" ^ !protocol_name ^ "_print_table_entry #e)) [" ^
    String.concat ";" (List.map (fun t -> get_table_name t.tblname) !tables) ^ "]" in

  "module " ^ !protocol_name_allcaps ^ ".Tables\n\nopen CVTypes\nopen " ^ !protocol_name_allcaps ^ ".Types\nopen State\n\n" ^
  str_table_record ^ "\n" ^
  str_table_init ^ "\n" ^
  str_table_return ^ "\n" ^
  str_table_update ^ "\n" ^
  str_table_print_entry ^ "\n" ^
  str_table_to_string ^ "\n" ^
  str_table_print ^ "\n"


let gen_str_events_interface () =
  let str_events = "noeq type " ^ !protocol_name ^ "_event =\n" ^
    List.fold_left
      (fun s e ->
        match e.t_desc with
        | FunApp (ef, _) -> s ^ "  | Event_" ^ ef.f_name ^ ": " ^
            (List.fold_left
              (fun s t -> s ^ get_type_name t ^ " -> ")
              ""
             (* ignore the first element from e and s: it is the bitstring corresponding to the replication indices. *)
             (List.tl (fst ef.f_type))) ^
            !protocol_name ^ "_event\n"
        | _ -> Parsing_helper.internal_error "Expected FunApp for event (do_implementation)"
      )
      ""
      !events in

  let str_events_print = "val " ^ !protocol_name ^ "_print_event: " ^ !protocol_name ^ "_event -> FStar.All.ML unit" in

  "module " ^ !protocol_name_allcaps ^ ".Events\n\n" ^
  "open CVTypes\n" ^
  "open " ^ !protocol_name_allcaps ^ ".Types\n" ^
  "open State\n\n" ^
  str_events ^ "\n" ^
  str_events_print


let gen_str_events_impl () =
  let str_events_print_let = "let " ^ !protocol_name ^ "_print_event e =\n" ^
    "  match e with\n" ^
    List.fold_left
      (fun s e ->
        match e.t_desc with
        | FunApp (ef, _) ->
	    let tyl = List.tl (fst ef.f_type) in
	    if tyl = [] then
	      s ^ "  | Event_" ^ ef.f_name ^ " ->\n" ^
	      "    IO.print_string \"" ^ ef.f_name ^ "\"; IO.print_newline ()\n"
	    else
	      s ^ "  | Event_" ^ ef.f_name ^ " " ^
              fold_enum tyl " " (fun e i -> "var" ^ string_of_int i) 0 ^ " ->\n" ^
              "    IO.print_string \"" ^ ef.f_name ^ ": { \";\n" ^
              fold_enum tyl "" (fun e i -> "    print_label_bytes " ^ " \"" ^ get_type_name e ^ "\" (" ^ get_write_serial e ^ " var" ^ string_of_int i ^ ") true;\n") 0 ^
              "    IO.print_string \"}\"; IO.print_newline ()\n"
        | _ -> Parsing_helper.internal_error "Expected FunApp for event (do_implementation)"
      )
      ""
      !events in

  "module " ^ !protocol_name_allcaps ^ ".Events\n\n" ^
  "open CVTypes\n" ^
  "open " ^ !protocol_name_allcaps ^ ".Types\n\n" ^
  str_events_print_let


let foreach_oracle oracles_for_modules f init =
  List.fold_left
    (fun s (_, _, oracles) -> StringMap.fold f oracles s)
    init
    oracles_for_modules

let foreach_following_oracle oracles_for_modules f init =
  foreach_oracle oracles_for_modules
    (fun _ od s ->
      List.fold_left
        (fun s (nr, ol, _) ->
          List.fold_left
            (fun s (name, bl) -> f s nr name bl)
            s
            ol)
        s
        od.list_of_returns)
  init


let gen_str_sessions_interface oracles_for_modules =
  (* Generate types for session states *)
  let str_oracle_name =
    foreach_oracle oracles_for_modules (fun name od s -> s ^ "  | " ^ get_oracle_name name ^ "\n")
      ("type " ^ (!protocol_name) ^ "_oracle_name: eqtype =\n") in

  let str_session_entry =
    foreach_following_oracle oracles_for_modules
      (fun s nr name bl ->
        s ^ "  | R" ^ string_of_int nr ^ "_" ^ alphabetize_string name ^ ": " ^
        (List.fold_left
          (fun s b ->
            s ^ get_binder_name b ^ ":" ^ (add_serde_type b.btype; get_type_name b.btype) ^ " -> ")
          ""
          bl) ^
        (!protocol_name) ^ "_session_entry\n")
      ("noeq type " ^ (!protocol_name) ^ "_session_entry =\n") in

  let str_session_entry_to_name =
    foreach_following_oracle oracles_for_modules
      (fun s nr name bl ->
        s ^ "  | R" ^ string_of_int nr ^ "_" ^ alphabetize_string name ^ " " ^
        (List.fold_left
          (fun s b ->
            s ^ "_ ")
          ""
          bl) ^
        "-> " ^ get_oracle_name name ^ "\n")
      ("let " ^ (!protocol_name) ^ "_session_entry_to_name se =\n" ^
       "  match se with\n") in

  let str_following_oracles =
    foreach_oracle oracles_for_modules
      (fun name od s ->
        s ^ "  | " ^ get_oracle_name name ^ " -> [" ^
        (match od.following_oracles with
        | None | Some [] -> ""
        | Some fol ->
            (List.fold_left
              (fun s name -> (match s with | "" -> "" | _ -> s ^ "; ") ^ get_oracle_name name)
              ""
              fol)) ^
        "]\n")
      ("let " ^ (!protocol_name) ^ "_following_oracles on =\n" ^
       "  match on with\n") in

  let str_session_rest =
    "val " ^ !protocol_name ^ "_print_session_entry: " ^ !protocol_name ^ "_session_entry -> FStar.All.ML unit\n\n" ^
    "let " ^ !protocol_name ^ "_session_type = SessionType " ^
    !protocol_name ^ "_oracle_name " ^ !protocol_name ^ "_session_entry " ^
    !protocol_name ^ "_following_oracles " ^ !protocol_name ^ "_session_entry_to_name\n\n"
  in

  "module " ^ !protocol_name_allcaps ^ ".Sessions\n\n" ^
  "open CVTypes\n" ^
  "open " ^ !protocol_name_allcaps ^ ".Types\n" ^
  "open State\n\n" ^
  str_oracle_name ^ "\n\n" ^
  str_session_entry ^ "\n\n" ^
  str_session_entry_to_name ^ "\n\n" ^
  str_following_oracles ^ "\n\n" ^
  str_session_rest


let gen_str_sessions_impl oracles_for_modules =
  let str_session_print_entry =
    foreach_following_oracle oracles_for_modules
      (fun s nr name bl ->
        s ^ "  | R" ^ string_of_int nr ^ "_" ^ alphabetize_string name ^ " " ^
        (List.fold_left
          (fun s b ->
            s ^ get_binder_name b ^ " ")
          ""
          bl) ^
        " ->\n" ^
        "    IO.print_string \"R" ^ string_of_int nr ^ "_" ^ name ^ ": {\\n\";\n" ^
        (List.fold_left
          (fun s b ->
            s ^ "    print_label_bytes \"" ^ get_binder_name b ^ "\" (" ^ get_write_serial b.btype ^ " " ^ get_binder_name b ^ ") true;\n")
          ""
          bl) ^
        "    IO.print_string \"}\\n\"\n"
      )
      ("let " ^ (!protocol_name) ^ "_print_session_entry se =\n" ^
       "  match se with\n") in

  "module " ^ !protocol_name_allcaps ^ ".Sessions\n\n" ^
  "open CVTypes\n" ^
  "open " ^ !protocol_name_allcaps ^ ".Types\n" ^
  "open State\n\n" ^
  str_session_print_entry


let gen_str_protocol () =

  let str_protocol =
    (* state_type *)
    "let " ^ !protocol_name ^ "_state_type = StateType " ^
    !protocol_name ^ "_table_type " ^
    !protocol_name ^ "_session_type " ^
    !protocol_name ^ "_event\n\n" ^
    (* state *)
    "type " ^ !protocol_name ^ "_state = state " ^
    !protocol_name ^ "_state_type\n\n" ^
    (* print_session *)
    "let " ^ !protocol_name ^ "_print_session (st: " ^
    !protocol_name ^ "_state) (" ^ session_id_variable ^ ": nat) : FStar.All.ML unit =\n" ^
    "  print_session #" ^ !protocol_name ^ "_state_type st " ^
    !protocol_name ^ "_print_session_entry " ^ session_id_variable ^ "\n"
  in

  "module " ^ !protocol_name_allcaps ^ ".Protocol\n\n" ^
  "open CVTypes\n" ^
  "open " ^ !protocol_name_allcaps ^ ".Types\n" ^
  "open " ^ !protocol_name_allcaps ^ ".Tables\n" ^
  "open " ^ !protocol_name_allcaps ^ ".Sessions\n" ^
  "open " ^ !protocol_name_allcaps ^ ".Events\n" ^
  "open State\n\n" ^
  str_protocol


let gen_str_types () =
  let str_types = List.fold_left
    (fun s t ->
      s ^
       match t.timplsize with
       | None -> "val " ^ get_type_name t ^ ": Type0\n"
       | Some l -> "" (* not generating anything for fixed types *))
    ""
    !types
  in

  let str_eq_types = List.fold_left
    (fun s t ->
      s ^
      (match t.timplsize with
      | None -> "val " ^ equal t ^ ": " ^ get_type_name t ^ " -> " ^ get_type_name t ^ " -> bool\n\n"
      | Some _ -> "")
    )
    ""
    !eq_types
  in

  let str_serde_types = List.fold_left
    (fun s t ->
      s ^
      (match t.timplsize with
      | None -> "val " ^ get_write_serial t ^ ": " ^ get_type_name t ^ " -> " ^ get_type_name Settings.t_bitstring ^ "\n" ^
                "val " ^ get_read_serial t ^ ": " ^ get_type_name Settings.t_bitstring ^ " -> option (" ^ get_type_name t ^ ")\n\n"
      | Some _ -> "")
    )
    ""
    !serde_types
  in

  let str_random_types = List.fold_left
    (fun s t ->
      s ^
      (match t.timplsize with
      | None -> "val " ^ get_random t ^ ": entropy -> entropy * " ^ get_type_name t ^ "\n\n"
      | Some _ -> "")
    )
    ""
    !random_types
  in

  "module " ^ !protocol_name_allcaps ^ ".Types\n\n" ^
  "open CVTypes\n\n" ^
  str_types ^ "\n\n" ^
  str_eq_types ^ "\n\n" ^
  str_serde_types ^ "\n\n" ^
  str_random_types


let gen_str_functions () =
  let str_functions =
    List.fold_left
      (fun s f ->
        s ^
        match f.f_impl with
        | Func x ->
            "val " ^ x ^ ": " ^
            (* parameter types *)
            (List.fold_left
              (fun s t -> s ^ get_type_name t ^ " -> ")
              ""
              (fst f.f_type)) ^
            (* additional types when needing entropy *)
            (if f.f_impl_ent then "entropy -> entropy * " else "") ^
            (* return type *)
            get_type_name (snd f.f_type) ^ "\n\n" ^

            (* inverse *)
            (if List.memq f !inv_functions then
              (match f.f_impl_inv with
              | None ->
                  (* if we have this error message here, we would no longer need it in match_pattern_complex(_ns) *)
                  error ("Inverse function of " ^ f.f_name ^ " not registered. Add a line 'implementation fun " ^ f.f_name ^ "=\"f1\" [inverse = \"f2\"].' in the source.")
              | Some inv ->

                  "val " ^ inv ^ ": " ^
                  (* parameter is the return type *)
                  get_type_name (snd f.f_type) ^
                  (* return type is option of the input type *)
                  " -> option (" ^
                  (String.concat " * " (List.map
                    (fun t -> get_type_name t)
                    (fst f.f_type))) ^ ")\n\n")
             else "")

        | Const x ->
            "val " ^ x ^ ": " ^
            get_type_name (snd f.f_type) ^ "\n\n"
        | SepFun | FuncEqual | FuncDiff -> ""
        | No_impl -> error ("Function or constant not registered:" ^ f.f_name))
      ""
      !functions
  in

  "module " ^ !protocol_name_allcaps ^ ".Functions\n\n" ^
  "open CVTypes\n" ^
  "open " ^ !protocol_name_allcaps ^ ".Types\n\n" ^
  str_functions


let gen_str_equations translatable_equations =

  let is_trivial_equation t =
    match t.t_desc with
    | FunApp (f, _) -> f = Settings.c_true
    | _ -> false
  in

  let (str_equations, last_nr) = List.fold_left
    (fun (s, i) (bl, t, t_if) ->
      (let binders = (List.fold_left
          (fun s b ->
            s ^ "(" ^ get_binder_name b ^ ":" ^ get_type_name b.btype ^ ") ")
          ""
          bl) in
      let equation = (* side condition *)
        (if is_trivial_equation t_if then "" else
          ("  (" ^ (translate_term_ns t_if "  ") ^ "\n" ^
          "  ) =>\n")) ^
        (* main equation *)
        ("  " ^ translate_term_ns t "  ") in

      s ^

      (* Not using this style at the moment because it is hard
         to control the SMTPat for general equations:
         We want to avoid using `not` in an SMTPat, for example.
      "val lemma_" ^ string_of_int i ^ "_inner " ^
      (* Binder List *)
      (if bl = [] then "(_:unit) " else binders) ^
      " : Lemma (\n" ^
      equation ^ ")\n" ^
      " [SMTPat (" ^ equation ^ ")]\n\n" ^


      "let lemma_" ^ string_of_int i ^ " " ^
      "() : Lemma (\n" ^
      (* Binder List *)
      (if bl = [] then "" else
        "  forall " ^ binders ^ ".\n"
      ) ^
      equation ^ ") = ()\n\n" *)

      "val lemma_" ^ string_of_int i ^ ": " ^
      "unit -> Lemma (\n" ^
      (* Binder List *)
      (if bl = [] then "" else
        "  forall " ^ binders ^ ".\n"
      ) ^
      equation ^ ")\n\n"
      , i + 1)
    )
    ("", 0)
    translatable_equations
  in

  let (str_inv_equations, last_nr) = List.fold_left
    (fun (s, i) f ->
      (match f.f_impl with
      | Func x when f.f_name <> "" ->
          (match f.f_impl_inv with
          | Some inv ->
              (* inv (f a) = Some (a) *)
              let inv_f =
                let binders = create_local_names "x" 0 (List.length (fst f.f_type)) in
                let binders_pat = create_local_names "y" 0 (List.length (fst f.f_type)) in
                let str_parameters = (List.fold_left2
                  (fun s b t ->
                    s ^ "(" ^ b ^ ":" ^ get_type_name t ^ ") ")
                  ""
                  binders
                  (fst f.f_type)) in
                let function_call = inv ^ " (" ^ x ^ " " ^
                  (if binders = [] then "()" else
                  (String.concat " " binders)) ^ ")" in
                let equation =
                  (* main equation *)
                  "  match " ^ function_call ^
                  " with\n" ^
                  "  | Some (" ^
                  (String.concat ", " binders_pat) ^ ") ->\n" ^
                  "      " ^
                  (if binders = [] then "True" else
                  (String.concat " /\\\n      " (List.mapi
                    (fun i t ->
                      (equal t) ^ " " ^ (List.nth binders i) ^ " " ^ (List.nth binders_pat i))
                    (fst f.f_type)
                  ))) ^ "\n" ^
                  "  | None -> False"
                in
                "val lemma_" ^ string_of_int i ^ "_inner " ^
                (if binders = [] then "(_:unit) " else str_parameters) ^
                " : Lemma (" ^
                equation ^ ")\n" ^
                "[SMTPat (" ^
                function_call ^
                ")]\n\n" ^

                "let lemma_" ^ string_of_int i ^ " " ^
                "() : Lemma (\n" ^
                (* Binder List *)
                (if binders = [] then ""
                else "  forall " ^
                str_parameters ^
                ".\n") ^
                equation ^
                ") = ()\n\n"
              in
              (* f (inv a) = a *)
              let f_inv =
                let returns_unit = ((snd f.f_type) = Settings.t_unit) in
                let binders_pat = create_local_names "y" 0 (List.length (fst f.f_type)) in
                let str_parameters = "(x:" ^ get_type_name (snd f.f_type) ^ ")" in
                let function_call = inv ^ (if returns_unit then " () " else " x ") in
                let equation =
                  "  match " ^ function_call ^
                  "  with\n" ^
                  "  | Some (" ^
                  (String.concat ", " binders_pat) ^ ") ->\n" ^
                  "      " ^
                  (if returns_unit then "True" else
                  (equal (snd f.f_type)) ^ " (" ^ x ^ " " ^ (if binders_pat = [] then "()" else String.concat " " binders_pat) ^ ") x"
                  ) ^ "\n" ^
                  "  | None -> " ^
                  (if binders_pat = [] then "True" else
                    "~ (exists " ^
                    (List.fold_left2
                      (fun s b t -> s ^ "(" ^ b ^ ":" ^ get_type_name t ^ ") ")
                      ""
                      binders_pat
                      (fst f.f_type)
                    ) ^
                    ". " ^
                    (equal (snd f.f_type)) ^ " (" ^ x ^ " " ^ (if binders_pat = [] then "()" else String.concat " " binders_pat) ^ ") x)") in

                "val lemma_" ^ string_of_int (i + 1) ^ "_inner " ^
                (if returns_unit then "(_:unit) " else str_parameters) ^
                ": Lemma (" ^
                equation ^
                ")\n" ^
                "[SMTPat (" ^
                function_call ^
                ")]\n\n" ^

                "let lemma_" ^ string_of_int (i + 1) ^ " " ^
                "() : Lemma (\n" ^
                (* Binder List *)
                (if returns_unit then ""
                else "  forall " ^
                str_parameters ^
                ".\n") ^
                equation ^
                ") = ()\n\n"
              in
              s ^ inv_f ^ f_inv
              , i + 2
          | None ->
              (* if we have this error message here, we would no longer need it in match_pattern_complex(_ns) *)
              error ("Inverse function of " ^ f.f_name ^ " not registered. Add a line 'implementation fun " ^ f.f_name ^ "=\"f1\" [inverse = \"f2\"].' in the source.")
          )
      | Func x (*when f.f_name = ""*) -> s, i (* We currently do not translate the tuple/detuple functions *)
      | Const _ | SepFun | FuncEqual | FuncDiff -> Parsing_helper.internal_error "Only non-constant non-letfun functions expected as functions that have an inverse."
      | No_impl -> error ("Function or constant not registered:" ^ f.f_name)
    ))
    ("", last_nr)
    !inv_functions in

  let (str_serde_equations, last_nr) =  List.fold_left
    (fun (s, i) t ->
      (match t.timplsize with
      | None ->
          let deser_fun =
            "  match " ^ get_read_serial t ^ " (" ^ get_write_serial t ^ " a) with\n" ^
            "  | Some b -> " ^ (equal t) ^ " a b\n" ^
            "  | None -> False" in

          let serde_fun =
            "  match " ^ get_read_serial t ^ " a with\n" ^
            "  | Some b -> " ^ (equal Settings.t_bitstring) ^ " (" ^ get_write_serial t ^ " b) a\n" ^
            "  | None -> ~ (exists (b:" ^ get_type_name t ^ "). " ^ equal Settings.t_bitstring ^ " (" ^ get_write_serial t ^ " b) a)" in

          s ^

          "val lemma_" ^ string_of_int i ^ "_inner (a:" ^
          get_type_name t ^ ") : Lemma (" ^
          deser_fun ^
          ")\n" ^
          "[SMTPat (" ^
          get_read_serial t ^ " (" ^ get_write_serial t ^ " a)" ^
          ")]\n\n" ^

          "let lemma_" ^ string_of_int i ^
          " () : Lemma (\n" ^
          "  forall (a:" ^ get_type_name t ^ ").\n" ^
          deser_fun ^
          ") = ()\n\n" ^

          "val lemma_" ^ string_of_int (i + 1) ^ "_inner (a:" ^
          get_type_name Settings.t_bitstring ^ ") : Lemma (" ^
          serde_fun ^
          ")\n" ^
          "[SMTPat (" ^
          get_read_serial t ^ " a" ^
          ")]\n\n" ^

          "let lemma_" ^ string_of_int (i + 1) ^
          " () : Lemma (\n" ^
          "  forall (a:" ^ get_type_name Settings.t_bitstring ^ ").\n" ^
          serde_fun ^
          ") = ()\n\n"
          , i + 2
      | Some _ -> s, i)
    )
    ("", last_nr)
    !serde_types in

  let (str_fun_equations, _) = get_fun_equations last_nr in

  "module " ^ !protocol_name_allcaps ^ ".Equations\n\n" ^
  "open CVTypes\n" ^
  "open " ^ !protocol_name_allcaps ^ ".Types\n" ^
  "open " ^ !protocol_name_allcaps ^ ".Functions\n\n" ^
  str_equations ^
  str_inv_equations ^
  str_serde_equations ^
  str_fun_equations


let print_to_file filename content =
  let f = open_out (Filename.concat !Settings.out_dir filename) in
  output_string f content;
  close_out f


let do_implementation filename (impl_letfuns, impl_processes) equations =
  set_protocol_name filename;
  
  check_no_module_name_clash (impl_letfuns, impl_processes);

  (* Set translations for some built-in types *)
  Settings.t_bitstring.timplname <- Some "bytes";
  Settings.t_bitstring.tequal <- Some "eq_bytes";
  Settings.t_bitstringbot.timplname <- Some "option bytes";
  Settings.t_bitstringbot.tequal <- Some "eq_obytes";
  Settings.t_bool.tserial <- Some ("serialize_bool", "deserialize_bool");
  Settings.f_or.f_impl <- Func "( || )";

  let oracles_for_modules =
     List.map
       (fun (x, opt, p) ->
         oracles := StringMap.empty;
         ignore(get_iprocess_oracles p true None 0);
         (x, opt, !oracles)
	     ) impl_processes
  in

  let translatable_equations = List.filter
    (fun (_, t, t_if) ->
      term_contains_no_library_defs t && term_contains_no_library_defs t_if)
    equations
  in

  if List.length equations <> List.length translatable_equations then (
    info ("Number of translatable equations: " ^ string_of_int (List.length translatable_equations) ^
          " out of " ^ string_of_int (List.length equations) ^ " equations.")
  );

  (* collect types, functions, etc, that are needed to implement all translatable equations *)
  List.iter
    (fun (_, t, t_if) -> get_term_types t; get_term_types t_if)
    translatable_equations;


  if impl_letfuns <> [] then (
    print_string "Generating implementation for letfuns ...\n";

    List.iter
      (fun (_,_,t) -> get_term_types t)
      impl_letfuns;

    (* Inside the Letfun module, we do not need to explicitly use the namespace. *)
    letfun_prefix := "";
    print_to_file (!protocol_name_allcaps ^ "." ^ letfun_module ^ ".fst") (get_letfun_implementation letfun_module impl_letfuns);
    print_to_file (!protocol_name_allcaps ^ "." ^ letfun_module ^ ".fsti") (get_letfun_interface letfun_module impl_letfuns)
  );
  (* In all other modules, we call explicitly into the Letfun namespace. *)
  letfun_prefix := !protocol_name_allcaps ^ "." ^ letfun_module ^ ".";

  print_string ("Generating Functions module ...\n");
  print_to_file (!protocol_name_allcaps ^ ".Functions.fsti") (gen_str_functions ());

  print_string ("Generating Table module ...\n");
  print_to_file (!protocol_name_allcaps ^ ".Tables.fsti") (gen_str_tables_interface ());
  print_to_file (!protocol_name_allcaps ^ ".Tables.fst") (gen_str_tables_impl ());

  print_string ("Generating Event module ...\n");
  print_to_file (!protocol_name_allcaps ^ ".Events.fsti") (gen_str_events_interface ());
  print_to_file (!protocol_name_allcaps ^ ".Events.fst") (gen_str_events_impl ());

  print_string ("Generating Session module ...\n");
  print_to_file (!protocol_name_allcaps ^ ".Sessions.fsti") (gen_str_sessions_interface oracles_for_modules);
  print_to_file (!protocol_name_allcaps ^ ".Sessions.fst") (gen_str_sessions_impl oracles_for_modules);

  print_string ("Generating Protocol module ...\n");
  print_to_file (!protocol_name_allcaps ^ ".Protocol.fst") (gen_str_protocol ());

  print_string ("Generating Types module ...\n");
  print_to_file (!protocol_name_allcaps ^ ".Types.fsti") (gen_str_types ());

  print_string ("Generating Equations module ...\n");
  print_to_file (!protocol_name_allcaps ^ ".Equations.fsti") (gen_str_equations translatable_equations);

  (* Modules for oracles *)
  List.iter
    (fun (x, opt, oracles) ->
      print_string ("Generating implementation for module " ^ x ^ " ...\n");
      print_to_file (!protocol_name_allcaps ^ "." ^ x ^ ".fst") (get_implementation x opt oracles);
      print_to_file (!protocol_name_allcaps ^ "." ^ x ^ ".fsti") (get_interface x opt oracles)
    )
    oracles_for_modules
