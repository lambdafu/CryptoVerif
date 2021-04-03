(* Transform the game using an equivalence coming from a cryptographic
   primitive. This is the key operation. 
   This transformation should support if/let/find/new/event inside terms.
*)

open Types

let whole_game = ref Terms.empty_game
(* Dummy game to designate the game just after the crypto transformation,
   before auto_sa_rename. Only its physical address is important *)
let whole_game_middle =
  { proc = Forgotten { text_display = ""; tex_display = None };
    expanded = false;
    game_number = -1;
    current_queries = [] }
let whole_game_next = ref Terms.empty_game

exception OneFailure of failure_reason

let display_failure_reason = function
    Term t -> 
      print_string ("At " ^ (string_of_int t.t_occ) ^ ", term ");
      Display.display_term t;
      print_string " could not be discharged";
      print_newline()
  | UntransformableTerm t ->
      print_string ("At " ^ (string_of_int t.t_occ) ^ ", term ");
      Display.display_term t;
      print_string " could not be discharged\n(it occurs as complex find condition or input channel, so cannot be tranformed)";
      print_newline()
  | RefWithIndicesWithoutMatchingStandardRef((b,l),(b',l')) ->
      Display.display_var b l;
      print_string " is mapped to ";
      Display.display_var b' l';
      print_string ".\nI could not find a usage of ";
      Display.display_binder b;
      print_string " mapped to ";
      Display.display_binder b';
      print_string " in a standard reference.\n"
  | RefWithIndicesWithIncompatibleStandardRef((b,l),(b',l'),k0) ->
      Display.display_var b l;
      print_string " is mapped to ";
      Display.display_var b' l';
      print_string ".\n";
      print_string ("Do not share the first " ^ (string_of_int k0) ^ " sequences of random variables with the expression(s) that map ");
      Display.display_binder b;
      print_string " to ";
      Display.display_binder b';
      print_string " in a standard reference.\n"
  | IncompatibleRefsWithIndices((b1,l1),(b1',l1'),(b2,l2),(b2',l2'),k0) ->
      Display.display_var b1 l1;
      print_string " is mapped to ";
      Display.display_var b1' l1';
      print_string ";\n";
      Display.display_var b2 l2;
      print_string " is mapped to ";
      Display.display_var b2' l2';
      print_string (".\nCommon prefix of length " ^ (string_of_int k0) ^ ".\n");
      print_string ("The corresponding expressions with standard references do not share the first " ^ (string_of_int k0) ^ " sequences of random variables\n.")
  | NoChange ->
      print_string "Nothing transformed\n"
  | NoChangeName bn ->
      print_string ("Nothing transformed using the suggested random variable " ^ (Display.binder_to_string bn) ^ "\n")
  | NoUsefulChange ->
      print_string "The transformation did not use the useful_change oracles, or oracles deemed useful by default.\n"
  | NameNeededInStopMode ->
      print_string "The transformation requires random variables, but you provided none and prevented me from adding some automatically.\n"

let fail failure_reason =
  if (!Settings.debug_cryptotransf) > 0 then
    display_failure_reason failure_reason;
  raise (OneFailure(failure_reason))

type where_info =
    FindCond | Event | ElseWhere

let equal_binder_pair_lists l1 l2 =
  (List.length l1 == List.length l2) && 
  (List.for_all2 (fun (b1,b1') (b2,b2') -> b1 == b2 && b1' == b2') l1 l2)

(* Finds terms that can certainly not be evaluated in the same
   session (because they are in different branches of if/find/let)
   *)

let incompatible_terms = ref []

let add_incompatible l1 l2 =
  List.iter (fun a ->
    List.iter (fun b ->
      if a == b then
	Parsing_helper.internal_error "An expression is compatible with itself!";
      incompatible_terms := (a,b):: (!incompatible_terms)) l2) l1

let rec incompatible_def_term t = 
  match t.t_desc with
    Var(b,l) -> t::(incompatible_def_term_list l)
  | FunApp(f,l) -> t::(incompatible_def_term_list l)
  | ReplIndex _ -> [t]
  | TestE(t1,t2,t3) -> 
      let def1 = incompatible_def_term t1 in
      let def2 = incompatible_def_term t2 in
      let def3 = incompatible_def_term t3 in
      add_incompatible def2 def3;
      t::(def1 @ (def2 @ def3))
  | FindE(l0, t3,_) ->
      let def3 = incompatible_def_term t3 in
      let accu = ref def3 in
      List.iter (fun (bl, def_list, t1, t2) ->
	let def = (incompatible_def_list def_list) 
	    @ (incompatible_def_term t1) 
	    @ (incompatible_def_term t2) in
	add_incompatible (!accu) def;
	accu := def @ (!accu)) l0;
      t::(!accu)
  | LetE(pat, t1, t2, topt) ->
      let def1 = incompatible_def_term t1 in
      let def2 = incompatible_def_pat pat in
      let def3 = incompatible_def_term t2 in
      let def4 = match topt with
	None -> []
      |	Some t3 -> incompatible_def_term t3 
      in
      add_incompatible def3 def4;
      t::(def1 @ def2 @ def3 @ def4)
  | ResE(b,t) ->
      incompatible_def_term t
  | EventAbortE _ -> [t]
  | EventE(t1,p) ->
      let deft1 = incompatible_def_term t1 in
      let defp = incompatible_def_term p in
      t :: deft1 @ defp
  | GetE _ | InsertE _ ->
      Parsing_helper.internal_error "get, insert should have been expanded"

and incompatible_def_term_list = function
    [] -> []
  | (a::l) -> 
      (incompatible_def_term_list l) @ 
      (incompatible_def_term a)

and incompatible_def_list = function
    [] -> []
  | ((b,l)::l') ->
      (incompatible_def_term_list l) @
      (incompatible_def_list l')

and incompatible_def_pat = function
    PatVar b -> []
  | PatTuple (f,l) -> incompatible_def_pat_list l
  | PatEqual t -> incompatible_def_term t

and incompatible_def_pat_list = function
    [] -> []
  | (a::l) -> 
      (incompatible_def_pat_list l) @
      (incompatible_def_pat a)


let rec incompatible_def_process p = 
  match p.i_desc with
    Nil -> []
  | Par(p1,p2) ->
      (incompatible_def_process p1) @
      (incompatible_def_process p2)
  | Repl(b,p) ->
      incompatible_def_process p 
  | Input((c,tl),pat,p) ->
      (incompatible_def_term_list tl) @
      (incompatible_def_pat pat) @
      (incompatible_def_oprocess p)

and incompatible_def_oprocess p =
  match p.p_desc with
    Yield | EventAbort _ -> []
  | Restr(b, p) ->
      incompatible_def_oprocess p 
  | Test(t,p1,p2) ->
      let def1 = incompatible_def_term t in
      let def2 = incompatible_def_oprocess p1 in
      let def3 = incompatible_def_oprocess p2 in
      add_incompatible def2 def3;
      def1 @ (def2 @ def3)
  | Find(l0, p2,_) ->
      let def3 = incompatible_def_oprocess p2 in
      let accu = ref def3 in
      List.iter (fun (bl, def_list, t, p1) ->
	let def = (incompatible_def_list def_list) @
	  (incompatible_def_term t) @
	  (incompatible_def_oprocess p1) in
	add_incompatible (!accu) def;
	accu := def @ (!accu)) l0;
      !accu
  | Output((c,tl),t2,p) ->
      (incompatible_def_term_list tl) @
      (incompatible_def_term t2) @
      (incompatible_def_process p)
  | Let(pat,t,p1,p2) ->
      let def1 = incompatible_def_term t in
      let def2 = incompatible_def_pat pat in
      let def3 = incompatible_def_oprocess p1 in
      let def4 = incompatible_def_oprocess p2 in
      add_incompatible def3 def4;
      def1 @ (def2 @ (def3 @ def4))
  | EventP(t,p) ->
      (incompatible_def_term t) @
      (incompatible_def_oprocess p)
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

let incompatible_defs p = 
  incompatible_terms := [];
  ignore (incompatible_def_process p);
  let result = !incompatible_terms in
  incompatible_terms := [];
  result

(* Flags *)

let stop_mode = ref false
let no_advice_mode = ref false

let gameeq_name_mapping = ref []
let no_other_term = ref false
let user_term_mapping = ref None    
    
(* In case we fail to apply the crypto transformation, we raise the
exception NoMatch, like when matching fails. This facilitates the
interaction with the matching functions, which are used as part of the
test to see whether we can apply the transformation. *)

(* Check if [t] is an instance of [term].
   Variables of term may be substituted by any term, except 
   - variables in name_list_g which must be kept, but may be indexed 
   (always the same indexes for all elements of name_list_g) 
   - variables in name_list_i which may be renamed to variables
   created by "new" of the same type, and indexed (always the same
   indexes for all elements of name_list_i, and the indexes of variables of 
   name_list_g must be a suffix of the indexes of variables in name_list_i)

   If it is impossible, raise NoMatch
   If it may be possible after some syntactic game transformations,
   return the list of these transformations.
   When the returned list is empty, t is an instance of term in the
   sense above.
 *)

(* The flag [global_sthg_discharged] is useful to check that applying the
considered cryptographic transformation is useful; this is needed because
otherwise the advice [SArenaming b] could be given when [b] is in positions
in which it will never be transformed *)
let global_sthg_discharged = ref false
let names_to_discharge = ref ([] : name_to_discharge_t)
let symbols_to_discharge = ref ([] : funsymb list)

let is_name_to_discharge b =
  List.exists (fun (b', _) -> b' == b) (!names_to_discharge)

(* Check if a variable in [names_to_discharge] occurs in [t] *)

let rec occurs_name_to_discharge t =
  match t.t_desc with
    Var(b,l) ->
      (is_name_to_discharge b) || (List.exists occurs_name_to_discharge l)
  | FunApp(f,l) ->
      List.exists occurs_name_to_discharge l
  | ReplIndex _ -> false
  | TestE _ | LetE _ | FindE _ | ResE _ | EventAbortE _ | EventE _ | GetE _ | InsertE _ -> 
      Parsing_helper.internal_error "If, find, let, new, event, event_abort, get, and insert should have been expanded (Cryptotransf.occurs_name_to_discharge)"
      
(* Check if a function symbol in [symbols_to_discharge] occurs in [t] *)

let rec occurs_symbol_to_discharge t =
  match t.t_desc with
    Var(b,l) ->
      List.exists occurs_symbol_to_discharge l
  | FunApp(f,l) ->
      (List.memq f (!symbols_to_discharge)) || (List.exists occurs_symbol_to_discharge l)
  | ReplIndex _ -> false
  | TestE _ | LetE _ | FindE _ | ResE _ | EventAbortE _ | EventE _ | GetE _ | InsertE _ -> 
      Parsing_helper.internal_error "If, find, let, new, event, event_abort, get, and insert should have been expanded (Cryptotransf.occurs_symbol_to_discharge)"
  
(* Association lists (binderref, value) *)

let rec assq_binderref br = function
    [] -> raise Not_found
  | (br',v)::l ->
      if Terms.equal_binderref br br' then
	v
      else
	assq_binderref br l

let rec assq_binder_binderref b = function
    [] -> raise Not_found
  | ((b',l'),v)::l ->
      if (b == b') && (Terms.is_args_at_creation b l') then
	v
      else
	assq_binder_binderref b l

let rec assq_idx l = function
  | [] -> raise Not_found
  | (l', t')::rest ->
      if Terms.equal_term_lists l l' then
	t'
      else
	assq_idx l rest
	  

let check_distinct_links lhs_array_ref_map bl =
  let seen_binders = ref [] in
  List.iter (List.iter (fun (b,_) ->
    try
      match assq_binder_binderref b lhs_array_ref_map with
	{ t_desc = Var(b',l) } -> 
	  if (List.memq b' (!seen_binders)) then 
	    begin
	      if (!Settings.debug_cryptotransf) > 4 then 
		print_string "check_distinct_links fails.\n";
	      raise NoMatch
	    end;
	  seen_binders := b' :: (!seen_binders)
      | _ -> Parsing_helper.internal_error "unexpected link in check_distinct_links"
    with Not_found ->
      (* binder not linked; should not happen when no useless new is
	 present in the equivalence Now happens also for all names of
	 the LHS that are not above the considered expression because
	 bl is the list of all name groups in the LHS, and not only
	 above the considered expression *) 
      ()
	)) bl

(* Suggests a transformation to explicit the value of b
   If there are several of b, we start by SArenaming b,
   they RemoveAssign will probably be suggested at the next
   try (there will now be a single definition for each variable
   replacing b). Advantage: we avoid doing RemoveAssign for copies
   of b for which it is not necessary.
 *)
let explicit_value b =
  match b.def with
    [] | [_] -> RemoveAssign (Binders [b])
  | _ -> SArenaming b

(*
ins_accu stores the advised instructions. 
The structure is the following:
   a list of triples (list of advised instructions, priority, names_to_discharge)
The priority is an integer; the lower integer means the higher priority.
The elements of the list are always ordered by increasing values of priority. 
The transformation may succeed by applying one list of advised instructions.
They will be tried by priority.

*)

let success_no_advice = [([],0,[])]

let is_success_no_advice = function 
    ([],_,_)::_ -> true
  | [] -> Parsing_helper.internal_error "ins_accu should not be empty"
  | _ -> false

(* Adds an advised instruction to ins_accu *)

let add_ins ins ins_accu =
  List.map (fun (l,p,n) -> ((Terms.add_eq ins l), p, n)) ins_accu

(* Makes a "or" between two lists of advised instructions, by merging the lists;
   the list is cut after the empty advice *)

let eq_ins_set l1 l2 =
  (List.for_all (fun i1 -> List.exists (Terms.equal_instruct i1) l2) l1) &&
  (List.for_all (fun i2 -> List.exists (Terms.equal_instruct i2) l1) l2)

let incl_ins_set l1 l2 =
  List.for_all (fun i1 -> List.exists (Terms.equal_instruct i1) l2) l1

let eq_name_set l1 l2 =
  (List.for_all (fun (b1,_) -> List.exists (fun (b2,_) -> b1 == b2) l2) l1) &&
  (List.for_all (fun (b2,_) -> List.exists (fun (b1,_) -> b1 == b2) l1) l2)

(* Adds a set of advised instructions, removing duplicate solutions *)

let add_ins_set (l1,p1,n1) l =
  (l1,p1,n1) :: (List.filter (fun (l2,p2,n2) ->
    not ((eq_name_set n1 n2) && (incl_ins_set l1 l2) && (p1 <= p2))
      ) l)

let rec merge_ins ins_accu1 ins_accu2 =
  match (ins_accu1, ins_accu2) with
    ((l1,p1,n1) as a1)::r1, ((l2,p2,n2) as a2)::r2 ->
      if p1 < p2 then 
	(* Put p1 first *)
	if l1 == [] then
	  [a1]
	else
	  add_ins_set a1 (merge_ins r1 ins_accu2)
      else if p1 > p2 then
	(* Put p2 first *)
	if l2 == [] then
	  [a2]
	else
	  add_ins_set a2 (merge_ins ins_accu1 r2)
      else
	(* Put the shortest list first when priorities are equal *)
	if l1 == [] then
	  [a1]
	else if l2 == [] then
	  [a2]
	else if List.length l1 <= List.length l2 then
	  add_ins_set a1 (merge_ins r1 ins_accu2)
	else
	  add_ins_set a2 (merge_ins ins_accu1 r2)
  | [], ins_accu2 -> ins_accu2
  | ins_accu1, [] -> ins_accu1

let merge_ins_fail f1 f2 =
  try
    let ins1 = f1() in
    try
      if is_success_no_advice ins1 then ins1 else merge_ins ins1 (f2())
    with NoMatch ->
      ins1
  with NoMatch ->
    f2()

(* Makes a "and" between two lists of advised instructions, by concatenating the sublists
   and adding priorities 

   First, "and" between one element and a list
*)

let and_ins1 (l,p,n) ins_accu =
  List.map (fun (l',p',n') -> ((Terms.union Terms.equal_instruct l l'), p+p', 
			       Terms.union (fun (x,_) (y,_) -> x == y) n n')) ins_accu

(* ... then "and" between two ins_accu *)

let rec and_ins ins_accu1 ins_accu2 =
  match ins_accu1 with
    [] -> []
  | lp1::r1 -> merge_ins (and_ins1 lp1 ins_accu2) (and_ins r1 ins_accu2)

  (* Truncate the advice according to the bounds
     max_advice_possibilities_beginning and 
     max_advice_possibilities_end, before doing the actual "and" *)

let truncate_advice ins =
  if ((!Settings.max_advice_possibilities_beginning) <= 0) ||
     ((!Settings.max_advice_possibilities_end) <= 0) then
    (* When the bounds are not positive, we allow an unbounded number
       of advised transformations. May be slow. *)
    ins
  else if List.length ins > !Settings.max_advice_possibilities_beginning + !Settings.max_advice_possibilities_end then
    let (l1,_) = Terms.split (!Settings.max_advice_possibilities_beginning) ins in
    l1 @ (Terms.lsuffix (!Settings.max_advice_possibilities_end) ins)
  else
    ins

let and_ins ins_accu1 ins_accu2 =
  let ins_accu1 = truncate_advice ins_accu1 in
  let ins_accu2 = truncate_advice ins_accu2 in
  and_ins ins_accu1 ins_accu2

(* Map the elements of a list, and make a "and" of the resulting
   advised instructions *)

let rec map_and_ins f = function
    [] -> success_no_advice
  | (a::l) -> and_ins (f a) (map_and_ins f l)

(* For debugging *)

let display_ins ins =
  List.iter (fun (l,p,n) -> Display.display_list Display.display_instruct l;
    print_string " priority: ";
    print_int p;
    print_string " names: ";
    Display.display_list (fun (b, _) -> Display.display_binder b) n;
    print_string "\n") ins

(* State of the system when trying to map a function in an equivalence and
   a subterm of the process

    unchanged_names_useless: true when the term we want to transform
    is in an event and the transformation has a penalty (ie priority)
    greater than Settings.priority_event_unchanged_rand. In this case,
    we do not set sthg_discharged when an unchanged restriction is
    discharged.  Indeed, when only unchanged restrictions are
    discharged, we prefer not applying the transformation and using
    the fact that unchanged restrictions can occur in events.

    advised_ins: list of advised instructions, 
    sthg_discharged, 
    names_to_discharge, 
    priority,
    lhs_array_ref_map: correspondence between variables and names/terms
    name_indexes

   *)

type state_t =
    { (* Part of the state fixed at initialization *)
      simp_facts : simp_facts;
      all_names_exp_opt : (binder * restropt) list list;
      mode : mode;
      unchanged_names_useless : bool;
      (* Part of the state updated during check_instance_of_rec *)
      advised_ins : instruct list;
      sthg_discharged : bool;
      names_to_discharge : name_to_discharge_t;
      priority : int;
      lhs_array_ref_map : ((binder * term list) * term) list;
      name_indexes : ((binder * term list) * term list) list }

let init_state simp_facts all_names_exp_opt mode where_info priority = 
  { simp_facts = simp_facts;
    all_names_exp_opt = all_names_exp_opt;
    mode = mode;
    unchanged_names_useless = (where_info = Event) && (priority >= !Settings.priority_event_unchanged_rand);
    advised_ins = [];
    sthg_discharged  = false;
    names_to_discharge = [];
    priority = 0;
    lhs_array_ref_map = [];
    name_indexes = [] }

let add_name_to_discharge2 (b, bopt) state =
  if List.exists (fun (b', _) -> b' == b) state.names_to_discharge then state else
  { state with names_to_discharge = (b, bopt)::state.names_to_discharge }

let explicit_value_state t state =
  match t.t_desc with
    Var(b,_) -> 
      { state with advised_ins = Terms.add_eq (explicit_value b) state.advised_ins }
  | _ -> Parsing_helper.internal_error "Var expected (should have been checked by is_var_inst)"

(* Intersection of sets of names to discharge, to get the names that must be discharged in all cases *)

let rec intersect_n l1 = function 
    [] -> []
  | ((b,_) as a::l) -> if List.exists (fun (b1,_) -> b1 == b) l1 then a::(intersect_n l1 l) else intersect_n l1 l

let rec get_inter_names = function
    [] -> []
  | [(_,_,a)] -> a
  | (_,_,a)::l -> intersect_n a (get_inter_names l)

(* [get_var_link] function associated to [check_instance_of_rec].
   See the interface of [Terms.match_funapp_advice] for the 
   specification of [get_var_link]. *)

let get_var_link all_names_exp_opt t state =
  match t.t_desc with
    Var (b,l) -> 
      (* return None for restrictions *)
      let is_restr = 
	if Terms.is_args_at_creation b l then
	  List.exists (List.exists (fun (b',_) -> b' == b)) all_names_exp_opt	  
	else 
	  true
      in
      if is_restr then 
	None
      else
	let vlink = 
	  try 
	    TLink (assq_binderref (b,l) state.lhs_array_ref_map)
	  with Not_found -> 
	    NoLink
	in
	Some (vlink, false) (* TO DO I consider that variables cannot be bound to the neutral element.
			       I would be better to allow the user to choose which variables can be bound
			       to the neutral element. *)
  | _ -> None

(* [is_var_inst]: [is_var_inst t] returns true when [t] is a variable
   that may be replaced by a product after applying advice. *)

let is_var_inst t =
  match t.t_desc with
    Var(b,_) ->
      if (!no_advice_mode) || (not (List.exists (function 
        { definition = DProcess { p_desc = Let _ }} -> true
      | { definition = DTerm { t_desc = LetE _ }} -> true
      | _ -> false) b.def)) then
        false
      else
        true
  | _ -> false

(* In check_instance_of_rec, mode = AllEquiv for the root symbol of functions marked [all] 
   in the equivalence. Only in this case a function symbol can be discharged. *)

let rec check_instance_of_rec next_f term t state =
  match (term.t_desc, t.t_desc) with
  | FunApp(f,l), FunApp(f',l') when f == f' ->
      let state' = 
	if (state.mode == AllEquiv) && (List.memq f (!symbols_to_discharge)) then
	  { state with sthg_discharged = true }
	else
	  state
      in
      Match_eq.match_funapp_advice check_instance_of_rec explicit_value_state (get_var_link state.all_names_exp_opt) is_var_inst next_f state.simp_facts term t state'
  | FunApp(f,l), FunApp(_,_) -> 
      raise NoMatch
	(* Might work after rewriting with an equation *)
  | FunApp(f,l), Var(b,_) ->
      begin
	(* Try to use the known facts to replace the variable 
	   with its value *)
      let t' = Terms.try_no_var state.simp_facts t in
      match t'.t_desc with
	Var _ ->
	  if (!no_advice_mode) || (not (List.exists (function 
	      { definition = DProcess { p_desc = Let _ }} -> true
	    | { definition = DTerm { t_desc = LetE _ }} -> true
	    | _ -> false) b.def)) then
	    raise NoMatch
	  else
            (* suggest assignment expansion on b *)
	    next_f { state with advised_ins = Terms.add_eq (explicit_value b) state.advised_ins }
      |	_ -> check_instance_of_rec next_f term t' state
      end
  | FunApp _, ReplIndex _ -> raise NoMatch
  | FunApp(f,l), (TestE _ | FindE _ | LetE _ | ResE _ | EventAbortE _ | EventE _ | GetE _ | InsertE _) ->
      Parsing_helper.internal_error "If, let, find, new, event, event_abort, get, and insert should have been expanded (Cryptotransf.check_instance_of_rec)"
  | Var(b,l), _ when Terms.is_args_at_creation b l ->
      begin
	try 
	  let t' = assq_binderref (b,l) state.lhs_array_ref_map in
	  (* (b,l) is already mapped *)
	  if not (Terms.equal_terms t t') then
	    raise NoMatch
	  else
	    next_f state
	with Not_found ->
	  (* (b,l) is not mapped yet *)
            begin
              try
                let name_group_opt = List.find (List.exists (fun (b',_) -> b' == b)) state.all_names_exp_opt in
		let name_group = List.map fst name_group_opt in
                match t.t_desc with
                  Var(b',l') ->
                    begin
                      (* check that b' is defined by a restriction *)
		      if not (Terms.is_restr b') then 
			begin
			  if (List.for_all (function
			      { definition = DProcess { p_desc = Restr _}} -> true
			    | { definition = DProcess { p_desc = Let _}} -> true
			    | _ -> false) b'.def) && (not (!no_advice_mode))
			  then
			    next_f { state with advised_ins = Terms.add_eq (explicit_value b') state.advised_ins }
			  else
			    begin
			      if (!Settings.debug_cryptotransf) > 6 then
				print_string ("Variable " ^ (Display.binder_to_string b') ^ " should be defined by a restriction.\n");
			      raise NoMatch
			    end
			end
		      else 
			begin
                          (* check that b' is of the right type *)
			  if b'.btype != b.btype then
			    begin
			      if (!Settings.debug_cryptotransf) > 6 then
				print_string ("Variable " ^ (Display.binder_to_string b') ^ " should have type " ^ b.btype.tname ^ " but has type " ^ b'.btype.tname ^ ".\n");
			      raise NoMatch
			    end; 
		          (* check that b' is not used in a query *)
			  if Settings.occurs_in_queries b' (!whole_game).current_queries then 
			    begin
			      if (!Settings.debug_cryptotransf) > 6 then
				print_string ("Variable " ^ (Display.binder_to_string b') ^ " occurs in queries.\n");
			      raise NoMatch
			    end;

			  (* See comment containing Terms.copy_term DeleteFacts: elsewhere in this file *)
			  let state' = { state with lhs_array_ref_map = ((b,l), Terms.copy_term DeleteFacts t):: state.lhs_array_ref_map } in
                          (* Note: when I catch NoMatch, backtrack on names_to_discharge *)
			  let bopt = List.assq b name_group_opt in
			  let state'' = 
			    try 
			      let bopt' = List.assq b' (!names_to_discharge) in
			      if !bopt' == DontKnow then bopt' := bopt else
			      if !bopt' != bopt then
				begin
				(* Incompatible options [unchanged]. May happen when the variable occurs in an event 
				   (so its option [unchanged] is required), but later we see that it does not have option [unchanged] *) 
				  if (!Settings.debug_cryptotransf) > 6 then
				    print_string ("Variable " ^ (Display.binder_to_string b') ^ " occurs in some event and may be changed by the cryptographic transformation.\n");
				  raise NoMatch
				end;
			      if (bopt == Unchanged) && state'.unchanged_names_useless then
				state'
			      else
				{ state' with sthg_discharged = true }
                            with Not_found ->
			      if !stop_mode then 
				begin
				(* Do not add more names in stop_mode *)
				  if (!Settings.debug_cryptotransf) > 6 then
				    print_string ("Cannot add variable " ^ (Display.binder_to_string b') ^ " in stop mode.\n");
				  raise NoMatch
				end
			      else
				add_name_to_discharge2 (b',ref bopt) state'
			  in
			  let group_head = List.hd name_group in
			  try
                            let indexes = assq_binderref (group_head, l) state''.name_indexes in
                            if not (Terms.equal_term_lists indexes l') then
			      begin
				if (!Settings.debug_cryptotransf) > 6 then
				  begin
				    print_string ("Indices of " ^ (Display.binder_to_string b') ^ " are ");
				    Display.display_list Display.display_term l';
				    print_string " but should be ";
				    Display.display_list Display.display_term indexes;
				    print_string ".\n"
				  end;
				raise NoMatch
			      end
			    else
			      next_f state''
			  with Not_found -> 
                            (* Note: when I catch NoMatch, backtrack on all_names_indexes *)
                            next_f { state'' with name_indexes = ((group_head,l), l') :: state''.name_indexes } 
			end
                    end
                | _ -> raise NoMatch
              with Not_found -> 
                begin
                  (* check that t is of the right type *)
                  if t.t_type != b.btype then
		    begin
		      if (!Settings.debug_cryptotransf) > 6 then
			begin
			  print_string "Term ";
			  Display.display_term t;
			  print_string (" should have type " ^ b.btype.tname ^ " but has type " ^ t.t_type.tname ^ ".\n")
			end;
		      raise NoMatch
		    end;
		  (* Terms.copy_term DeleteFacts: When [Settings.use_known_equalities_crypto] is true,
		     a term that occurs elsewhere in the game may end up occurring inside the
		     term [t] due to term copies made by [try_no_var]. 
		     We use [Terms.copy_term DeleteFacts] to make sure that it is not physically equal
		     to the term that appears elsewhere in the game, and we remove the facts.
		     Otherwise, CryptoVerif might use the information collected at the other
		     occurrence of that term to transform it, and that may not be correct.
		     However, we keep the occurrence so that the term can be designated in the [terms: ...] indication. 
		     Other occurrences of Terms.copy_term DeleteFacts in this file come from the same
		     reason. *)
		  next_f { state with lhs_array_ref_map = ((b,l), Terms.copy_term DeleteFacts t):: state.lhs_array_ref_map }
                end
            end
      end
  | Var(b,l), _ -> 
      (* variable used with indices given in argument *)
      begin
	(* Check if (b,l) is already mapped *)
	try 
	  let t' = assq_binderref (b,l) state.lhs_array_ref_map in
	  (* (b,l) is already mapped *)
	  if not (Terms.equal_terms t t') then
	    raise NoMatch
	  else
	    next_f state
	with Not_found ->
	  (* (b,l) is not mapped yet *)
          match t.t_desc with
            Var(b',l') ->
                    begin
                      (* check that b' is defined by a restriction *)
		      if not (Terms.is_restr b') then 
			begin
			  if (List.for_all (function
			      { definition = DProcess { p_desc = Restr _} } -> true
			    | { definition = DProcess { p_desc = Let _} } -> true
			    | _ -> false) b'.def) && (not (!no_advice_mode))
			  then
			    next_f { state with advised_ins = Terms.add_eq (explicit_value b') state.advised_ins }
			  else
			    begin
			      if (!Settings.debug_cryptotransf) > 6 then
				print_string ("Variable " ^ (Display.binder_to_string b') ^ " should be defined by a restriction.\n");
			      raise NoMatch
			    end
			end
		      else 
			begin
                          (* check that b' is of the right type *)
			  if b'.btype != b.btype then 
			    begin
			      if (!Settings.debug_cryptotransf) > 6 then
				print_string ("Variable " ^ (Display.binder_to_string b') ^ " should have type " ^ b.btype.tname ^ " but has type " ^ b'.btype.tname ^ ".\n");
			      raise NoMatch
			    end; 
		          (* check that b' is not used in a query *)
			  if Settings.occurs_in_queries b' (!whole_game).current_queries then 
			    begin
			      if (!Settings.debug_cryptotransf) > 6 then
				print_string ("Variable " ^ (Display.binder_to_string b') ^ " occurs in queries.\n");
			      raise NoMatch
			    end;

			  (* See comment containing Terms.copy_term DeleteFacts: elsewhere in this file *)
			  let state' = { state with lhs_array_ref_map = ((b,l), Terms.copy_term DeleteFacts t)::state.lhs_array_ref_map } in
                          (* Note: when I catch NoMatch, backtrack on names_to_discharge *)
			  try
			    let name_group_opt = List.find (List.exists (fun (b',_) -> b' == b)) state.all_names_exp_opt in
			    let name_group = List.map fst name_group_opt in
			    let group_head = List.hd name_group in
			    let bopt = List.assq b name_group_opt in
			    let state'' = 
			      try 
				let bopt' = List.assq b' (!names_to_discharge) in
				if !bopt' == DontKnow then bopt' := bopt else
				if !bopt' != bopt then
				  begin
				  (* Incompatible options [unchanged]. May happen when the variable occurs in an event 
				     (so its option [unchanged] is required), but later we see that it does not have option [unchanged] *) 
				    if (!Settings.debug_cryptotransf) > 6 then
				      print_string ("Variable " ^ (Display.binder_to_string b') ^ " occurs in some event and may be changed by the cryptographic transformation.\n");
				    raise NoMatch
				  end;
				if (bopt == Unchanged) && state'.unchanged_names_useless then
				  state'
				else
				  { state' with sthg_discharged = true }
                              with Not_found ->
				if !stop_mode then 
				  begin
				  (* Do not add more names in stop_mode *)
				    if (!Settings.debug_cryptotransf) > 6 then
				      print_string ("Cannot add variable " ^ (Display.binder_to_string b') ^ " in stop mode.\n");
				    raise NoMatch
				  end
				else
				  add_name_to_discharge2 (b',ref bopt) state'
			    in
			    try
                              let indexes = assq_binderref (group_head,l) state''.name_indexes in
                              if not (Terms.equal_term_lists indexes l') then
				begin
				  if (!Settings.debug_cryptotransf) > 6 then
				    begin
				      print_string ("Indices of " ^ (Display.binder_to_string b') ^ " are ");
				      Display.display_list Display.display_term l';
				      print_string " but should be ";
				      Display.display_list Display.display_term indexes;
				      print_string ".\n"
				    end;
				  raise NoMatch
				end
			      else
				next_f state''
			    with Not_found -> 
                            (* Note: when I catch NoMatch, backtrack on all_names_indexes *)
			      next_f { state'' with name_indexes = ((group_head,l), l') :: state''.name_indexes } 
			  with Not_found ->
			    Display.display_binder b;
			    print_string " not in ";
			    Display.display_list (Display.display_list (fun (b,_) -> Display.display_binder b)) state.all_names_exp_opt;
			    Parsing_helper.internal_error "Array reference in the left-hand side of an equivalence should always be a reference to a restriction"
			end
                    end
          | _ -> raise NoMatch
      end
  | _ -> Parsing_helper.internal_error "if, find, defined, replication indices should have been excluded from left member of equivalences"

let list_to_term_opt f = function
    [] -> None
  | l ->
      (* See comment containing Terms.copy_term DeleteFacts: elsewhere in this file *)
      Some (Terms.make_prod f (List.map (Terms.copy_term DeleteFacts) l))

(* [comp_neut] is a comparison to the neutral element (of the equational
   theory of the root function symbol of [t]), which should be added
   as a context around the transformed term of [t]. 

   [term] is a term in the left-hand side of an equivalence.
   [t] is a term in the game.
   [check_instance_of] tests whether [t] is an instance of [term].
   It calls [next_f] in case of success, and raises NoMatch in case of failure. *) 

let check_instance_of state0 next_f comp_neut term t =
  if (!Settings.debug_cryptotransf) > 5 then
    begin
      print_string "Check instance of ";
      Display.display_term term;
      print_string " ";
      Display.display_term t;
      print_newline();
    end;
  let next_f product_rest state =
    if not state.sthg_discharged then raise NoMatch;
    if state.advised_ins == [] then
      check_distinct_links state.lhs_array_ref_map state.all_names_exp_opt;
    if (!Settings.debug_cryptotransf) > 4 then
      begin
	print_string "check_instance_of ";
	Display.display_term term;
	print_string " ";
	Display.display_term t;
	if state.advised_ins == [] then
	  print_string " succeeded\n"
	else
	  begin
	    print_string " succeeded with advice ";
	    Display.display_list Display.display_instruct state.advised_ins;
	    print_string " priority: ";
	    print_int state.priority;
	    print_string "\n"
	  end
      end;
    next_f product_rest state
  in
  match term.t_desc with
    FunApp(f,[_;_]) when f.f_eq_theories != NoEq && f.f_eq_theories != Commut &&
      not ((state0.mode == AllEquiv) && (List.memq f (!symbols_to_discharge))) ->
      (* f is a binary function with an equational theory that is
	 not commutativity -> it is a product-like function;
	 when f has to be discharged, we cannot match a subproduct, 
	 because occurrences of f would remain, so we can use the
	 default case below. *)
      let l = Terms.simp_prod Terms.simp_facts_id (ref false) f term in
      let l' = Terms.simp_prod state0.simp_facts (ref false) f t in
      begin
	match f.f_eq_theories with
	  NoEq | Commut -> Parsing_helper.internal_error "Transf_crypto.check_instance_of: cases NoEq, Commut should have been eliminated"
	| AssocCommut | AssocCommutN _ | CommutGroup _ | ACUN _ ->
	    Match_eq.match_AC_advice check_instance_of_rec  
	      explicit_value_state (get_var_link state0.all_names_exp_opt) is_var_inst
	      (fun rest state' -> 
		let product_rest =
		  match rest, comp_neut with
		    [], None -> None
		  | _ -> Some (f, list_to_term_opt f rest, None, comp_neut)
		in
		next_f product_rest state') state0.simp_facts f false false true l l' state0
	| Assoc | AssocN _ | Group _ -> 
	    Match_eq.match_assoc_advice_subterm check_instance_of_rec  
	      explicit_value_state (get_var_link state0.all_names_exp_opt) is_var_inst
	      (fun rest_left rest_right state' ->
		let product_rest =
		  match rest_left, rest_right, comp_neut with
		    [], [], None -> None
		  | _ -> 
		      Some (f, list_to_term_opt f rest_left, 
			    list_to_term_opt f rest_right, comp_neut)
		in
		next_f product_rest state') state0.simp_facts f l l' state0
      end
  | _ -> 
      (* When f is a symbol to discharge in mode [all],
	 the following assertion may not hold. 
	 assert (comp_neut == None); *)
      let product_rest =
	match comp_neut, t.t_desc with
	  None, _ -> None
	| _, FunApp(f, [_;_]) when f.f_eq_theories != NoEq && f.f_eq_theories != Commut -> 
	    (* When [comp_neut] is not None, the root function symbol of [t] has
	       an equational theory that is not NoEq/Commut.
	       Indeed, [comp_neut] is set when we have f(...) = ... and that
	       can be transformed into f(...) = neut using the equational theory of f;
	       [t] is then set to f(...). *)
	    Some(f, None, None, comp_neut)
	| _ -> assert false
      in
      check_instance_of_rec (next_f product_rest) term t state0 

(* Check whether t is an instance of a subterm of term
   Useful when t is just a test (if/find) or an assignment,
   so that by syntactic transformations of the game, we may
   arrange so that a superterm of t is an instance of term *)

let rec check_instance_of_subterms state0 next_f term t =
  let next_f_internal state =
    if not state.sthg_discharged then raise NoMatch;
    if state.advised_ins == [] then
      check_distinct_links state.lhs_array_ref_map state.all_names_exp_opt;
    if (!Settings.debug_cryptotransf) > 5 then
      begin
	print_string "check_instance_of_subterms ";
	Display.display_term term;
	print_string " ";
	Display.display_term t;
	if state.advised_ins == [] then
	  print_string " succeeded\n"
	else
	  begin
	    print_string " succeeded with advice ";
	    Display.display_list Display.display_instruct state.advised_ins;
	    print_string " priority: ";
	    print_int state.priority;
	    print_string "\n"
	  end
      end;
    next_f state
  in

  (* When t starts with a function, the matching can succeeds only
     when the considered subterm of term starts with the same function.
     (The product with the neutral element can be simplified out before.)
     We exploit this property in particular when t starts with a product,
     to try the matches only with the same product. *)
  match t.t_desc with
    FunApp(prod,[_;_]) when prod.f_eq_theories != NoEq && prod.f_eq_theories != Commut ->
      begin
	let l' = Terms.simp_prod state0.simp_facts (ref false) prod t in
	let state = 
	  match term.t_desc with
	    FunApp(prod',_) when prod' == prod ->
	      if (state0.mode == AllEquiv) && (List.memq prod (!symbols_to_discharge)) then
		{ state0 with sthg_discharged = true }
	      else
		state0
	  | _ -> state0
	in
	match prod.f_eq_theories with
	  NoEq | Commut -> Parsing_helper.internal_error "Transf_crypto.check_instance_of_subterms: cases NoEq, Commut should have been eliminated"
	| AssocCommut | AssocCommutN _ | CommutGroup _ | ACUN _ ->
	    let match_AC allow_full l =
	      Match_eq.match_AC_advice check_instance_of_rec 
		explicit_value_state (get_var_link state.all_names_exp_opt) 
		is_var_inst (fun _ state -> next_f_internal state) state.simp_facts
		prod true allow_full false l l' state
	    in
	    let rec check_instance_of_list = function
		[] -> raise NoMatch
	      | term::l ->
		  try 
		    check_instance_of_subterms_rec true term
		  with NoMatch -> 
		    check_instance_of_list l
	    and check_instance_of_subterms_rec allow_full term =
	      match term.t_desc with
		Var _ | ReplIndex _ -> raise NoMatch
	      | FunApp(f,_) when f == prod ->
		  begin
		    let l = Terms.simp_prod Terms.simp_facts_id (ref false) f term in
		    try
		      match_AC allow_full l
		    with NoMatch ->
		      check_instance_of_list l
		  end
	      |	FunApp(f,([t1;t2] as l)) when f.f_cat == Equal || f.f_cat == Diff ->
		  if Terms.is_fun prod t1 || Terms.is_fun prod t2 then
		    match prod.f_eq_theories with
		      ACUN(xor, neut) ->
			check_instance_of_subterms_rec true (Terms.app xor [t1;t2]) 
		    | CommutGroup(prod, inv, neut) -> 
			begin
			  try 
			    check_instance_of_subterms_rec true (Terms.app prod [t1; Terms.app inv [t2]])
			  with NoMatch ->
			    let term' = (Terms.app prod [t2; Terms.app inv [t1]]) in
			    let l = Terms.simp_prod Terms.simp_facts_id (ref false) prod term' in
			    (* I don't need to try the elements of l individually, since this has
			       already been done in the previous case *) 
			    match_AC true l
			end
		    | _ -> check_instance_of_list l
		  else
		    check_instance_of_list l
	      | FunApp(f,l) ->
		  check_instance_of_list l
	      | TestE _ | LetE _ | FindE _ | ResE _ | EventAbortE _ | EventE _ | GetE _ | InsertE _ ->
		  Parsing_helper.internal_error "if, let, find, new, event, event_abort, get, and insert should have been excluded from left member of equivalences"
	    in
	    check_instance_of_subterms_rec false term
	| Assoc | AssocN _ | Group _ -> 
	    let match_assoc allow_full l =
	      Match_eq.match_assoc_advice_pat_subterm check_instance_of_rec 
		explicit_value_state (get_var_link state.all_names_exp_opt) 
		is_var_inst next_f_internal state.simp_facts prod allow_full l l' state
	    in
	    let rec check_instance_of_list = function
		[] -> raise NoMatch
	      | term::l ->
		  try 
		    check_instance_of_subterms_rec true term
		  with NoMatch -> 
		    check_instance_of_list l
	    and check_instance_of_subterms_rec allow_full term =
	      match term.t_desc with
		Var _ | ReplIndex _ -> raise NoMatch
	      | FunApp(f,_) when f == prod ->
		  begin
		    let l = Terms.simp_prod Terms.simp_facts_id (ref false) f term in
		    try
		      match_assoc allow_full l
		    with NoMatch ->
		      check_instance_of_list l
		  end
	      |	FunApp(f,([t1;t2] as l)) when f.f_cat == Equal || f.f_cat == Diff ->
		  begin
		    if Terms.is_fun prod t1 || Terms.is_fun prod t2 then
		      match prod.f_eq_theories with
			Group(prod, inv, neut) ->
			  begin
			    let l1 = Terms.simp_prod Terms.simp_facts_id (ref false) prod (Terms.app prod [t1; Terms.app inv [t2]]) in
			    let l2 = Terms.remove_inverse_ends Terms.simp_facts_id (ref false) (prod, inv, neut) l1 in
			    let rec apply_up_to_roll seen' rest' =
			      try 
				match_assoc true (rest' @ (List.rev seen'))
			      with NoMatch ->
				match rest' with
				  [] -> raise NoMatch
				| a::rest'' -> apply_up_to_roll (a::seen') rest''
			    in
			    try 
			      apply_up_to_roll [] l2
			    with NoMatch ->
			      let l3 = List.rev (List.map (Terms.compute_inv Terms.try_no_var_id (ref false) (prod, inv, neut)) l2) in
			      try 
				apply_up_to_roll [] l3
			      with NoMatch -> 
				check_instance_of_list l2
			  end
		      |	_ -> check_instance_of_list l
		    else
		      check_instance_of_list l
		  end
	      | FunApp(f,l) ->
		  check_instance_of_list l
	      | TestE _ | LetE _ | FindE _ | ResE _ | EventAbortE _ | EventE _ | GetE _ | InsertE _ ->
		  Parsing_helper.internal_error "if, let, find, new, event, event_abort, get, and insert should have been excluded from left member of equivalences"
	    in
	    check_instance_of_subterms_rec false term
      end
  | _ -> 
      let rec check_instance_of_list = function
	  [] -> raise NoMatch
	| term::l ->
	    try
	      check_instance_of_rec next_f_internal term t state0
	    with NoMatch ->
	      try 
		check_instance_of_subterms_rec term
	      with NoMatch -> 
		check_instance_of_list l
      and check_instance_of_subterms_rec term =
	match term.t_desc with
	  Var _ | ReplIndex _ -> raise NoMatch
	| FunApp(f,l) ->
	    check_instance_of_list l 
	| TestE _ | LetE _ | FindE _ | ResE _ | EventAbortE _ | EventE _ | GetE _ | InsertE _ ->
	    Parsing_helper.internal_error "if, let, find, new, event, event_abort, get, and insert should have been excluded from left member of equivalences"
      in
      check_instance_of_subterms_rec term

(* Reverse substitution: all array references must be computable using
   indexes, and these values are replaced with variables 
   of cur_array *)

let rec reverse_subst indexes cur_array t =
  let rec find l1 l2 = match (l1, l2) with
    t1::r1, t2::r2 -> if Terms.equal_terms t1 t then t2 else find r1 r2 
  | [], [] -> 
      Terms.build_term t 
	(match t.t_desc with
	  Var(b,l) -> Var(b, reverse_subst_index indexes cur_array l)
	| ReplIndex _ -> 
	    if (!Settings.debug_cryptotransf) > 4 then 
	      print_string "reverse_subst failed\n";
	    raise NoMatch 
	| FunApp(f,l) -> FunApp(f, List.map (reverse_subst indexes cur_array) l)
	| TestE _ | LetE _ | FindE _ | ResE _ | EventAbortE _ | EventE _ | GetE _ | InsertE _ -> 
	    Parsing_helper.internal_error "If, find, let, new, event, event_abort, get, and insert should have been expanded (Cryptotransf.reverse_subst)")
  | _ -> Parsing_helper.internal_error "Lists should have the same length in reverse_subst"
  in
  find indexes cur_array

and reverse_subst_index indexes cur_array l =
  List.map (reverse_subst indexes cur_array) l 

(* First pass: check and collect mappings of variables and expressions *)

type one_exp =
   { source_exp_instance : term; (* The expression to replace -- physical occurrence *)
     after_transfo_let_vars : (binder * binder) list; 
        (* List of (b,b') where b is a binder created by a let in
           the right member of the equivalence and b' is its image in 
           the transformed process. The indexes at creation of b' are cur_array_exp *)
     cur_array_exp : repl_index list; 
        (* Value of cur_array at this expression in the process (including
           replication and find indices). *)
     name_indexes_exp : (binder list * term list) list; 
        (* Values of indexes of names in this expression *)
     before_transfo_array_ref_map : (binderref * binderref) list;
     mutable after_transfo_array_ref_map : (binderref * binderref) list;
     (* after_transfo_array_ref_map is declared mutable, because it will be computed
	only after the whole map is computed, so we first define it as [] and later
	assign its real value to it.
        ((b, l), (b', l'))
        b = binder in the LHS
	l = its indices in the LHS
        b' = the corresponding binder in the process
        l' = its indices in the process
     *)
     mutable after_transfo_input_index_map : (term list * (binder * term list)) list;
        (* List of (l, (b', l')) where l is a sequence of indices using
	   indices passed as input in the RHS of equivalence, l' is the corresponding
	   sequence of indices in the process, and b' is the random variable in
	   the process corresponding to the first restriction in the list
	   of restrictions that use index l. (We use b' as identifier for the
	   encode function used for encoding l'.) *)
     before_transfo_input_vars_exp : (binder * term) list;
        (* List of (b,t) where b is a binder defined by an input in the 
           left member of the equivalence and the term t is its image in the process *)        
     after_transfo_input_vars_exp : (binder * term) list ;
        (* List of (b,t) where b is a binder defined by an input in the 
           right member of the equivalence and the term t is its image in the process *)
     before_exp_instance : term option;
     product_rest : (funsymb * term option * term option * (funsymb * term) option) option
       (* In case the source_exp_instance is a product, and source_exp
	  matches only a subproduct, before_exp_instance is the instance of
	  source_exp and product_rest contains 
	  Some(prod, left_rest, right_rest, comp_neut) such that
	  - When comp_neut = None,
	  source_exp_instance = prod(left_rest, prod(before_exp_instance, right_rest)).
	  When left_rest/right_rest are None, they are considered as empty.
	  (This is useful when the product has no neutral element.)
	  - When comp_neut = Some(eqdiff, neut),
	  source_exp_instance = (prod(left_rest, prod(before_exp_instance, right_rest)) eqdiff neut)
	  where eqdiff is either = or <> and neut is the neutral element of the product.
	  When source_exp matches the whole source_exp_instance,
	  product_rest = None and before_exp_instance is equal to source_exp_instance (modulo known equalities).
	  before_exp_instance is set only when no advice is needed to apply the transformation
	  *)
   }

type dest_t =
  | ForNew of binder
  | ForExp

type count_t =
    { name_table_above_opt : (binder * binder) list list option;
      indices_above : term list;
      indices : counted_indices } 
      (* Represents a number of repetitions, for computing a replication bound
	 or the number of calls to an oracle.
	 The number of repetitions is the product of the bounds
	 of the product of indices stored in [indices] with flag [Counted].
	 The associated name table [name_table_above_opt] serves in optimizing repetitions
	 across several such records: when several records have different name tables above the considered replication, we can take their maximum instead of their sum. *)

type mapping =
   { mutable expressions : one_exp list; (* List of uses of this expression, described above *)
     before_transfo_name_table : (binder * binder) list list;
     after_transfo_name_table : (binder * binder) list list;
     before_transfo_restr : (binder * binder) list;
        (* List of (b, b') where b is a binder created by a restriction in the
           left member of the equivalence, and b' is its image in the initial process. *)
     source_exp : term; (* Left-member expression in the equivalence *)
     source_args : binder list; (* Input arguments in left-hand side of equivalence *)
     after_transfo_restr : (binder * binder) list; 
        (* List of (b, b') where b is a binder created by a restriction in the
           right member of the equivalence, and b' is its image in the transformed process.
           The indexes at creation of b' are name_list_i_indexes *)
     rev_subst_name_indexes : (binder list * term list) list; 
        (* List of binders at creation of names in name_list_i in the process *)
     target_cur_array : repl_index list; (* cur_array in the right member of the equivalence *)
     target_exp : term; (* Right-member expression in the equivalence *)
     target_args : binder list; (* Input arguments in right-hand side of equivalence *)
     count : (repl_index * dest_t * count_t) list;
        (* Replication binders of the right member of the equivalence, 
	   and number of times each of them is repeated. *)
     count_calls : channel * count_t;
        (* Oracle name and number of calls to this oracle. *)
     mutable encode_fun_for_indices : funsymb option
   }

(* expression to insert for replacing source_exp_instance 
     = (after_transfo_input_vars_exp, 
        after_transfo_restr[name_indexes_exp], 
        after_transfo_let_vars[cur_array_exp]) ( target_exp )
*)

let map = ref ([] : mapping list)

(* For debugging *)

let display_mapping () =
  print_string "Mapping:\n";
  List.iter (fun mapping ->
    print_string "Exp:\n";
    List.iter (fun exp ->
      print_string "  At "; print_int exp.source_exp_instance.t_occ; print_string ", ";
      Display.display_term exp.source_exp_instance; print_newline();
      if exp.before_transfo_array_ref_map != [] then
	begin
	  print_string "  Name mapping: ";
	  Display.display_list (fun ((b,l),(b',l')) -> Display.display_var b l;
	    print_string " -> ";
	    Display.display_var b' l') exp.before_transfo_array_ref_map;
	  print_newline()
	end;
      print_string "  Arguments: ";
      Display.display_list (fun (b,t) -> Display.display_binder b;
	print_string " -> ";
	Display.display_term t) exp.before_transfo_input_vars_exp;
      print_newline();
      match exp.product_rest with
      | None -> ()
      | Some(prod, left_rest, right_rest, comp_neut) ->
	  print_string "Exp is inside product: ";
	  let disp_right_rest() =
	    match right_rest with
	    | None -> print_string "..."
	    | Some right_t ->
		print_string prod.f_name;
		print_string "(..., ";
		Display.display_term right_t;
		print_string ")"
	  in
	  begin
	    match left_rest with
	    | None -> disp_right_rest()
	    | Some left_t -> 
		print_string prod.f_name;
		print_string "(";
		Display.display_term left_t;
		print_string ", ";
		disp_right_rest();
		print_string ")"
	  end;
	  begin
	    match comp_neut with
	    | None -> ()
	    | Some(eq_diff, neut) ->
		print_string " "; 
		print_string eq_diff.f_name;
		print_string " "; 
		Display.display_term neut
	  end;
	  print_newline()
	    ) mapping.expressions;
    print_string "Source exp: ";
    Display.display_term mapping.source_exp;
    print_newline();
    print_string "Name mapping: ";
    Display.display_list (fun (b,b') -> Display.display_binder b;
      print_string " -> ";
      Display.display_binder b') mapping.before_transfo_restr;
    print_newline()
      ) (!map);
  print_newline()

let empty_equiv = (((NoName,[],[],[],StdEqopt,Decisional),[]) : equiv_nm)
let equiv = ref empty_equiv
let equiv_names_lhs_opt = ref []
let equiv_names_lhs = ref []
let equiv_names_lhs_flat = ref []

let incompatible_terms = ref []

let rebuild_map_mode = ref false

let rec find_map t =
  let rec find_in_map = function
      [] -> raise Not_found 
    | (mapping::l) ->
	let rec find_in_exp = function
	    [] -> find_in_map l
	  | one_exp::expl ->
	      if one_exp.source_exp_instance == t then
		(mapping, one_exp)
	      else
		find_in_exp expl
	in
	find_in_exp mapping.expressions
  in
  find_in_map (!map)

let is_incompatible t1 t2 =
  List.exists (fun (t1',t2')  -> ((t1 == t1') && (t2 == t2')) || 
  ((t1 == t2') && (t2 == t1'))) (!incompatible_terms)

let rec find_rm lm lm_list rm_list =
  match (lm_list,rm_list) with
    [],_ | _,[] -> Parsing_helper.internal_error "Could not find left member"
  | (a::l,b::l') -> 
      if lm == a then b else find_rm lm l l'


let rec insert ch l r m p = function
    [] -> [(ch,l,r,m,p)]
  | (((_,_,_,_,p') as a)::rest) as accu ->
      if p < p' then (ch,l,r,m,p)::accu else a::(insert ch l r m p rest)

let rec collect_expressions accu accu_names_lm accu_names_rm accu_repl_rm mode lm rm = 
  match lm, rm with
    ReplRestr(repl_opt, restr, funlist), ReplRestr(repl_opt', restr', funlist') ->
      let repl' =
	match repl_opt, repl_opt' with
	| Some _, Some repl' -> repl'
	| _ -> Parsing_helper.internal_error "replication missing in equiv, should have been added in check.ml"
      in
      List.iter2 (fun fg fg' ->
        collect_expressions accu (restr :: accu_names_lm) (restr' :: accu_names_rm) (repl' :: accu_repl_rm) mode fg fg') funlist funlist'
  | Fun(ch, args, res, (priority, _)), Fun(ch', args', res', _) ->
      accu := insert ch (accu_names_lm, args, res) (accu_names_rm, accu_repl_rm, args', res') mode priority (!accu)
  | _ -> Parsing_helper.internal_error "left and right members of equivalence do not match"

let rec collect_all_names accu lm rm = 
  match lm, rm with
    ReplRestr(_, restr, funlist), ReplRestr(_, restr', funlist') ->
      accu := (List.map (fun (b, _) -> 
	(b, 
	 if List.exists (fun (b',bopt') ->
	   (Terms.equiv_same_vars b b') &&
	   (bopt' == Unchanged)) restr' 
	 then Unchanged else NoOpt
	    )) restr) :: (!accu);
      List.iter2 (collect_all_names accu) funlist funlist'
  | Fun _, Fun _ -> ()
  | _ -> Parsing_helper.internal_error "left and right members of equivalence do not match"

let add_var accu b =
  if not (List.memq b (!accu)) then
    accu := b :: (!accu)
	
let rec letvars_from_term accu t =
  match t.t_desc with
    Var(_,l) | FunApp(_,l) -> 
      List.iter (letvars_from_term accu) l
  | ReplIndex _ -> ()
  | TestE(t1,t2,t3) ->
      letvars_from_term accu t1;
      letvars_from_term accu t2;
      letvars_from_term accu t3
  | LetE(pat,t1, t2, topt) -> 
      vars_from_pat accu pat; letvars_from_term accu t1;
      letvars_from_term accu t2; 
      begin
	match topt with
	  None -> ()
	| Some t3 -> letvars_from_term accu t3
      end
  | FindE(l0,t3,_) ->
      List.iter (fun (bl,def_list,t1,t2) ->
	(* Nothing to do for def_list: it contains only Var and Fun.
	   Variables that are in conditions of Find are handled differently,
	   because they do not have the same args_at_creation. *)
	letvars_from_term accu t2
	      ) l0;
      letvars_from_term accu t3      
  | ResE(b,t) ->
      add_var accu b;
      letvars_from_term accu t
  | EventAbortE(f) -> ()
  | EventE(t,p) ->
      letvars_from_term accu t;
      letvars_from_term accu p
  | GetE _ | InsertE _ ->
      Parsing_helper.internal_error "get and insert should not occur in Transf_crypto.letvars_from_term"
	
and vars_from_pat accu = function
    PatVar b -> add_var accu b
  | PatTuple (f,l) -> List.iter (vars_from_pat accu) l
  | PatEqual t -> letvars_from_term accu t

let new_binder2 b args_at_creation = 
  Terms.create_binder b.sname b.btype args_at_creation

let new_binder3 ri args_at_creation = 
  Terms.create_binder "u" ri.ri_type args_at_creation

let new_repl_index3 t =
  Terms.create_repl_index "ri" t.t_type

let new_repl_index4 ri =
  Terms.create_repl_index "ri" ri.ri_type

let rec longest_common_suffix above_indexes current_indexes =
  match above_indexes with
    [] -> 0
  | (first_above_indexes :: rest_above_indexes) ->
      let l_rest = longest_common_suffix rest_above_indexes current_indexes in
      let l_cur = Terms.len_common_suffix first_above_indexes current_indexes in
      max l_rest l_cur

let rec make_count repl ordered_indexes rev_subst_name_indexes before_transfo_name_table =
  match repl, ordered_indexes, rev_subst_name_indexes, before_transfo_name_table with
    [],[],[],[] -> []
  | (repl1::repll,index1::indexl,rev_subst_index1::rev_subst_indexl,nt1::ntl) ->
      let entry = 
	match nt1 with
	| [] -> assert false
	| (_,first_name)::_ ->
	    let idx_above =
	      match rev_subst_indexl with
	      | [] -> []
	      | rev_subst_next::_ -> rev_subst_next
	    in
	    let idx_current = List.rev_map (fun i ->
	      (i, if List.exists (Terms.is_repl_index i) idx_above then NotCounted else Counted)
		) first_name.args_at_creation
	    in
	    (repl1, ForNew first_name,
	     { name_table_above_opt = Some ntl;
	       indices_above = idx_above;
	       (* The field [indices] always contains the current replication indices in
                  reverse order *)
	       indices = idx_current })
      in
      entry :: (make_count repll indexl rev_subst_indexl ntl)
  | _ -> Parsing_helper.internal_error "make_count" 

(* Find the array indices that are really useful in the term t *)

let rec used_indices indices t =
  match t.t_desc with
    Var(_,l) | FunApp(_,l) -> 
      List.iter (used_indices indices) l
  | ReplIndex i ->
      begin
	try
	  let used_ref = List.assq i indices in
	  used_ref := true
	with Not_found ->
	  assert false
      end
  | TestE _ | LetE _ |FindE _ | ResE _ | EventAbortE _  | EventE _ | GetE _ | InsertE _ ->
      Parsing_helper.internal_error "If, find, let, new, event, event_abort, get, and insert should have been expanded (Cryptotransf.used_indices)"

let make_count_exp ch torg repl ordered_indexes rev_subst_name_indexes before_transfo_name_table =
  match repl, ordered_indexes, rev_subst_name_indexes, before_transfo_name_table with
  | (repl1::repll,index1::indexl,rev_subst_index1::rev_subst_indexl,nt1::ntl) ->
      (* [index1] must be the current array indices at [torg] *) 
      let top_indices_used =
	List.map (fun t -> (Terms.repl_index_from_term t, ref false)) index1
      in
      (* Mark the indices that are really useful (they occur in [torg]) *)
      used_indices top_indices_used torg;
      let idx_above = List.concat indexl in
      let idx_current =
	List.rev_map (fun (i, used_ref) ->
	  (i, if (not (!used_ref)) ||
	         List.exists (Terms.is_repl_index i) idx_above then NotCounted else Counted)
	    ) top_indices_used
      in
      let entry = 
	(repl1, ForExp,
	 { name_table_above_opt = Some ntl;
	   indices_above = idx_above;
	   (* The field [indices] always contains the current replication indices in
              reverse order *)
	   indices = idx_current })
      in
      entry :: (make_count repll indexl rev_subst_indexl ntl),
      (ch, { name_table_above_opt = None;
	     indices_above = [];
	     (* The field [indices] always contains the current replication indices in
                reverse order *)
	     indices = List.rev_map (fun (i, used_ref) -> (i,if !used_ref then Counted else NotCounted)) top_indices_used})
  | _ -> assert false  
	
let check_same_args_at_creation = function
    [] -> ()
  | (a::l) -> 
      if not (List.for_all (fun b -> 
	(Terms.equal_lists (==) b.args_at_creation a.args_at_creation)) l)
      then 
	begin
	  if (!Settings.debug_cryptotransf) > 4 then 
	    print_string "The LHS of the equivalence requires the same indices (= args at creation), the game uses different indices.\n";
	  raise NoMatch
	end

(* l1 and l2 are tables [[(binder in equiv, corresponding name);...];...]
   common_names return the number of name groups in common between l1 and l2 *)

let all_diff l1 l2 =
  if not (List.for_all (fun b -> not (List.memq b (List.map snd (List.concat l1))))
    (List.map snd (List.concat l2))) then 
    begin
      if (!Settings.debug_cryptotransf) > 4 then 
	print_string "Some random variables are common but not all.\n";
      raise NoMatch
    end

let rec common_names_rev l1 l2 =
  match l1,l2 with
    [],_ -> 0
  | _,[] -> 0
  | la1::lrest1, la2::lrest2 ->
      if (List.length la1 == List.length la2) && 
	(List.for_all2 (fun (b1, b1') (b2, b2') ->
	  (b1 == b2) && (b1' == b2')) la1 la2) then
	begin
	  let r = common_names_rev lrest1 lrest2 in
	  if (r == 0) && (la1 == []) then 
	    0
	  else
	    1+r
	end
      else
	begin
	  all_diff l1 l2;
	  0
	end

(* Compute the formula for upper indexes from current indexes *)

let rec rev_subst_indexes current_rev_subst name_table indexes =
  match name_table, indexes with
    [],[] -> []
  | name_table1::rest_name_table, ((names, index)::rest_indexes) ->
      begin
      if names == [] && index == [] then
	([],[])::(rev_subst_indexes current_rev_subst rest_name_table rest_indexes)
      else
	let args_at_creation = List.map Terms.term_from_repl_index (snd (List.hd name_table1)).args_at_creation in
	let subst_idx = 
	  match current_rev_subst with
	  | None -> index
	  | Some (cur_idx, cur_args_at_creation) ->
	      reverse_subst_index cur_idx cur_args_at_creation index
	in
	(names, subst_idx)::
	(rev_subst_indexes (Some (index, args_at_creation)) rest_name_table rest_indexes)
      end
  | _ -> Parsing_helper.internal_error "rev_subst_indexes"

(* Add missing names in the environment, if any *)

exception Next_empty
exception CouldNotComplete

let get_name b env =
  match List.assq b env with
    { t_desc = Var(b',_) } -> b'
  | _ -> Parsing_helper.internal_error "unexpected value for name in env"

let rec check_compatible name_indexes env rev_subst_name_indexes names_exp name_table =
  match (rev_subst_name_indexes, names_exp, name_table) with
    [],[],[] -> ()
  | (_::rev_subst_name_indexes_rest, names_exp_first::names_exp_rest, 
     name_table_first::name_table_rest) ->
       (* Complete the environment env if compatible *)
       List.iter2 (fun b1 (b,b') ->
	 if b != b1 then
	   begin
	     if (!Settings.debug_cryptotransf) > 4 then 
	       print_string "Check compatible failed(1).\n";
	     raise NoMatch
	   end;
	 try 
	   if (get_name b1 (!env)) != b' then
	     begin
	       if (!Settings.debug_cryptotransf) > 4 then 
		 print_string "Check compatible failed(2).\n";
	       raise NoMatch
	     end
	 with Not_found ->
	   env := (b,Terms.term_from_binder b') :: (!env)) names_exp_first name_table_first;
       (* Complete the indexes name_indexes if needed
	  The first indexes are always set, because there is at least one name in
	  the first sequence -- the one use to complete the sequence. We set the indexes
	  in the next sequence if there is one. *)
       begin
	 match (rev_subst_name_indexes_rest, names_exp_rest) with
	   [],[] -> ()
	 | (names, indexes)::_, (b0::_)::_ ->
	     begin
	     try 
	       ignore (assq_binder_binderref b0 (!name_indexes))
	       (* Found; will be checked for compatibility later *)
	     with Not_found ->
	       (* Add missing indexes *)
	       let b1 = List.hd names_exp_first in 
	       let indexes_above = assq_binder_binderref b1 (!name_indexes) in
	       let args_at_creation = (get_name b1 (!env)).args_at_creation in
	       name_indexes := (Terms.binderref_from_binder b0,
		 List.map (Terms.subst args_at_creation indexes_above) indexes) :: (!name_indexes)
	     end
	 | _ -> Parsing_helper.internal_error "bad length in check_compatible (2)"
       end;   
       check_compatible name_indexes env rev_subst_name_indexes_rest names_exp_rest name_table_rest
  | _ -> Parsing_helper.internal_error "bad length in check_compatible"

let rec complete_with name_indexes env names_exp b0 = function
    [] -> raise CouldNotComplete (* Could not complete: the name is not found in the map *)
  | (mapping::rest_map) ->
      let b0' = get_name b0 (!env) in
      let rec find_b0' rev_subst_name_indexes name_table = 
	match (rev_subst_name_indexes, name_table) with
	  [],[] -> (* Not found, try other map element *)
	    complete_with name_indexes env names_exp b0 rest_map
	| (_::rev_subst_rest), (name_table_first::name_table_rest) ->
	    if List.exists (fun (b,b') -> b' == b0') name_table_first then
	      check_compatible name_indexes env rev_subst_name_indexes names_exp name_table
	    else
	      find_b0' rev_subst_rest name_table_rest
	| _ -> Parsing_helper.internal_error "bad length in complete_with"
      in
      find_b0' mapping.rev_subst_name_indexes mapping.before_transfo_name_table 

let rec complete_env name_indexes env = function
    [] -> ()
  | (bl::names_exp_rest) ->
      if bl = [] then
	complete_env name_indexes env names_exp_rest
      else 
	let name_present b = List.mem_assq b (!env) in
	if List.for_all name_present bl then
	  try
	    complete_env name_indexes env names_exp_rest
	  with Next_empty ->
	    complete_with name_indexes env (bl::names_exp_rest) (List.hd bl) (!map)
	else
	  try
	    let b0 = List.find name_present bl in
	    complete_with name_indexes env (bl::names_exp_rest) b0 (!map)
	  with Not_found ->
	    raise Next_empty


let complete_env_call name_indexes env all_names_exp =
  let env_ref = ref env in
  let name_indexes_ref = ref name_indexes in
  try
    complete_env name_indexes_ref env_ref all_names_exp;
    (!name_indexes_ref, !env_ref)
  with Next_empty -> (* Could not complete *)
    raise CouldNotComplete


(* Returns the list of variables defined in a term.
   Raises NoMatch when it defines several times the same variable. *)

let rec get_def_vars accu t =
  match t.t_desc with
    Var(_,l) | FunApp(_,l) -> List.fold_left get_def_vars accu l
  | ReplIndex _ -> accu
  | TestE(t1,t2,t3) ->
      get_def_vars (get_def_vars (get_def_vars accu t1) t2) t3
  | LetE(pat,t1,t2,topt) ->
      let accu' =
	match topt with
	  None -> accu
	| Some t3 -> get_def_vars accu t3
      in
      get_def_vars_pat (get_def_vars (get_def_vars accu' t1) t2) pat
  | ResE(b,t) ->
      if List.memq b accu then 
	begin
	    if (!Settings.debug_cryptotransf) > 4 then 
	      print_string "Variable defined several times (1).\n";
	  raise NoMatch
	end;
      get_def_vars (b::accu) t
  | FindE(l0,t3,_) ->
      let accu' = get_def_vars accu t3 in
      List.fold_left (fun accu (bl,_,t1,t2) ->
	let vars = List.map fst bl in
	if List.exists (fun b -> List.memq b accu) vars then
	  begin
	    if (!Settings.debug_cryptotransf) > 4 then 
	      print_string "Variable defined several times (2).\n";
	    raise NoMatch
	  end;
	get_def_vars (get_def_vars (vars @ accu) t1) t2) accu' l0
  | EventAbortE(f) ->
      accu
  | EventE(t,p) ->
      get_def_vars (get_def_vars accu t) p
  | GetE _ | InsertE _ ->
      Parsing_helper.internal_error "get and insert should not occur in Transf_crypto.get_def_vars"

and get_def_vars_pat accu = function
    PatVar b ->
      if List.memq b accu then 
	begin
	  if (!Settings.debug_cryptotransf) > 4 then 
	    print_string "Variable defined several times (3).\n";
	  raise NoMatch
	end;
      b::accu
  | PatTuple(_,l) ->
      List.fold_left get_def_vars_pat accu l
  | PatEqual t -> get_def_vars accu t


(* [has_repl_index t] returns true when [t] contains a replication index *)

let rec has_repl_index t =
  match t.t_desc with
    Var(_,l) | FunApp(_,l) -> 
      List.exists has_repl_index l
  | ReplIndex _ -> true
  | TestE _ | LetE _ |FindE _ | ResE _ | EventAbortE _ | EventE _ | GetE _ | InsertE _ ->
      Parsing_helper.internal_error "If, find, let, new, event, event_abort, get, and insert should have been expanded (Cryptotransf.has_repl_index)"

  

let rec try_list f = function
    [] -> false
  | a::l -> 
      try
	f a
      with NoMatch ->
	try_list f l

type 'a check_res =
    Success of 'a
  | AdviceNeeded of to_do_t
  | NotComplete of to_do_t

let add_gameeq_name_mapping before_transfo_restr exp =
    (* Check the compatibility of the name mapping of the new expression
       with the one given by the user and the name mapping of previous expressions *)
  List.iter (fun ((b,_),(b',_)) ->
    try
      if (List.assq b' (!gameeq_name_mapping)) != b then
	Parsing_helper.internal_error "Game mapping incompatibility should have been detected earlier (1)"
    with Not_found ->
      gameeq_name_mapping := (b',b)::(!gameeq_name_mapping)
					) exp.before_transfo_array_ref_map;
  List.iter (fun (b,b') ->
    try
      if (List.assq b' (!gameeq_name_mapping)) != b then 
	Parsing_helper.internal_error "Game mapping incompatibility should have been detected earlier (2)"
    with Not_found ->
      gameeq_name_mapping := (b',b)::(!gameeq_name_mapping)	  
					) before_transfo_restr

	
let rec checks all_names_lhs (ch, (restr_opt, args, res_term), (restr_opt', repl', args', res_term'), mode, priority) 
    product_rest where_info cur_array defined_refs t state =
  let restr = List.map (List.map fst) restr_opt in
  let rec separate_env restr_env input_env array_ref_env = function
      [] -> (restr_env, input_env, array_ref_env)
    | (((b,l),t) as a)::r ->
	let (restr_env', input_env', array_ref_env') = 
	  separate_env restr_env input_env array_ref_env r
	in
	if (List.exists (List.memq b) restr) && 
	  (Terms.is_args_at_creation b l) then
	  ((b,t)::restr_env', input_env', array_ref_env')
	else if List.exists (List.memq b) all_names_lhs then
	  (restr_env', input_env', a::array_ref_env')
	else
	  begin
	    if not (Terms.is_args_at_creation b l) then
	      Parsing_helper.internal_error "Array references in LHS of equivalences should refer to random numbers";
	    (restr_env', (b,t)::input_env', array_ref_env')
	  end
  in
  let (restr_env, input_env, array_ref_env) =
    separate_env [] [] [] state.lhs_array_ref_map
  in

  let rec instantiate t =
    match t.t_desc with
    | FunApp(f,l) -> Terms.app f (List.map instantiate l)
    | Var(b,l) ->
	assq_binderref (b,l) state.lhs_array_ref_map
    | _ -> Parsing_helper.internal_error "if, find, defined, replication indices should have been excluded from left member of equivalences"
  in
  let before_exp_instance =
    try
      Some (instantiate res_term)
    with Not_found ->
      (* It may happen that not all variables are set, in case some advice is needed,
         or we match a subterm of [res_term]. In this case, the transformation will
	 not succeed; we do not set [before_exp_instance] *)
      None
  in
  
  let args_ins = 
    and_ins1 (state.advised_ins, state.priority + priority, state.names_to_discharge) (* Take into account the priority *)
      (map_and_ins  (fun (b,t) ->
	(* Check the arguments of the function *)
	check_term where_info [] None cur_array defined_refs t t
	  ) input_env) 
  in
  (* Also check the product rests before and after the transformed term,
     if any *)
  let to_do =
    match product_rest with
      None -> args_ins
    | Some(prod, left_rest, right_rest, comp_neut) ->
	let ins_with_left_rest = 
	  match left_rest with
	    None -> args_ins
	  | Some(t_left) ->
	      and_ins (check_term where_info [] None cur_array defined_refs t_left t_left) args_ins
	in
	match right_rest with
	  None -> ins_with_left_rest
	| Some(t_right) ->
	    and_ins (check_term where_info [] None cur_array defined_refs t_right t_right) ins_with_left_rest
  in
  
  try
    (* Adding missing names if necessary *)
    let (name_indexes, restr_env) = complete_env_call state.name_indexes restr_env restr in

    let before_transfo_name_table = List.map (List.map (fun b ->
      match List.assq b restr_env with
	{ t_desc = Var(b',_) } -> (b, b')
      | _ -> Parsing_helper.internal_error "unexpected link in check_term 2"
	    )) restr
    in
    
    let before_transfo_array_ref_map = List.map (function 
	(br, { t_desc = Var(b',l') }) -> (br, (b',l'))
      | _ -> Parsing_helper.internal_error "Variable expected") array_ref_env
    in
    
    let indexes_ordered = List.map (function 
	(b::_ as lrestr) -> 
          begin
            try
              (lrestr, assq_binder_binderref b name_indexes)
            with Not_found ->
	      Parsing_helper.internal_error "indexes missing"
          end
      | [] -> ([],[])) restr
    in
    
    let cur_array_terms = List.map Terms.term_from_repl_index cur_array in
    let indexes_ordered' = 
      match indexes_ordered with
	([],[]) :: l -> ([],cur_array_terms)::l
      | _ -> indexes_ordered
    in

    List.iter (fun name_group ->
      check_same_args_at_creation (List.map snd name_group)) before_transfo_name_table;
    List.iter (fun ((b1,l1), (b1',_)) ->
      List.iter (fun ((b2,l2), (b2',_)) ->
	if (Terms.equal_term_lists l1 l2) &&
	  not (Terms.equal_lists (==) b1'.args_at_creation b2'.args_at_creation) then
	  begin
	    if (!Settings.debug_cryptotransf) > 4 then 
	      print_string "The LHS of the equivalence requires the same indices (explicit indices), the game uses different indices.\n";
	    raise NoMatch
	  end
	    ) before_transfo_array_ref_map
	) before_transfo_array_ref_map;
	
    let before_transfo_restr = List.concat before_transfo_name_table in
    (* Mapping from input variables to terms *)
    let after_transfo_input_vars_exp = 
      List.map (fun (b,t) ->
	(find_rm b args args', t)) input_env
    in
    (* Variables defined by let/new in the right member expression *)
    let let_vars' = ref [] in
    letvars_from_term let_vars' res_term';
    let after_transfo_let_vars = 
      if (!Settings.optimize_let_vars) && (where_info != FindCond) then
	(* Try to find an expression from which we could reuse the let variables.
	   We do not try to reuse let variables when we are in a "find" condition,
	   because variables in "find" conditions must have a single definition.
	   Moreover, the sharing of variables is possible only when the
	   two expressions have the same replication indices above them;
	   otherwise, we may use variables with a bad [args_at_creation] field. *)
	let rec find_incomp_same_exp = function
	    [] -> (* Not found; create new let variables *)
	      List.map (fun b -> (b, new_binder2 b cur_array)) (!let_vars')
	  | (mapping::rest_map) ->
	      if mapping.target_exp == res_term' then
		try
		  let exp = List.find (fun exp ->
		    (Terms.equal_terms exp.source_exp_instance t) &&
		    (is_incompatible exp.source_exp_instance t) &&
		    (Terms.equal_lists (==) exp.cur_array_exp cur_array)
		      ) mapping.expressions in
		    (* Found, reuse exp.after_transfo_let_vars *)
		  exp.after_transfo_let_vars
		with Not_found ->
		  find_incomp_same_exp rest_map
	      else
		find_incomp_same_exp rest_map
	in
	find_incomp_same_exp (!map)
      else
	List.map (fun b -> (b, new_binder2 b cur_array)) (!let_vars')
    in
	
    (* Compute rev_subst_indexes
       It must be possible to compute indexes of upper restrictions in 
       the equivalence from the indexes of lower restrictions.
       Otherwise, raise NoMatch *)
    let rev_subst_name_indexes = rev_subst_indexes None before_transfo_name_table indexes_ordered in
	
    (* Check the compatibility of the name mapping of the new expression
       with the one given by the user and the one of previous expressions,
       recorded in gameeq_name_mapping *)
    begin
      let vm = !gameeq_name_mapping in
      List.iter (fun ((b,_),(b',_)) ->
	try
	  let b1 = List.assq b' vm in
	  if b1 != b then
	    begin
	      if (!Settings.debug_cryptotransf) > 4 then 
		print_string ("Variable " ^ (Display.binder_to_string b') ^ 
			      " of the game, associated to " ^ (Display.binder_to_string b) ^ 
			      " in the LHS of the equivalence, but it should be associated to " ^ (Display.binder_to_string b1) ^ " (1).\n");
	      raise NoMatch
	    end
	with Not_found -> ()
	    ) before_transfo_array_ref_map;
      List.iter (fun (b,b') ->
	try
	  let b1 = List.assq b' vm in
	  if b1 != b then 
	    begin
	      if (!Settings.debug_cryptotransf) > 4 then 
		print_string ("Variable " ^ (Display.binder_to_string b') ^ 
			      " of the game, associated to " ^ (Display.binder_to_string b) ^ 
			      " in the LHS of the equivalence, but it should be associated to " ^ (Display.binder_to_string b1) ^ " (2).\n");
	      raise NoMatch
	    end
	with Not_found -> ()
	    ) before_transfo_restr
    end;

   (* We check the compatibility of array references for the current expression
       if ((b,_),(b',_)) in before_transfo_array_ref_map, and
       if (b1,b') in before_transfo_restr, then b1 = b.
       This point is implied by the final checks performed in
       check_lhs_array_ref, but performing it earlier allows to backtrack
       and choose other expressions *)

    let name_compat b b' b1 b1' =
      if b1' == b' && b1 != b then 
	begin
	  if (!Settings.debug_cryptotransf) > 4 then 
	    print_string ("Variable " ^ (Display.binder_to_string b') ^ 
			  " of the game, associated to both " ^ (Display.binder_to_string b) ^ 
			  " and " ^ (Display.binder_to_string b1) ^ " in the LHS of the equivalence.\n");
	  raise NoMatch
	end
    in

    List.iter (fun ((b,_),(b',_)) ->
      List.iter (fun (b1, b1') ->
	name_compat b b' b1 b1'
	    ) before_transfo_restr
      ) before_transfo_array_ref_map;

    let rec name_compat_restr = function
	[] -> ()
      | (b,b') :: rest ->
	  List.iter (fun (b1, b1') ->
	    name_compat b b' b1 b1'
	      ) rest;
	  name_compat_restr rest
    in
    name_compat_restr before_transfo_restr;

    let rec name_compat_array_ref_map = function
	[] -> ()
      | ((b,_),(b',_)) :: rest ->
	  List.iter (fun ((b1,_),(b1',_)) ->
	    name_compat b b' b1 b1'
	      ) rest;
	  name_compat_array_ref_map rest
    in
    name_compat_array_ref_map before_transfo_array_ref_map;
    
    (* Common names with other expressions
       When two expressions use a common name, 
       - the common names must occur at the same positions in the equivalence
       - if a name is common, all names above it must be common too, and the function that computes the 
       indexes of above names from the indexes of the lowest common name must be the same.
       *)
    let longest_common_suffix = ref 0 in
    let exp_for_longest_common_suffix = ref None in
    (*if (!Settings.debug_cryptotransf) > 4 then display_mapping();*)
    List.iter (fun mapping ->
      let name_table_rev = List.rev before_transfo_name_table in
      let map_name_table_rev = List.rev mapping.before_transfo_name_table in
      let new_common_suffix =
	common_names_rev name_table_rev map_name_table_rev
      in
      if new_common_suffix > 0 then
	begin
	  let common_rev_subst_name_indexes1 = Terms.lsuffix (new_common_suffix - 1) rev_subst_name_indexes in
	  let common_rev_subst_name_indexes2 = Terms.lsuffix (new_common_suffix - 1) mapping.rev_subst_name_indexes in
	  if not (List.for_all2 (fun (_,r1) (_,r2) -> Terms.equal_term_lists r1 r2) common_rev_subst_name_indexes1 common_rev_subst_name_indexes2) then
	    begin
	      if (!Settings.debug_cryptotransf) > 4 then 
		print_string "The function that computes the indexes of above random variables from the indexes of the lowest common random variable is not the same.\n";
	      raise NoMatch
	    end
	end;
      if new_common_suffix > (!longest_common_suffix) then
	begin
	  longest_common_suffix := new_common_suffix;
	  exp_for_longest_common_suffix := Some mapping
	end
	  
	) (!map);
    
    let after_transfo_table_builder nt r = 
      match nt with
	[] -> List.map (fun (b,_) -> (b, new_binder2 b cur_array)) r
      | ((_,one_name)::_) ->
	  List.map (fun (b,bopt) -> 
	    try 
	      (* Try to reuse old binder when possible:
		 marked unchanged and same string name, same number, and same type 
		 b' = binder associated to b before the transformation *)
	      let b' = snd (List.find (fun (bf_name, _) -> Terms.equiv_same_vars b bf_name) nt)
	      in
	      (* If b is marked [unchanged], we reuse the old binder b'.
		 Otherwise, we cannot reuse the old binder b', but we generate
		 a new binder with the same name as b' (but a different integer index).
		 Reusing the name should make games easier to read. *)
	      (b, if bopt == Unchanged then b' else new_binder2 b' one_name.args_at_creation)
	    with Not_found ->
	      (b, new_binder2 b one_name.args_at_creation)) r
    in
    let after_transfo_name_table = 
      match !exp_for_longest_common_suffix with
	None -> 
	  List.map2 after_transfo_table_builder before_transfo_name_table restr_opt'
      | Some exp ->
	  let diff_name_table = Terms.remove_suffix (!longest_common_suffix) before_transfo_name_table in
	  let diff_restr' = Terms.remove_suffix (!longest_common_suffix) restr_opt' in
	  let common_name_table = Terms.lsuffix (!longest_common_suffix) exp.after_transfo_name_table in
	  (List.map2 after_transfo_table_builder diff_name_table diff_restr') @ common_name_table
    in
    
    let after_transfo_restr = List.concat after_transfo_name_table in
    
    let exp =
      { source_exp_instance = t;
	name_indexes_exp = indexes_ordered';
	before_transfo_array_ref_map = before_transfo_array_ref_map;
	after_transfo_array_ref_map = [];
	after_transfo_input_index_map = [];
	after_transfo_let_vars = after_transfo_let_vars;
	cur_array_exp = cur_array;
	before_transfo_input_vars_exp = input_env;
	after_transfo_input_vars_exp = after_transfo_input_vars_exp;
	before_exp_instance = before_exp_instance;	
	product_rest = product_rest
	  }
    in
    
    (* If we are in a find condition, verify that we are not going to 
       create finds on variables defined in the condition of find,
       and that the variable definitions that we introduce are all 
       distinct.
       Also verify that we are not going to introduce "new" or "event" 
       in a find condition. *)
    
    if where_info == FindCond then
      begin
	let ((_, lm, rm, _, _, _),name_mapping) = !equiv in 
	Array_ref.array_ref_eqside rm;
	let def_vars = get_def_vars [] res_term' in
	if List.exists Array_ref.has_array_ref def_vars then
	  begin
	    if (!Settings.debug_cryptotransf) > 4 then 
	      print_string "The transformed term occurs in a condition of find, and the transformation may create finds on variables defined in the condition of find.\n";
	    raise NoMatch
	  end;
	Array_ref.cleanup_array_ref()
      end;
    
    match to_do with
      ([],_,_)::_ ->
	Success(to_do, indexes_ordered, restr_env, name_indexes, rev_subst_name_indexes, 
		before_transfo_name_table, before_transfo_restr, after_transfo_name_table, 
		after_transfo_restr, exp)
    | [] -> Parsing_helper.internal_error "ins_accu should not be empty (5)"
    | _ -> AdviceNeeded(to_do)
	  
  with CouldNotComplete ->
    if (!Settings.debug_cryptotransf) > 5 then
      begin
	print_string "failed to discharge ";
	Display.display_term t;
	print_string " (could not complete missing names)\n"
      end;
    match to_do with
      ([],_,_)::_ ->
        (* Accept not being able to complete missing names if I am in "rebuild map" mode *)
	if (!rebuild_map_mode) then NotComplete(to_do) else raise NoMatch
    | [] -> Parsing_helper.internal_error "ins_accu should not be empty (6)"
    | _ -> AdviceNeeded(to_do)

(* ta_above: when there is a test (if/find) or an assignment
   just above t, contains the instruction to expand this test or assignment;
   otherwise empty list 

   Return the list of transformations to apply before so that the desired
   transformation may work. When this list is empty, the desired transformation
   is ok. Raises NoMatch when the desired transformation is impossible,
   even after preliminary changes.

   when comp_neut = None, torg = t
   when comp_neut = Some(f, neut), torg = FunApp(f, [t; neut])
   torg is the full transformed term, including the context '= neut' or '<> neut'.
   t is the part of the term that is matched with the left-hand side
   of the equivalence.
*)

and check_term where_info ta_above comp_neut cur_array defined_refs t torg =
  if not ((occurs_name_to_discharge t) || 
          (occurs_symbol_to_discharge t) ||
	  ((* When the user_term_mapping mentions term t, 
              we transform it even if it does not contain
	      anything to discharge; the things to discharge may appear 
              by determining the values of variables. *)
	  match !user_term_mapping with
	    None -> false
	  | Some tm -> List.exists (fun (occ,_) -> occ == t.t_occ) tm)) then
    (* The variables in names_to_discharge and 
       the symbols in occurs_symbol_to_discharge do not occur in t => OK *)
    begin
      (* When the user_term_mapping is present, I look for a subterm
	 that might need to be transformed because it is mentioned
	 in that mapping. *)
      match !user_term_mapping with
	None -> success_no_advice
      |	Some tm ->
	  match t.t_desc with
	    FunApp(f,l) ->
	      map_and_ins (fun t' -> check_term where_info [] None cur_array defined_refs t' t') l
	  | _ -> 
	      success_no_advice
    end
  else
    try 
      let (mapping, exp) = find_map torg in
      (* The term torg is already discharged in the map => OK
	 The term torg itself is ok, we just need to recheck the arguments
	 of torg; they may need to be further discharged when a new name
	 has been added in names_to_discharge. *)
      let args_ins = 
	map_and_ins  (fun (_,t') ->
	  check_term where_info [] None cur_array defined_refs t' t'
	    ) exp.before_transfo_input_vars_exp
      in
      (* Also check the product rests before and after the transformed term,
	 if any *)
      match exp.product_rest with
	None -> args_ins
      |	Some(prod, left_rest, right_rest, comp_neut) ->
	  let ins_with_left_rest = 
	    match left_rest with
	      None -> args_ins
	    | Some(t_left) ->
		and_ins (check_term where_info [] None cur_array defined_refs t_left t_left) args_ins
	  in
	  match right_rest with
	    None -> ins_with_left_rest
	  | Some(t_right) ->
	      and_ins (check_term where_info [] None cur_array defined_refs t_right t_right) ins_with_left_rest
    with Not_found ->
      (* First try to find a matching source expression in the equivalence to apply *)
      let ((_, lm, rm, _, _, _),name_mapping) = !equiv in 
      let transform_to_do = ref [] in
      (* Store in accu_exp all expressions in priority order *)
      let accu_exp = ref [] in
      List.iter2 (fun (lm1,mode) (rm1,_) -> collect_expressions accu_exp [] [] [] mode lm1 rm1) lm rm;
      let all_names_lhs = !equiv_names_lhs in
      (* Prepare a function to replace variables with their values *)
      let simp_facts = 
	if !Settings.use_known_equalities_crypto then
	  try 
	    let facts = Facts.get_facts_at (DTerm t) in
	    Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) facts 
	  with Contradiction ->
	    (* This term is in fact unreachable *)
	    Terms.simp_facts_id
	else
	  Terms.simp_facts_id
      in
      (* Try all expressions in accu_exp, in order. When an expression succeeds without
         advice, we can stop, since all future expressions don't have higher priority *)
      let r = try_list (fun ((ch, (restr_opt, args, res_term), (restr_opt', repl', args', res_term'), mode, priority) as current_exp) ->
	begin
	  match !user_term_mapping with
	    None -> ()
	  | Some tm ->
	      try
		(* When the user specified a term different from the one 
                   currently_tried, fail, and try another one. *)
		let user_res_term = List.assq t.t_occ tm in
		if res_term != user_res_term then
		  raise NoMatch
	      with Not_found ->
		(* The user specified no transformed term for the current term.
		   If the mapping is supposed to be exhaustive, fail;
		   otherwise continue *)
		if !no_other_term then
		  raise NoMatch
	end;
	try
	  let state0 = init_state simp_facts (!equiv_names_lhs_opt) mode where_info priority in
	  check_instance_of state0 (fun product_rest state -> 
	    let old_map = !map in
	    let vcounter = Terms.get_var_num_state() in
	    match checks all_names_lhs current_exp product_rest where_info cur_array defined_refs torg state with
	      Success(to_do, indexes_ordered, restr_env, name_indexes, rev_subst_name_indexes, 
		      before_transfo_name_table, before_transfo_restr, after_transfo_name_table, 
		      after_transfo_restr, exp) -> 
	        begin

		  let count, count_calls = 
		    match exp.name_indexes_exp with
		      (_::_,top_indices)::_ -> (* The down-most sequence of restrictions is not empty *)
			make_count repl' (List.map snd exp.name_indexes_exp) (List.map snd rev_subst_name_indexes) before_transfo_name_table,
			(ch, { name_table_above_opt = None;
			       indices_above = [];
			       indices = List.map (fun i ->
				 (i, Counted)
				   ) exp.cur_array_exp })
		        (* Another solution would use top_indices instead of
			   exp.cur_array_exp
		           It's not clear a priori which one is smaller... *)
		    | ([], top_indices)::rest -> 
			make_count_exp ch torg repl' (List.map snd exp.name_indexes_exp) (List.map snd rev_subst_name_indexes) before_transfo_name_table
		    | [] ->
		        (* There is no replication at all in the LHS => 
			   the expression must be evaluated once *)
			if has_repl_index torg then
			  begin
			    if (!Settings.debug_cryptotransf) > 4 then
			      print_string "There is no replication in the LHS of the equivalence, and the expression needs to be evaluated in the game for several different values of replication indices.\n";
			    raise NoMatch
			  end;
			if List.exists (fun mapping -> mapping.source_exp == res_term) (!map) then
			  begin
			    if (!Settings.debug_cryptotransf) > 4 then
			      print_string "There is no replication in the LHS of the equivalence, and the expression occurs several times in the game.\n";
			    raise NoMatch
			  end;
			[],
			(ch, { name_table_above_opt = None;
			       indices_above = [];
			       indices = [] })
		  in

	          (* verify that all restrictions will be correctly defined after the transformation *)
		  List.iter (fun (_,b,def_check) ->
		    List.iter (fun res_def_check ->
		      if res_term == res_def_check then
			try
			  match List.assq b restr_env with
			    { t_desc = Var(b_check,_) } -> 
			      let l_check = assq_binder_binderref b name_indexes in
		              (*print_string "Checking that ";
			      Display.display_term (Terms.term_from_binderref (b_check, l_check));
			      print_string " is defined... "; *)
			      if not (List.exists (Terms.equal_binderref (b_check, l_check)) defined_refs) then
				begin
				  if (!Settings.debug_cryptotransf) > 4 then
				    begin
				      print_string "Variable ";
				      Display.display_term (Terms.term_from_binderref (b_check, l_check));
				      print_string " may not be defined after game transformation.\n"
				    end;
				  raise NoMatch
				end;
		              (* print_string "Ok.\n" *)
			  | _ -> Parsing_helper.internal_error "unexpected link in check_term 3"
			with Not_found ->
			  Parsing_helper.internal_error "binder not found when verifying that all restrictions will be defined after crypto transform"
			    ) def_check;
		    ) name_mapping;

	     (* if the down-most (first in restr) sequence of
                restrictions is not empty, the result expression must
                be a function of the indexes of those names (checked
                using reverse substitutions) *)
	     begin
	     match indexes_ordered with
	       (_::_,down_indexes)::_ -> (* The down-most sequence of restrictions is not empty *)
     	       begin
		 (* Check that names in name_list_i are always used in
		    the same expression *)
	 	 (* TO DO this test could be made more permissive to
		    succeed in all cases when the names in name_list_i
		    occur in a single expression.
		    More generally, it would be nice to allow
		    different session identifiers when they are
		    related by an equality.
		    For instance, if name_list_i_indexes is iX, and
		    jX[iX[i]] = i, then i should also be allowed, and
		    the result of the reverse subtitution applied to i
		    is jX. *)
		 let cur_array' = List.map (fun e -> 
		   Terms.create_repl_index "tmpcur" e.t_type) down_indexes 
		 in
		 let cur_array_terms' = List.map Terms.term_from_repl_index cur_array' in
		 let rev_subst_fun = reverse_subst down_indexes cur_array_terms' in
		 let args_rev_subst = List.map (fun (b, t) -> (b, rev_subst_fun t)) exp.before_transfo_input_vars_exp in
		 let array_ref_rev_subst = List.map (fun (br, br') -> (br, rev_subst_fun (Terms.term_from_binderref br'))) exp.before_transfo_array_ref_map in
		 (* NOTE If we are in a find condition, the
		    find indices are included in cur_array, so that we
		    make sure that the term can be expressed as a
		    function of the down-most indices of the
		    replication without using the indices of
		    find. (Otherwise, a different expression may be
		    evaluated for each value of the indices of find,
		    so several evaluations for each value of the
		    down_most restriction *)
	         (* SUCCESS store the mapping in the mapping list *)
		 let one_name = snd (List.hd before_transfo_restr) in
		 let rec find_old_mapping = function
		     [] -> (* No old mapping found, create a new one *)
		       add_gameeq_name_mapping before_transfo_restr exp;
		       let new_mapping =
			 { expressions = [ exp ];
			   before_transfo_name_table = before_transfo_name_table;
			   after_transfo_name_table = after_transfo_name_table;
			   before_transfo_restr = before_transfo_restr;
			   source_exp = res_term;
			   source_args = args;
			   after_transfo_restr = after_transfo_restr;
			   rev_subst_name_indexes = rev_subst_name_indexes;
			   target_cur_array = repl';
			   target_exp = res_term';
			   target_args = args';
			   count = count;
			   count_calls = count_calls;
			   encode_fun_for_indices = None
		         } 
		       in
		       map := new_mapping :: (!map)
		   | (mapping::rest) -> 
		       if (List.exists (fun (b,b') -> b' == one_name) mapping.before_transfo_restr) && 
			 (mapping.source_exp == res_term) then
			 (* Old mapping found, just add the current expression in the 
			    list of expressions of this mapping, after a final check *)
			 begin
			   (* if a name in the down-most sequence of restrictions is common, the result expressions
                              must be equal up to change of indexes (checked using reverse substitutions) *)
			   let exp' = List.hd mapping.expressions in
			   let exp'_instantiate_indices = Terms.subst cur_array' (snd (List.hd exp'.name_indexes_exp)) in
			   (* Since one name the down-most sequence of restrictions is in common, 
		              we have already checked that all names are in common, and 
			      that the function that computes the indexes of above names from 
			      the indexes of the lowest common name is the same.
			      We check that the arguments are the same and that the indices
			      of array references are also the same, modulo substitution of
			      array indices. 
			      Then the result expression is the same modulo substitution of 
			      array indices. *)
			   if not ((List.for_all2 (fun (b, t) (b', t') ->
			             assert (b == b');
			             Terms.equal_terms (exp'_instantiate_indices t) t'
			               ) args_rev_subst exp'.before_transfo_input_vars_exp)
				     &&
				   (List.for_all2 (fun (br, t) (br', br_im') ->
				     assert (Terms.equal_binderref br br');
				     Terms.equal_terms (exp'_instantiate_indices t) (Terms.term_from_binderref br_im')
				       ) array_ref_rev_subst exp'.before_transfo_array_ref_map))
                           (* The previous test (shown below) was incorrect in case source_exp_instance 
			      contains a product that is only partly matched by source_exp.
			      Furthermore, it did not take into account equalities between
			      terms that could have been exploited to match the source expression.

			      let t' = reverse_subst down_indexes cur_array_terms' torg in
			      (Terms.equal_terms exp'.source_exp_instance 
			      (Terms.subst cur_array' (snd (List.hd exp'.name_indexes_exp)) t')) *)
			   then
			     begin
			       if (!Settings.debug_cryptotransf) > 4 then
				 print_string "There is no replication under the last restriction in the LHS of the equivalence, and the expression needs to be evaluated several times in the game for the same restriction and with different arguments.\n";
			       raise NoMatch
			     end;
			   add_gameeq_name_mapping before_transfo_restr exp;
			   mapping.expressions <- exp :: mapping.expressions
			 end
                       else 
			 find_old_mapping rest
		 in
		 find_old_mapping (!map)
	       end
	     | _ -> 
	       begin
	         (* SUCCESS store the mapping in the mapping list *)
		 (*Caused a bug, and anyway does not really reduce the number 
		   of branches of find, since we later avoid creating several 
		   branches when the names are common and no let variables
		   are used. Just allows to reuse the same index variables 
		   for the various branches. (This bug appears with 
		   examplesnd/testenc. It is caused by a mixing of current
		   array indexes for various occurrences of the same 
		   expression.)

		    Try to reuse an existing mapping to optimize
                    (reduces the number of find and the probability difference)
                 try 
		   let mapping' = List.find (fun mapping' -> 
		     List.exists (fun exp' -> Terms.equal_terms exp'.source_exp_instance torg) mapping'.expressions) (!map)
		   in
		   mapping'.expressions <- exp :: mapping'.expressions
		 with Not_found -> *)
		   add_gameeq_name_mapping before_transfo_restr exp;
		   let new_mapping = 
		     { expressions = [ exp ];
		       before_transfo_name_table = before_transfo_name_table;
		       after_transfo_name_table = after_transfo_name_table;
		       before_transfo_restr = before_transfo_restr;
		       source_exp = res_term;
		       source_args = args;
		       after_transfo_restr = after_transfo_restr;
		       rev_subst_name_indexes = rev_subst_name_indexes;
		       target_cur_array = repl';
		       target_exp = res_term';
		       target_args = args';
		       count = count;
		       count_calls = count_calls;
		       encode_fun_for_indices = None
		       (* TO DO (to reduce probability difference)
			  When I have several times the same expression, possibly with different
			  indexes, I should count the probability difference only once.
			  I should make some effort so that name_list_g_indexes is a suffix of 
			  the indexes of the expression.
			  Also, when not all indexes in cur_array_terms appear in the
			  expression, I could make only the product of the longest
			  prefix of cur_array_terms that appears.
			  *)
		   } 
		   in 
		   map := new_mapping :: (!map)
	       end;
	     end;
	     transform_to_do := merge_ins to_do (!transform_to_do);
	     true
	   end
	    | AdviceNeeded(to_do) -> 
		map := old_map;
		Terms.set_var_num_state vcounter; (* Forget variables *)
		transform_to_do := merge_ins to_do (!transform_to_do);
		raise NoMatch
	    | NotComplete(to_do) ->
		transform_to_do := merge_ins to_do (!transform_to_do);
		true
		  ) comp_neut res_term t 

	with NoMatch ->
	  if (!Settings.debug_cryptotransf) > 5 then
	    begin
	      print_string "failed to discharge ";
	      Display.display_term t;
	      print_string "\n"
	    end;
	    (* When t is just under a test (if/find) or an assignment,
	       try subterms of res_term *)
	  if ta_above != [] then
	    begin
	      (* When ta_above != [], comp_neut = None, so torg = t *)
	      let state0 = init_state simp_facts (!equiv_names_lhs_opt) mode where_info priority in
	      check_instance_of_subterms state0 (fun state -> 
		match checks all_names_lhs current_exp None where_info cur_array defined_refs t state with
		  Success(to_do,_,_,_,_,_,_,_,_,_) |  AdviceNeeded(to_do) | NotComplete(to_do) ->
		    transform_to_do := merge_ins (and_ins1 (ta_above,0,[]) to_do) (!transform_to_do)
			 ) res_term t
	    end;
	  raise NoMatch
	    ) (!accu_exp)
      in

      if (!transform_to_do) != [] then global_sthg_discharged := true;

      if r then
        (* If r is true, the transformation can be done without advice
	   (even if that may not be the highest priority), then I don't consider
           transforming only subterms. Another way would be to always try to transform
           subterms but with a lower priority. *)
        !transform_to_do
      else
        try 
	  if comp_neut != None then raise NoMatch;
          merge_ins (!transform_to_do) (check_term_try_subterms where_info cur_array defined_refs t)
        with NoMatch ->
	  if (!transform_to_do) == [] then raise NoMatch else (!transform_to_do)

and check_term_try_subterms where_info cur_array defined_refs t =
  (* If fails, try a subterm; if t is just a variable in names_to_discharge,
     the transformation is not possible *)
  match t.t_desc with
    Var(b,l) ->
      begin
	try 
	  let bopt = List.assq b (!names_to_discharge) in
	  if (where_info == Event) && (!bopt != NoOpt) then
	    begin
	      (* Note: if the current option is "DontKnow" and in fact it will later
		 become "NoOpt", then the transformation will fail. It might have succeeded
		 with advice SArenaming... *)
	      if !bopt == DontKnow then bopt := Unchanged;
	      map_and_ins (fun t' -> check_term where_info [] None cur_array defined_refs t' t') l
	    end
	  else if (not (!no_advice_mode)) && (List.length b.def > 1) then
	    (* If b has several definitions, advise SArenaming, so that perhaps
	       the transformation becomes possible after distinguishing between
	       these definitions *)
	    [([SArenaming b],0,[])]
	  else
            raise NoMatch
	with Not_found ->
	  map_and_ins (fun t' -> check_term where_info [] None cur_array defined_refs t' t') l
      end
  | FunApp(f,l) ->
      if List.memq f (!symbols_to_discharge) then
	raise NoMatch
      else
	begin
	  match l with
	    [_;_] when f.f_eq_theories != NoEq && f.f_eq_theories != Commut ->
              (* f is a binary function with an equational theory that is
		 not commutativity -> it is a product-like function 

		 We apply the statements only to subterms that are not products by f.
		 Subterms that are products by f are already handled above
		 using [check_instance_of]. *)
	      let l' = Terms.simp_prod Terms.simp_facts_id (ref false) f t in
	      map_and_ins (fun t' -> check_term where_info [] None cur_array defined_refs t' t') l'
	  | [t1;t2] when f.f_cat == Equal || f.f_cat == Diff ->
	      begin
		match Terms.get_prod_list Terms.try_no_var_id l with
		  ACUN(xor, neut) ->
		    let comp_neut = Some(f, Terms.app neut []) in
		    let t' = Terms.app xor [t1;t2] in
		    merge_ins_fail
		      (fun () -> check_term where_info [] comp_neut cur_array defined_refs t' t)
		      (fun () ->
			if List.memq xor (!symbols_to_discharge) then raise NoMatch;
			let l' = Terms.simp_prod Terms.simp_facts_id (ref false) xor t' in
			map_and_ins (fun t' -> check_term where_info [] None cur_array defined_refs t' t') l')
		| CommutGroup(prod, inv, neut) -> 
		    let comp_neut = Some(f, Terms.app neut []) in
		    merge_ins_fail
		      (fun () -> 
			let t' = Terms.app prod [t1; Terms.app inv [t2]] in
			check_term where_info [] comp_neut cur_array defined_refs t' t)
		      (fun () -> merge_ins_fail
			 (fun () -> 
			   let t'' = Terms.app prod [t2; Terms.app inv [t1]] in
			   check_term where_info [] comp_neut cur_array defined_refs t'' t)
			 (fun () ->
			   if List.memq prod (!symbols_to_discharge) then raise NoMatch;
			   let l1' = Terms.simp_prod Terms.simp_facts_id (ref false) prod t1 in
			   let l2' = Terms.simp_prod Terms.simp_facts_id (ref false) prod t2 in
			   map_and_ins (fun t' -> check_term where_info [] None cur_array defined_refs t' t') (l1' @ l2')))
		| Group(prod, inv, neut) -> 
		    let comp_neut = Some(f, Terms.app neut []) in
		    let l1 = Terms.simp_prod Terms.simp_facts_id (ref false) prod 
			(Terms.app prod [t1; Terms.app inv [t2]]) in
		    let l2 = Terms.remove_inverse_ends Terms.simp_facts_id (ref false) (prod, inv, neut) l1 in
		    let rec apply_up_to_roll seen' rest' =
		      merge_ins_fail
			(fun () ->
			  let t0 = (Terms.make_prod prod (rest' @ (List.rev seen'))) in
			  check_term where_info [] comp_neut cur_array defined_refs t0 t)
			(fun () ->
			  match rest' with
			    [] -> raise NoMatch
			  | a::rest'' -> apply_up_to_roll (a::seen') rest'')
		    in
		    merge_ins_fail 
		      (fun () -> apply_up_to_roll [] l2)
		      (fun () -> merge_ins_fail
			  (fun () ->
			    let l3 = List.rev (List.map (Terms.compute_inv Terms.try_no_var_id (ref false) (prod, inv, neut)) l2) in
			    apply_up_to_roll [] l3)
			  (fun () ->
			    let l1' = Terms.simp_prod Terms.simp_facts_id (ref false) prod t1 in
			    let l2' = Terms.simp_prod Terms.simp_facts_id (ref false) prod t2 in
			    map_and_ins (fun t' -> check_term where_info [] None cur_array defined_refs t' t') (l1' @ l2')))
		| _ -> 
		    map_and_ins (fun t' -> check_term where_info [] None cur_array defined_refs t' t') l
	      end
	  | _ -> 
	      map_and_ins (fun t' -> check_term where_info [] None cur_array defined_refs t' t') l
	end
  | ReplIndex _ -> success_no_advice
  | TestE _ | LetE _ | FindE _ | ResE _ | EventAbortE _ | EventE _ | GetE _ | InsertE _ -> 
      Parsing_helper.internal_error "If, find, let, new, event, event_abort, get, and insert should have been expanded (Cryptotransf.check_term_try_subterms)"

let check_term where_info ta_above cur_array defined_refs t =
  let ins_to_do = check_term where_info ta_above None cur_array defined_refs t t in
  names_to_discharge := (get_inter_names ins_to_do) @ (!names_to_discharge);
  ins_to_do

(* For debugging *)

let check_term where_info l c defined_refs t =
  try
    let r = check_term where_info l c defined_refs t in
    if (!Settings.debug_cryptotransf) > 5 then
      begin
	print_string "check_term ";
	Display.display_term t;
	begin
	  match r with
	    ([],_,_)::_ -> print_string " succeeded\n"
	  | [] -> Parsing_helper.internal_error "ins_accu should not be empty (4)"
	  | _ ->
	      print_string " succeeded with advice\n";
              display_ins r
	end
      end;
    r
  with NoMatch ->
    fail (Term t)

let rec get_binders = function
    PatVar b -> 
      if !no_advice_mode then
	[]
      else
	[explicit_value b]
  | PatTuple (f,l) -> Terms.map_union Terms.equal_instruct get_binders l
  | PatEqual t -> []

(* [check_cterm t] checks that [t] contains no name or function symbol to 
   discharge, so that it can be left unchanged by the transformation *)

let rec check_cterm t =
  match t.t_desc with
    Var(b,l) ->
      if is_name_to_discharge b then
	raise NoMatch;
      List.iter check_cterm l
  | ReplIndex _ -> ()
  | FunApp(f,l) ->
      if List.memq f (!symbols_to_discharge) then
	raise NoMatch;
      List.iter check_cterm l
  | TestE(t1,t2,t3) ->
      check_cterm t1;
      check_cterm t2;
      check_cterm t3
  | FindE(l0,t3,_) ->
      List.iter (fun (bl, def_list, t1, t2) ->
	List.iter (fun (b,_) ->
	  if is_name_to_discharge b then
	    raise NoMatch) bl;
	List.iter check_cbr def_list;
	check_cterm t1;
	check_cterm t2) l0;
      check_cterm t3
  | LetE(pat,t1,t2,topt) ->
      check_cpat pat;
      check_cterm t1;
      check_cterm t2;
      begin
	match topt with
	  None -> ()
	| Some t3 -> check_cterm t3
      end
  | ResE(b,t) -> 
      if is_name_to_discharge b then
	raise NoMatch;
      check_cterm t
  | EventAbortE _ -> ()
  | EventE(t,p) -> check_cterm t; check_cterm p
  | GetE _ | InsertE _ ->
      Parsing_helper.internal_error "get, insert should have been expanded"

and check_cbr (_,l) =
  List.iter check_cterm l

and check_cpat = function
    PatVar b -> 
      if is_name_to_discharge b then
	raise NoMatch
  | PatTuple(f,l) -> List.iter check_cpat l
  | PatEqual t -> check_cterm t

(* For debugging *)

let check_cterm t =
  try
    check_cterm t 
  with NoMatch ->
    fail (UntransformableTerm t)


let rec check_any_term where_info ta_above accu cur_array defined_refs t =
  if Terms.check_simple_term t then
    and_ins (check_term where_info ta_above cur_array defined_refs t) accu
  else
    match t.t_desc with
    | Var(b,l) ->
	if is_name_to_discharge b then
	  raise NoMatch;
	check_any_term_list where_info [] accu cur_array defined_refs l
    | ReplIndex _ -> assert false
    | FunApp(f,l) ->
	if List.memq f (!symbols_to_discharge) then
	  raise NoMatch;
	check_any_term_list where_info [] accu cur_array defined_refs l
    | TestE(t1,t2,t3) ->
	check_any_term where_info []
	  (check_any_term where_info []
	     (check_any_term where_info [] accu cur_array defined_refs t1)
	     cur_array defined_refs t2)
	  cur_array defined_refs t3
    | FindE(l0,t3,_) ->
	let accu_ref = ref (check_any_term where_info [] accu cur_array defined_refs t3) in
	List.iter (fun (bl, def_list, t1, t2) ->
	  List.iter (fun (b,_) ->
	    if is_name_to_discharge b then
	      raise NoMatch) bl;
	  let repl_indices = List.map snd bl in
	  let (defined_refs_t1, defined_refs_t2) = Terms.defined_refs_find bl def_list defined_refs in
	  List.iter check_cbr def_list;
	  accu_ref :=
	     check_any_term where_info []
	       (check_any_term FindCond [] (!accu_ref) (repl_indices @ cur_array) defined_refs_t1 t1)
	       cur_array defined_refs_t2 t2
	       ) l0;
	!accu_ref
    | LetE(pat,t1,t2,topt) ->
	let vars = List.map Terms.binderref_from_binder (Terms.vars_from_pat [] pat) in
	let ins_pat = check_pat where_info accu cur_array defined_refs pat in
	let defined_refs' = vars @ defined_refs in
	let ins_t1 = check_any_term where_info (get_binders pat) ins_pat cur_array defined_refs' t1 in
	let ins_t2 = check_any_term where_info [] ins_t1 cur_array defined_refs' t2 in
	begin
	  match topt with
	    None -> ins_t2
	  | Some t3 -> check_any_term where_info [] ins_t2 cur_array defined_refs t3
	end
    | ResE(b,t) -> 
	check_any_term where_info [] accu cur_array ((Terms.binderref_from_binder b)::defined_refs) t
    | EventAbortE _ -> accu
    | EventE(t,p) ->
        (* Event not allowed in conditions of Find *)
	assert (where_info != FindCond);
	check_any_term where_info []
	  (check_event_term accu cur_array defined_refs t)
	  cur_array defined_refs p
    | GetE _ | InsertE _ ->
	Parsing_helper.internal_error "get, insert should have been expanded"

and check_pat where_info accu cur_array defined_refs = function
    PatVar b -> accu
  | PatTuple (f,l) -> check_pat_list where_info accu cur_array defined_refs l
  | PatEqual t -> check_any_term where_info [] accu cur_array defined_refs t

and check_pat_list where_info accu cur_array defined_refs = function
    [] -> accu
  | pat::l ->
      check_pat_list where_info
	(check_pat where_info accu cur_array defined_refs pat)
	cur_array defined_refs l

and check_event_term accu cur_array defined_refs t =
  if Terms.check_simple_term t then
    and_ins (check_term Event [] cur_array defined_refs t) accu
  else
    check_any_term ElseWhere [] accu cur_array defined_refs t
	
and check_any_term_list where_info ta_above accu cur_array defined_refs = function
    [] -> accu
  | (t::l) ->
      check_any_term_list where_info ta_above
	(check_any_term where_info ta_above accu cur_array defined_refs t)
	cur_array defined_refs l
    

let rec check_process accu cur_array defined_refs p =
  match p.i_desc with
    Nil -> accu
  | Par(p1,p2) ->
      check_process (check_process accu cur_array defined_refs p1) cur_array defined_refs p2
  | Repl(b,p) ->
      check_process accu (b::cur_array) defined_refs p
  | Input((c,tl),pat,p) ->
      List.iter check_cterm tl;
      let vars = List.map Terms.binderref_from_binder (Terms.vars_from_pat [] pat) in 
      let ins_pat = check_pat ElseWhere accu cur_array defined_refs pat in
      check_oprocess ins_pat cur_array (vars @ defined_refs) p

and check_oprocess accu cur_array defined_refs p = 
  match p.p_desc with
    Yield | EventAbort _ -> accu 
  | Restr(b,p) ->
      check_oprocess accu cur_array ((Terms.binderref_from_binder b)::defined_refs) p
  | Test(t,p1,p2) ->
      let accu' = check_any_term ElseWhere [] accu cur_array defined_refs t in
      (check_oprocess (check_oprocess accu' cur_array defined_refs p1) cur_array defined_refs p2)
  | Find(l0, p2, _) ->
      let accu_ref = ref (check_oprocess accu cur_array defined_refs p2) in
      List.iter (fun (bl, def_list, t, p1) ->
	let repl_indices = List.map snd bl in
	let (defined_refs_t, defined_refs_p1) = Terms.defined_refs_find bl def_list defined_refs in
	List.iter check_cbr def_list;
	accu_ref :=
	   check_oprocess
	     (check_any_term FindCond [] (!accu_ref) (repl_indices @ cur_array) defined_refs_t t)
	     cur_array defined_refs_p1 p1) l0;
      !accu_ref
  | Let(pat,t,p1,p2) ->
      let vars = List.map Terms.binderref_from_binder (Terms.vars_from_pat [] pat) in
      let ins_pat = check_pat ElseWhere accu cur_array defined_refs pat in
      let defined_refs' = vars @ defined_refs in
      let ins_t = check_any_term ElseWhere (get_binders pat) ins_pat cur_array defined_refs' t in
      check_oprocess (check_oprocess ins_t cur_array defined_refs' p1) cur_array defined_refs p2
  | Output((c,tl),t2,p) ->
      let tl_ins = check_any_term_list ElseWhere [] accu cur_array defined_refs tl in
      let t2_ins = check_any_term ElseWhere [] tl_ins cur_array defined_refs t2 in
      check_process t2_ins cur_array defined_refs p
  | EventP(t,p) ->
     let t_ins = check_event_term accu cur_array defined_refs t in
     check_oprocess t_ins cur_array defined_refs p
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

let check_process old_to_do =
  check_process old_to_do [] [] (Terms.get_process (!whole_game)) 

(* Additional checks for variables in the LHS that are accessed with indices given in argument *)

let check_lhs_array_ref() =
  List.iter (fun mapping ->
    List.iter (fun one_exp -> 
      let bf_array_ref_map = 
	List.map (fun ((b,l),(b',l')) ->
	  (* Find an expression M (mapping') that uses b' associated with b in a standard reference.
	     If there is no such expression, the transformation fails. *)
	  let mapping' =
	    try
	      List.find (fun mapping' ->
		List.exists (fun (b1,b1') -> (b1 == b) && (b1' == b')) mapping'.before_transfo_restr
		  ) (!map)
	    with Not_found ->
	      fail (RefWithIndicesWithoutMatchingStandardRef((b,l),(b',l')))
	  in
	  (* Display.display_var b l;
	  print_string " is mapped to ";
	  Display.display_var b' l';
	  print_string ".\n"; *)
	  (* Verify the condition on a prefix that is a sequence of replication indices:
	     if l has a prefix of length k0 that is a sequence of replication indices then
             mapping and mapping' share (at least) the first k0 sequences of random variables
	     (i.e. the last k0 elements of before_transfo_name_table)
	     { l'/b'.args_at_creation } \circ mapping'.rev_subst_name_indexes[j1-1] \circ ... \circ mapping'.rev_subst_name_indexes[k0] =
	     one_exp.name_indexes_exp[k0]
	     *)
	  let k0 = Terms.len_common_suffix l (List.map Terms.term_from_repl_index b.args_at_creation) in
	  if k0 > 0 then
	    begin
	      if not (List.for_all2 equal_binder_pair_lists
			(Terms.lsuffix k0 mapping.before_transfo_name_table)
			(Terms.lsuffix k0 mapping'.before_transfo_name_table))
	      then 
		fail (RefWithIndicesWithIncompatibleStandardRef((b,l),(b',l'),k0));
	      (* TO DO implement support for array references that use
	      both arguments and replication indices. Also modify
	      check.ml accordingly to allow such references 
	      (see TO DO in check.ml, function get_arg_array_ref) *)
	      Parsing_helper.internal_error "Error: array references that use both arguments and replication indices are not supported yet in the LHS of equivalences\n"
	    end;
	  ((b,l),(b',l'),mapping')
	    ) one_exp.before_transfo_array_ref_map
      in
      (* Verify the condition on common prefixes:
	 if (b1,l1),(b1',l1'),mapping1' and (b2,l2),(b2',l2'),mapping2' occur in the list,
	 l1 and l2 have a common prefix of length k0 that consists not only of replication indices,
	 then mapping1' and mapping2' share (at least) the first k0 sequences of random variables
	      (i.e. the last k0 elements of before_transfo_name_table)
	 { l1'/b1'.args_at_creation } \circ mapping1'.rev_subst_name_indexes[j1-1] \circ ... \circ mapping1'.rev_subst_name_indexes[k0] =
	 { l2'/b2'.args_at_creation } \circ mapping2'.rev_subst_name_indexes[j2-1] \circ ... \circ mapping2'.rev_subst_name_indexes[k0]
         where j1 = List.length l1, j2 = List.length l2
	 mapping.rev_subst_name_indexes[k] = the k-th element of the list starting from the end (the last element is numbered 1)
      *)
      let rec common_prefix = function
	  ((b1,l1),(b1',l1'),mapping1')::r ->
	    List.iter (function ((b2,l2),(b2',l2'),mapping2') ->
	      let k0 = Terms.len_common_suffix l1 l2 in
	      if k0 > Terms.len_common_suffix l1 (List.map Terms.term_from_repl_index b1.args_at_creation) then
		begin
		  if not (List.for_all2 equal_binder_pair_lists
			    (Terms.lsuffix k0 mapping1'.before_transfo_name_table)
			    (Terms.lsuffix k0 mapping2'.before_transfo_name_table))
		  then 
		    fail (IncompatibleRefsWithIndices((b1,l1),(b1',l1'),(b2,l2),(b2',l2'),k0));
	          (* TO DO implement support for array references that share
		     arguments. Also modify check.ml accordingly to allow such 
		     references 
		     (see TO DO in check.ml, function check_common_index) *)
		  Parsing_helper.internal_error "Error: array references that share arguments are not supported yet in the LHS of equivalences\n"
		end
	      ) r
	| [] -> ()
      in
      common_prefix bf_array_ref_map;

      (* Initialize one_exp.after_transfo_array_ref_map *)
      let (_, name_mapping) = (!equiv) in
      (*  map_list maps arguments of the LHS to arguments of the RHS
	  and replication indices of the LHS to replication indices of the RHS *)
      let args_assq = List.combine mapping.source_args mapping.target_args in
      let rec map_list args_at_creation = function
	  t :: r ->
	    begin
	      match t.t_desc with
		Var(b,l) -> 
		  begin
		    try
		      (* Argument of the LHS -> argument of the RHS *)
		      (Terms.term_from_binder (List.assq b args_assq))::(map_list args_at_creation r)
		    with Not_found -> 
		      Parsing_helper.internal_error "Variables used as array index should occur in the arguments"
		  end
	      |	ReplIndex b ->
		  (* Replication index *)
		  List.map Terms.term_from_repl_index (Terms.lsuffix (1+List.length r) args_at_creation)
	      | _ ->  Parsing_helper.internal_error "Variable or replication index expected as index in array reference"
	    end
	| [] -> []
      in
      (* print_string "Mapping start\n"; *)
      List.iter (fun (b_after,b_before,_) ->
	let l_b = List.filter (fun ((b,_),_,_) -> b == b_before) bf_array_ref_map in
	List.iter (fun ((_,l),(_,l'),mapping') ->
	  let b_after' = List.assq b_after mapping'.after_transfo_restr in
	  let l = map_list b_after.args_at_creation l in
	  (* print_string "Mapping ";
	  Display.display_var b_after l;
	  print_string " to ";
	  Display.display_var b_after' l';
	  print_newline(); *)
	  one_exp.after_transfo_array_ref_map <- ((b_after, l), (b_after', l')) :: one_exp.after_transfo_array_ref_map
	    ) l_b
	  ) name_mapping;

      (* Build the correspondence table from sequences of indices that
	 use indices passed as arguments to the oracle.
	 The indices [l] in the LHS of equiv correspond to [l'] in the process,
	 according to [bf_array_ref_map].
	 They also correspond to [l_rhs] in the RHS of equiv.
	 The encoding function for [l'] is bijectively associated to the
	 first variable in the list of restrictions that associates [b] to [b'],
	 this variable is [b'']. *)
      one_exp.after_transfo_input_index_map <-
	 List.map (fun ((b, l), (b', l'), mapping') ->
	   let l_rhs = map_list mapping'.target_cur_array l in
	   (* Find the restriction list that contains (b,b') *)
	   let lrestr = List.find (fun lrestr ->
	     List.exists (fun (b1,b1') -> (b1 == b) && (b1' == b')) lrestr
	       ) mapping'.before_transfo_name_table
	   in
	   (* [b''] the first variable in the restriction list that contains [b'] *)
	   let (_,b'') = List.hd lrestr in
	   (l_rhs, (b'', l')) 
	     ) bf_array_ref_map
	
	) mapping.expressions
      ) (!map)

(* Second pass: perform the game transformation itself *)

(* Constraint l1 = l2 *)

let rec make_constra_equal l1 l2 =
  match (l1,l2) with
    [],[] -> None
  | (a1::l1),(a2::l2) ->
      begin
      let t = Terms.make_equal a1 a2 in
      match make_constra_equal l1 l2 with
	None -> Some t
      |	Some t' -> Some (Terms.make_and t t')
      end
  | _ -> Parsing_helper.internal_error "Not same length in make_constra_equal"

(* Constraint eq_left = eq_right { cur_array_im / cur_array } *)

let rec make_constra cur_array cur_array_im eq_left eq_right =
  match (eq_left, eq_right) with
    [],[] -> None
  | (a::l),(b::l') -> 
      begin
      let t = Terms.make_equal a (Terms.subst cur_array cur_array_im b) in
      match make_constra cur_array cur_array_im l l' with
	None -> Some t
      |	Some t' -> Some (Terms.make_and t t')
      end
  | _ -> Parsing_helper.internal_error "Not same length in make_constra"
  
let and_constra c1 c2 =
  match (c1, c2) with
    (None, _) -> c2
  | (_, None) -> c1
  | (Some t1, Some t2) -> Some (Terms.make_and t1 t2)

let rename_br loc_rename br =
  try 
    assq_binderref br loc_rename
  with Not_found -> 
    Parsing_helper.internal_error "variable not found in rename_def_list"
      
let rename_def_list loc_rename def_list = 
  List.map (rename_br loc_rename) def_list

let introduced_events = ref []

(* Functions for encoding indices *)

let build_encode_fun name arg_types result_type =
  { f_name = Terms.fresh_id name;
    f_type = arg_types, result_type;
    f_cat = Tuple; (* Category Tuple implies that distinct functions yield distinct results (for any arguments *)
    f_options = Settings.fopt_COMPOS;
    f_statements = [];
    f_collisions = [];
    f_eq_theories = NoEq;
    f_impl = No_impl;
    f_impl_inv = None }
    
let encode_funs_for_binders = ref []

let encode_fun_for result_type b =
  let encode_funs_for_type = 
    try
      List.assq result_type (!encode_funs_for_binders)
    with Not_found ->
      let encode_funs_for_type = ref [] in
      encode_funs_for_binders := (result_type, encode_funs_for_type) :: (!encode_funs_for_binders);
      encode_funs_for_type
  in
  try
    List.assq b (!encode_funs_for_type)
  with Not_found ->
    let f = build_encode_fun
	("encode_idx_"^b.sname)
	(List.map (fun ri -> ri.ri_type) b.args_at_creation)
	result_type
    in
    encode_funs_for_type := (b, f) :: (!encode_funs_for_type);
    f
  
let encode_funs_for_exps = ref []

let encode_fun_for_exp result_type arg_types mapping =
  match mapping.encode_fun_for_indices with
  | Some f -> f
  | None ->
      let f = build_encode_fun "encode_idx_exp" arg_types result_type in
      mapping.encode_fun_for_indices <- Some f;
      begin
	try
	  let l = List.assq result_type (!encode_funs_for_exps) in
	  l := f :: (!l)
	with Not_found ->
	  encode_funs_for_exps := (result_type, ref [f]) :: (!encode_funs_for_exps)
      end;
      f

(* The encoding functions for indices are bijectively associated 
- either to the variable in the process corresponding to the first restriction 
of the list of restrictions that creates variables with the considered 
indices in the LHS of equiv.
- or to the expression itself in the process when the indices correspond to all
indices of the oracle, and there is no restriction under the replication
just above the definition of the oracle in the LHS of equiv.
(In this case, the [mapping] element contains a single [one_exp] element,
so we can associate the encoding function to the [mapping] element.)

The next type specifies these two cases. *)

type encode_fun_spec =
  | EncodeFunBinder of binder
  | EncodeFunExp of mapping
	
let rec put_restr l p =
  match l with
    [] -> p
  | (a::l) -> Terms.oproc_from_desc (Restr(a, put_restr l p))

let rec put_restr_term l t =
  match l with
  | [] -> t
  | a::l -> Terms.build_term t (ResE(a, put_restr_term l t))
                                    
let rec transform_term t =
  try
    let (mapping, one_exp) = find_map t in
    (* Mapping found; transform the term *)
    if (!Settings.debug_cryptotransf) > 5 then
      begin
	print_string "Instantiating term ";
	Display.display_term t;
	print_string " into ";
	Display.display_term mapping.target_exp;
	print_newline();
	print_string "Arguments: ";
	List.iter (fun (b,t) ->
	  Display.display_binder b;
	  print_string " -> ";
	  Display.display_term t;
	  print_newline()
	    ) one_exp.after_transfo_input_vars_exp;
        match one_exp.product_rest with
	| None -> ()
	| Some(prod, left_rest, right_rest, comp_neut) ->
	    begin
	      match left_rest with
	      | None -> ()
	      | Some t_left -> print_string "Left complement: "; Display.display_term t_left; print_newline()
	    end;
	    begin
	      match right_rest with
	      | None -> ()
	      | Some t_right ->  print_string "Right complement: "; Display.display_term t_right; print_newline()
	    end
      end;
    let restr_to_put = 
      (* When restrictions in the image have no corresponding
	 restriction in the source process, just put them
         immediately before the transformed term *)
      match mapping.before_transfo_name_table with
	[]::_ -> List.map snd (List.hd mapping.after_transfo_name_table)
      | _ -> []
    in
    let instance = Terms.delete_info_term (instantiate_term one_exp.cur_array_exp false [] [] mapping one_exp mapping.target_exp) in
    let result = 
    match one_exp.product_rest with
      None -> instance
    | Some(prod, left_rest, right_rest, comp_neut) ->
	let instance_with_left =
	  match left_rest with
	    None -> instance
	  | Some(t_left) -> Terms.app prod [transform_term t_left; instance]
	in
	let instance_with_both_sides =
	  match right_rest with
	    None -> instance_with_left
	  | Some(t_right) -> Terms.app prod [instance_with_left; transform_term t_right]
	in
	match comp_neut with
	  None -> instance_with_both_sides
	| Some(eqdiff, neut) -> Terms.app eqdiff [instance_with_both_sides; neut]
    in
    let result = put_restr_term restr_to_put result in
    if (!Settings.debug_cryptotransf) > 5 then
      begin
	print_string "yields "; Display.display_term result; print_newline()
      end;
    result
  with Not_found ->
    (* Mapping not found, the term is unchanged. Visit subterms *)
    Terms.build_term t 
      (match t.t_desc with
	Var(b,l) -> Var(b, List.map transform_term l)
      | FunApp(f,l) -> FunApp(f, List.map transform_term l)
      |	ReplIndex b -> ReplIndex b 
      | TestE _ | LetE _ | FindE _ | ResE _ | EventAbortE _ | EventE _ | GetE _ | InsertE _ -> 
	  Parsing_helper.internal_error "If, find, let, new, event, event_abort get, and insert should have been expanded (Cryptotransf.transform_term)")

and instantiate_term cur_array in_find_cond loc_rename loc_rename_idx mapping one_exp t =
  match t.t_desc with
    Var(b,l) ->
      begin
	try 
	  Terms.term_from_binderref (assq_binderref (b,l) loc_rename)
	with Not_found ->
	  (* map array accesses using one_exp.after_transfo_array_ref_map *) 
	  try
	    Terms.term_from_binderref (assq_binderref (b,l) one_exp.after_transfo_array_ref_map)
	  with Not_found -> 
          if not (Terms.is_args_at_creation b l) then
	    begin
	      Display.display_var b l;
              Parsing_helper.internal_error "Unexpected variable reference in instantiate_term"
	    end;
          try
	    transform_term (List.assq b one_exp.after_transfo_input_vars_exp)
	  with Not_found ->
	    try
	      Terms.term_from_binder (List.assq b one_exp.after_transfo_let_vars)
	    with Not_found ->
              let rec find_var restr indexes =
                match (restr, indexes) with
                  [], [] -> Parsing_helper.internal_error ("Variable " ^ (Display.binder_to_string b) ^ " not found in instantiate_term")
                | (restr1::restrl, (_,index1)::indexl) ->
		    begin
		      try
			Terms.term_from_binderref (List.assq b restr1, index1)
		      with Not_found ->
                        find_var restrl indexl
		    end
		| _ -> Parsing_helper.internal_error "restr and indexes have different lengths"
              in
              find_var mapping.after_transfo_name_table one_exp.name_indexes_exp
      end
  | ReplIndex _ ->
      Parsing_helper.internal_error "Replication index should not occur in instantiate_term"
      (* The code for the right-hand side of equivalences in check.ml 
	 checks that only expected variable references occur, and in 
	 particular replication indices do not occur. *)
  | FunApp(f,l) ->
      if List.exists (fun t -> t.t_type.tcat != BitString) l then
	begin
	  (* f must be an "encode_..." function *)
	  assert (f.f_cat == Tuple);
	(* Encoding of indices 
	   possible cases:
           - suffix of cur_array
	   - indices passed as argument
	   - indices of find
	   *)
	let l_len = List.length l in
	(* l = suffix of mapping.target_cur_array:
	   if l = mapping.target_cur_array with the n first elements omitted, then
	   - the variables in the n-th (starting from 0) list of restrictions of 
	   mapping.after_transfo_name_table use indices l
	   - the variables in the n-th (starting from 0) list of restrictions of 
	   mapping.before_transfo_name_table use indices that correspond to l with a renaming.
	   - in the process, these indices correspond to the n-th (starting from 0)
	   element of one_exp.name_indexes_exp
	   - the encoding function is bijectively associated to the first variable 
	   in the n-th (starting from 0) list of restrictions of 
	   mapping.before_transfo_name_table, named b'.
	   - however, when n = 0, it is possible that there is no such b':
	   there is no restriction just under the oracle definition.
	   In this case, the encoding function is bijectively associated to the
	   mapping element (and there is a single one_exp element in the mapping).
	   *)
	let find_index_seq_cur_array_suffix() = 
	  let cur_array_len = List.length mapping.target_cur_array in
          if cur_array_len >= l_len then
	    let cur_array_suffix = Terms.lsuffix l_len mapping.target_cur_array in
	    if List.for_all2 (fun t ri ->
	      match t.t_desc with
	      | ReplIndex ri' -> ri == ri'
	      | _ -> false) l cur_array_suffix then
	      (* Found: l is a suffix of mapping.target_cur_array *)
	      let (_,index1) = List.nth one_exp.name_indexes_exp (cur_array_len - l_len) in
	      let lrestr = List.nth mapping.before_transfo_name_table (cur_array_len - l_len) in
	      let fencode = 
		match lrestr with
		| [] ->
		(* Empty list of restrictions is allowed just before an input *)
		    assert (cur_array_len = l_len);
		    EncodeFunExp mapping
		| (b,b')::_ ->
		    EncodeFunBinder b'
	      in
	      (fencode, index1)
	    else
	      raise Not_found
	  else
	    raise Not_found
	in
	(* l = indices passed as argument.
	   Use the correpondence table built in one_exp.after_transfo_input_index_map *)
	let rec find_index_seq_input_indices = function
	  | [] -> raise Not_found
	  | (l0,(b',l'))::rest ->
	      if Terms.equal_term_lists l0 l then
		(* Found *)
		(EncodeFunBinder b', l')
	      else
		find_index_seq_input_indices rest
	in
	let (encode_fun_spec, l') = 
	  try
	    find_index_seq_cur_array_suffix()
	  with Not_found ->
	    try
	      find_index_seq_input_indices one_exp.after_transfo_input_index_map
	    with Not_found ->
	      try
	      (* l = indices of find
		 Use the correspondence table [loc_rename_idx] *)
		assq_idx l loc_rename_idx 
	      with Not_found -> 
		Display.display_term t;
		Parsing_helper.internal_error ("Sequence of indices not found in instantiate_term")
	in
	let fencode = 
	  match encode_fun_spec with
	  | EncodeFunExp mapping' ->
	      encode_fun_for_exp (snd f.f_type) (List.map (fun t -> t.t_type) l') mapping'
	  | EncodeFunBinder b' ->
	      encode_fun_for (snd f.f_type) b'
	in
	Terms.build_term t (FunApp(fencode, l'))
	end
      else
	Terms.build_term t (FunApp(f, List.map (instantiate_term cur_array in_find_cond loc_rename loc_rename_idx mapping one_exp) l))
  | TestE(t1,t2,t3) ->
      Terms.build_term t
	(TestE(instantiate_term cur_array in_find_cond loc_rename loc_rename_idx mapping one_exp t1,
	       instantiate_term cur_array in_find_cond loc_rename loc_rename_idx mapping one_exp t2,
	       instantiate_term cur_array in_find_cond loc_rename loc_rename_idx mapping one_exp t3))
  | FindE(l0, t3, find_info) -> 
      (* - a variable in def_list cannot refer to an index of 
	 another find; this is forbidden in syntax.ml. *)
      let find_exp = ref [] in
      List.iter (fun (bl,def_list,t1,t2) ->
	let bl_vars = List.map fst bl in
	let bl_vars_terms = List.map Terms.term_from_binder bl_vars in
	let bl_indices = List.map snd bl in
	let add_find (indexes, constra, var_map, idx_map) =
	  let vars = List.map (fun ri -> new_binder3 ri cur_array) indexes in
	  let vars_terms = List.map Terms.term_from_binder vars in
	  let loc_rename' = var_map @ loc_rename in
	  let loc_rename_idx' = idx_map @ loc_rename_idx in
	  (* replace replication indices with the corresponding variables in var_map *)
	  let var_map'' = List.map (function ((b,l),(b',l')) ->
	    ((b, List.map (Terms.subst bl_indices bl_vars_terms) l), 
	     (b', List.map (Terms.subst indexes vars_terms) l'))
	      ) var_map 
	  in
	  let loc_rename'' = var_map'' @ loc_rename in
	  let idx_map'' = List.map (function (l, (encode_fun_spec, l')) ->
	    (List.map (Terms.subst bl_indices bl_vars_terms) l,
	     (encode_fun_spec, List.map (Terms.subst indexes vars_terms) l'))
	      ) idx_map
	  in
	  let loc_rename_idx'' = idx_map'' @ loc_rename_idx in
	  find_exp :=
	     (List.combine vars indexes, 
	      begin
		let def_list' = rename_def_list var_map def_list in 
		match constra with
		  None -> def_list'
		| Some t -> 
		    (* when constra = Some t, I need to add in the def_list the array accesses that occur in t *)
		    let accu = ref def_list' in
		    Terms.get_deflist_subterms accu t;
		    !accu
	      end, 
	      begin
		let cur_array_cond = indexes @ cur_array in
		let t1' = instantiate_term cur_array_cond true loc_rename' loc_rename_idx' mapping one_exp t1 in
		match constra with
		  None -> t1' 
		| Some t -> Terms.make_and t t1'
	      end,
	      instantiate_term cur_array in_find_cond loc_rename'' loc_rename_idx'' mapping one_exp t2) :: (!find_exp)
	in
	match def_list with
	| [] ->
	    assert (bl == []);
	    add_find ([], None, [], [])
	| (_,(({ t_desc = ReplIndex(b0) }::_) as l1))::_ ->
	    let l_index = List.length bl in
	    let n = 
	      try
		Terms.find_in_list b0 bl_indices
	      with Not_found -> 
		l_index
		  (*Parsing_helper.internal_error "Variables in right member of equivalences should have as indexes the indexes defined by find\n"*)
	    in
	    let l_cur_array_suffix = List.length l1 - (l_index - n) in
            (* The longest sequence of indices of a variable in def_list is l_cur_array_suffix + l_index *)
	    (*let cur_array = List.map fst mapping.count in
	    let cur_array_suffix = Terms.lsuffix l_cur_array_suffix cur_array in*)
	    List.iter (fun mapping' ->
	      let cur_var_map = ref [] in
	      let cur_idx_map = ref [] in
	      let var_not_found = ref [] in
	      let depth_mapping = List.length mapping'.before_transfo_name_table in
	      if depth_mapping >= l_index + l_cur_array_suffix then
	      (* Check that the top-most l_cur_array_suffix sequences of fresh names
		 are common between mapping and mapping' *)
	      if List.for_all2 equal_binder_pair_lists
		  (Terms.lsuffix l_cur_array_suffix mapping'.before_transfo_name_table)
		  (Terms.lsuffix l_cur_array_suffix mapping.before_transfo_name_table) then
	      begin
	      (* Sanity check: check that the fresh names are also common after transformation *)
	      if not (List.for_all2 equal_binder_pair_lists
		  (Terms.lsuffix l_cur_array_suffix mapping'.after_transfo_name_table)
		  (Terms.lsuffix l_cur_array_suffix mapping.after_transfo_name_table)) then
		Parsing_helper.internal_error "Names are common before transformation but not after!";
	      let vcounter = Terms.get_var_num_state() in
	      let one_exp0 = List.hd mapping'.expressions in
	      let max_indexes = snd (List.nth one_exp0.name_indexes_exp (depth_mapping - (l_index + l_cur_array_suffix))) in
	      let map_indexes0_binders = List.map new_repl_index3 max_indexes in
	      let map_indexes0 = List.map Terms.term_from_repl_index map_indexes0_binders in
	      let (find_indexes, map_indexes, constra) =
		if l_cur_array_suffix > 0 then
		  let cur_array_indexes = snd (List.nth one_exp0.name_indexes_exp (depth_mapping - l_cur_array_suffix)) in
	          (* if cur_array_indexes is a suffix of max_indexes *)
		  let cur_array_suffix = 
		    (List.length cur_array_indexes <= List.length max_indexes) &&
		    (List.for_all2 Terms.equal_terms cur_array_indexes 
			(Terms.lsuffix (List.length cur_array_indexes) max_indexes))
		  in
		  if cur_array_suffix then
		      let find_indexes = Terms.remove_suffix (List.length cur_array_indexes) map_indexes0_binders in
		      let first_indexes = Terms.remove_suffix (List.length cur_array_indexes) map_indexes0 in
		      let map_indexes = first_indexes @ (snd (List.nth one_exp.name_indexes_exp (List.length one_exp.name_indexes_exp - l_cur_array_suffix))) in
		      (find_indexes, map_indexes, None)
		  else
		    try
		      let cur_array_indexes0 = reverse_subst_index max_indexes map_indexes0 cur_array_indexes in
		      let constra = make_constra_equal cur_array_indexes0 (snd (List.nth one_exp.name_indexes_exp (List.length one_exp.name_indexes_exp - l_cur_array_suffix))) in
		      (map_indexes0_binders, map_indexes0, constra)
		    with NoMatch ->
		      Parsing_helper.internal_error "reverse_subst_index failed in instantiate_term (1)"
		else
		  (map_indexes0_binders, map_indexes0, None)
	      in
	      List.iter (fun (b,l) ->
		try
		  let b' = List.assq b mapping'.after_transfo_restr in
		  let indexes = snd (List.nth one_exp0.name_indexes_exp (depth_mapping - List.length l)) in
		  cur_var_map := ((b,l),(b',reverse_subst_index max_indexes map_indexes indexes))::(!cur_var_map)
		with
		| Not_found ->
		    var_not_found := (b,l) :: (!var_not_found)
		| NoMatch ->
		    Parsing_helper.internal_error "reverse_subst_index failed in instantiate_term (2)"
		      ) def_list;
	      (* Compute cur_idx_map *)
	      let cur_array_suffix = Terms.lsuffix l_cur_array_suffix l1 in
	      (* We map indices [(suffix of bl_indices) @ cur_array_suffix]
		 We start with the longest list, [bl_indices @ cur_array_suffix] *)
	      let l_max = l_index + l_cur_array_suffix in
	      let max_l = (List.map Terms.term_from_repl_index bl_indices) @ cur_array_suffix in
	      let indexes_l = Terms.skip (depth_mapping - l_max) one_exp0.name_indexes_exp in
	      let before_name_table_l = Terms.skip (depth_mapping - l_max) mapping'.before_transfo_name_table in
	      let rec build_cur_idx_map indexes_l before_name_table_l l =
		(* We stop when l == cur_array_suffix *)
		if l == cur_array_suffix then () else 
		match indexes_l, before_name_table_l, l with
		| [], [], [] -> ()
		| (_,indexes)::indexes_rest, lrestr::before_name_table_rest, _::rest ->
		    let l' = reverse_subst_index max_indexes map_indexes indexes in
		    let encode_fun = 
		      match lrestr with
		      | [] -> 
		          (* Empty list of restrictions is allowed just before an input *)
			  assert (depth_mapping == l_max && l == max_l);
			  EncodeFunExp mapping'
		      | (_,b')::_ ->
			  EncodeFunBinder b'
		    in
		    cur_idx_map := (l, (encode_fun, l')) ::(!cur_idx_map);
		    build_cur_idx_map indexes_rest before_name_table_rest rest
		| _ ->
		    Parsing_helper.internal_error "build_cur_idx_map: lists should have same length"
	      in
	      build_cur_idx_map indexes_l before_name_table_l max_l;
	      
	      if (!var_not_found) == [] then
		begin
	          (* when several mappings have as common names all names referenced in the find
	             and the find does not reference let vars, then only one find expression should be
		     generated for all these mappings (they will yield the same find expression
		     up to renaming of bound variables)
		     The function find previous mapping looks for a previous mapping with
		     all names referenced in the find common with mapping' *) 
		  let rec find_previous_mapping = function
		      [] -> false
		    | (mapping''::l) ->
			if mapping'' == mapping' then false else
			let depth_mapping'' = List.length mapping''.before_transfo_name_table in
			if (depth_mapping'' >= l_index + l_cur_array_suffix) &&
			  (List.for_all2 equal_binder_pair_lists
			     (Terms.skip (depth_mapping - l_index - l_cur_array_suffix) mapping'.before_transfo_name_table)
			     (Terms.skip (depth_mapping'' - l_index - l_cur_array_suffix) mapping''.before_transfo_name_table)) then
			  true
			else
			  find_previous_mapping l
		  in
		  if find_previous_mapping (!map) then
		    Terms.set_var_num_state vcounter (* Forget index variables, since no find branch will be generated for this mapping *)
		  else
		    add_find (find_indexes, constra, !cur_var_map, !cur_idx_map)
		end
	      else if depth_mapping = l_index + l_cur_array_suffix then
	        (* Some variable was not found in after_transfo_restr;
	           Try to find it in after_transfo_let_vars
	           This is possible only if all indexes in the mapping are defined *)
		(* WARNING!! This code assumes that no find refers at the same time to
                   two let-variables defined in functions in parallel under the same replication
		   ==> we check in check.ml that this never happens. *)
		try 
		  let seen_let_vars = ref [] in
		  List.iter (fun one_exp' ->
		    (* When an expression with the same after_transfo_let_vars has already been seen,
		       we do not repeat the creation of a find. Indeed, this would yield exactly the same
		       references. *)
		    if not (List.memq one_exp'.after_transfo_let_vars (!seen_let_vars)) then
		    let exp_cur_var_map = ref (!cur_var_map) in
		    if (Terms.equal_term_lists (snd (List.hd one_exp'.name_indexes_exp)) (List.map Terms.term_from_repl_index one_exp'.cur_array_exp)) then
		      begin
			List.iter (fun (b,l) ->
			  let b' = List.assq b one_exp'.after_transfo_let_vars in
			  if List.length b'.args_at_creation != List.length map_indexes then
			    Parsing_helper.internal_error "Bad length for indexes (1)";
			  exp_cur_var_map := ((b,l),(b',map_indexes)) :: (!exp_cur_var_map)
				      ) (!var_not_found);
			seen_let_vars := one_exp'.after_transfo_let_vars :: (!seen_let_vars);
			add_find (find_indexes, constra, !exp_cur_var_map, !cur_idx_map)
		      end
		    else
		      begin
			let exp_map_indexes = List.map new_repl_index4 one_exp'.cur_array_exp in
			let constra2 = 
		    (* Constraint 
		         map_indexes = (snd (List.hd one_exp'.name_indexes_exp)) { exp_map_indexes / one_exp'.cur_array_exp } *)
			  make_constra one_exp'.cur_array_exp
			    (List.map Terms.term_from_repl_index exp_map_indexes)
			    map_indexes (snd (List.hd one_exp'.name_indexes_exp))
			in
			List.iter (fun (b,l) ->
			  let b' = List.assq b one_exp'.after_transfo_let_vars in
			  if List.length b'.args_at_creation != List.length exp_map_indexes then
			    Parsing_helper.internal_error "Bad length for indexes (2)";
			  exp_cur_var_map := ((b,l),(b',List.map Terms.term_from_repl_index exp_map_indexes)) :: (!exp_cur_var_map)
				  ) (!var_not_found);
			seen_let_vars := one_exp'.after_transfo_let_vars :: (!seen_let_vars);
			add_find (find_indexes @ exp_map_indexes, and_constra constra constra2, !exp_cur_var_map, !cur_idx_map)
		      end
			) mapping'.expressions
		with Not_found ->
	    (* Variable really not found; this mapping does not
	       correspond to the expected function *)
		  Terms.set_var_num_state vcounter (* Forget index variables, since no find branch will be generated for this mapping *)
	      else
		Terms.set_var_num_state vcounter (* Forget index variables, since no find branch will be generated for this mapping *)
              end
		    ) (!map)
	| _ -> Parsing_helper.internal_error "Bad index for find variable") l0;
      Terms.build_term t (FindE(!find_exp, instantiate_term cur_array in_find_cond loc_rename loc_rename_idx mapping one_exp t3, find_info))
  | LetE(pat,t1,t2,topt) ->
      let loc_rename_ref = ref loc_rename in
      let pat' = instantiate_pattern cur_array in_find_cond loc_rename_ref loc_rename_idx mapping one_exp pat in
      let loc_rename' = !loc_rename_ref in
      Terms.build_term t 
	(LetE(pat',
	      instantiate_term cur_array in_find_cond loc_rename' loc_rename_idx mapping one_exp t1,
	      instantiate_term cur_array in_find_cond loc_rename' loc_rename_idx mapping one_exp t2,
	      match topt with
		None -> None
	      |	Some t3 -> Some (instantiate_term cur_array in_find_cond loc_rename loc_rename_idx mapping one_exp t3)))
  | ResE(b,t') ->
      Terms.build_term t 
	(ResE((try
	  List.assq b one_exp.after_transfo_let_vars
        with Not_found ->
	  Parsing_helper.internal_error "Variable not found (ResE)"), 
	      instantiate_term cur_array in_find_cond loc_rename loc_rename_idx mapping one_exp t'))
  | EventAbortE(f) ->
      (* Create a fresh function symbol, in case the same equivalence has already been applied before *)
      let f' = { f_name = Terms.fresh_id f.f_name;
		 f_type = f.f_type;
		 f_cat = f.f_cat;
		 f_options = f.f_options;
		 f_statements = f.f_statements;
		 f_collisions = f.f_collisions;
		 f_eq_theories = f.f_eq_theories;
                 f_impl = No_impl;
                 f_impl_inv = None }
      in
      (* Add the event to introduced_events, to add it in the difference 
	 of probability and in the queries *)
      introduced_events := f' :: (!introduced_events);
      Terms.build_term t (EventAbortE(f'))
  | EventE _ | GetE _ | InsertE _ ->
      Parsing_helper.internal_error "event, get, insert should not occur in the RHS of equivalences"
	

and instantiate_pattern cur_array in_find_cond loc_rename_ref loc_rename_idx mapping one_exp = function
    PatVar b ->
      if in_find_cond then
	let b' = new_binder2 b cur_array in
	loc_rename_ref := (Terms.binderref_from_binder b, Terms.binderref_from_binder b') :: (!loc_rename_ref);
	PatVar b'
      else
	PatVar(try
	  List.assq b one_exp.after_transfo_let_vars
	with Not_found ->
	  Parsing_helper.internal_error "Variable not found")
  | PatTuple (f,l) -> PatTuple (f,List.map (instantiate_pattern cur_array in_find_cond loc_rename_ref loc_rename_idx mapping one_exp) l)
  | PatEqual t -> PatEqual (instantiate_term cur_array in_find_cond (!loc_rename_ref) loc_rename_idx mapping one_exp t)


(*
None: b is not a name to discharge
Some l: b found as first element of a sequence of variables.
-> put restrictions in l instead of the restriction that creates b
or when l = [],  b found as an element of a sequence of variables,
but not the first one; put no restriction instead of the restriction
that creates b
*)

let rec find_b_rec b = function
    [] -> None
  | (mapping::rmap) ->
      let (_,name_mapping) = !equiv in
      try
	let (b_left,_) = List.find (fun (_,b') -> b' == b) mapping.before_transfo_restr in
	let b_right_list = List.map (fun (x,_,_) -> x) (List.filter (fun (_,b',_) -> b' == b_left) name_mapping) in
	Some (List.map (fun b_right -> List.assq b_right mapping.after_transfo_restr) b_right_list)
      with Not_found ->
	find_b_rec b rmap

let rec check_not_touched t =
  match t.t_desc with
    Var(b,l) -> 
      begin
	match find_b_rec b (!map) with
	  None -> ()
	| Some _ -> Parsing_helper.internal_error "An array index should not be a random number, so should not be touched by cryptographic transformations."
      end
  | FunApp(f,l) -> List.iter check_not_touched l
  | ReplIndex _ -> ()
  | _ -> Parsing_helper.internal_error "If/find/let forbidden in defined condition of find"


let rec update_def_list suppl_def_list (b,l) =
  begin
  match find_b_rec b (!map) with
    None -> ()
  | Some l' -> 
      (* Do not add a condition that is already present *)
      let l' = List.filter (fun b' -> b' != b) l' in
      suppl_def_list := (List.map (fun b' -> (b',List.map (Terms.delete_info_term) l)) l') @ (!suppl_def_list)
  end;
  List.iter check_not_touched l
  (*List.iter (update_def_list_term suppl_def_list) l

and update_def_list_term suppl_def_list t =
  match t.t_desc with
    Var(b,l) -> update_def_list suppl_def_list (b,l)
  | FunApp(f,l) -> List.iter (update_def_list_term suppl_def_list) l
  | _ -> Parsing_helper.internal_error "If/find/let forbidden in defined condition of find"
*)

let rec transform_any_term t =
  if Terms.check_simple_term t then
    transform_term t 
  else
    match t.t_desc with
    | Var(b,l) ->
	Terms.build_term t (Var(b, List.map transform_any_term l))
    | ReplIndex i -> Terms.build_term t (ReplIndex i)
    | FunApp(f,l) ->
	Terms.build_term t (FunApp(f, List.map transform_any_term l))
    | ResE(b,t') ->
     (* Remove restriction when it is now useless *)
	let t'' = transform_any_term t' in
	begin
	  match find_b_rec b (!map) with
	  | None -> Terms.build_term t (ResE(b,t''))
	  | Some l ->
	      put_restr_term l 
		(if (not (List.memq b l)) && (b.root_def_std_ref || b.root_def_array_ref) then
		  Terms.build_term t (LetE(PatVar b, Stringmap.cst_for_type b.btype, t'', None))
		else
		  t'')
	end
    | TestE(t0, t1, t2) ->
	Terms.build_term t (TestE(transform_any_term t0, 
	                          transform_any_term t1,
                                  transform_any_term t2))
    | FindE(l0, p2, find_info) ->
	Terms.build_term t (FindE(List.map transform_term_find_branch l0, 
	                          transform_any_term p2, find_info))
    | LetE(pat,t0,t1,topt) ->
	Terms.build_term t (LetE(transform_pat pat, transform_any_term t0, 
				 transform_any_term t1,
				 match topt with
				 | None -> None
				 | Some t2 -> Some (transform_any_term t2)))
    | EventE(t0,t1) ->
	Terms.build_term t (EventE(transform_any_term t0,
	                           transform_any_term t1))
    | EventAbortE f -> Terms.build_term t (EventAbortE f)
    | GetE _ | InsertE _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

and transform_term_find_branch (bl, def_list, t, p1) = 
  let new_def_list = ref def_list in
  List.iter (update_def_list new_def_list) def_list;
  (bl, !new_def_list, transform_any_term t, transform_any_term p1) 

and transform_pat = function
  | PatVar b -> PatVar b
  | PatTuple (f,l) -> PatTuple (f,List.map transform_pat l)
  | PatEqual t -> PatEqual (transform_any_term t)

let rec transform_process cur_array p =
  Terms.iproc_from_desc (
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) ->
      Par(transform_process cur_array p1,
	  transform_process cur_array p2)
  | Repl(b,p) ->
      Repl(b, (transform_process (b::cur_array) p))
  | Input((c,tl),pat,p) ->
      let p' = transform_oprocess cur_array p in
      let pat' = transform_pat pat in
      Input((c, tl), pat', p'))
	
and transform_oprocess cur_array p = 
  match p.p_desc with
    Yield -> Terms.oproc_from_desc Yield
  | EventAbort f -> Terms.oproc_from_desc (EventAbort f)
  | Restr(b,p) ->
      (* Remove restriction when it is now useless *)
      let p' = transform_oprocess cur_array p in
      begin
	match find_b_rec b (!map) with
	  None -> Terms.oproc_from_desc (Restr(b,p'))
	| Some l ->
	    put_restr l 
	      (if (not (List.memq b l)) && (b.root_def_std_ref || b.root_def_array_ref) then
		Terms.oproc_from_desc (Let(PatVar b, Stringmap.cst_for_type b.btype, p', Terms.oproc_from_desc Yield))
              else
		p')
      end
  | Test(t,p1,p2) ->
      Terms.oproc_from_desc (Test(transform_any_term t, 
	   transform_oprocess cur_array p1, 
	   transform_oprocess cur_array p2))
  | Find(l0, p2, find_info) ->
      Terms.oproc_from_desc (Find(List.map (transform_find_branch cur_array) l0, 
	   transform_oprocess cur_array p2, find_info))
  | Let(pat,t,p1,p2) ->
      Terms.oproc_from_desc (Let(transform_pat pat, transform_any_term t, 
	  transform_oprocess cur_array p1, 
	  transform_oprocess cur_array p2))
  | Output((c,tl),t2,p) ->
      Terms.oproc_from_desc (Output((c, List.map transform_any_term tl), transform_any_term t2, 
	     transform_process cur_array p))
  | EventP(t,p) ->
      Terms.oproc_from_desc (EventP(transform_any_term t,
	     transform_oprocess cur_array p))
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

and transform_find_branch cur_array (bl, def_list, t, p1) = 
  let new_def_list = ref def_list in
  List.iter (update_def_list new_def_list) def_list;
  (bl, !new_def_list, transform_any_term t, transform_oprocess cur_array p1) 


let rec update_def_list_simplif_t t =
  Terms.build_term_at t (
  match t.t_desc with
  | Var(b,l) -> Var(b, List.map update_def_list_simplif_t l)
  | FunApp(f,l) -> FunApp(f, List.map update_def_list_simplif_t l)
  | (ReplIndex _ | EventAbortE _) as d -> d
  | TestE(t1,t2,t3) -> TestE(update_def_list_simplif_t t1,
			     update_def_list_simplif_t t2,
			     update_def_list_simplif_t t3)
  | FindE(l0, p2, find_info) ->
      let l0' =
	List.fold_right (fun (bl, def_list, t1, p1) laccu ->
	  try
	    let find_branch' =
	      let t1' = update_def_list_simplif_t t1 in
	      let p1' = update_def_list_simplif_t p1 in
	      let already_defined = Facts.get_def_vars_at (DTerm t) in
	      let newly_defined = Facts.def_vars_from_defined (Facts.get_initial_history (DTerm t)) def_list in
	      Facts.update_def_list_term already_defined newly_defined bl def_list t1' p1'
	    in
	    find_branch' :: laccu
	  with Contradiction ->
	    (* The variables in the defined condition cannot be defined,
	       I can just remove the branch *)
	    laccu
	  ) l0 []
      in
      FindE(l0', update_def_list_simplif_t p2, find_info)
  | LetE(pat, t1, t2, topt) ->
      LetE(update_def_list_simplif_pat pat,
	   update_def_list_simplif_t t1,
	   update_def_list_simplif_t t2,
	   match topt with
	   | None -> None
	   | Some t3 -> Some (update_def_list_simplif_t t3))
  | ResE(b,t) ->
      ResE(b, update_def_list_simplif_t t)
  | EventE(t1,p) ->
      EventE(update_def_list_simplif_t t1,
	     update_def_list_simplif_t p)
  | InsertE _ | GetE _ -> 
      Parsing_helper.internal_error "Get/Insert should not appear here")

and update_def_list_simplif_pat = function
  | (PatVar _) as pat -> pat
  | PatTuple(f,l) -> PatTuple(f, List.map update_def_list_simplif_pat l)
  | PatEqual t -> PatEqual (update_def_list_simplif_t t)
    
let rec update_def_list_simplif p =
  Terms.iproc_from_desc (
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) ->
      Par(update_def_list_simplif p1,
	  update_def_list_simplif p2)
  | Repl(b,p) ->
      Repl(b, update_def_list_simplif p)
  | Input((c,tl),pat,p) ->
      Input((c,List.map update_def_list_simplif_t tl),
	    update_def_list_simplif_pat pat,
	    update_def_list_simplifo p))

and update_def_list_simplifo p = 
  Terms.oproc_from_desc (
  match p.p_desc with
    Yield -> Yield
  | EventAbort f -> EventAbort f
  | Restr(b,p) -> Restr(b, update_def_list_simplifo p)
  | Test(t,p1,p2) ->
      Test(update_def_list_simplif_t t, 
	   update_def_list_simplifo p1, 
	   update_def_list_simplifo p2)
  | Find(l0, p2, find_info) ->
      let l0' =
	List.fold_right (fun (bl, def_list, t, p1) laccu ->
	  try
	    let find_branch' =
	      let t' = update_def_list_simplif_t t in
	      let p1' = update_def_list_simplifo p1 in
	      let already_defined = Facts.get_def_vars_at (DProcess p) in
	      let newly_defined = Facts.def_vars_from_defined (Facts.get_initial_history (DProcess p)) def_list in
	      Facts.update_def_list_process already_defined newly_defined bl def_list t' p1'
	    in
	    find_branch' :: laccu
	  with Contradiction ->
	    (* The variables in the defined condition cannot be defined,
	       I can just remove the branch *)
	    laccu
	  ) l0 []
      in
      Find(l0', update_def_list_simplifo p2, find_info)
  | Let(pat,t,p1,p2) ->
      Let(update_def_list_simplif_pat pat,
	  update_def_list_simplif_t t, 
	  update_def_list_simplifo p1, 
	  update_def_list_simplifo p2)
  | Output((c,tl),t2,p) ->
      Output((c, List.map update_def_list_simplif_t tl),
	     update_def_list_simplif_t t2, 
	     update_def_list_simplif p)
  | EventP(t,p) ->
      EventP(update_def_list_simplif_t t,
	     update_def_list_simplifo p)
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here")
	
let do_crypto_transform p = 
  Array_ref.array_ref_process p;
  let r = transform_process [] p in
  Array_ref.cleanup_array_ref();
  let r' =
    if !Settings.use_known_equalities_crypto then
      begin
	let r = Terms.move_occ_process r in
	Def.build_def_process None r;
	Incompatible.build_compatible_defs r;
	let r' = update_def_list_simplif r in
	Def.empty_def_process r;
	Incompatible.empty_comp_process r;
	r'
      end
    else
      r
  in
  r'

(* Compute the runtime of the context *)

let rec get_time_map t =
  let (mapping, one_exp) = find_map t in
  let args = List.map snd one_exp.after_transfo_input_vars_exp in
  (* Number of indexes at that expression in the process *)
  let il = List.length one_exp.cur_array_exp in
  (* Number of indexes at that expression in the equivalence *)
  let ik = List.length mapping.before_transfo_name_table in
  (* Replication indices of the LHS of the equivalence *)
  let repl_lhs = List.map (fun (brepl, _, _) -> brepl) mapping.count in
  let indices_exp = one_exp.name_indexes_exp  in
  (args, il, ik, repl_lhs, indices_exp)

type time_computed_t =
  | NotComputedYet
  | Computed of polynom
  | SingleUsage
    
let time_computed = ref NotComputedYet

let compute_runtime single_usage =
  match !time_computed with
  | Computed t -> t
  | NotComputedYet ->
      let tt = Polynom.sum (Computeruntime.compute_runtime_for_context (!whole_game) (!equiv) get_time_map (List.map fst (!names_to_discharge)))
	  (Polynom.probaf_to_polynom (AttTime))
      in
      if single_usage then
	begin
	  time_computed := SingleUsage;
	  tt
	end
      else
	begin
	  let res = Polynom.probaf_to_polynom (Time (ref "", Context(!whole_game), Polynom.polynom_to_probaf tt)) in
	  time_computed := Computed res;
	  res
	end
  | SingleUsage ->
      Parsing_helper.internal_error "Time should be used once and is queried several times"

(* Compute the difference of probability *)

(* We represent the number of usages of a repl. binder as follows:
   it is a list of lists of pairs (nt, v) where
       - nt is a name table (names in lhs of equivalence, names in initial process),
         or None
       - v is the number of usages associated with the expression of name table nt
   When several expressions have the same name table nt and it is not None, 
   they should be counted only once. 
   When the name table nt is None, each expression should be counted
   as many times as it appears.
   These pairs are grouped in a list, which is to be understood as a sum.
   (It corresponds to expressions that may be executed consecutively.)
   These lists are themselves grouped in another list, which is to be understood
   as a maximum. (It corresponds to sets of expressions that cannot be both
   evaluated, due to tests (if/find/let).)
*)

let is_in_map exp =
  List.exists (fun { expressions = e } ->
    List.exists (fun one_exp -> one_exp.source_exp_instance == exp) e) (!map)

let rec is_transformed t =
  (is_in_map t) || 
  (match t.t_desc with
  | Var(_,l) | FunApp(_,l) -> List.exists is_transformed l
  | ReplIndex _ -> false
  | TestE(t1,t2,t3) ->
      (is_transformed t1) || (is_transformed t2) || (is_transformed t3)
  | FindE(l0, t3,_) ->
      (is_transformed t3) ||
      (List.exists (fun (bl, def_list, t1, t2) ->
	(is_transformed t1) || (is_transformed t2)) l0)
  | LetE(pat, t1, t2, topt) ->
      (is_transformed_pat pat) ||
      (is_transformed t1) || (is_transformed t2) ||
      (match topt with
      | None -> false
      | Some t3 -> is_transformed t3)
  | ResE(b,t) ->
      is_transformed t
  | EventAbortE _ -> false
  | EventE(t1, t) ->
      (is_transformed t1) || (is_transformed t)
  | GetE _ | InsertE _ ->
      Parsing_helper.internal_error "get, insert should have been expanded")

and is_transformed_pat = function
  | PatVar b -> false
  | PatTuple(_,l) -> List.exists is_transformed_pat l
  | PatEqual t -> is_transformed t
    
type count_get =
    ReplCount of param
  | OracleCount of channel

let rec get_repl_from_count b_repl = function
    [] -> raise Not_found
  | ((b, dest, count_v)::l) -> 
      if (b_repl == Terms.param_from_type b.ri_type) && (dest == ForExp) then
	count_v
      else
	get_repl_from_count b_repl l

let get_oracle_count c (c', count_v) =
  if c == c' then
    count_v
  else
    raise Not_found

(* Structure for counting replication bounds and oracle calls *)

type el_link_t =
  | Elem of count_elem
  | ElLink of el_link_t ref
      
type formula =
    FElem of el_link_t ref
  | FZero
  | FPlus of formula * formula
  | FDiffBranch of repl_index list * formula * formula

let rec get_elem link =
  match !link with
  | Elem el -> el
  | ElLink link -> get_elem link

let get_elem1 link =
  match !link with
  | Elem el -> el
  | ElLink link -> assert false

(* Display functions, for debugging *)

let display_count_link count_link =
  let count_el = get_elem count_link in
  let (lhs_instance, _, _, _, _, _, _, _) = count_el.el_compat_info in
  Display.display_term lhs_instance;
  if (!Settings.debug_cryptotransf) > 2 then
    begin
      print_string " Indices above: ";
      Display.display_list Display.display_term count_el.el_indices_above;
      print_string " Indices: ";
      Display.display_list (fun (i,flag) ->
	Display.display_repl_index i;
	print_string
	  (match flag with
	  | NotCounted -> " ign"
	  | Counted -> " cnt")
	  ) count_el.el_indices;
      print_string " Count: ";
    end
  else
    print_string "  ";
  Display.display_proba 0 (Polynom.polynom_to_probaf [1.0,count_el.el_count]);
  print_newline()
	
let rec display_formula ind = function
  | FElem count_link ->
      print_string ind;
      display_count_link count_link
  | FZero ->
      print_string (ind^"0\n")
  | FPlus(f1,f2) ->
      print_string (ind^"Plus\n");
      display_formula (ind^"  ") f1;
      display_formula (ind^"  ") f2
  | FDiffBranch(cur_array,f1,f2) ->
      print_string (ind^"DiffBranch ");
      Display.display_list Display.display_repl_index cur_array;
      print_newline();
      display_formula (ind^"  ") f1;
      display_formula (ind^"  ") f2

(* Optimize the number of calls to oracles using #O *)

type optim_proba_state_t =
    { remaining_indices: term list;
      found_oracles: channel list;
      mutable current_candidate: (channel * term list) option }

let rec find_oracles state t =
  match t.t_desc with
  | ReplIndex _ -> ()
  | Var(b,l) -> find_oracles_br state (b,l)
  | FunApp(_,l) -> List.iter (find_oracles state) l
  | _ -> Parsing_helper.internal_error "If/let/find/new unexpected in find_oracles"

and find_oracles_br state (b,l) =
  let can_improve_current_candidate =
    match state.current_candidate with
    | None -> List.length l > 1
    | Some (_,l') ->
	(List.length l > List.length l') &&
	(List.for_all2 Terms.equal_terms (Terms.lsuffix (List.length l') l) l')
  in
  if can_improve_current_candidate &&
    (Terms.is_included_distinct Terms.equal_terms l state.remaining_indices)
  then
    try
      state.current_candidate <- Some (Computeruntime.get_oracle b, l)
    with Not_found ->
      List.iter (find_oracles state) l
  else
    List.iter (find_oracles state) l

let rec find_all_oracles state ttransf =
  if List.length state.remaining_indices <= 1 then state else
  begin
    find_oracles state ttransf;
    match state.current_candidate with
    | None -> state
    | Some (ch, l) ->
	let new_state =
	  { remaining_indices = Terms.remove_fail Terms.equal_terms state.remaining_indices l;
	    found_oracles = ch :: state.found_oracles;
	    current_candidate = None }
	in
	find_all_oracles new_state ttransf
  end
	
let get_opt_probaf indices ttransf =
  if (not (!Settings.use_oracle_count_in_result)) || (List.length indices <= 1) then
    Polynom.build_monomial (List.map (fun i -> Count (Terms.param_from_type i.ri_type)) indices)
  else
    let state =
      { remaining_indices = List.map Terms.term_from_repl_index indices;
	found_oracles = [];
	current_candidate = None }
    in
    let state' = find_all_oracles state ttransf in
    Polynom.build_monomial
      ((List.map (fun t -> Count (Terms.param_from_type t.t_type)) state'.remaining_indices) @
       (List.map (fun ch -> OCount ch) state'.found_oracles))
	
	
let seen_compat_info = ref []
let seen_names_count = ref []
    
(* Equality of name tables *)
	
let equal_nt1 la1 la2 =
  (List.length la1 == List.length la2) && 
  (List.for_all2 (fun (b1, b1') (b2, b2') ->
    (b1 == b2) && (b1' == b2')) la1 la2)

let equal_ntl la1 la2 =
  (List.length la1 == List.length la2) && 
  (List.for_all2 equal_nt1 la1 la2)

(* May raise Contradiction when [call2] is unreachable *)
let match_oracle_call_list list1  call2 =
  if list1 = [] then None else
  let proba_state = Proba.get_current_state() in
  let (t2, true_facts2, defined_vars2, above_indices2, all_indices2, initial_indices2, used_indices2, really_used_indices2) = call2.el_compat_info in
  let simp_facts2 = Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) true_facts2 in
  try
    let el_ref_found = 
      List.find (fun el_ref ->
	let call1 = get_elem1 el_ref in
	match Depanal.match_oracle_call simp_facts2 call1.el_compat_info call2.el_compat_info with
	| Some common_compat_info ->
	    el_ref := Elem { call1 with el_compat_info = common_compat_info };
	    true
	| None -> false
	      ) list1
    in
    Some el_ref_found
  with Not_found ->
    Proba.restore_state proba_state;
    None
    
let get_repl_from_map true_facts0 b_repl exp =
  let (mapping, one_exp) = find_map exp in
  let count_v = 
    match b_repl with
      ReplCount p -> get_repl_from_count p mapping.count
    | OracleCount c -> get_oracle_count c mapping.count_calls
  in
  let before_exp_instance =
    match one_exp.before_exp_instance with
    | None -> Parsing_helper.internal_error "before_exp_instance should be set when the crypto transformation completes"
    | Some before_exp_instance -> before_exp_instance
  in
  (* Collect all facts that are known to be true *)
  let true_facts = 
    try
      true_facts0 @ (Facts.get_facts_at (DTerm exp))
    with Contradiction ->
      [Terms.make_false()]
  in
  (* Collect all variables known to be defined *)
  let defined_vars =
    try
      List.map Terms.term_from_binderref (Facts.get_def_vars_at (DTerm exp))
    with Contradiction ->
      []
  in
  let (indices_kept, compat_info_elem) = Depanal.filter_indices before_exp_instance true_facts defined_vars count_v.indices_above one_exp.cur_array_exp count_v.indices in
  let el =
    { el_compat_info = compat_info_elem;
      el_incompatible = [];
      el_name_table_above_opt = count_v.name_table_above_opt;
      el_indices_above = count_v.indices_above;
      el_indices = indices_kept;
      el_count = get_opt_probaf (Depanal.get_counted indices_kept) exp;
      el_active = true;
      el_color = 0;
      el_index = -1 }
  in
  (* Invariant: all elements of [!seen_compat_info] are of the form
     [ref (Elem el)]. We use [ElLink] only for elements we remove from
     [!seen_compat_info]. *)

  (* Oracle calls with different name tables, they cannot correspond to
     the same oracle call *)
  let (same_nt, different_nt) =
    List.partition (fun el_ref ->
      match (get_elem1 el_ref).el_name_table_above_opt, el.el_name_table_above_opt with
      | Some nt1, Some nt2 -> equal_ntl nt1 nt2
      | _ -> true
	    ) (!seen_compat_info)
  in
  try
    match match_oracle_call_list same_nt el with
    | Some el_ref -> el_ref
    | None ->
	let el_ref' = ref (Elem el) in
	let same_nt' =
	  List.filter (fun el_ref ->
	    try 
	      match match_oracle_call_list [el_ref'] (get_elem1 el_ref) with
	      | Some el_ref' ->
		  el_ref := ElLink el_ref';
		  false
	      | None -> true
	    with Contradiction ->
	      (* In fact, [el_ref] is not executable, remove it *)
	      false
		  ) same_nt
	in
	seen_compat_info := el_ref' :: same_nt' @ different_nt;
	el_ref'
  with Contradiction ->
    (* In fact, this oracle [el] is not executable *)
    raise Not_found


let rec find_new_in_count p b_new = function
  | [] -> raise Not_found
  | (b_repl', ForNew b_new', count_v)::_
      when Terms.param_from_type b_repl'.ri_type == p && b_new' == b_new ->
	count_v
  | _::rest ->
      find_new_in_count p b_new rest

(* Finding one entry with "b_repl, ForNew b_new" is enough:
   the other entries are identical since when there is common
   name in 2 name tables, the other names above and in the same
   group of "new" must be the same, and the rev_subst_name_indexes
   must be the same. *)
	
let rec find_new_in_map p b_new = function
  | [] -> raise Not_found
  | entry::rest ->
      try
	find_new_in_count p b_new entry.count
      with Not_found ->
	find_new_in_map p b_new rest

let eq_ch (c1,tl1) (c2, tl2) =
  (c1 == c2) && (Terms.equal_term_lists tl1 tl2)

let rec get_oracle_idx_for_nodes lidx desired_result = function
  | [] -> raise Not_found
  | n::rest -> 
      let rec aux n = 
	match n.definition with
	| DInputProcess({ i_desc = Input((c,tl) as ch,_,_) })
	    when (List.length tl > 1) &&
	  (Terms.is_included_distinct Terms.equal_terms tl lidx) &&
	  (match desired_result with
	  | None -> true
	  | Some ch' -> eq_ch ch ch') ->
	      if rest == [] then ch else
	      begin
		try
		  (* Check that we can get the same result for the other nodes *)
		  ignore (get_oracle_idx_for_nodes lidx (Some ch) rest);
		  ch
		with Not_found ->
		  next n
	      end	    
	| _ ->
	    next n
      and next n =
	match n.above_node with
	| None -> raise Not_found
	| Some n' -> aux n'
      in
      aux n

let get_oracle lidx b =
  get_oracle_idx_for_nodes lidx None b.def

let get_opt_probaf_for_new indices b_new =
  if (not (!Settings.use_oracle_count_in_result)) || (List.length indices <= 1) then
    Polynom.build_monomial (List.map (fun i -> Count (Terms.param_from_type i.ri_type)) indices)
  else
    try
      let indices_terms = List.map Terms.term_from_repl_index indices in
      let (ch, idx_for_ch) = get_oracle indices_terms b_new in
      let remaining_indices = Terms.remove_fail Terms.equal_terms indices_terms idx_for_ch in
      Polynom.build_monomial
	((OCount ch)::
	 (List.map (fun t -> Count (Terms.param_from_type t.t_type)) remaining_indices))
    with Not_found -> 
      Polynom.build_monomial (List.map (fun i -> Count (Terms.param_from_type i.ri_type)) indices)
      
let get_repl_from_map_new b_repl b_new =
  try
    List.assq b_new (!seen_names_count)
  with Not_found ->
    let count_v =
      match b_repl with
      | ReplCount p ->
	  find_new_in_map p b_new (!map)
      | OracleCount _ -> raise Not_found
    in
    let br_new = Terms.binderref_from_binder b_new in
    (* Collect all facts that are known to be true.
       Considering all definitions of [b_new] replaces the use of 
       [Depanal.same_oracle_call] done in [get_repl_from_map]
       for counting oracle calls.
       It is slightly less precise, because we get only the common
       known facts directly, so we may filter fewer indices. 
       In [get_repl_from_map], we consider 2 oracle calls to be
       the same only if the common known facts allow to filter
       the same indices as the ones at one of the 2 oracle calls. *)
    let true_facts =
      try
	Facts.facts_from_defined None [br_new]
      with Contradiction ->
	[Terms.make_false()]
    in
    (* Collect all variables known to be defined *)
    let defined_vars =
      try
	List.map Terms.term_from_binderref (Facts.def_vars_from_defined None [br_new])
      with Contradiction ->
	[]
    in
    let term_new = Terms.term_from_binderref br_new in
    let (indices_kept, compat_info_elem) = Depanal.filter_indices term_new true_facts defined_vars count_v.indices_above b_new.args_at_creation count_v.indices in
    let el =
      { el_compat_info = compat_info_elem;
	el_incompatible = [];
	el_name_table_above_opt = count_v.name_table_above_opt;
	el_indices_above = count_v.indices_above;
	el_indices = indices_kept;
	el_count = get_opt_probaf_for_new (Depanal.get_counted indices_kept) b_new;
	el_active = true;
	el_color = 0;
	el_index = -1 }
    in
    let el_ref = ref (Elem el) in
    seen_names_count := (b_new, el_ref) :: (!seen_names_count);
    el_ref
  
    
let add_elem e f =
  match f with
    FZero -> FElem e
  | _ -> FPlus(FElem e, f)

let add f1 f2 =
  match f1,f2 with
    FZero, _ -> f2
  | _, FZero -> f1
  | _ -> FPlus(f1,f2)

let add_diff_branch cur_array f1 f2 =
  match f1,f2 with
    FZero, _ -> f2
  | _, FZero -> f1
  | _ -> FDiffBranch(cur_array, f1, f2)


let rec repl_count_term cur_array true_facts b_repl t =
  let accu' = 
    try
      let el_ref = get_repl_from_map true_facts b_repl t in
      FElem el_ref
    with Not_found -> 
      FZero
  in
  match t.t_desc with
    FunApp(f,[t1;t2]) when f == Settings.f_and ->
      if is_transformed t2 then
	(* t2 is evaluated only when t1 is true (otherwise, I know 
	   that the conjunction is false without evaluating t2), so I 
	   can add t1 to true_facts when dealing with t2 *)
	add accu'
	  (add (repl_count_term cur_array true_facts b_repl t1)
	     (repl_count_term cur_array (t1::true_facts) b_repl t2))
      else
	(* t2 is not transformed. For increasing precision, I assume 
	   that t2 is evaluated first, and then t1, so that t1 is evaluated 
	   only when t2 is true *)
	add accu' (repl_count_term cur_array (t2::true_facts) b_repl t1)
  | FunApp(f,[t1;t2]) when f == Settings.f_or ->
      if is_transformed t2 then
	(* t2 is evaluated only when t1 is false (otherwise, I know 
	   that the disjunction is true without evaluating t2), so I 
	   can add (not t1) to true_facts when dealing with t2 *)
	add accu'
	  (add (repl_count_term cur_array true_facts b_repl t1)
	     (repl_count_term cur_array ((Terms.make_not t1)::true_facts) b_repl t2)) 
      else
	(* t2 is not transformed. For increasing precision, I assume 
	   that t2 is evaluated first, and then t1, so that t1 is evaluated 
	   only when t2 is false *)
	add accu' (repl_count_term cur_array ((Terms.make_not t2)::true_facts) b_repl t1)
  | Var(_,l) | FunApp(_,l) ->
      add accu' (repl_count_term_list cur_array true_facts b_repl l)
  | ReplIndex _ | EventAbortE _ -> accu'
  | TestE(t, p1, p2) ->
      add (repl_count_term cur_array true_facts b_repl t)
	(add_diff_branch cur_array (repl_count_term cur_array true_facts b_repl p1)
	   (repl_count_term cur_array true_facts b_repl p2)) 
  | FindE(l0, p2, _) ->
      let rec find_lp = function
	  [] -> repl_count_term cur_array true_facts b_repl p2
	| (_,_,_,p1)::l ->
	    add_diff_branch cur_array (repl_count_term cur_array true_facts b_repl p1) (find_lp l)
      in
      let accu = find_lp l0 in
      let rec find_lt = function
	  [] -> accu
	| (bl,_,t,_)::l -> 
	    let cur_array' = (List.map snd bl) @ cur_array in
	    add (repl_count_term cur_array' true_facts b_repl t) (find_lt l)
      in
      find_lt l0
  | LetE(pat, t, p1, p2opt) ->
      add (add (repl_count_term cur_array true_facts b_repl t)
	     (repl_count_pat cur_array true_facts b_repl pat))
	(add_diff_branch cur_array
	   (repl_count_term cur_array true_facts b_repl p1)
	   (match p2opt with
	   | None -> FZero
	   | Some p2 -> repl_count_term cur_array true_facts b_repl p2)) 
  | ResE(b, p) ->
      let count_p = repl_count_term cur_array true_facts b_repl p in
      begin
	try
	  add_elem (get_repl_from_map_new b_repl b) count_p
	with Not_found ->
	  count_p
      end
  | EventE(t,p) -> 
      add (repl_count_term cur_array true_facts b_repl t)
	(repl_count_term cur_array true_facts b_repl p)
  | GetE _ | InsertE _ ->
      Parsing_helper.internal_error "get, insert should have been expanded"

and repl_count_term_list cur_array true_facts b_repl = function
    [] -> FZero
  | (a::l) ->
      add (repl_count_term_list cur_array true_facts b_repl l)
	(repl_count_term cur_array true_facts b_repl a) 

and repl_count_pat cur_array true_facts b_repl = function
    PatVar b -> FZero
  | PatTuple(_, l) -> repl_count_pat_list cur_array true_facts b_repl l
  | PatEqual t ->  repl_count_term cur_array true_facts b_repl t

and repl_count_pat_list cur_array true_facts b_repl = function
    [] -> FZero
  | (a::l) ->
      add (repl_count_pat_list cur_array true_facts b_repl l)
	(repl_count_pat cur_array true_facts b_repl a) 

let rec repl_count_process cur_array b_repl p =
  match p.i_desc with
    Nil -> FZero
  | Par(p1,p2) ->
      add (repl_count_process cur_array b_repl p1) (repl_count_process cur_array b_repl p2) 
  | Repl(b,p) ->
      repl_count_process (b::cur_array) b_repl p
  | Input((c,tl),pat,p) ->
      add (repl_count_term_list cur_array [] b_repl tl)
	(add (repl_count_pat cur_array [] b_repl pat) (repl_count_oprocess cur_array b_repl p))

and repl_count_oprocess cur_array b_repl p = 
  match p.p_desc with
    Yield | EventAbort _ -> FZero
  | Restr(b,p) ->
      let count_p = repl_count_oprocess cur_array b_repl p in
      begin
	try
	  add_elem (get_repl_from_map_new b_repl b) count_p
	with Not_found ->
	  count_p
      end
  | Test(t,p1,p2) ->
      add (repl_count_term cur_array [] b_repl t)
	(add_diff_branch cur_array (repl_count_oprocess cur_array b_repl p1) (repl_count_oprocess cur_array b_repl p2)) 
  | Let(pat, t, p1, p2) ->
      add (add (repl_count_term cur_array [] b_repl t)
	     (repl_count_pat cur_array [] b_repl pat))
	(add_diff_branch cur_array (repl_count_oprocess cur_array b_repl p1) (repl_count_oprocess cur_array b_repl p2)) 
  | Find(l0,p2, _) ->
      let rec find_lp = function
	  [] -> repl_count_oprocess cur_array b_repl p2
	| (_,_,_,p1)::l -> add_diff_branch cur_array (repl_count_oprocess cur_array b_repl p1) (find_lp l)
      in
      let accu = find_lp l0 in
      let rec find_lt = function
	  [] -> accu
	| (bl,_,t,_)::l ->
	    let cur_array' = (List.map snd bl) @ cur_array in
	    add (repl_count_term cur_array' [] b_repl t) (find_lt l)
      in
      find_lt l0
  | Output((c,tl),t2,p) ->
      add (repl_count_term_list cur_array [] b_repl tl)
	(add (repl_count_term cur_array [] b_repl t2)
	   (repl_count_process cur_array b_repl p))
  | EventP(t,p) -> 
      add (repl_count_term cur_array [] b_repl t)
	(repl_count_oprocess cur_array b_repl p) 
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

(* [formula_to_coef f]
   The formula [f] contains elements that all have the same monomial
   [el_count] (see [formula_to_polynom] below).
   We want to compute the sum of all elements in [f], except
   that we take the max when two elements are incompatible
   (cannot be both executed), either
   - by 
   [not (Depanal.is_compatible_indices el1.el_compat_info el2.el_compat_info)]
   - because they are in different branches of a test, as specified by
   [FDiffBranch(cur_array, f1, f2)], provided [cur_array] appears
   at the same positions in the determined or counted indices in
   both elements, as verified by 
   [is_included_same_position cur_array el1.el_indices el2.el_indices].

   Since the monomial is always the same, we just need to compute
   the coeficient for this monomial, counting 1 for each element
   in the formula. The desired coefficient is then the size of the
   maximum set of compatible elements in the formula.

   To do that, we build a graph whose nodes are the elements in the
   formula, and two nodes are linked by an edge when they are incompatible.
   Then we compute the size of the maximum independent set for this graph.

   Tarjan, R. E.; Trojanowski, A. E. (1977), Finding a maximum independent set,
   SIAM Journal on Computing, 6 (3): 537–546, doi:10.1137/0206038.
   http://i.stanford.edu/pub/cstr/reports/cs/tr/76/550/CS-TR-76-550.pdf
   provides a good algorithm for that, in O(2^(n/3)).
   Here, for simplicity, we implement a more naive algorithm in O(2^n).
   (Note: this is the dual of the well-known maximal clique problem.
   It is an NP-complete problem.)
      *)

let rec component_to_coef = function
  | [] -> 0
  | [n] ->
      if n.el_active then 1 else 0
  | n::rest ->
      if not n.el_active then
	component_to_coef rest
      else
	begin
	  n.el_active <- false;
	  (* [coef1] corresponds to the case in which the maximum 
             independent set does not contain [n] *)
	  let coef1 = component_to_coef rest in
	  let deactivated = ref [] in
	  List.iter (fun el ->
	    if el.el_active then
	      begin
		deactivated := el :: !(deactivated);
		el.el_active <- false
	      end
		) n.el_incompatible;
	  (* [coef2] corresponds to the case in which the maximum 
             independent set contains [n], so it does not contain
	     the nodes incompatible with [n], which have been 
	     temporarily deactivated. *)
	  let coef2 = 1 + component_to_coef rest in
	  List.iter (fun el -> el.el_active <- true) (!deactivated);
	  n.el_active <- true;
	  max coef1 coef2
	end
	
(* [get_component component_ref node] gets a connected component from [node]. 
   The nodes of the component are stored in [component_ref]. 
   All nodes must initially have color 0. The nodes of the component
   have color 2 after the computation. *)
	
let rec get_component component_ref node =
  if node.el_color = 0 then
    begin
      node.el_color <- 1;
      component_ref := node :: (!component_ref);
      List.iter (get_component component_ref) node.el_incompatible;
      node.el_color <- 2
    end
      
(* [graph_to_coef nodes] splits the graph of nodes [nodes]
   into connected components, and computes the sum of the
   coefficients for each component. *)
	
let rec graph_to_coef = function
  | [] -> 0
  | node :: rest ->
      if not node.el_active then
	graph_to_coef rest
      else
	let component_ref = ref [] in
	get_component component_ref node;
	let component = !component_ref in
	List.iter (fun el -> el.el_color <- 0) component;
	let coef1 = component_to_coef component in
	List.iter (fun el -> el.el_active <- false) component;
	let coef2 = graph_to_coef rest in
	coef1 + coef2
	
let is_incomp_diffbranch cur_array el1 el2 =
  let mapping = Depanal.build_idx_mapping
      (el1.el_indices_above, el1.el_indices)
      (el2.el_indices_above, el2.el_indices)
  in
  List.for_all (fun b -> List.exists (fun (i1, i2opt) ->
    match i2opt with
    | Some i2 -> b == i2 && b == i1
    | _ -> false) mapping) cur_array


(* [set_idx (idx, nodes) formula] sets in the index of
   all nodes in the formula. 
   [idx] is first index to use, 
   [nodes] is the list of already seen nodes.
   It returns the first unused index, to use next,
   as well as the list of nodes in [nodes] and [formula]. *)
let rec set_idx ((idx, nodes) as accu) = function
  | FZero -> accu
  | FElem e ->
      let e = get_elem e in
      if e.el_index = -1 then
	begin
	  e.el_index <- idx; (idx+1, e::nodes)
	end
      else
	accu
  | FPlus(f1,f2)| FDiffBranch(_, f1, f2) ->
      set_idx (set_idx accu f1) f2

(* [iter_f func formula] applies function [func] to
   each element in [formula] *)
let rec iter_f f = function
  | FZero -> ()
  | FElem e -> f (get_elem e)
  | FPlus(f1,f2)| FDiffBranch(_, f1, f2) ->
      iter_f f f1;
      iter_f f f2

let rec build_incomp_fdiffbranch incomp_matrix = function
  | FZero | FElem _ -> ()
  | FPlus(f1,f2) ->
      build_incomp_fdiffbranch incomp_matrix f1;
      build_incomp_fdiffbranch incomp_matrix f2;
      iter_f (fun el1 ->
	iter_f (fun el2 ->
	  let i1 = el1.el_index in
	  let i2 = el2.el_index in
	  incomp_matrix.(i1).(i2) <- false;
	  incomp_matrix.(i2).(i1) <- false
	       ) f2
	  ) f1
  | FDiffBranch(cur_array, f1, f2) ->
      build_incomp_fdiffbranch incomp_matrix f1;
      build_incomp_fdiffbranch incomp_matrix f2;
      iter_f (fun el1 ->
	iter_f (fun el2 ->
	  let i1 = el1.el_index in
	  let i2 = el2.el_index in
	  if incomp_matrix.(i1).(i2) &&
	    (not (is_incomp_diffbranch cur_array el1 el2))
	  then
	    begin
	      incomp_matrix.(i1).(i2) <- false;
	      incomp_matrix.(i2).(i1) <- false
	    end
	       ) f2
	  ) f1

let rec build_incomp_depanal incomp_matrix = function
    [] -> ()
  | el1::rest ->
      build_incomp_depanal incomp_matrix rest;
      List.iter (fun el2 ->
	let i1 = el1.el_index in
	let i2 = el2.el_index in
	if not (incomp_matrix.(i1).(i2)) &&
	  not (Depanal.is_compatible_indices el1.el_compat_info el2.el_compat_info) then
	  begin
	    incomp_matrix.(i1).(i2) <- true;
	    incomp_matrix.(i2).(i1) <- true
	  end
	    ) rest
	
let formula_to_coef f =
  iter_f (fun el -> el.el_index <- -1) f;
  let (nidx,nodes) = set_idx (0,[]) f in
  (* Initially consider all elements as incompatible *)
  let incomp_matrix = Array.make_matrix nidx nidx true in
  (* Mark all nodes compatible, except those always 
     in different branches of FDiffBranches, with cur_array
     occurring at the same positions. 
     It is important to proceed in this way, in case the
     same node occurs at several positions (due to the 
     Depanal.same_oracle_call test), some compatible
     according to FDiffBranch, some not: it should be considered
     compatible in this case *)
  build_incomp_fdiffbranch incomp_matrix f;
  (* Mark nodes incompatible when Depanal.is_compatible_indices
     says it. *)
  build_incomp_depanal incomp_matrix nodes;
  (* Translate the matrix into an adjacency list *)
  List.iter (fun el1 ->
    el1.el_incompatible <-
       List.filter (fun el2 ->
	 let i1 = el1.el_index in
	 let i2 = el2.el_index in
	 incomp_matrix.(i1).(i2)
	   ) nodes
      ) nodes;
  (* Now the graph is built *)
  List.iter (fun el -> el.el_color <- 0) nodes;
  graph_to_coef nodes

(* [partition_formula p f] returns (f1,f2) where f1
   contains the part of [f] whose elements satisfy [p],
   and f2 is the rest of [f]. *)
    
let rec partition_formula p = function
  | (FElem elem) as e ->
      if p elem then
	(e, FZero)
      else
	(FZero, e)
  | FZero ->
      (FZero, FZero)
  | FPlus (f1, f2) ->
      let (f1, f1') = partition_formula p f1 in
      let (f2, f2') = partition_formula p f2 in
      (add f1 f2, add f1' f2')
  | FDiffBranch(cur_array, f1, f2) ->
      let (f1, f1') = partition_formula p f1 in
      let (f2, f2') = partition_formula p f2 in
      (add_diff_branch cur_array f1 f2, add_diff_branch cur_array f1' f2')

(* [get_one_elem f] returns [None] when [f] contains 
   no element, and [Some elem] when [f] contains
   at least one element [elem]. *)
	
let rec get_one_elem = function
  | FZero -> None
  | FElem elem -> Some elem
  | FPlus(f1,f2) | FDiffBranch(_,f1,f2) ->
      begin
	match get_one_elem f1 with
	| (Some _) as x -> x
	| None -> get_one_elem f2
      end

(* Elements that different [el_name_table_above_opt] necessarily
   correspond to different values of the above replication index,
   so we can take a max between them. To do that, we partition the
   formula according to the value of [el_name_table_above_opt],
   and take the max of the obtained coefficient.
   (All elements in [f] here have the same monomial [el_count], 
   see [formula_to_polynom] below, so it is enough to compute the
   coefficient of this monomial.) *)
	
let rec formula_to_coef_partition_name_table f =
  match get_one_elem f with
  | None ->
      0
  | Some elem ->
      match (get_elem elem).el_name_table_above_opt with
      | None -> formula_to_coef f
      | Some nt ->
	  let (f_this_nt, f_rest) = 
	    partition_formula (fun elem' ->
	      match (get_elem elem').el_name_table_above_opt with
	      | None -> assert false
	      | Some nt' -> equal_ntl nt nt') f
	  in
	  let coef1 = formula_to_coef f_this_nt in
	  let coef_rest = formula_to_coef_partition_name_table f_rest in
	  max coef1 coef_rest

(* [formula_to_polynom f] converts the formula [f] into a polynom.
   It first partitions the formula [f] into elements that have the
   same monomial [el_count] and computes the coefficient of these
   monomials. There are two motivations for doing that:
   1/ we want a fairly simple result, so we will not combine max
   with polynoms. Hence, when we have two terms with different
   monomials, we can only add them. The max will be taken only
   on the coefficients (when possible).
   (Before, this was done using Polynom.max, but the implementation
   that first partitions the formula is more efficient, because
   the runtime of [formula_to_coef] is exponential in the size
   of the formula, so it is better to call [formula_to_coef] with
   small formulas.)
   2/ this is needed for soundness: when we use different #O values
   inside monomials corresponding to the same indices, we must take
   the sum, not the max. Example:
   !N1 !N2 if ... then ... O1() := new n ... else ... O2() := new n
   the number created N's is bounded by #O1 + #O2, not by max(#O1, #O2);
   it could also be bounded by N1 * N2, and this case we can take the
   max between the "then" and the "else" which can both create N1 * N2
   times n, but are mutually exclusive.
*)
	    
let rec formula_to_polynom f =
  match get_one_elem f with
  | None ->
      Polynom.zero
  | Some elem ->
      let monomial = (get_elem elem).el_count in
      let (f_this_monomial, f_rest) =
	partition_formula (fun elem' -> Polynom.same_monomial (get_elem elem').el_count monomial) f
      in
      let coef = float_of_int (formula_to_coef_partition_name_table f_this_monomial) in
      (coef, monomial)::(formula_to_polynom f_rest)
    

let rec rename_term before map one_exp t =
  match t.t_desc with
    FunApp(f,l) -> 
      Terms.build_term t (FunApp(f, List.map (rename_term before map one_exp) l))
  | Var(b,l) -> 
      begin
	if not (Terms.is_args_at_creation b l) then
          Parsing_helper.internal_error "Unexpected variable reference in rename_term";
	if before then
	  try
	    List.assq b one_exp.before_transfo_input_vars_exp
	  with Not_found ->
	    Terms.term_from_binder (List.assq b map.before_transfo_restr)
	    (* Raises Not_found when the variable is not found.
	       In this case, the considered expression has no contribution 
	       to the maximum length. *)
	else
	  try
	    List.assq b one_exp.after_transfo_input_vars_exp
	  with Not_found ->
	    try
	      Terms.term_from_binder (List.assq b one_exp.after_transfo_let_vars)
	    with Not_found ->
		Terms.term_from_binder (List.assq b map.after_transfo_restr)
      end
  | _ -> Parsing_helper.internal_error "If/let/find/res and replication indices not allowed in rename_term"
	(* Replication indices cannot occur because 
	   - in the initial probability formulas, in syntax.ml, the variable
	   references are always b[b.args_at_creation].
	   - these probability formulas are not modified before being
	   passed to rename_term. In particular, Computeruntime.make_length_term,
	   which may create Maxlength(g, repl_index), is not called before 
	   passing t to rename_term; it is called after.
	   Proba.instan_time only deals with collisions. *)

let single_att_time prob =
  let count_att_time = ref 0 in
  let rec aux prob =
    (!count_att_time >= 2) ||
    (match prob with
    | AttTime -> incr count_att_time; !count_att_time >= 2
    | _ -> Terms.exists_sub_probaf aux prob)
  in
  ignore (aux prob);
  !count_att_time <= 1
	
let rec map_probaf env prob =
  let single_att_time_prob = single_att_time prob in
  let rec aux under_complex_time = function
    | (Cst _ | Card _ | TypeMaxlength _ | EpsFind | EpsRand _ | PColl1Rand _ | PColl2Rand _ ) as x -> Polynom.probaf_to_polynom x
    | Proba(p,l) ->
	Polynom.probaf_to_polynom (Proba(p, List.map (fun prob ->
	  if Proba.is_complex_time prob then
	    let prob' = Polynom.polynom_to_probaf (aux true prob) in
	    match prob' with
	    | Time _ -> prob' (* in case the complex time formula was reduced
                                 to just the runtime of the adversary *)
	    | _ -> Time(ref "", Complex, prob')
	  else
	    Polynom.polynom_to_probaf (aux false prob)
	      ) l))
  | ActTime(f, l) -> 
      Polynom.probaf_to_polynom (ActTime(f, List.map (fun prob -> 
      Polynom.polynom_to_probaf (aux under_complex_time prob)) l))
  | (Max _ | Maxlength _) as y ->
      let accu = ref Polynom.empty_minmax_accu in
      let rec add_max = function
	| Max(l) -> List.iter add_max l
	| Maxlength(g,t) ->
	    List.iter (fun map -> 
	      List.iter (fun one_exp -> 
		try
		  let (game, before) =
		    if g == Terms.lhs_game then
		      !whole_game, true
		    else if g == Terms.rhs_game then
		      whole_game_middle, false
		    else
		      Parsing_helper.internal_error "Maxlength should refer to the LHS or the RHS of the equivalence"
		  in
		  Computeruntime.make_length_term accu game (rename_term before map one_exp t)
		with Not_found -> 
		  ()
		    ) map.expressions
		) (!map)
	| x ->
	    Polynom.add_max accu
	      (Polynom.polynom_to_probaf (aux under_complex_time x))
      in
      add_max y;
      Polynom.probaf_to_polynom (Polynom.p_max (!accu))
  | Min(l) -> 
      let accu = ref Polynom.empty_minmax_accu in
      let rec add_min = function
	| Min(l) -> List.iter add_min l
	| x ->
	    Polynom.add_min accu
	      (Polynom.polynom_to_probaf (aux under_complex_time x))
      in
      List.iter add_min l;
      Polynom.probaf_to_polynom (Polynom.p_min (!accu))
  | Length(f,l) ->
      Polynom.probaf_to_polynom (Length(f, List.map (fun prob -> 
	Polynom.polynom_to_probaf (aux under_complex_time prob)) l))
  | Count p -> 
      begin
	try
	  List.assq p (! (fst env))
	with Not_found ->
	  seen_compat_info := [];
	  seen_names_count := [];
	  let v = repl_count_process [] (ReplCount p) (Terms.get_process (!whole_game)) in
	  if (!Settings.debug_cryptotransf) > 1 then
	    begin
	      if (!seen_compat_info) != [] then
		begin
		  assert((!seen_names_count) = []);
		  print_string ("List of oracles for "^p.pname^"\n");
		  List.iter display_count_link (!seen_compat_info)
		end
	      else if (!seen_names_count) != [] then
		begin
		  print_string ("List of names for "^p.pname^"\n");
		  List.iter (fun (_,el_ref) -> display_count_link el_ref) (!seen_names_count)
		end
	      else
		print_string ("Nothing for "^p.pname^"\n")
	    end;
	  seen_compat_info := [];
	  seen_names_count := [];
	  let v' = formula_to_polynom v in
	  fst env := (p, v') :: (! (fst env));
	  v'
      end
  | OCount c -> 
      begin
	try
	  List.assq c (! (snd env))
	with Not_found ->
	  seen_compat_info := [];
	  let v = repl_count_process [] (OracleCount c) (Terms.get_process (!whole_game)) in
	  if (!Settings.debug_cryptotransf) > 1 then
	    begin
	      if (!seen_compat_info) != [] then
		begin
		  print_string ("List of oracles for #"^c.cname^"\n");
		  List.iter display_count_link (!seen_compat_info)
		end
	      else
		print_string ("Nothing for #"^c.cname^"\n")
	    end;
	  seen_compat_info := [];
	  let v' = formula_to_polynom v in
	  snd env := (c, v') :: (! (snd env));
	  v'
      end
  | Mul(x,y) ->
      Polynom.product (aux under_complex_time x) (aux under_complex_time y)
  | Add(x,y) ->
      Polynom.sum (aux under_complex_time x) (aux under_complex_time y)
  | Sub(x,y) ->
      Polynom.sub (aux under_complex_time x) (aux under_complex_time y)
  | Div(x,y) -> Polynom.probaf_to_polynom 
	(Polynom.p_div(Polynom.polynom_to_probaf (aux under_complex_time x), 
		       Polynom.polynom_to_probaf (aux under_complex_time y)))
  | Power(x,n) -> Polynom.power_to_polynom_map (aux under_complex_time) x n
  | Zero -> Polynom.zero
  | AttTime ->
      let single_usage = under_complex_time && single_att_time_prob in
      compute_runtime single_usage
  | OptimIf(cond, p1, p2) ->
      if Proba.is_sure_cond (aux under_complex_time) cond then
	aux under_complex_time p1
      else
	aux under_complex_time p2
  | Time _ -> Parsing_helper.internal_error "Unexpected time"
  in
  aux false prob
    
let compute_proba ((_,_,_,set,_,_),_) =
  Depanal.reset [] (!whole_game);
  let proba = 
    List.filter (function SetProba (Zero) -> false
      | _ -> true)
      (List.map (function 
	  SetProba r ->
	    let probaf' =  map_probaf (ref [], ref []) r in
	    SetProba (Polynom.polynom_to_probaf probaf')
	| SetEvent _ | SetAssume -> 
	    Parsing_helper.internal_error "Event/assume should not occur in probability formula") set)
  in
  (* Add the probabilities of the collisions eliminated to optimize the counts *)
  let proba_coll = Depanal.final_add_proba() in
  proba @ proba_coll

(* Main transformation function 
   with automatic determination of names_to_discharge *)

let rec find_restr accu p =
  match p.i_desc with
    Nil -> ()
  | Par(p1,p2) ->
      find_restr accu p1;
      find_restr accu p2
  | Repl(_,p) -> find_restr accu p
  | Input(_,_,p) -> find_restro accu p

and find_restro accu p =
  match p.p_desc with
    Yield | EventAbort _ -> ()
  | Let(_,_,p1,p2) | Test(_,p1,p2) -> 
      find_restro accu p1;
      find_restro accu p2
  | Find(l0,p2,_) ->
      List.iter (fun (_,_,_,p1) -> find_restro accu p1) l0;
      find_restro accu p2
  | Restr(b,p) ->
      if (not (List.memq b (!accu))) &&
         (* Consider only the restrictions such that a restriction
            of the same type occurs in the equivalence we want to apply. *)
         (List.exists (fun b_eq -> b.btype == b_eq.btype) (!equiv_names_lhs_flat))
      then
	accu := b :: (!accu);
      find_restro accu p
  | Output(_,_,p) -> 
      find_restr accu p
  | EventP(_,p) ->
      find_restro accu p
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

(* Returns either TSuccess (prob, p') -> game transformed into p' with difference of probability prob
   or TFailure l where l is a list of possible transformations:
   values for equiv, names_to_discharge, and preliminary transformations to do *)
let rec try_with_partial_assoc old_to_do apply_equiv names =
  let old_names_to_discharge = !names_to_discharge in
  let to_do = check_process old_to_do in
  if (!Settings.debug_cryptotransf) > 2 then display_mapping();
  if (!names_to_discharge != old_names_to_discharge) then
    try_with_partial_assoc to_do apply_equiv names
  else
    let still_to_discharge = List.filter (fun b -> not (is_name_to_discharge b)) names in
    if still_to_discharge != [] then
      begin
	let added_name = (List.hd still_to_discharge, ref DontKnow) in
	names_to_discharge := added_name :: (!names_to_discharge);
	try_with_partial_assoc (and_ins1 ([],0,[added_name]) to_do) apply_equiv still_to_discharge
      end
    else (* The list of names to discharge is completed *)
      if (!rebuild_map_mode) && (is_success_no_advice to_do) then
	begin
	  rebuild_map_mode := false; (* When I'm just looking for advice, 
					I don't mind if the map of names cannot be fully completed *)
	  try_with_partial_assoc to_do apply_equiv []
      (* It is necessary to keep the old to_do instruction list and add to it
	 because when the transformation succeeds without advice 
	 but has other solutions with advice and higher priority, then the transformation
	 is recorded in the map and so not rechecked on the next iteration of check_process.
	 Therefore, the corresponding advice is not found on that iteration, and 
	 but is found in the previous iteration. *)
	end
      else 
	(!names_to_discharge, to_do)

let try_with_known_names names apply_equiv =
  map := [];
  rebuild_map_mode := true;
  (* Try to guess the correct name mapping just from types *)
  List.iter (fun n ->
    if not (List.exists (fun (b,_) -> b == n)  (!gameeq_name_mapping)) then
      (* n has not been mapped yet, try to find the right image from its type *)
      match List.filter (fun b_eq -> b_eq.btype == n.btype) (!equiv_names_lhs_flat) with
	[] -> (* Found no variable of the right type,
	         the transformation cannot succeed! *)
	  fail (NoChangeName n)
      |	[b_eq] -> 
	  (* Found exactly one variable of the right type,
	     n will for sure be mapped to that variable *)
	  gameeq_name_mapping := (n, b_eq) :: (!gameeq_name_mapping)
      |	_ -> (* Several possibilities, will see later *)
	  ()
    ) names;
  (* When the corresponding name in the equivalence is not known, 
     we rebuild the list of names to discharge by adding them one by one.
     This is better for Diffie-Hellman. *)
  let names_rev = List.rev names in
  names_to_discharge := 
     if (!gameeq_name_mapping) == [] then
       [(List.hd names_rev, ref DontKnow)]
     else
       List.map (fun (n,_) -> (n, ref DontKnow)) (!gameeq_name_mapping);
  try_with_partial_assoc [([],0,!names_to_discharge)] apply_equiv names_rev

    
(*
  names_to_discharge := names;
  map := [];
  rebuild_map_mode := true;
  try_with_partial_assoc apply_equiv
*)

let rec found_in_fungroup t = function
    ReplRestr(_,_,funlist) ->
      List.exists (found_in_fungroup t) funlist
  | Fun(_,_,res,_) -> res == t

let is_exist t ((_,lm,_,_,_,_),_) =
  List.exists (fun (fg, mode) ->
    (mode == ExistEquiv) && (found_in_fungroup t fg)) lm

let rec is_useful_change_rec t = function
    ReplRestr(_,_,fgl) -> List.exists (is_useful_change_rec t) fgl
  | Fun(_,_,t',(_,options)) ->
    (options == UsefulChange) &&
    (t' == t)

let is_useful_change t ((_,lm,_,_,_,_),_) =
  List.exists (fun (fg, mode) -> is_useful_change_rec t fg) lm
  
let rec has_useful_change_rec = function
    ReplRestr(_,_,fgl) -> List.exists has_useful_change_rec fgl
  | Fun(_,_,t',(_,options)) ->
      options == UsefulChange

let has_useful_change ((_,lm,_,_,_,_),_) =
  List.exists (fun (fg, mode) -> has_useful_change_rec fg) lm
  

let copy_var2 b =
  match b.link with
    NoLink -> b
  | TLink t -> Terms.binder_from_term t  

let copy_repl_index2 b =
  match b.ri_link with
    NoLink -> b
  | TLink t -> Terms.repl_index_from_term t  

let rec copy_term2 t = 
  Terms.build_term t (match t.t_desc with
    Var(b,l) -> Var(copy_var2 b, List.map copy_term2 l)
  | FunApp(f,l) -> FunApp(f, List.map copy_term2 l)
  | ReplIndex b -> ReplIndex (copy_repl_index2 b)
  | _ -> Parsing_helper.internal_error "let, if, find, new and event forbidden in left member of equivalences")

let subst2 mapping t =
  let (_,name_mapping) = !equiv in 
  let link b b' =
    b.link <- TLink (Terms.term_from_binder b');
    List.iter2 (fun t t' -> t.ri_link <- TLink (Terms.term_from_repl_index t')) b.args_at_creation b'.args_at_creation
  in
  let unlink b =
    b.link <- NoLink;
    List.iter (fun t -> t.ri_link <- NoLink) b.args_at_creation 
  in
  List.iter (fun (b',b,_) -> link b b') name_mapping;
  List.iter2 link mapping.source_args mapping.target_args;
  let t' = copy_term2 t in
  List.iter (fun (_,b,_) -> unlink b) name_mapping;
  List.iter unlink mapping.source_args;
  t'
  

let map_has_exist (((_, lm, _, _, _, _),_) as apply_equiv) map =
  (map != []) && (
  if has_useful_change apply_equiv then
    List.exists (fun mapping ->  
      (try
	not (Terms.equal_terms (subst2 mapping mapping.source_exp) mapping.target_exp) 
      with _ -> true) 
	&& (is_useful_change mapping.source_exp apply_equiv)
	) map
  else
    (* Either the equivalence has no "Exist" *)
    (List.for_all (fun (fg, mode) -> mode == AllEquiv) lm) ||
    (* or the map maps at least one "Exist" member of the equivalence *)
    (List.exists (fun mapping -> is_exist mapping.source_exp apply_equiv) map))
    &&
    (* At least one element of map has a different expression in the
       left- and right-hand sides of the equivalence and is marked "useful_change" *)
    (List.exists (fun mapping ->  
      (try
	not (Terms.equal_terms (subst2 mapping mapping.source_exp) mapping.target_exp) 
      with _ -> true) 
	) map)

(* Update [maxlength] inside probability formulas to take into account
   renamings done by [ins] *)    
    
let rec update_max_length_probaf ins = function
  | (Time(_,(Context _ | Game _),_)) as x -> x
  | (Max _ | Maxlength _) as y ->
      let accu = ref Polynom.empty_minmax_accu in
      let rec add_max = function
	| Max(l) -> List.iter add_max l
	| (Maxlength(g,t)) as x ->
	    if g == whole_game_middle then
	      match t.t_desc with
	      | Var(b,_) ->
		  begin
		    try 
		      let rename_ins =
			List.find (function
			  | DSArenaming(b0, targets) -> b == b0
			  | _ -> false) ins
		      in
		      match rename_ins with
		      | DSArenaming(_, targets) ->
			  List.iter (fun b -> Polynom.add_max accu (Maxlength(!whole_game_next, Terms.term_from_binder b))) targets
		      | _ -> assert false
		    with Not_found -> 
		      Polynom.add_max accu (Maxlength(!whole_game_next, t))
		  end
	      | ReplIndex _ -> Polynom.add_max accu (Maxlength(!whole_game_next, t))
	      | _ -> Parsing_helper.internal_error "update_term: term in argument of maxlength should be a variable or a replication index"
	    else
	      Polynom.add_max accu x
	| x -> Polynom.add_max accu (update_max_length_probaf ins x)
      in
      add_max y;
      Polynom.p_max (!accu)
  | p -> Terms.map_sub_probaf (update_max_length_probaf ins) p
	
let update_maxlength ins proba =
  List.map (function
    | SetProba r -> SetProba (update_max_length_probaf ins r)
    | SetEvent _ | SetAssume -> 
	Parsing_helper.internal_error "Event/assume should not occur in probability formula") proba

    
type trans_res =
  TSuccessPrio of setf list * detailed_instruct list * game
| TFailurePrio of to_do_t * ((binder * binder) list * failure_reason) list

let transfo_finish apply_equiv p q =
  (* Compute the probability before doing the game transformation,
     so that the information in the initial process is not destroyed
     by the computation of information on the transformed process
     when we do [update_def_list_simplif] *)
  let proba' = compute_proba apply_equiv in
  print_string "Proba. computed "; flush stdout;
  let g' = { proc = RealProcess (do_crypto_transform p);
	     expanded = false;
	     game_number = -1;
	     current_queries = q } in
  let ins' = [DCryptoTransf(apply_equiv, Detailed(Some (!gameeq_name_mapping, [], !stop_mode),
						  (match !user_term_mapping with
						    None -> None
						  | Some tm -> Some (tm, !no_other_term))))]
  in
  print_string "Transf. done "; flush stdout;
  let (g'', proba'', ins'') = Transf_auto_sa_rename.auto_sa_rename g' in
  whole_game_next := g'';
  (* Rewrite probability to refer to variables after auto_sa_rename *)
  let proba' = update_maxlength ins'' proba' in
  (g'', proba'' @ proba', ins'' @ ins')
	
let rec try_with_restr_list apply_equiv = function
    [] -> TFailurePrio([],[])
  | (b::l) ->
        begin
	  rebuild_map_mode := true;
          names_to_discharge := b;
	  global_sthg_discharged := false;
	  map := [];
	  gameeq_name_mapping := [];
	  let vcounter = Terms.get_var_num_state() in
	  if (!Settings.debug_cryptotransf) > 0 then
	    begin
	      if b != [] then
		begin
		  print_string "Trying with random coins ";
		  Display.display_binder (fst (List.hd b));
		  print_newline()
		end;
	    end;
          try 
            let (discharge_names,to_do) = try_with_partial_assoc [([],0,!names_to_discharge)] apply_equiv [] in
	    (* If global_sthg_discharged is false, nothing done; b is never used in positions
               in which it can be discharged; try another restriction list *)
	    if not (!global_sthg_discharged) then 
	      fail NoChange;
	    begin
	      match b with
		[] -> ()
	      |	[bn, bopt] -> 
		  if (!bopt) == DontKnow then
		    (* The suggested name has not been used at all, fail*)
		    fail (NoChangeName bn)
	      |	_ -> Parsing_helper.internal_error "Unexpected name list in try_with_restr_list"
	    end;
	    (* When (!map) == [], nothing done; in fact, b is never used in the game; try another name *)
            if is_success_no_advice to_do then
	      begin
		check_lhs_array_ref();
		if map_has_exist apply_equiv (!map) then
		  begin
		    if (!Settings.debug_cryptotransf) > 0 then 
		      begin
			print_string "Success with ";
			Display.display_list Display.display_binder (List.map fst (!names_to_discharge));
			print_newline()
		      end;
		    print_string "Transf. OK "; flush stdout;
		    if (!Settings.debug_cryptotransf) > 1 then display_mapping(); 
		    let (g',proba',ins') = transfo_finish apply_equiv (Terms.get_process (!whole_game)) (!whole_game).current_queries in
		    TSuccessPrio (proba', ins', g')
		  end
		else
		  fail NoUsefulChange
	      end
            else
	      begin
		Terms.set_var_num_state vcounter; (* This transformation failed, forget the variables *)
		match try_with_restr_list apply_equiv l with
		  (TSuccessPrio _) as result -> result
		| TFailurePrio (l',failure_reasons) ->
		    TFailurePrio (merge_ins to_do l',failure_reasons)
	      end
          with OneFailure failure_reason -> 
	    Terms.set_var_num_state vcounter; (* This transformation failed, forget the variables *)
	    if (b == []) then
	      match try_with_restr_list apply_equiv l with
		(TSuccessPrio _) as result -> result
	      | TFailurePrio (l',failure_reasons) ->
		  TFailurePrio (l', (!gameeq_name_mapping, failure_reason)::failure_reasons)
	    else
	      (* When b != [], 
		 we do not register the reason why the transformation failed. 
		 It is likely that it is just because the tried name b
		 has no relation with the tried crypto transformation.
		 I would like to give an explanation a bit more often,
		 but it is difficult to give it for reasonable names b. *)
	      try_with_restr_list apply_equiv l
        end


let try_with_restr_list (((_, lm, _, _, _, _),_) as apply_equiv) restr =
  if (List.for_all (fun (fg, mode) -> mode == AllEquiv) lm) then
    (* Try with no name; the system will add the needed names if necessary *)
    try_with_restr_list apply_equiv [[]]
  else
    begin
      (* Try with at least one name *)
      if !stop_mode then
	(* In stop_mode, cannot add names, so fail *)
	TFailurePrio ([], [[],NameNeededInStopMode])
      else
	try_with_restr_list apply_equiv (List.map (fun b -> [b, ref DontKnow]) restr)
    end

let rec build_symbols_to_discharge_term t = 
  match t.t_desc with
    FunApp(f,_) ->
      symbols_to_discharge := f :: (!symbols_to_discharge)
  | _ -> ()

let rec build_symbols_to_discharge = function
    ReplRestr(_,_,fun_list) ->
      List.iter build_symbols_to_discharge fun_list
  | Fun(_,_,t,_) ->
      build_symbols_to_discharge_term t
      
let events_proba_queries events =
  let pub_vars = Settings.get_public_vars (!whole_game).current_queries in
  List.split (List.map (fun f ->
    let q_proof = ref ToProve in
    let proba = SetEvent(f, !whole_game_next, pub_vars, q_proof) in
    let query = ((Terms.build_event_query f pub_vars, !whole_game_next), q_proof) in
    (proba, query)
      ) events)

let get_advised_info initial_user_info advised_transfo n =
  let names_to_discharge = List.map fst n in
  let var_map, var_list, stop =
    match initial_user_info with
    | VarList(vl, stop) -> ([], vl, stop)
    | Detailed(Some (var_map, vl, stop), _) -> (var_map, vl, stop)
    | Detailed(None, _) -> ([], [], false)
  in
  let var_list' = 
    if stop then
      var_list
    else
      (* If we advise SArenaming for a name to discharge, put it in
         the list of the variables if it is not already there.
	 When we retry the transformation, it will be retried for one
	 of the SArenamed versions. 
	 I do not add all names_to_discharge because only some of
	 them may be used after SArenaming. (Some may be linked to
	 a definition of the SArenamed variable that we cannot transform.) *)
      let add_vl var_list = function
	| SArenaming b ->
	    if (not (List.memq b var_list))
		&& (not (List.exists (fun (b', _) -> b' == b) var_map))
		&& (List.memq b names_to_discharge) then b::var_list else var_list
	| _ -> var_list
      in
      let var_list' = List.fold_left add_vl var_list advised_transfo in
      if var_list' == [] then
	names_to_discharge
	(* I tried the following, but it breaks some examples,
	   especially with public-key encryption.
	   Explanation: in the example examples-1.28-converted/basic/denning-sacco-corr3Block-auto.cv

	   With the code above, we have:
Trying equivalence ind_cca2(enc)... Failed.
Doing remove assignments of binder pkB... Done.
Doing remove assignments of binder skB... Done.
Trying equivalence ind_cca2(enc) with rkB, r2_3... Failed.
Doing SA rename Rkey... Done.
...

	   With the code below:
Trying equivalence ind_cca2(enc)... Failed.
Doing remove assignments of binder pkB... Done.
Doing remove assignments of binder skB... Done.
Trying equivalence ind_cca2(enc) with r2_3... Failed:
Random variables: r2_3 -> r2
The transformation did not use the useful_change oracles, or oracles deemed useful by default.
	   CV uses the oracle enc(m,pk,r), which is not marked [useful_change]
	   => the transformation fails.
	   Above, the additional name rkB leads to advising SArename Rkey.
	   That makes the transformation succeed.
	   The reason why it fails may be that the last element of 
	   names_to_discharge is not always the one that was inserted first by 
	   try_with_restr_list. (In the example, try_with_restr_list probably
	   started with rkB and added r2_3 because of the [all] option
	   on the oracle enc(m,pk,r).)

        begin
	  match names_to_discharge with
	  | [] -> []
	  | _ -> 
	      [* Just put the first name to discharge found, if there is some.
                 The rest will be reconstructed when we reapply the transformation.
		 It may be different after applying the advice *]
	      [List.hd (List.rev names_to_discharge)] 
	end *)
      else
	var_list'
  in
  if var_map == [] then
    VarList(var_list', stop)
  else
    Detailed(Some(var_map, var_list', stop), None)
  (* 
     I tried to pass the name mapping to the next try, 
     but it did not work well: that name mapping may in fact be wrong.
  let n' = List.map fst n in
  let n'' = List.filter (fun n1 -> not (List.exists (fun (n1',_) -> n1' == n1) (!gameeq_name_mapping))) n' in
  Detailed(Some(!gameeq_name_mapping, n'', !stop_mode), None) *)

let crypto_transform no_advice (((_,lm,rm,_,_,opt2),_) as apply_equiv) user_info g =
  let p = Terms.get_process g in
  let names = 
    match user_info with
      VarList(l, stop) ->
	stop_mode := stop;
	gameeq_name_mapping := [];
	l
    | Detailed(var_map, term_map) ->
	begin
	  match term_map with
	    Some(tmap, stop) ->
	      no_other_term := stop;
	      user_term_mapping := Some tmap
	  | None ->
	      no_other_term := false;
	      user_term_mapping := None
	end;
	begin
	  match var_map with
	    Some (vmap, vl, stop) ->
	      stop_mode := stop;
	      gameeq_name_mapping := vmap;
	      vl @ (List.map fst vmap)
	  | None ->
	      stop_mode := false;
	      gameeq_name_mapping := [];
	      []
	end
  in
  no_advice_mode := no_advice;
  equiv := apply_equiv;
  equiv_names_lhs_opt := [];
  List.iter2 (fun (lm1,_) (rm1, _) -> collect_all_names equiv_names_lhs_opt lm1 rm1) lm rm;
  equiv_names_lhs := List.map (List.map fst) (!equiv_names_lhs_opt);
  equiv_names_lhs_flat := List.concat (!equiv_names_lhs);
  whole_game := g;
  introduced_events := [];
  time_computed := NotComputedYet;
  symbols_to_discharge := [];
  encode_funs_for_binders := [];
  encode_funs_for_exps := [];
  let vcounter = Terms.get_var_num_state() in
  List.iter (fun (fg, mode) ->
    if mode == AllEquiv then build_symbols_to_discharge fg) lm;
  Improved_def.improved_def_game None true g;
  if !Settings.optimize_let_vars then
    incompatible_terms := incompatible_defs p;
  let result = 
  if (names == []) then
    begin
      (* I need to determine the names to discharge from scratch *)
      let restr = ref [] in
      find_restr restr p;
      match try_with_restr_list apply_equiv (!restr) with
	TSuccessPrio(prob, ins, g') -> 
	  let (ev_proba, ev_q) = events_proba_queries (!introduced_events) in
	  if ev_q != [] then
	    g'.current_queries <- ev_q @ List.map (fun (q, poptref) -> (q, ref (!poptref))) g'.current_queries;
	  TSuccess(prob @ ev_proba, ins, g')
      |	TFailurePrio (l,failure_reasons) -> 
	  if ((!Settings.debug_cryptotransf) > 0) && (l != []) then 
	    print_string "Advice given\n";
	  Terms.set_var_num_state vcounter; (* Forget created variables when the transformation fails *)
	  TFailure (List.map (fun (l,p,n) -> (apply_equiv, get_advised_info user_info l n, l)) l, failure_reasons)
    end
  else
    begin
      (* names_to_discharge is at least partly known *)
      try 
        let (discharge_names, to_do) = try_with_known_names names apply_equiv in
        if is_success_no_advice to_do then
	  begin
	    check_lhs_array_ref();
	    if map_has_exist apply_equiv (!map) then
	      begin
		if (!Settings.debug_cryptotransf) > 0 then 
		  begin
		    print_string "Success with ";
		    Display.display_list Display.display_binder (List.map fst discharge_names);
		    print_newline()
		  end;
		print_string "Transf. OK "; flush stdout;
		if (!Settings.debug_cryptotransf) > 1 then display_mapping(); 
		let (g',proba',ins') = transfo_finish apply_equiv p g.current_queries in
		let (ev_proba, ev_q) = events_proba_queries (!introduced_events) in
		if ev_q != [] then
		  g'.current_queries <- ev_q @ List.map (fun (q, poptref) -> (q, ref (!poptref))) g'.current_queries;
		TSuccess (ev_proba @ proba', ins', g')
	      end
	    else
	      fail NoUsefulChange
	  end
        else
	  begin
	    if (!Settings.debug_cryptotransf) > 0 then 
	      print_string "Advice given\n";
	    Terms.set_var_num_state vcounter; (* Forget created variables when the transformation fails *)
            TFailure (List.map (fun (l,p,n) -> (apply_equiv, get_advised_info user_info l n, l)) to_do, [])
	  end
      with OneFailure failure_reason -> 
	Terms.set_var_num_state vcounter; (* Forget created variables when the transformation fails *)
	TFailure ([], [!gameeq_name_mapping, failure_reason])
    end
  in
  (* Cleanup to save memory *)
  Improved_def.empty_improved_def_game true g;
  whole_game := Terms.empty_game;
  whole_game_next := Terms.empty_game;
  equiv := empty_equiv;
  equiv_names_lhs_opt := [];
  equiv_names_lhs := [];
  equiv_names_lhs_flat := [];
  incompatible_terms := [];
  gameeq_name_mapping := [];
  user_term_mapping := None;
  names_to_discharge := [];
  symbols_to_discharge := [];
  map := [];
  introduced_events := [];
  encode_funs_for_binders := [];
  encode_funs_for_exps := [];
  result
