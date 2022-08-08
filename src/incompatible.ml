open Types

(* Build the "incompatible" field for each program point [pp]. It
   contains the mapping of occurrences of program points [pp']
   incompatible with [pp] to the length [l] such that if [pp] with
   indices [arg] and [pp'] with indices [args'] are both executed,
   then the suffixes of length [l] of [args] and [args'] must be
   different.
   Supports LetE/FindE/ResE/TestE everywhere *)

(* Empty the "incompatible" field of all program points. *)

let rec empty_comp_pattern = function
    PatVar b -> ()
  | PatTuple (f,l) -> List.iter empty_comp_pattern l
  | PatEqual t -> empty_comp_term t

and empty_comp_term t =
  t.t_incompatible <- Occ_map.empty;
  match t.t_desc with
    Var (_,l) | FunApp(_,l)-> List.iter empty_comp_term l
  | ReplIndex _ -> ()
  | TestE(t1,t2,t3) -> 
      empty_comp_term t1;
      empty_comp_term t2;
      empty_comp_term t3
  | FindE(l0,t3,_) ->
      List.iter (fun (bl,def_list,t1,t2) ->
	List.iter (fun (_,l) -> List.iter empty_comp_term l) def_list;
	empty_comp_term t1;
	empty_comp_term t2) l0;
      empty_comp_term t3
  | LetE(pat,t1,t2,topt) ->
      empty_comp_pattern pat;
      empty_comp_term t1;
      empty_comp_term t2;
      begin
	match topt with
	  None -> ()
	| Some t3 -> empty_comp_term t3
      end
  | ResE(b,p) ->
      empty_comp_term p
  | EventAbortE _ -> ()
  | EventE(t,p) ->
      empty_comp_term t;
      empty_comp_term p
  | GetE(tbl,patl,topt,p1,p2,_) -> 
      List.iter empty_comp_pattern patl;
      begin
	match topt with
	  None -> ()
	| Some t -> empty_comp_term t
      end;
      empty_comp_term p1;
      empty_comp_term p2
  | InsertE(tbl,tl,p) ->
      List.iter empty_comp_term tl;
      empty_comp_term p

let rec empty_comp_process p = 
  p.i_incompatible <- Occ_map.empty;
  match p.i_desc with
    Nil -> ()
  | Par(p1,p2) -> 
      empty_comp_process p1;
      empty_comp_process p2
  | Repl(b,p) ->
      empty_comp_process p
  | Input((c,tl),pat,p) ->
      List.iter empty_comp_term tl;
      empty_comp_pattern pat;
      empty_comp_oprocess p

and empty_comp_oprocess p =
  p.p_incompatible <- Occ_map.empty;
  match p.p_desc with
    Yield | EventAbort _ -> ()
  | Restr(b,p) ->
      empty_comp_oprocess p
  | Test(t,p1,p2) ->
      empty_comp_term t;
      empty_comp_oprocess p1;
      empty_comp_oprocess p2
  | Find(l0,p2,_) ->
      List.iter (fun (bl,def_list,t,p1) ->
	List.iter (fun (_,l) -> List.iter empty_comp_term l) def_list;
	empty_comp_term t;
	empty_comp_oprocess p1) l0;
      empty_comp_oprocess p2
  | Output((c,tl),t',p) ->
      List.iter empty_comp_term tl;
      empty_comp_term t';
      empty_comp_process p
  | Let(pat,t,p1,p2) ->
      empty_comp_pattern pat;
      empty_comp_term t;
      empty_comp_oprocess p1;
      empty_comp_oprocess p2
  | EventP(t,p) ->
      empty_comp_term t;
      empty_comp_oprocess p
  | Get(tbl,patl,topt,p1,p2,_) -> 
      List.iter empty_comp_pattern patl;
      begin
	match topt with
	  None -> ()
	| Some t -> empty_comp_term t
      end;
      empty_comp_oprocess p1;
      empty_comp_oprocess p2
  | Insert(tbl,tl,p) ->
      List.iter empty_comp_term tl;
      empty_comp_oprocess p

(* Compute the "incompatible" field for all program points *)

let rec compatible_def_term cur_array_length current_incompatible t = 
  t.t_incompatible <- current_incompatible;
  match t.t_desc with
    Var(_,l) | FunApp(_,l) -> 
      List.iter (compatible_def_term cur_array_length current_incompatible) l
  | ReplIndex i -> 
      ()
  | TestE(t1,t2,t3) -> 
      compatible_def_term cur_array_length current_incompatible t1;
      compatible_def_term cur_array_length current_incompatible t2;
      let t3_incompatible = Occ_map.add current_incompatible t2.t_occ t2.t_max_occ cur_array_length in
      compatible_def_term cur_array_length t3_incompatible t3 
  | FindE(l0, t3, _) ->
      let accu_incompatible = ref current_incompatible in
      List.iter (fun (bl, def_list, t1, t2) ->
	let cur_array_length_cond = cur_array_length + List.length bl in
	List.iter (fun (_,l) -> 
	  List.iter (compatible_def_term cur_array_length_cond current_incompatible) l) def_list;
	compatible_def_term cur_array_length_cond current_incompatible t1;
	compatible_def_term cur_array_length (!accu_incompatible) t2;
	accu_incompatible := (Occ_map.add (!accu_incompatible) t2.t_occ t2.t_max_occ cur_array_length)
	     ) l0;
      compatible_def_term cur_array_length (!accu_incompatible) t3
  | LetE(pat, t1, t2, topt) ->
      compatible_def_term cur_array_length current_incompatible t1;
      compatible_def_pat cur_array_length current_incompatible pat;
      compatible_def_term cur_array_length current_incompatible t2;
      begin
	match topt with
	  None -> ()
	| Some t3 -> 
	    let t3_incompatible = Occ_map.add current_incompatible t2.t_occ t2.t_max_occ cur_array_length in
	    compatible_def_term cur_array_length t3_incompatible t3 
      end
  | ResE(b,t2) ->
      compatible_def_term cur_array_length current_incompatible t2
  | EventAbortE _ ->
      ()
  | EventE(t,p) ->
      compatible_def_term cur_array_length current_incompatible t;
      compatible_def_term cur_array_length current_incompatible p
  | GetE _ | InsertE _ -> 
      Parsing_helper.internal_error "Get/Insert should have been reduced at this point"

and compatible_def_pat cur_array_length current_incompatible = function
    PatVar b -> ()
  | PatTuple (f,l) -> List.iter (compatible_def_pat cur_array_length current_incompatible) l
  | PatEqual t -> compatible_def_term cur_array_length current_incompatible t

let rec compatible_def_process cur_array_length current_incompatible p =
  p.i_incompatible <- current_incompatible;
  match p.i_desc with
    Nil -> ()
  | Par(p1,p2) ->
      compatible_def_process cur_array_length current_incompatible p1;
      compatible_def_process cur_array_length current_incompatible p2
  | Repl(b,p) ->
      compatible_def_process (cur_array_length+1) current_incompatible p
  | Input((c,tl),pat,p2) ->
      List.iter (compatible_def_term cur_array_length current_incompatible) tl;
      compatible_def_pat cur_array_length current_incompatible pat;
      compatible_def_oprocess cur_array_length current_incompatible p2 

and compatible_def_oprocess cur_array_length current_incompatible p =
  p.p_incompatible <- current_incompatible;
  match p.p_desc with
    Yield | EventAbort _ -> ()
  | Restr(b, p2) ->
      compatible_def_oprocess cur_array_length current_incompatible p2 
  | Test(t,p1,p2) ->
      compatible_def_term cur_array_length current_incompatible t;
      compatible_def_oprocess cur_array_length current_incompatible p1;
      let p2_incompatible = Occ_map.add current_incompatible p1.p_occ p1.p_max_occ cur_array_length in
      compatible_def_oprocess cur_array_length p2_incompatible p2 
  | Find(l0, p2, _) ->
      let accu_incompatible = ref current_incompatible in
      List.iter (fun (bl, def_list, t, p1) ->
	let cur_array_length_cond = cur_array_length + List.length bl in
	List.iter (fun (_,l) -> 
	  List.iter (compatible_def_term cur_array_length_cond current_incompatible) l) def_list;
	compatible_def_term cur_array_length_cond current_incompatible t;
	compatible_def_oprocess cur_array_length (!accu_incompatible) p1;
	accu_incompatible := (Occ_map.add (!accu_incompatible) p1.p_occ p1.p_max_occ cur_array_length)
	     ) l0;
      compatible_def_oprocess cur_array_length (!accu_incompatible) p2
  | Output((c,tl),t2,p) ->
      List.iter (compatible_def_term cur_array_length current_incompatible) tl;
      compatible_def_term cur_array_length current_incompatible t2;
      compatible_def_process cur_array_length current_incompatible p
  | Let(pat,t,p1,p2) ->
      compatible_def_term cur_array_length current_incompatible t;
      compatible_def_pat cur_array_length current_incompatible pat;
      compatible_def_oprocess cur_array_length current_incompatible p1;
      let p2_incompatible = Occ_map.add current_incompatible p1.p_occ p1.p_max_occ cur_array_length in
      compatible_def_oprocess cur_array_length p2_incompatible p2 
  | EventP(t,p) ->
      compatible_def_term cur_array_length current_incompatible t;
      compatible_def_oprocess cur_array_length current_incompatible p
  | Get _ | Insert _ -> 
      Parsing_helper.internal_error "Get/Insert should have been reduced at this point"


let build_compatible_defs p = 
  compatible_def_process 0 Occ_map.empty p

(* [occ_from_pp pp] returns the occurrence of program point [pp] *)

let occ_from_pp = function
    DProcess(p) -> p.p_occ
  | DTerm(t) -> t.t_occ
  | DInputProcess(p) -> p.i_occ
  | _ -> raise Not_found

(* [incomp_from_pp pp] returns a triple containing
   - the occurrence of program point [pp]
   - the maximum occurrence of program points under [pp] in the syntax tree.
   (the occurrences of program points under [pp] are then
   in the interval [occurrence of [pp], max. occ. under [pp]])
   - the mapping of occurrences of program points [pp'] incompatible with [pp]
   to the length [l] such that if [pp] with indices [arg]
   and [pp'] with indices [args'] are both executed, then
   the suffixes of length [l] of [args] and [args'] must be different.
   Raises [Not_found] when [pp] does not uniquely identify a program point. *) 

let incomp_from_pp = function
    DProcess(p) -> p.p_occ, p.p_max_occ, p.p_incompatible
  | DTerm(t) -> t.t_occ, t.t_max_occ, t.t_incompatible
  | DInputProcess(p) -> p.i_occ, p.i_max_occ, p.i_incompatible
  | _ -> raise Not_found

(* [map_max f l], where [f] is a function from list elements to integers,
   returns the maximum of [f a] for elements [a] in [l] *)

let rec map_max f = function
    [] -> 0
  | a::l -> max (f a) (map_max f l)

(* [incompatible_suffix_length_pp pp pp'] returns a length [l] such
   that if [pp] with indices [args] and [pp'] with indices [args'] are
   both executed, then the suffixes of length [l] of [args] and
   [args'] must be different.
   Raises [Not_found] when [pp] with indices [args] and [pp'] with
   indices [args'] can be executed for any [args,args'].*)

let incompatible_suffix_length_pp pp pp' =
  let occ, _, occ_map = incomp_from_pp pp in
  let occ', _, occ_map' = incomp_from_pp pp' in
  try 
    Occ_map.find occ occ_map' 
  with Not_found ->
    Occ_map.find occ' occ_map 

(* [both_pp (args, pp) (args', pp')] returns true when
   program point [pp] with indices [args] and 
   program point [pp'] with indices [args'] can both be executed. *)

let both_pp (args, pp) (args', pp') =
  try
    let suffix_l = incompatible_suffix_length_pp pp pp' in
    let args_skip = Terms.lsuffix suffix_l args in
    let args_skip' = Terms.lsuffix suffix_l args' in
    not (List.for_all2 Terms.equal_terms args_skip args_skip')
  with Not_found -> 
    true
     
(* [both_pp_add_fact fact_accu (args, pp) (args', pp')] 
   adds to [fact_accu] a fact inferred from the execution of both
   program point [pp] with indices [args] and 
   program point [pp'] with indices [args'], if any.*)
	
let both_pp_add_fact fact_accu (args, pp) (args', pp') =
  try
    let suffix_l = incompatible_suffix_length_pp pp pp' in
    let args_skip = Terms.lsuffix suffix_l args in
    let args_skip' = Terms.lsuffix suffix_l args' in
    (Terms.make_or_list (List.map2 Terms.make_diff args_skip args_skip')) :: fact_accu
  with Not_found ->
    fact_accu

(* [incompatible_suffix_length_onepp pp b'] returns a length [l] such
   that if [pp] with indices [args] is executed and [b'[args]] 
   is defined, then the suffixes of length [l] of [args] and
   [args'] must be different.
   Raises [Not_found] when [pp] with indices [args] can be executed 
   and [b'[args']] can be defined for any [args,args'].*)

let incompatible_suffix_length_onepp pp b' =
  let pp_occ, _, pp_occ_map = incomp_from_pp pp in
  map_max (fun n' ->
    let (occ', _, occ_map') = incomp_from_pp n'.definition_success in
    try 
      Occ_map.find pp_occ occ_map' 
    with Not_found ->
      Occ_map.find occ' pp_occ_map 
	) b'.def

(* [incompatible_suffix_length b b'] returns a length [l] such that if
   [b[args]] and [b'[args']] are both defined, then the suffixes of
   length [l] of [args] and [args'] must be different.
   Raises [Not_found] when [b[args]] and [b'[args']] can be defined 
   for any [args,args']. *)

let incompatible_suffix_length b b' =
  map_max (fun n -> incompatible_suffix_length_onepp n.definition_success b') b.def

(* [is_compatible (b,args) (b',args')] returns true when
   [b[args]] and [b'[args']] may both be defined *)

let is_compatible (b,args) (b',args') =
  (b == b') || 
  (try
    let suffix_l = incompatible_suffix_length b b' in
    let args_skip = Terms.lsuffix suffix_l args in
    let args_skip' = Terms.lsuffix suffix_l args' in
    (not (List.for_all2 Terms.equal_terms args_skip args_skip'))
  with Not_found -> true)

(* [is_compatible_node (b,args) n (b',args')] returns true when
   [b[args]] and [b'[args']] may both be defined, with [b[args]]
   defined at node [n]. *)

let is_compatible_node (b,args) n (b',args') =
  (b == b') || 
  (try
    let suffix_l = incompatible_suffix_length_onepp n.definition_success b' in
    (*print_string ("incompatible_suffix_length 1 " ^ b.sname ^ "_" ^ (string_of_int b.vname) ^ " " ^ b'.sname ^ "_" ^ (string_of_int b'.vname) ^ " = "); print_int suffix_l; print_newline(); *)
    let args_skip = Terms.lsuffix suffix_l args in
    let args_skip' = Terms.lsuffix suffix_l args' in
    (not (List.for_all2 Terms.equal_terms args_skip args_skip'))
  with Not_found -> true)

(* [both_def_add_fact fact_accu (b,args) (b',args')]
   adds to [fact_accu] a fact that always holds when
   [b[args]] and [b'[args']] are both defined, if any. *)

let both_def_add_fact fact_accu (b,args) (b',args') =
  if b != b' then 
    try
      let suffix_l = incompatible_suffix_length b b' in
      let args_skip = Terms.lsuffix suffix_l args in
      let args_skip' = Terms.lsuffix suffix_l args' in
      (Terms.make_or_list (List.map2 Terms.make_diff args_skip args_skip')) :: fact_accu
    with Not_found -> 
      fact_accu
  else
    fact_accu

(* [both_def_list_facts old_def_list def_list] returns facts
   inferred from the knowledge that the variables in [def_list] and
   [old_def_list] are simultaneously defined. It considers pairs
   of variables in [def_list] and of one variable in [def_list]
   and one in [old_def_list], but does not consider pairs of variables
   in [old_def_list] as those should have been taken into account before.
   Uses the field "incompatible" set by Terms.build_compatible_defs
 *)

let rec accu_pair f accu = function
    [] -> accu
  | (a::l) -> 
      let accu = List.fold_left (fun accu' a' -> f accu' a a') accu l in
      accu_pair f accu l

let both_def_list_facts fact_accu old_def_list def_list =
  (* Remove the already defined variables from the new def_list *)
  let new_def_list = List.filter (fun br -> not (Terms.mem_binderref br old_def_list)) def_list in
  (* Check that the newly defined variables are compatible with each other *)
  let fact_accu = accu_pair both_def_add_fact fact_accu new_def_list in
  (* ... and with all the previously defined variables *)
  List.fold_left (fun accu br -> List.fold_left (fun accu' br' -> 
    both_def_add_fact accu' br br') accu new_def_list) fact_accu old_def_list

(* [def_pp_add_fact fact_accu (pp,args) (b',args')] 
   adds to [fact_accu] a fact inferred from the execution of 
   program point [pp] with indices [args] and 
   the definition of variable [b'] with indices [args'], if any.
   [b[args']] may be defined before or after the execution
   of program point [pp] with indices [args]. *)

let def_pp_add_fact fact_accu (pp,args) (b',args') =
  try
    let suffix_l = incompatible_suffix_length_onepp pp b' in
    let args_skip = Terms.lsuffix suffix_l args in
    let args_skip' = Terms.lsuffix suffix_l args' in
    (Terms.make_or_list (List.map2 Terms.make_diff args_skip args_skip')) :: fact_accu
  with Not_found -> 
    fact_accu

(* [def_list_pp fact_accu pp_args def_list] returns facts
   inferred from the knowledge that the variables in [def_list] are
   defined and the program point [pp_args] is executed.
   (The variables in [def_list] may be defined before or after
   executing the program point [pp_args].
   Uses the field "incompatible" set by Terms.build_compatible_defs
 *)
let def_list_pp fact_accu pp_args def_list =
  List.fold_left (fun accu br -> 
     def_pp_add_fact accu pp_args br) fact_accu def_list


(* [not_after_suffix_length_one_pp pp length_cur_array_pp b'] returns
   the shortest length [l] such that the program point [pp] cannot be
   executed with indices [args] after the definition of variable [b']
   with indices [args'] when [args] and [args'] have a common suffix of
   length [l].  
   Raises [Not_found] when [pp] with indices [args] can be executed
   after the definition of [b'[args']] for any [args,args'].
   [length_cur_array_pp] is the number of replication indices at
   program point [pp]. *)

let not_after_suffix_length_one_pp pp length_cur_array_pp b' =
  let pp_occ, pp_max_occ, pp_occ_map = incomp_from_pp pp in
  map_max (fun n' ->
    let (occ', _, occ_map') = incomp_from_pp n'.definition_success in
    try 
      Occ_map.find pp_occ occ_map' 
    with Not_found ->
      try
	Occ_map.find occ' pp_occ_map
      with Not_found ->
	if pp_occ <= occ' && occ' <= pp_max_occ then
	  length_cur_array_pp (* since b' is defined under pp, b' has more indices than pp *)
	else
	  raise Not_found
	) b'.def

(* [not_after_suffix_length_one_pp_one_node pp length_cur_array_pp n'] returns
   the shortest length [l] such that the program point [pp] cannot be
   executed with indices [args] after the node [n']
   with indices [args'] when [args] and [args'] have a common suffix of
   length [l].  
   Raises [Not_found] when [pp] with indices [args] can be executed
   after the node [n'[args']] for any [args,args'].
   [length_cur_array_pp] is the number of replication indices at
   program point [pp]. *)

let not_after_suffix_length_one_pp_one_node pp length_cur_array_pp n' =
  let pp_occ, pp_max_occ, pp_occ_map = incomp_from_pp pp in
  let (occ', _, occ_map') = incomp_from_pp n'.definition_success in
  try 
    Occ_map.find pp_occ occ_map' 
  with Not_found ->
    try
      Occ_map.find occ' pp_occ_map
    with Not_found ->
      if pp_occ < occ' && occ' <= pp_max_occ then
	length_cur_array_pp (* since n' is under pp, n' has more indices than pp *)
      else
	raise Not_found

(* [get_start_block_pp n] returns the program point corresponding
   to the input that starts the input...output block of code that
   contains node [n]. *)
	  
let rec get_start_block_pp n =
  match n.above_node with
  | None -> 
    (* n is the initial node *)
      n.definition
  | Some n' -> 
      match n.definition with
	DInputProcess({ i_desc = Input _}) as pp -> pp
      | _ -> get_start_block_pp n'

(* [get_facts pp] returns the fact_info at program point [pp] *)

let get_facts pp =
  match pp with
    DProcess p -> p.p_facts
  | DInputProcess p -> p.i_facts
  | DTerm t ->  t.t_facts
  | _ -> None

(* [incompatible_current_suffix_length history n] returns the shortest
   length [l] such that the current program point of [history] cannot
   be executed with indices [args] after the node [n] with indices
   [args'] when [args] and [args'] have a common suffix of length [l].
   Raises [Not_found] when that program point with indices [args] can
   be executed after the node [n[args']] for any [args,args']. *)

let incompatible_current_suffix_length history n =
  let pp = 
    if history.current_in_different_block then
      get_start_block_pp history.current_node
    else
      history.current_point
  in
  let cur_array =
    match get_facts pp with
      None -> raise Not_found
    | Some(cur_array,_,_,_,_,_,_) -> cur_array
  in
  not_after_suffix_length_one_pp_one_node pp (List.length cur_array) n

(* [incompatible_nodelist_different_block_suffix_length (nl, args) n]
   returns the shortest length [l] such that an input...output block
   containing a node in [nl] cannot be executed with indices [args]
   after the node [n] with indices [args'] when [args] and [args']
   have a common suffix of length [l].
   Raises [Not_found] when they can be executed for any [args,args']. *)

let incompatible_nodelist_different_block_suffix_length (nl, args) n =
  let length_cur_array_pp = List.length args in
  map_max (fun n1 ->
    let pp = get_start_block_pp n1 in
    not_after_suffix_length_one_pp_one_node pp length_cur_array_pp n) nl

(* [incompatible_nodelist_same_block_suffix_length (nl, args) n]
   returns the shortest length [l] such that a node in [nl] cannot be
   executed with indices [args] after the node [n] with indices
   [args'] when [args] and [args'] have a common suffix of length [l].
   Raises [Not_found] when they can be executed for any [args,args']. *)

let incompatible_nodelist_same_block_suffix_length (nl, args) n =
  let length_cur_array_pp = List.length args in
  map_max (fun n1 ->
    let pp = n1.definition in
    not_after_suffix_length_one_pp_one_node pp length_cur_array_pp n) nl

(* [is_compatible_history (n,args) history] returns true when 
   the information in [history] is compatible with the execution
   of node [n] with indices [args] before that history. *)
    
let is_compatible_history (n,args) history =
  (try
    let suffix_l = incompatible_current_suffix_length history n in
    (*print_string "is_compatible_history "; print_int suffix_l;
    print_string " args length: "; print_int (List.length args);
    print_string " cur_array length: "; print_int (List.length history.cur_array); print_newline(); *)
    let args_skip = Terms.lsuffix suffix_l args in
    let args_skip' = Terms.lsuffix suffix_l history.cur_array in
    (not (List.for_all2 Terms.equal_terms args_skip args_skip'))
  with Not_found -> true) &&
  (List.for_all (fun (nl',args') ->
    try
      let suffix_l = incompatible_nodelist_different_block_suffix_length (nl', args') n in
      let args_skip = Terms.lsuffix suffix_l args in
      let args_skip' = Terms.lsuffix suffix_l args' in
      (not (List.for_all2 Terms.equal_terms args_skip args_skip'))
    with Not_found -> true
	) history.def_vars_in_different_blocks) && 
  (List.for_all (fun (nl',args') ->
    try
      let suffix_l = incompatible_nodelist_same_block_suffix_length (nl', args') n in
      let args_skip = Terms.lsuffix suffix_l args in
      let args_skip' = Terms.lsuffix suffix_l args' in
      (not (List.for_all2 Terms.equal_terms args_skip args_skip'))
    with Not_found -> true
	) history.def_vars_maybe_in_same_block)

(* [facts_compatible_history fact_accu (nl,args) history] returns
   [fact_accu] with additional facts inferred from the execution of a
   node in [nl] with indices [args] before the history [history]. *)

let facts_compatible_history fact_accu (nl,args) history = 
  let fact_accu1 =
    try
      let suffix_l = map_max (incompatible_current_suffix_length history) nl in
    (*print_string ("incompatible_suffix_length 1 " ^ b.sname ^ "_" ^ (string_of_int b.vname) ^ " " ^ b'.sname ^ "_" ^ (string_of_int b'.vname) ^ " = "); print_int suffix_l; print_newline(); *)
      let args_skip = Terms.lsuffix suffix_l args in
      let args_skip' = Terms.lsuffix suffix_l history.cur_array in
      (Terms.make_or_list (List.map2 Terms.make_diff args_skip args_skip')) :: fact_accu
    with Not_found -> fact_accu
  in
  let fact_accu2 =
    List.fold_left (fun fact_accu (nl',args') ->
      try
	let suffix_l = map_max (incompatible_nodelist_different_block_suffix_length (nl', args')) nl in
	let args_skip = Terms.lsuffix suffix_l args in
	let args_skip' = Terms.lsuffix suffix_l args' in
	(Terms.make_or_list (List.map2 Terms.make_diff args_skip args_skip')) :: fact_accu
    with Not_found -> fact_accu
	) fact_accu1 history.def_vars_in_different_blocks
  in
  List.fold_left (fun fact_accu (nl',args') ->
    try
      let suffix_l = map_max (incompatible_nodelist_same_block_suffix_length (nl', args')) nl in
      let args_skip = Terms.lsuffix suffix_l args in
      let args_skip' = Terms.lsuffix suffix_l args' in
      (Terms.make_or_list (List.map2 Terms.make_diff args_skip args_skip')) :: fact_accu
    with Not_found -> fact_accu
	) fact_accu2 history.def_vars_maybe_in_same_block
  
(* [def_at_pp_add_fact fact_accu pp args (b',args')] adds to
   [fact_accu] a fact that always holds when [b'[args']] is defined
   before the execution of program point [pp] with indices [args], if
   any. *)

let def_at_pp_add_fact fact_accu pp args (b',args') =
  let length_cur_array_pp = List.length args in
  try
    let suffix_l = not_after_suffix_length_one_pp pp length_cur_array_pp b' in
    let args_skip = Terms.lsuffix suffix_l args in
    let args_skip' = Terms.lsuffix suffix_l args' in
    (Terms.make_or_list (List.map2 Terms.make_diff args_skip args_skip')) :: fact_accu
  with Not_found -> 
    fact_accu
    
(* [def_list_at_pp_facts pp args def_list] returns facts
   inferred from the knowledge that the variables in [def_list]
   are defined before the execution of program point [pp] with indices [args].
   (Typically, that some indices in [args] are different
   from some indices of variables in [def_list].) *)

let def_list_at_pp_facts fact_accu pp args def_list =
    List.fold_left (fun accu -> def_at_pp_add_fact accu pp args) fact_accu def_list

(* [may_def_before (b,args) (b',args')] returns true when
   [b[args]] may be defined before or at the same time as [b'[args']] *)

let may_def_before (b,args) (b',args') =
  (* b defined at the same time as b' *)
  (b == b') || (List.exists (fun n -> List.memq b n.binders) b'.def) ||
  (* b[args] defined before b'[args'] *)
  (try
    let length_cur_array_b' = List.length args' in
    let suffix_l = map_max (fun n -> not_after_suffix_length_one_pp n.definition_success length_cur_array_b' b) b'.def in
    let args_skip = Terms.lsuffix suffix_l args in
    let args_skip' = Terms.lsuffix suffix_l args' in
    (not (List.for_all2 Terms.equal_terms args_skip args_skip'))
  with Not_found -> true)

