open Types
open Parsing_helper

type 'a eqtester = 'a -> 'a -> bool

let whole_game = ref Terms.empty_game
    
let cur_branch_var_list = ref []
    (* List of pairs (variable in current branch, variable in else branch)
       for variables with array references, a single definition, and
       a different name in different branches *)

let all_branches_var_list = ref []
    (* All lists cur_branch_var_list for the various branches *)

let var_no_array_ref = ref []
    (* Variables that must not have array references in the final game *)

let global_map = ref []
    (* List of pairs of variables, to map variables with array references *)

let eq_oblig = ref []
    (* Equality obligations between terms *)

let eq_oblig_def_list = ref []
    (* Equality obligations between def_lists *)

let ok_arrays_first_branch = ref []
let ok_arrays_second_branch = ref []
    (* [ok_arrays_first_branch] contains the list of variables that
       are defined and used only in the first merged branch, and such that 
       all array accesses have curarray_suffix as suffix of the argument.
       [ok_arrays_second_branch] is similar for the second branch.
       These variables are allowed to be renamed during the merge,
       even though they have array references. *)


let has_array_ref b =
  Array_ref.has_array_ref_non_exclude b || Settings.occurs_in_queries b (!whole_game).current_queries

let diff_message ?(show_diff_reason = false) occ1 occ2 msg =
  if show_diff_reason then
    print_string ("At "^(string_of_int occ1)^
		  " in this process and at "^(string_of_int occ2)^
		  " on the other end, "^msg^".\n")
    
(* [merge_var next_f map b b'] records that variable [b] in the first branch to merge
   corresponds to variable [b'] in the second branch. 
   This may be done by adding (b,b') to [map] (for variables without array accesses after merge) 
   or to [global_map] (for variables with array accesses but local to one of the branches).
   In case of success, it calls [next_f] with the updated [map].
   In case of failure, it returns false. *)

let merge_var ?show_diff_reason occ occ' next_f map b b' =
  if b == b' then
    next_f map
  else if (b.btype != b'.btype) then
    begin
      diff_message ?show_diff_reason occ occ'
	("variables "^(Display.binder_to_string b)^" in this process and "^(Display.binder_to_string b')^" on the other end have different types");
      false
    end
  else if (Settings.occurs_in_queries b (!whole_game).current_queries) || (Settings.occurs_in_queries b' (!whole_game).current_queries) then
    (* Never happens when show_diff_reason = true *)
    false
  else 
    let ar_b = Array_ref.has_array_ref_non_exclude b in
    let ar_b' = Array_ref.has_array_ref_non_exclude b' in
    if (not ar_b) && (not ar_b') then
      next_f ((Terms.term_from_binder b,Terms.term_from_binder b')::map)
    else if (List.memq b (!ok_arrays_first_branch)) &&
            (List.memq b' (!ok_arrays_second_branch)) then
      begin
	(* check no previous entry with b or b' but not both in global_map *)
        if List.exists (fun (b1, b1') ->
	  let result = (b == b1 && b' != b1') || (b != b1 && b' == b1') in
	  if result then
	    diff_message ?show_diff_reason occ occ'
	      ("incoherent renaming: variables "^(Display.binder_to_string b)^" in this process is mapped "^(Display.binder_to_string b')^" on the other end, but "^(Display.binder_to_string b1)^" was already mapped to "^(Display.binder_to_string b1'));
	  result
	    ) (!global_map) then
           false
        else
          begin
	    (* Do not add if same entry already present. *)
	    if not (List.exists (fun (b1,b1') -> b == b1 && b' == b1') (!global_map)) then
	      global_map := (b,b') :: (!global_map);
	    next_f map
          end
      end
    else if !Settings.merge_arrays then
      begin
	if ar_b then var_no_array_ref := b :: (!var_no_array_ref);
	if ar_b' then var_no_array_ref := b' :: (!var_no_array_ref);
	if ar_b && ar_b' && (b.count_def == 1) && (b'.count_def == 1) then
          (* When there are variables with different names in the various
             branches and they have array references, we advise MergeArrays. *)
	  cur_branch_var_list := (b,b') :: (!cur_branch_var_list);
	next_f ((Terms.term_from_binder b,Terms.term_from_binder b')::map)
      end
    else 
      begin
	diff_message ?show_diff_reason occ occ'
	  ("variables "^(Display.binder_to_string b)^" in this process and "^(Display.binder_to_string b')^" on the other end have array references that prevent renaming");
	false
      end

(* [merge_var_list] is the same as [merge_var] but for lists of variables *)

let rec merge_var_list ?show_diff_reason occ occ' next_f map bl bl' =
  match bl,bl' with
    [], [] -> next_f map
  | [], _ | _, [] ->
      diff_message ?show_diff_reason occ occ'
	"find with different number of indices";
      false
  | ((b,_)::bl, (b',_)::bl') ->
      merge_var ?show_diff_reason occ occ'
	(fun map' -> merge_var_list ?show_diff_reason occ occ' next_f map' bl bl') map b b'
      
(* [equal_terms_ren map t t'] records in [eq_oblig] the constraint
   that the image by [map] and [global_map] of the term [t] must be 
   equal to [t'].  
   This constraint is verified in [equal_store_arrays] after the 
   whole processes/terms have been compared.
   The image by [map] is computed in [equal_terms_ren], while
   the image by [global_map] is computed at test time in 
   [equal_store_arrays].
   [equal_terms_ren] always returns true. *)

let equal_terms_ren ?show_diff_reason map t t' = 
  if t.t_type != t'.t_type then
    begin
      diff_message ?show_diff_reason t.t_occ t'.t_occ
	"terms have different types";
      false
    end
  else
    begin
      List.iter (fun (t1,t1') ->
	match t1.t_desc with
	  Var(b,_) -> b.link <- TLink t1'
	| ReplIndex b -> b.ri_link <- TLink t1'
	| _ -> Parsing_helper.internal_error "Mergebranches.equal_terms_ren: map should contain only Var/ReplIndex") map;
      let mapped_t = Terms.copy_term Terms.Links_RI_Vars t in
      List.iter (fun (t1,t1') ->
	match t1.t_desc with
	  Var(b,_) -> b.link <- NoLink
	| ReplIndex b -> b.ri_link <- NoLink
	| _ -> Parsing_helper.internal_error "Mergebranches.equal_terms_ren: map should contain only Var/ReplIndex") map;
      (* We test the equality of processes by first testing that
	 they have the same structure, and collecting all needed 
	 equalities of terms in eq_oblig. When the processes have
	 the same structure, we will later verify that the terms are
	 indeed equal. This is because testing equality of terms
	 is more costly. *)
      eq_oblig := (t.t_occ, mapped_t, t'.t_occ, t') :: (!eq_oblig);
      true
    end


(* [eq_deflist map dl dl'] records in [eq_oblig_def_list] the constraint
   that the image by [map] and [global_map] of the defined condition [dl] must be 
   equal to [dl'], similarly to [equal_terms_ren] above.  *)

let eq_deflist map occ dl occ' dl' = 
  begin
    List.iter (fun (t1,t1') ->
      match t1.t_desc with
	Var(b,_) -> b.link <- TLink t1'
      | ReplIndex b -> b.ri_link <- TLink t1'
      | _ -> Parsing_helper.internal_error "Mergebranches.eq_deflist: map should contain only Var/ReplIndex") map;
    let mapped_dl = Terms.copy_def_list Terms.Links_RI_Vars dl in
    List.iter (fun (t1,t1') ->
      match t1.t_desc with
	Var(b,_) -> b.link <- NoLink
      | ReplIndex b -> b.ri_link <- NoLink
      | _ -> Parsing_helper.internal_error "Mergebranches.eq_deflist: map should contain only Var/ReplIndex") map;
  (* We test the equality of processes by first testing that
     they have the same structure, and collecting all needed 
     equalities of def lists in eq_oblig_def_list. When the processes have
     the same structure, we will later verify that the def lists are
     indeed equal. This is because testing equality of terms
     is more costly. *)
    eq_oblig_def_list := (occ, mapped_dl, occ', dl') :: (!eq_oblig_def_list);
    true
  end

(* [equal_pat_ren map map_ref pat pat'] records that the image by
   by [map] and [global_map] of the pattern [pat] must be equal to
   [pat']. 
   [map] is the initial correspondence between variables;
   [map_ref] is initially equal to [map] and is updated by 
   adding variables bound by the patterns [pat] and [pat'].
   [equal_pat_ren] returns false when the image by
   by [map] and [global_map] of the pattern [pat] cannot be 
   equal to [pat']. The constraints needed to have equality
   are collected in [eq_oblig] and [eq_oblig_def_list]. *)

let rec equal_pat_ren ?show_diff_reason occ occ' map map_ref pat pat' =
  match pat, pat' with
    PatVar b, PatVar b' ->
      merge_var ?show_diff_reason occ occ' (fun map' -> map_ref := map'; true) (!map_ref) b b'
  | PatTuple(f,l), PatTuple(f',l') ->
      if f != f' then
	begin
	  diff_message ?show_diff_reason occ occ' "patterns have different function symbols";
	  false
	end
      else
	List.for_all2 (equal_pat_ren ?show_diff_reason occ occ' map map_ref) l l'
  | PatEqual t, PatEqual t' -> 
      equal_terms_ren ?show_diff_reason map t t' 
  | _ ->
      diff_message ?show_diff_reason occ occ' "patterns do not match";
      false

(* [equal_find_cond map t t'] records that the image by
   by [map] and [global_map] of the term [t] must be equal to
   [t']. It returns false when the equality is impossible.
   The constraints needed to have equality
   are collected in [eq_oblig] and [eq_oblig_def_list].

   [equal_process] and [equal_oprocess] are similar, for
   input and output processes respectively. *)

let same_nb_branch ?show_diff_reason occ occ' l0 l0' =
  if List.length l0 == List.length l0' then
    true
  else
    begin
      diff_message ?show_diff_reason occ occ' "finds have different numbers of branches";
      false
    end

let same_unique ?show_diff_reason occ occ' l0 find_info l0' find_info' =
  if (Terms.equal_find_info
	(Terms.is_unique (Some (!whole_game)) l0 find_info)
	(Terms.is_unique (Some (!whole_game)) l0' find_info'))
  then true
  else
    begin
      diff_message ?show_diff_reason occ occ' "find is unique on one side only";
      false
    end

let same_nb_index ?show_diff_reason occ occ' bl bl' =
  if List.length bl == List.length bl' then
    true
  else
    begin
      diff_message ?show_diff_reason occ occ' "some find branches have different numbers of indices";
      false
    end
      
let rec equal_find_cond ?show_diff_reason map t t' =
  match t.t_desc, t'.t_desc with
    (Var _ | FunApp _ | ReplIndex _), (Var _ | FunApp _ | ReplIndex _) -> 
      equal_terms_ren ?show_diff_reason map t t'
  | TestE(t1,t2,t3), TestE(t1',t2',t3') ->
      (equal_terms_ren ?show_diff_reason map t1 t1') &&
      (equal_find_cond ?show_diff_reason map t2 t2') &&
      (equal_find_cond ?show_diff_reason map t3 t3')
  | FindE(l0,t3,find_info), FindE(l0',t3',find_info') ->
      (equal_find_cond ?show_diff_reason map t3 t3') &&
      (same_nb_branch ?show_diff_reason t.t_occ t'.t_occ l0 l0') &&
      (same_unique ?show_diff_reason t.t_occ t'.t_occ l0 find_info l0' find_info') &&
      (List.for_all2 (fun (bl, def_list, t, t1)
	  (bl', def_list', t', t1') ->
	    (* I don't check here that the types of the indices are the same, but
	       this is checked by merge_var_list below. *)
	    (same_nb_index ?show_diff_reason t.t_occ t'.t_occ bl bl') &&
	    let map' = (List.map2 (fun (_, b) (_,b') -> (Terms.term_from_repl_index b, Terms.term_from_repl_index b')) bl bl') @ map in
	    (eq_deflist map' t.t_occ def_list t'.t_occ def_list') &&
	    (equal_find_cond ?show_diff_reason map' t t') &&
	    (merge_var_list ?show_diff_reason t.t_occ t'.t_occ
	       (fun map'' -> equal_find_cond ?show_diff_reason map'' t1 t1') map bl bl')
	      ) l0 l0')
  | LetE(pat,t1,t2,topt),LetE(pat',t1',t2',topt') ->
      (equal_terms_ren ?show_diff_reason map t1 t1') &&
      (match topt, topt' with
	None, None -> true
      |	Some t3, Some t3' -> equal_find_cond map ?show_diff_reason t3 t3'
      |	_ ->
	  diff_message ?show_diff_reason t.t_occ t'.t_occ "else branch of let present on one side only";
	  false) &&
      (let map_ref = ref map in
      let eq_pat = equal_pat_ren ?show_diff_reason t.t_occ t'.t_occ map map_ref pat pat' in
      eq_pat && (equal_find_cond ?show_diff_reason (!map_ref) t2 t2'))
  | ResE(b,t), ResE(b',t') ->
      merge_var ?show_diff_reason t.t_occ t'.t_occ
	(fun map' -> equal_find_cond ?show_diff_reason map' t t') map b b'
  | (EventAbortE f, EventAbortE f') ->
      if f != f' then
	diff_message ?show_diff_reason t.t_occ t'.t_occ "events with different names";
      f == f'
  | (EventE _, EventE _) ->
      Parsing_helper.internal_error "Events should not occur in find conditions"
  | (GetE _, GetE _) | (InsertE _, InsertE _) ->
      Parsing_helper.internal_error "Get/Insert should not occur in Transf_merge.equal_find_cond"
  | _ ->
      diff_message ?show_diff_reason t.t_occ t'.t_occ "terms differ";
      false

let same_channel ?show_diff_reason occ occ' map (c,tl) (c',tl') =
  if c != c' then
    begin
      diff_message ?show_diff_reason occ occ' "channels differ";
      false
    end
  else if (List.length tl != List.length tl') then
    begin
      diff_message ?show_diff_reason occ occ' "channels with different numbers of indices";
      false
    end
  else
    List.for_all2 (equal_terms_ren ?show_diff_reason map) tl tl'
	
let rec equal_process ?show_diff_reason map p p' =
  match p.i_desc, p'.i_desc with
    Nil, Nil -> true
  | Par(p1,p2), Par(p1',p2') -> 
      (equal_process ?show_diff_reason map p1 p1') &&
      (equal_process ?show_diff_reason map p2 p2')
  | Repl(b,p1), Repl(b',p1') -> 
      if b == b' then
	equal_process ?show_diff_reason map p1 p1'
      else if b.ri_type != b'.ri_type then
	begin
	  diff_message ?show_diff_reason p.i_occ p'.i_occ "replications with different bounds";
	  false
	end
      else
	equal_process ?show_diff_reason ((Terms.term_from_repl_index b, Terms.term_from_repl_index b')::map) p1 p1'
  | Input(ch, pat, p1), Input(ch', pat', p1') ->
      (same_channel ?show_diff_reason p.i_occ p'.i_occ map ch ch') &&
      (let map_ref = ref map in
      let eq_pat = equal_pat_ren ?show_diff_reason p.i_occ p'.i_occ map map_ref pat pat' in
      eq_pat && (equal_oprocess ?show_diff_reason (!map_ref) p1 p1'))
  | _ ->
      diff_message ?show_diff_reason p.i_occ p'.i_occ "processes differ";
      false

and equal_oprocess ?show_diff_reason map p p' =
  match p.p_desc, p'.p_desc with
    Yield, Yield -> true
  | EventAbort f, EventAbort f' ->
      if f != f' then
	begin
	  diff_message ?show_diff_reason p.p_occ p'.p_occ "events with different names";
	  false
	end
      else
	true
  | Restr(b,p1), Restr(b',p1') ->
      merge_var ?show_diff_reason p.p_occ p'.p_occ
	(fun map' -> equal_oprocess ?show_diff_reason map' p1 p1') map b b'
  | Test(t,p1,p2), Test(t',p1',p2') ->
      (equal_terms_ren ?show_diff_reason map t t') &&
      (equal_oprocess ?show_diff_reason map p1 p1') &&
      (equal_oprocess ?show_diff_reason map p2 p2')
  | Let(pat, t, p1, p2), Let(pat', t', p1', p2') ->
      (equal_terms_ren ?show_diff_reason map t t') &&
      (equal_oprocess ?show_diff_reason map p2 p2') &&
      (let map_ref = ref map in
      let eq_pat = equal_pat_ren ?show_diff_reason p.p_occ p'.p_occ map map_ref pat pat' in
       eq_pat && (equal_oprocess ?show_diff_reason (!map_ref) p1 p1'))
  | Output(ch,t2,p1), Output(ch',t2',p1') ->
      (same_channel ?show_diff_reason p.p_occ p'.p_occ map ch ch') &&
      (equal_terms_ren ?show_diff_reason map t2 t2') &&
      (equal_process ?show_diff_reason map p1 p1')
  | EventP(t,p), EventP(t',p') ->
      (equal_terms_ren ?show_diff_reason map t t') &&
      (equal_oprocess ?show_diff_reason map p p')
  | Find(l,p1, find_info), Find(l',p1', find_info') ->
      (equal_oprocess ?show_diff_reason map p1 p1') &&
      (same_nb_branch ?show_diff_reason p.p_occ p'.p_occ l l') &&
      (same_unique ?show_diff_reason p.p_occ p'.p_occ l find_info l' find_info') &&
      (List.for_all2 (fun 
	(bl, def_list, t, p1)
	  (bl', def_list', t', p1') ->
	    (* I don't check here that the types of the indices are the same, but
	       this is checked by merge_var_list below. *)
	    (same_nb_index ?show_diff_reason p.p_occ p'.p_occ bl bl') &&
	    let map' = (List.map2 (fun (_, b) (_,b') -> (Terms.term_from_repl_index b, Terms.term_from_repl_index b')) bl bl') @ map in
	    (eq_deflist map' p.p_occ def_list p'.p_occ def_list') &&
	    (equal_find_cond ?show_diff_reason map' t t') &&
	    (merge_var_list ?show_diff_reason p.p_occ p'.p_occ
	       (fun map'' -> equal_oprocess ?show_diff_reason map'' p1 p1') map bl bl')
	      ) l l')
  | (Get _, Get _) | (Insert _, Insert _) ->
      Parsing_helper.internal_error "Get/Insert should not occur in Transf_merge.equal_oprocess"
  | _ ->
      diff_message ?show_diff_reason p.p_occ p'.p_occ "processes differ";
      false


(* [collect_def_vars_term def_vars t] collects variables defined in a term [t]
   in the list [def_vars]. On return, the list contains [(b, ref n, ref 0)] for each
   variable [b] defined in the term [t], where [n] is the number of definitions of [b] in [t].

   [collect_def_vars_pattern], [collect_def_vars_def_list], [collect_def_vars_process], 
   and [collect_def_vars_oprocess] are similar for patterns, defined conditions, input processes,
   and output processes respectively. *)

let add def_vars b =
  try 
    let (n_def, _) = List.assq b (!def_vars) in
    incr n_def
  with Not_found ->
    def_vars := (b, (ref 1, ref 0)) :: (!def_vars)

let rec collect_def_vars_term def_vars t = 
  match t.t_desc with
    Var(_, l) | FunApp(_,l) ->
      List.iter (collect_def_vars_term def_vars) l
  | ReplIndex i -> ()
  | TestE(t1,t2,t3) ->
      collect_def_vars_term def_vars t1;
      collect_def_vars_term def_vars t2;
      collect_def_vars_term def_vars t3
  | LetE(pat, t1, t2, topt) ->
      collect_def_vars_pattern def_vars pat;
      collect_def_vars_term def_vars t1;
      collect_def_vars_term def_vars t2;
      begin
	match topt with
	  None -> ()
	| Some t3 -> collect_def_vars_term def_vars t3
      end
  | FindE(l0,t3,_) ->
      List.iter (fun (bl,def_list, t1,t2) ->
	List.iter (fun (b,_) -> add def_vars b) bl;
	collect_def_vars_def_list def_vars def_list;
	collect_def_vars_term def_vars t1;
	collect_def_vars_term def_vars t2) l0;
      collect_def_vars_term def_vars t3
  | ResE(b,t) ->
      add def_vars b;
      collect_def_vars_term def_vars t
  | EventAbortE _ -> ()
  | EventE(t,p) ->
      collect_def_vars_term def_vars t;
      collect_def_vars_term def_vars p
  | GetE _ | InsertE _ ->
      Parsing_helper.internal_error "Get/Insert should not appear in Transf_merge.collect_def_vars_term"

and collect_def_vars_pattern def_vars = function
    PatVar b -> add def_vars b
  | PatTuple (f,l) -> List.iter (collect_def_vars_pattern def_vars) l
  | PatEqual t -> collect_def_vars_term def_vars t

and collect_def_vars_def_list def_vars def_list =
  List.iter (fun (_,l) -> 
    List.iter (collect_def_vars_term def_vars) l
    ) def_list

let rec collect_def_vars_process def_vars p =
  match p.i_desc with
    Nil -> ()
  | Par(p1,p2) -> 
      collect_def_vars_process def_vars p1;
      collect_def_vars_process def_vars p2
  | Repl(b,p) ->
      collect_def_vars_process def_vars p
  | Input((_,tl),pat,p) ->
      List.iter (collect_def_vars_term def_vars) tl;      
      collect_def_vars_pattern def_vars pat;
      collect_def_vars_oprocess def_vars p

and collect_def_vars_oprocess def_vars p = 
  match p.p_desc with
    Yield | EventAbort _ -> ()
  | Restr(b,p) ->
      add def_vars b;
      collect_def_vars_oprocess def_vars p
  | Test(t,p1,p2) ->
      collect_def_vars_term def_vars t;      
      collect_def_vars_oprocess def_vars p1;
      collect_def_vars_oprocess def_vars p2
  | Find(l0,p2,_) ->
      List.iter (fun (bl,def_list,t,p1) ->
	List.iter (fun (b,_) -> add def_vars b) bl;
	collect_def_vars_def_list def_vars def_list;
	collect_def_vars_term def_vars t;      
	collect_def_vars_oprocess def_vars p1) l0;
      collect_def_vars_oprocess def_vars p2
  | Output((_,tl),t2,p) ->
      List.iter (collect_def_vars_term def_vars) tl;      
      collect_def_vars_term def_vars t2;
      collect_def_vars_process def_vars p
  | Let(pat, t, p1, p2) ->
      collect_def_vars_pattern def_vars pat;
      collect_def_vars_term def_vars t;      
      collect_def_vars_oprocess def_vars p1;
      collect_def_vars_oprocess def_vars p2
  | EventP(t,p) ->
      collect_def_vars_term def_vars t;      
      collect_def_vars_oprocess def_vars p
  | Get(tbl,patl,topt,p1,p2,_) ->
      List.iter (collect_def_vars_pattern def_vars) patl;
      (match topt with 
         | Some t -> collect_def_vars_term def_vars t
         | None -> ());
      collect_def_vars_oprocess def_vars p1;
      collect_def_vars_oprocess def_vars p2
  | Insert(tbl,tl,p) ->
      List.iter (collect_def_vars_term def_vars) tl;
      collect_def_vars_oprocess def_vars p

(* [check_array_ref_term in_scope curarray_suffix ok_vars t] removes from
   [ok_vars] all variables that have array accesses with arguments that do not
   contain [curarray_suffix] as a suffix. 
   [in_scope] is the list of variables that are in scope at [t].
   (Variables not defined in the branch that we want to merge can be ignored.)
   [ok_vars] initially contains [(b, (ref n, ref 0))] for each variable [b]
   defined [n] times (n >= 1) in the branch that we want to merge.
   The component [ref 0] is updated to contain the number array accesses
   to [b] in the term [t]. 

   [check_array_ref_pattern], [check_array_ref_def_list],
   [check_array_ref_process], and [check_array_ref_oprocess] are
   similar for patterns, defined conditions, input processes, and
   output processes respectively.  *)

(*    [remove b l] returns the list [l] without the element [(b,_)]
      when it is present *)

let rec remove b = function
    [] -> []
  | ((b',_) as a)::l ->
      if b == b' then l else a::(remove b l)

(*    [is_suffix curarray_suffix l] returns true when [curarray_suffix] 
      is a suffix of [l] *)

let is_suffix curarray_suffix l =
  let ls = List.length curarray_suffix in
  let ll = List.length l in
  (ll >= ls) && (List.for_all2 (fun ri t -> 
    match t.t_desc with
      ReplIndex ri' -> ri == ri'
    | _ -> false) curarray_suffix (Terms.skip (ll - ls) l))
  
let array_access curarray_suffix ok_vars b l =
  (* There is an array reference b[l]
     If curarray_suffix not suffix of l, remove b from ok_vars if it was in.
     Otherwise, increment the number of accesses to b stored in ok_vars *)
  if is_suffix curarray_suffix l then
    try
      let (_, n_array_access) = List.assq b (!ok_vars) in
      incr n_array_access
    with Not_found -> ()
  else
    ok_vars := remove b (!ok_vars)

let rec check_array_ref_term in_scope curarray_suffix ok_vars t = 
  match t.t_desc with
    Var(b, l) -> 
      if not (Terms.is_args_at_creation b l && List.memq b in_scope) then
	array_access curarray_suffix ok_vars b l;
      List.iter (check_array_ref_term in_scope curarray_suffix ok_vars) l
  | ReplIndex i -> ()
  | FunApp(_,l) ->
      List.iter (check_array_ref_term in_scope curarray_suffix ok_vars)  l
  | TestE(t1,t2,t3) ->
      check_array_ref_term in_scope curarray_suffix ok_vars t1;
      check_array_ref_term in_scope curarray_suffix ok_vars t2;
      check_array_ref_term in_scope curarray_suffix ok_vars t3
  | LetE(pat, t1, t2, topt) ->
      check_array_ref_pattern in_scope curarray_suffix ok_vars pat;
      check_array_ref_term in_scope curarray_suffix ok_vars t1;
      check_array_ref_term (Terms.vars_from_pat in_scope pat) curarray_suffix ok_vars t2;
      begin
	match topt with
	  None -> ()
	| Some t3 -> check_array_ref_term in_scope curarray_suffix ok_vars t3
      end
  | FindE(l0,t3,_) ->
      List.iter (fun (bl,def_list, t1,t2) ->
	let in_scope' = (List.map fst bl) @ in_scope in
	check_array_ref_def_list in_scope curarray_suffix ok_vars def_list;
	check_array_ref_term in_scope curarray_suffix ok_vars t1;
	check_array_ref_term in_scope' curarray_suffix ok_vars t2) l0;
      check_array_ref_term in_scope curarray_suffix ok_vars t3
  | ResE(b,t) ->
      check_array_ref_term (b::in_scope) curarray_suffix ok_vars t
  | EventAbortE _ -> ()
  | EventE(t,p) ->
      check_array_ref_term in_scope curarray_suffix ok_vars t;      
      check_array_ref_term in_scope curarray_suffix ok_vars p
  | GetE _ | InsertE _ ->
      Parsing_helper.internal_error "Get/Insert should not appear in Transf_merge.check_array_ref_term"

and check_array_ref_pattern in_scope curarray_suffix ok_vars = function
    PatVar b -> ()
  | PatTuple (f,l) -> List.iter (check_array_ref_pattern in_scope curarray_suffix ok_vars) l
  | PatEqual t -> check_array_ref_term in_scope curarray_suffix ok_vars t

and check_array_ref_def_list in_scope' curarray_suffix ok_vars def_list =
  List.iter (fun (b,l) -> 
    List.iter (check_array_ref_term in_scope' curarray_suffix ok_vars) l;
    if not (Terms.is_args_at_creation b l && List.memq b in_scope') then
      array_access curarray_suffix ok_vars b l 
	) def_list

let rec check_array_ref_process in_scope curarray_suffix ok_vars p =
  match p.i_desc with
    Nil -> ()
  | Par(p1,p2) -> 
      check_array_ref_process in_scope curarray_suffix ok_vars p1;
      check_array_ref_process in_scope curarray_suffix ok_vars p2
  | Repl(b,p) ->
      check_array_ref_process in_scope curarray_suffix ok_vars p
  | Input((_,tl),pat,p) ->
      List.iter (check_array_ref_term in_scope curarray_suffix ok_vars) tl;
      check_array_ref_pattern in_scope curarray_suffix ok_vars pat;
      check_array_ref_oprocess (Terms.vars_from_pat in_scope pat) curarray_suffix ok_vars p

and check_array_ref_oprocess in_scope curarray_suffix ok_vars p = 
  match p.p_desc with
    Yield | EventAbort _ -> ()
  | Restr(b,p) ->
      check_array_ref_oprocess (b::in_scope) curarray_suffix ok_vars p
  | Test(t,p1,p2) ->
      check_array_ref_term in_scope curarray_suffix ok_vars t;      
      check_array_ref_oprocess in_scope curarray_suffix ok_vars p1;
      check_array_ref_oprocess in_scope curarray_suffix ok_vars p2
  | Find(l0,p2,_) ->
      List.iter (fun (bl,def_list,t,p1) ->
	let in_scope' = (List.map fst bl) @ in_scope in
	check_array_ref_def_list in_scope curarray_suffix ok_vars def_list;
	check_array_ref_term in_scope curarray_suffix ok_vars t;      
	check_array_ref_oprocess in_scope' curarray_suffix ok_vars p1) l0;
      check_array_ref_oprocess in_scope curarray_suffix ok_vars p2
  | Output((_,tl),t2,p) ->
      List.iter (check_array_ref_term in_scope curarray_suffix ok_vars) tl;
      check_array_ref_term in_scope curarray_suffix ok_vars t2;
      check_array_ref_process in_scope curarray_suffix ok_vars p
  | Let(pat, t, p1, p2) ->
      check_array_ref_pattern in_scope curarray_suffix ok_vars pat;
      check_array_ref_term in_scope curarray_suffix ok_vars t;      
      check_array_ref_oprocess (Terms.vars_from_pat in_scope pat) curarray_suffix ok_vars p1;
      check_array_ref_oprocess in_scope curarray_suffix ok_vars p2
  | EventP(t,p) ->
      check_array_ref_term in_scope curarray_suffix ok_vars t;      
      check_array_ref_oprocess in_scope curarray_suffix ok_vars p
  | Get(tbl,patl,topt,p1,p2,_) ->
      List.iter (check_array_ref_pattern in_scope curarray_suffix ok_vars) patl;
      let in_scope' = Terms.vars_from_pat_list in_scope patl in
      (match topt with 
         | Some t -> check_array_ref_term in_scope' curarray_suffix ok_vars t
         | None -> ());
      check_array_ref_oprocess in_scope' curarray_suffix ok_vars p1;
      check_array_ref_oprocess in_scope curarray_suffix ok_vars p2
  | Insert(tbl,tl,p) ->
      List.iter (check_array_ref_term in_scope curarray_suffix ok_vars) tl;
      check_array_ref_oprocess in_scope curarray_suffix ok_vars p

(* [get_in_scope fact_info] returns the list of variables currently
   in scope at [fact_info]. *)

let get_in_scope fact_info =
  match fact_info with
    Some(_,_,_,_,_,_,n) -> Terms.add_def_vars_node [] n
  | None -> Parsing_helper.internal_error "facts should have been set"

(* [filter_good_vars l] starts from a list containing
   [(b, (n_def, n_array_access))] for variable [b] defined in a branch
   we want to merge, with [n_def] definitions of [b] and [n_array_access]
   array accesses to [b] in that branch. It returns a sub-list containing
   [b] for each variable [b] defined and accessed only in that branch. *)

let rec filter_good_vars = function
    [] -> []
  | (b, (n_def, n_array_access))::l ->
      if b.count_array_ref < b.count_exclude_array_ref + !n_array_access then
	begin
	  print_string ((Display.binder_to_string b) ^ ": " ^
			(string_of_int b.count_array_ref) ^ " total array ref; " ^
			(string_of_int b.count_exclude_array_ref) ^ " excluded array ref; " ^
			(string_of_int (!n_array_access)) ^ " array ref in branch\n");
	end;
      assert (b.count_array_ref >= b.count_exclude_array_ref + !n_array_access);
      assert (b.count_def >= !n_def);
      if (b.count_array_ref = b.count_exclude_array_ref + !n_array_access) &&
	 (b.count_def = !n_def)
      then
	(* All array accesses to [b] are excluded or in the considered branch;
	   All definitions of [b] are in the considered branch. *)
	b::(filter_good_vars l)
      else
	filter_good_vars l

(* [collect_good_vars curarray_suffix_opt t] returns the list of variables
   defined in [t], accessed only in the term [t], and such that [curarray_suffix]
   is a suffix of the arguments of all accesses to these variables,
   when [curarray_suffix_opt = Some curarray_suffix].
   When [curarray_suffix_opt = None], it returns the empty list.

   [collect_good_vars_oprocess] is similar for processes. *)

let collect_good_vars curarray_suffix_opt t =
  match curarray_suffix_opt with
    None -> []
  | Some curarray_suffix ->
      let ok_vars = ref [] in
      collect_def_vars_term ok_vars t;
      let in_scope = [] (*get_in_scope t.t_facts*) in
      check_array_ref_term in_scope curarray_suffix ok_vars t;
      filter_good_vars (!ok_vars)
  
let collect_good_vars_oprocess curarray_suffix_opt p =
  match curarray_suffix_opt with
    None -> []
  | Some curarray_suffix ->
      let ok_vars = ref [] in
      collect_def_vars_oprocess ok_vars p;
      let in_scope = [] (*get_in_scope p.p_facts*) in
      check_array_ref_oprocess in_scope curarray_suffix ok_vars p;
      filter_good_vars (!ok_vars)

(* [equal_find_cond] is similar to the function [equal_find_cond] 
   defined above, but sets [ok_arrays_first_branch] and [ok_arrays_second_branch]
   before starting.

   [equal_oprocess] is similar for processes. *)

let equal_find_cond curarray_suffix t t' =
  ok_arrays_first_branch := collect_good_vars curarray_suffix t;
  ok_arrays_second_branch := collect_good_vars curarray_suffix t';
    (* [ok_arrays_first_branch] contains the list of variables 
       defined in [t], such that all array accesses are in [t] (or excluded)
       and all array accesses have [curarray_suffix] as suffix of indices.
       [ok_arrays_second_branch] is similar for [t']. *)
  equal_find_cond [] t t'

let equal_oprocess curarray_suffix p p' =
  ok_arrays_first_branch := collect_good_vars_oprocess curarray_suffix p;
  ok_arrays_second_branch := collect_good_vars_oprocess curarray_suffix p';
(*  print_string "ok_arrays_first_branch = "; Display.display_list Display.display_binder (!ok_arrays_first_branch); print_newline();
  print_string "ok_arrays_second_branch = "; Display.display_list Display.display_binder (!ok_arrays_second_branch); print_newline(); *)
  equal_oprocess [] p p'

(* For simplification of terms *)

(* Applying a substitution *)

let reduced_subst = ref false

let rec apply_subst1 t tsubst =
     match tsubst.t_desc with
       FunApp(f,[redl;redr]) when f.f_cat == Equal || f.f_cat == LetEqual ->
         begin
           if Terms.equal_terms t redl then 
	     begin
	       reduced_subst := true;
	       redr
	     end
           else
             match t.t_desc with
               Var(b,l) ->
	         Terms.build_term t (Var(b, List.map (fun t' -> apply_subst1 t' tsubst) l))
             | FunApp(f,l) when f.f_cat != LetEqual ->
	         Terms.build_term t (FunApp(f, List.map (fun t' -> apply_subst1 t' tsubst) l))
             | _ -> t
         end
     | _ -> Parsing_helper.internal_error "substitutions should be Equal or LetEqual terms"

let rec apply_all_subst t = function
    [] -> t
  | (a::l) ->
      let t' = apply_subst1 t a in
      if !reduced_subst then t' else apply_all_subst t l

let rec reduce ((subst2, _, _) as simp_facts) t =
  reduced_subst := false;
  let t' = apply_all_subst t subst2 in
  if !reduced_subst then 
    reduce simp_facts t' 
  else
    t

(* simp_equal_terms tests equality between t and t', modulo rewrite rules in 
   simp_facts. Returns true when equal, false otherwise.  *)

let simp_equal_terms simp_facts t t' =
  let t = reduce simp_facts t in
  let t' = reduce simp_facts t' in
  Terms.equal_terms t t'

(* simp_equal_def_list tests that two defined conditions are equal.
   It allows reordering elements of the defined conditions.
   Rewriting of terms using simp_facts is allowed because the facts
   in simp_facts anyway deal only with variables that are already
   known to be defined. 

   simp_equal_binderref does the equality test for one binder reference. *)

let simp_equal_binderref simp_facts br br' =
  simp_equal_terms simp_facts (Terms.term_from_binderref br) (Terms.term_from_binderref br')

let simp_equal_def_list simp_facts dl dl' =
  (List.for_all (fun br' -> List.exists (fun br -> simp_equal_binderref simp_facts br br') dl) dl') &&
  (List.for_all (fun br -> List.exists (fun br' -> simp_equal_binderref simp_facts br br') dl') dl) 

    
let rec orient t1 t2 = 
  match t1.t_desc, t2.t_desc with
    (Var(b,l), _) when
    (not (Terms.refers_to b t2)) && 
    (not (Terms.is_restr b)) -> true
  | (Var(b1,l1), Var(b2,l2)) when
    (b1 == b2) && (List.for_all2 orient l1 l2) -> true
  | (ReplIndex b1, ReplIndex b2) -> true
  | (FunApp(f1,l1), FunApp(f2,l2)) when
    (f1 == f2) && (List.for_all2 orient l1 l2) -> true
  | _ -> false
    
(* Apply reduction rules defined by statements to term t *)

let reduced = Facts.reduced

let rec apply_reds simp_facts t =
  let t = reduce simp_facts t in
  reduced := false;
  let t' = Facts.apply_eq_statements_and_collisions_subterms_once (reduce_rec simp_facts) Facts.no_dependency_anal Terms.simp_facts_id t in
  if !reduced then 
    apply_reds simp_facts t' 
  else
    t

(* [reduce_rec simp_facts f t] simplifies the term [t] knowing the fact [f] 
   in addition to the already known facts [simp_facts]. It returns
   the reduced term as well as a boolean that is true 
   when [t] has really been modified. *)

and reduce_rec simp_facts f t =
  let reduced_tmp = !reduced in
  reduced := false;
  let t'' =
    Terms.auto_cleanup (fun () ->
      let simp_facts' = simplif_add simp_facts f in
      let t' = reduce simp_facts' t in
      Facts.apply_eq_statements_subterms_once Terms.simp_facts_id t')
  in
  let red = !reduced in
  reduced := reduced_tmp;
  (t'', red)
      
and add_fact ((subst2, facts, elsefind) as simp_facts) fact =
  (* print_string "Adding "; Display.display_term fact; print_newline(); *)
  match fact.t_desc with
    FunApp(f,[t1;t2]) when f.f_cat == LetEqual ->
      begin
	match t1.t_desc with
	  Var(b,l) -> 
	    let t1' = Terms.build_term t1 (Var(b, List.map (reduce simp_facts) l))
	    in
	    let t2' = reduce simp_facts t2 in
	    let rec try_red_t1 = function
		[] -> (* Could not reduce t1' *)
		  subst_simplify2 simp_facts (Terms.make_let_equal t1' t2')
	      | { t_desc = FunApp(f'',[t1'';t2''])}::l when f''.f_cat == LetEqual ->
		  if Terms.equal_terms t1'' t1' then 
		    simplif_add simp_facts (Terms.make_equal t2' t2'')
		  else
		    try_red_t1 l
	      | _::l -> try_red_t1 l
	    in
	    try_red_t1 subst2
	| _ ->
	    Display.display_term fact;
	    Parsing_helper.internal_error "LetEqual terms should have a variable in the left-hand side"
      end
  | FunApp(f,[t1;t2]) when f.f_cat == Equal ->
      begin
	try
	  let (l1,l2) = Facts.simplify_equal t1 t2 in
	  simplif_add_list simp_facts (List.map2 Terms.make_equal l1 l2)
	with Facts.Unchanged ->
	  if orient t1 t2 then
	    subst_simplify2 simp_facts fact
	  else if orient t2 t1 then
	    subst_simplify2 simp_facts (Terms.make_equal t2 t1)
	  else
	    (subst2, fact::facts, elsefind)
      end
  | FunApp(f,[t1;t2]) when f == Settings.f_and ->
      simplif_add (add_fact simp_facts t1) t2
  | _ -> 
      if Terms.is_false fact then raise Contradiction else
      if Terms.is_true fact then simp_facts else
      (subst2, fact::facts, elsefind)

and subst_simplify2 (subst2, facts, elsefind) link =
  let subst2'' = ref [] in
  let not_subst2_facts = ref [] in
  List.iter (fun t0 ->
    match t0.t_desc with
      FunApp(f, [t;t']) when f.f_cat == Equal || f.f_cat == LetEqual ->
	(* When f.f_cat == LetEqual, t itself cannot be reduced by link,
	   since otherwise the left-hand side of link is t, and this
           term should have been reduced into t' by t0 before.
	   However, subterms of t may be reduced by link.
	   
	   When f.f_cat == LetEqual and we reduce only t' (not t),
	   we might directly add 
	   Terms.make_let_equal t (try_no_var simp_facts t1') to subst2''
	   However, it is not clear what "simp_facts" should really be...
         *)
	let (t1, t1', reduced) = 
	  match t'.t_desc with
	    Var _ | ReplIndex _ ->
	      reduced_subst := false;
	      let t1 = apply_subst1 t link in
	      let t1' = apply_subst1 t' link in
	      (t1,t1',!reduced_subst)
	  | FunApp _ ->
	      reduced_subst := false;
	      let t1 = apply_subst1 t link in
	      let red = !reduced_subst in
	      (* Applying reductions here slows down simplification *)
	      reduced := false;
	      let simp_facts_tmp = (link :: (!subst2''), facts, elsefind) in
	      let t1' = Facts.apply_eq_statements_and_collisions_subterms_once (reduce_rec simp_facts_tmp) Facts.no_dependency_anal Terms.simp_facts_id (reduce simp_facts_tmp t') in
	      (t1, t1', red || (!reduced) || (!reduced_subst))
	  | _ -> Parsing_helper.internal_error "If/let/find/new not allowed in subst_simplify2"
	in
	if reduced then
	  not_subst2_facts := (Terms.app f [t1; t1']) :: (!not_subst2_facts)
	else
	  subst2'' := t0 :: (!subst2'')
    | _ -> Parsing_helper.internal_error "substitutions should be Equal or LetEqual terms"
    ) subst2;
  simplif_add_list (link :: (!subst2''),[], elsefind) ((!not_subst2_facts) @ facts)

and simplif_add ((subst2, facts, elsefind) as simp_facts) fact =
(*  print_string "simplif_add "; Display.display_term fact; 
  print_string " knowing\n"; display_facts simp_facts; print_newline();*)
  let fact' = apply_reds simp_facts fact in
  add_fact simp_facts fact'

and simplif_add_list simp_facts = function
    [] -> simp_facts
  | (a::l) -> simplif_add_list (simplif_add simp_facts a) l


      

(* f is a function that compares processes; if in different branches 
   of these processes with have two variables (b,b') with arrays accesses,
   it stores (b,b') in diff_var_list.
   If f returns false, the comparison failed. 
   If diff_var_list is not empty, the comparison also failed, but we advise
   merging of arrays so that diff_var_list becomes empty on the next try.
*)

(* Exception CannotFormAdvice is raised when the variable pairs
   stored in cur_branch_var_list do not have the same variables
   in the same order in the second component (corresponding to the "else" branch)
   in all branches that we want to merge. This means that the merging
   we should do is not the same for all branches. This is not handled
   by MergeArrays, so we simply give up and do not give advice. *)

exception CannotFormAdvice

let rec form_advise all_branches =
  let first_branch = List.hd all_branches in
  List.iter (fun bl ->
    if List.length bl != List.length first_branch then
      raise CannotFormAdvice
      (*Parsing_helper.internal_error "All branches should have the same number of variables to merge"*)) all_branches;
  match first_branch with
    [] -> []
  | (_,b0)::_ ->
      let first_vars = List.map List.hd all_branches in
      List.iter (fun (_,b0') ->
	if b0 != b0' then
	  raise CannotFormAdvice
	  (*Parsing_helper.internal_error "The variables should be in the same order in all branches"*)) first_vars;
      let first_elem = (b0, Parsing_helper.dummy_ext) :: 
	(List.map (fun (b,_) -> (b, Parsing_helper.dummy_ext)) first_vars) 
      in
      first_elem :: (form_advise (List.map List.tl all_branches))
  

let store_arrays_to_normal f =
  cur_branch_var_list := [];
  all_branches_var_list := [];
  var_no_array_ref := [];
  let r = f() in
  if not r then
    begin
      var_no_array_ref := [];
      all_branches_var_list := [];
      Array_ref.cleanup_exclude_array_ref();
      false
    end
  else if List.for_all (fun bl -> bl == []) (!all_branches_var_list) then
    begin
      let r' = not (List.exists has_array_ref (!var_no_array_ref)) in
      var_no_array_ref := [];
      all_branches_var_list := [];
      Array_ref.cleanup_exclude_array_ref();
      r'
    end 
  else 
    begin
      (* Note: I cannot advise MergeArrays with mode MCreateBranchVarAtTerm/AtProc here,
	 because this function is called from simplification, and simplification can
	 modify the process afterwards, so that the term/process references might no longer
	 be correct. I should use mode MCreateBranchVarAtTerm/AtProc in the specialized
	 MergeBranches transformation. *)
      begin
	try
	  Settings.advise := Terms.add_eq (MergeArrays(List.rev (form_advise (!all_branches_var_list)), MCreateBranchVar)) (!Settings.advise);
	with CannotFormAdvice ->
	  ()
      end;
      var_no_array_ref := [];
      all_branches_var_list := [];
      Array_ref.cleanup_exclude_array_ref();
      false
    end
  

(* [rename map t] replaces variables in the term [t] according to [map]:
   [map] is a list of pairs of variables (b,b'); each variable
   b is then replaced with b'. 

   [rename_br] and [rename_def_list] are similar, for binder references
   (b,l) and defined conditions of find respectively. *)

let rec rename map t =
  Terms.build_term t (
  match t.t_desc with
    Var(b,l) -> 
      let b' =
	try
	  List.assq b map 
	with Not_found ->
	  b
      in
      Var(b', List.map (rename map) l)
  | FunApp(f,l) ->
      FunApp(f, List.map (rename map) l)
  | (ReplIndex i) as x -> x
  | _ -> Parsing_helper.internal_error "if/let/find/new/... should have been expanded in Transf_merge.rename")

let rename_br map (b,l) =
  let b' =
    try
      List.assq b map 
    with Not_found ->
      b
  in
  (b', List.map (rename map) l)

let rename_def_list map def_list =
  List.map (rename_br map) def_list



let equal_store_arrays ?show_diff_reason eq_test true_facts p p' =
  eq_oblig := [];
  eq_oblig_def_list := [];
  global_map := [];
  let r = eq_test p p' in
  if not r then
    begin
      cur_branch_var_list := [];
      eq_oblig := [];
      eq_oblig_def_list := [];
      global_map := [];
      ok_arrays_first_branch := [];
      ok_arrays_second_branch := [];
      false
    end
  else
    begin
      try 
	let (subst, facts, elsefind) = true_facts in
	let true_facts' = simplif_add_list (subst, [], []) facts in
	let r = 
	  List.for_all (fun (occ,t,occ',t') ->
	    if simp_equal_terms true_facts' (rename (!global_map) t) t' then
	      true
	    else
	      begin
		diff_message ?show_diff_reason occ occ' "terms cannot be proved equal";
		false
	      end) (!eq_oblig) &&
	  List.for_all (fun (occ,dl,occ',dl') ->
	    if simp_equal_def_list true_facts' (rename_def_list (!global_map) dl) dl' then
	      true
	    else
	      begin
		diff_message ?show_diff_reason occ occ' "defined conditions differ in a branch of find";
		false
	      end) (!eq_oblig_def_list) 
	in
	all_branches_var_list := (!cur_branch_var_list) :: (!all_branches_var_list);
	cur_branch_var_list := [];
	eq_oblig := [];
	eq_oblig_def_list := [];
	global_map := [];
	ok_arrays_first_branch := [];
	ok_arrays_second_branch := [];
	r
      with Contradiction ->
	(* A contradiction is discovered when adding the facts in true_facts.
	   This means that the current program point is in fact not reachable.
           This may happen because the addition procedure is not exactly the same
           as that used in the rest of simplification, so it may discover some
           new information, but it should be extremely rare. For simplicity, 
	   we ignore the information that the current program point is unreachable. *)
	cur_branch_var_list := [];
	eq_oblig := [];
	eq_oblig_def_list := [];
	global_map := [];
	ok_arrays_first_branch := [];
	ok_arrays_second_branch := [];
	false
    end

let equal eq_test true_facts p p' =
  store_arrays_to_normal (fun () -> 
    equal_store_arrays eq_test true_facts p p')
      
let needed_vars vars = List.exists has_array_ref vars

let can_merge_all_branches_store_arrays eq_test above_p_facts true_facts l0 p3 =
  let in_scope = get_in_scope above_p_facts in
  List.iter (fun (bl, def_list, t1, p2) ->
    var_no_array_ref := (List.map fst bl) @ (!var_no_array_ref);
    Array_ref.exclude_array_ref_def_list in_scope def_list;
    Array_ref.exclude_array_ref_term in_scope t1) l0;
  List.for_all (fun (_, def_list, t1, p2) ->
    (not (Terms.may_abort_counted (Some (!whole_game)) t1)) &&
    (equal_store_arrays eq_test true_facts p2 p3)) l0

(* was called from transf_simplify 
let can_merge_all_branches eq_test above_p_facts true_facts l0 p3 =
  store_arrays_to_normal (fun () ->
    can_merge_all_branches_store_arrays eq_test above_p_facts true_facts l0 p3)
*)

let can_merge_one_branch_store_arrays eq_test above_p_facts true_facts (bl, def_list, t1, p2) p3 =
  let in_scope = get_in_scope above_p_facts in
  Array_ref.exclude_array_ref_def_list in_scope def_list;
  Array_ref.exclude_array_ref_term in_scope t1;
  var_no_array_ref := (List.map fst bl) @ (!var_no_array_ref);
  equal_store_arrays eq_test true_facts p2 p3

(* was called from transf_simplify 
let can_merge_one_branch eq_test above_p_facts true_facts br p3 =
  store_arrays_to_normal (fun () ->
    can_merge_one_branch_store_arrays eq_test above_p_facts true_facts br p3)
*)

(* Transformation MergeArrays with merging of array references *)

exception Failed

let has_done_merge = ref false

(* We may use variables to distinguish the branches, and still merge
the arrays even if in some cases we need to know from which branch
they come *)

type new_branch_var_t =
    NoBranchVar
  | CreateBranchVar of binder list
  | CreateBranchVarAtProc of process list * binder list
  | CreateBranchVarAtTerm of term list * binder list

let rename_var (source_to_target_list, _) b =
  let rec ren = function
      [] -> b
    | (source_vars, target_var)::r ->
	if List.memq b source_vars then 
	  target_var
	else
	  ren r
  in
  ren source_to_target_list

let rec swap_rows_columns l =
  if List.hd l == [] then
    []
  else
    (List.map List.hd l)::(swap_rows_columns (List.map List.tl l))

let rec assq2 l1 l2 b =
  match (l1,l2) with
    [],[] -> raise Not_found
  | (b1::r1,b2::r2) ->
      if b1 == b then
	b2
      else
	assq2 r1 r2 b
  | _ -> Parsing_helper.internal_error "Lists should have same length in assq2"

let rec assq2l source_to_target_list l2 b =
  match source_to_target_list with
    [] -> raise Not_found 
  | (source_vars,_)::r ->
      try
	assq2 source_vars l2 b
      with Not_found ->
	assq2l r l2 b

let rec apply_list f target_new_def target_sv_brl sv_brl v =
  match target_new_def with
    [] -> v
  | (target_b, target_l)::r ->
      let v' = apply_list f r target_sv_brl sv_brl v in
      f (Terms.Rename(target_l, target_b, assq2 target_sv_brl sv_brl target_b)) v'

let add_def_var_find_cond rename_instr t b =
  match rename_instr with
    ((source_vars, target_var)::_), CreateBranchVar brl ->
      begin
	try
	  let b2 = assq2 source_vars brl b in
	  Terms.build_term t (LetE(PatVar b2, Stringmap.cst_for_type b2.btype, t, None))
	with Not_found -> 
	  t
      end
  | _ -> t

let add_def_var_proc rename_instr p b =
  match rename_instr with
    ((source_vars, target_var)::_), CreateBranchVar brl ->
      begin
	try
	  let b2 = assq2 source_vars brl b in
	  Terms.oproc_from_desc (Let(PatVar b2, Stringmap.cst_for_type b2.btype, p, Terms.oproc_from_desc Yield))
	with Not_found -> 
	  p
      end
  | _ -> p

let rec merge_term rename_instr t =
  match t.t_desc with
    Var(b,l) ->
      Terms.build_term t (Var(rename_var rename_instr b,
			       List.map (merge_term rename_instr) l))
  | FunApp(f,l) ->
      Terms.build_term t (FunApp(f, List.map (merge_term rename_instr) l))
  | ReplIndex _ -> t
  | ResE _ | EventAbortE _ | TestE _ | LetE _ | FindE _ | EventE _ | GetE _ | InsertE _ ->
      Parsing_helper.internal_error "new/event/event_abort/if/let/find/get/insert unexpected in terms"

let merge_find_branches proc_display proc_subst proc_rename proc_equal proc_merge proc_add_def_var merge_find_cond pp 
    rename_instr l0 p3 find_info =
  let (source_to_target_list, br_vars) = rename_instr in
  let already_defined = 
    match Incompatible.get_facts pp with
      Some (_, _, _, def_vars, _, _, def_node) ->
        def_vars @ def_node.def_vars_at_def @ 
	(List.map (fun b -> (b, List.map Terms.term_from_repl_index b.args_at_creation)) (Terms.add_def_vars_node [] def_node))
    | None -> Parsing_helper.internal_error "p_facts should have been defined"
  in
  let branches_to_merge = ref [] in
  let branches_to_leave_unchanged = ref [] in
  List.iter (function ((bl, def_list, t, p) as branch) ->
    let accu = ref [] in
    List.iter (Terms.close_def_subterm accu) def_list;
    let new_def_conditions = Terms.setminus_binderref (!accu) already_defined in
    let new_def_conditions_to_rename = List.filter (fun (b,l) -> 
      List.exists (fun (source_vars, _) -> 
	List.memq b source_vars) source_to_target_list) new_def_conditions 
    in
    match new_def_conditions_to_rename with
      [] -> 
	(* The branch should be left as it is *)
	branches_to_leave_unchanged := branch :: (!branches_to_leave_unchanged)
    | x ->
        (* The branch should be merged with other branches of that find *)
	branches_to_merge := (x, branch) :: (!branches_to_merge)
					      ) l0;
  let l0 = 
    if (!branches_to_merge) == [] then 
      (* Ok, done, just rename as below *)
      l0
    else
      begin
        (*
	print_string "Branches to merge:\n";
	List.iter (function new_def,(bl, def_list, t, p) ->
	  print_string "new_def: ";
	  Display.display_def_list new_def;
	  print_string " find ";
	  Display.display_list (fun (b,b') -> 
	    Display.display_binder b; print_string " = "; Display.display_repl_index b') bl;
	  print_string " suchthat defined(";
	  Display.display_def_list def_list;
	  print_string ") && ";
	  Display.display_term t;
	  print_string " then\n";
	  proc_display p
	    ) (!branches_to_merge);
	*)
	try
	  let branches_to_merge = !branches_to_merge in
	  
	  (* choose one of branches_to_merge as target branch (the one that 
	     uses target_var as new_def_conditions_to_rename, if any; otherwise
	     just take one branch at random) *)
	  let (target_new_def, ((target_bl, target_def_list, target_t, target_p) as target_branch)) =
	    try
	      List.find (fun (new_def,_) -> 
		List.exists (fun (b,_) -> 
		  List.exists (fun (_, target_var) -> b == target_var) source_to_target_list
		    ) new_def) branches_to_merge
	    with Not_found ->
              List.hd branches_to_merge
          in
          (*
	    The candidate branches are obtained by renaming target_b[target_l] to
	    b[target_l] for each b in source_vars. We should check that the branches
	    of branches_to_merge are equivalent to those. If this is true, we
	    can replace them with target_branch after renaming all elements of
	    source_vars to target_var. 
	    
	    - Check that the new_def_conditions_to_rename of these
	    branches consist of (b,l) for b that belong to the same
	    "source_vars" branch in the same branch and to distinct
	    "source_vars" branches in distinct branches.  *)
	  let source_vars_by_branches = 
	    swap_rows_columns (List.map fst source_to_target_list)
	  in
	  let (target_b0, target_l) = List.hd target_new_def in
	  let target_sv_brl =
	    List.find (fun bl -> List.memq target_b0 bl) source_vars_by_branches
	  in
	  let remaining_source_vars_by_branches = ref source_vars_by_branches in
	  let branches_to_merge =
	    List.map (fun (new_def, branch) ->
	      let (b0,_) = List.hd new_def in
	      let rec find_b0 seen = function
		  [] -> 
                    (* b0 not found: b0 belongs to a branch that was already found before,
		       so two branches use a variable that belongs to the same "source_vars" branch *) 
		    raise Failed
		| (sv_brl::r) ->
		    if List.memq b0 sv_brl then
		      begin
		        (* b0 found in sv_brl -> all other vars of new_def should also be
			   in sv_brl *)
			List.iter (fun (b,_) -> if not (List.memq b sv_brl) then raise Failed) new_def;
			remaining_source_vars_by_branches := List.rev_append seen r;
			sv_brl
		      end
		    else
		      find_b0 (sv_brl::seen) r
	      in
	      (find_b0 [] (!remaining_source_vars_by_branches), new_def, branch)
		) branches_to_merge
	  in
          (*
	    - Rename all bl of these branches to the bl of the target branch.
	    *)
	  let branches_to_merge_remain = 
	    List.filter (function _,new_def,_ -> new_def != target_new_def) branches_to_merge 
	  in
          let branches_to_merge_remain' = List.map (function sv_brl,new_def,(bl, def_list, t, p) ->
	    if needed_vars (List.map fst bl) then 
	      raise Failed;
	    if List.length bl != List.length target_bl then
	      raise Failed;
	    (* TO DO Instead of failing when the variables do not have
	       corresponding types, we could try to reorder them so that
	       they have matching types, or even to satisfy the
	       constraint that l = target_l below. However, it seems
	       difficult to guarantee that the right order will always be
	       found if there is one, since these criteria do not provide 
	       a unique order. *)
	    let subst_cond_source = List.map snd bl in
	    let subst_cond_target = List.map (fun (_,b) -> Terms.term_from_repl_index b) target_bl in
	    let subst_proc = List.map2 (fun (b,_) (b',_) -> 
	      if b.btype != b'.btype then raise Failed;
	      (b, Terms.term_from_binder b')) bl target_bl in
	    sv_brl, List.map (fun (b,l) -> (b, List.map (Terms.subst subst_cond_source subst_cond_target) l)) new_def,
	    (target_bl, Terms.subst_def_list subst_cond_source subst_cond_target def_list, 
	     Terms.subst subst_cond_source subst_cond_target t, proc_subst subst_proc p)
	      ) branches_to_merge_remain
	  in
          (*
	    - Check that the new_def_conditions_to_rename of these branches
	    consist of (b,l) for the same l (modulo known equalities)
	    *)
	  let (true_facts,pps,def_vars,history) = Facts.get_facts_at pp in
	  let simp_facts = simplif_add_list ([],[],[]) true_facts in
	  List.iter (fun (b,l) ->
	    if not (Terms.equal_lists (equal (equal_find_cond None) simp_facts) l target_l) then
	      raise Failed
		) (List.tl target_new_def);
	  List.iter (function _,new_def,_ -> 
	    List.iter (fun (b,l) ->
	      if not (Terms.equal_lists (equal (equal_find_cond None) simp_facts) l target_l) then
		raise Failed
		  ) new_def
	      ) branches_to_merge_remain';
          (*
	    - If not all branches of source_vars appear as new_def_conditions_to_rename,
	    check that the remaining branches are not needed, i.e.
	    check that 
	         let def_list' be obtained by renaming target_b[target_l] to b[target_l] 
                 in the "def_list" of target_branch (use Terms.copy_binder (Terms.Rename(target_l, target_b, b)))
	         b[target_l] cannot be defined when def_list' is defined
	    where target_b[target_l] is an element of target_new_def and b is the variable
	    corresponding to target_b in the missing branch (i.e. b = assq2 target_sv_brl sv_brl target_b).
	    *)
          List.iter (fun sv_brl ->
            (* sv_brl is a missing branch *)
	    let def_list' = List.map (apply_list Terms.copy_binder target_new_def target_sv_brl sv_brl) target_def_list in
	    let accu = ref [] in
	    List.iter (Terms.close_def_subterm accu) def_list';
	    try
	      let (facts, _, _) = Facts.facts_from_defined pps def_vars history def_list' in
	      let fact_accu = 
		List.fold_left (fun accu br -> 
		  List.fold_left (fun accu' (target_b,target_l) -> 
		    let b = assq2 target_sv_brl sv_brl target_b in 
		    Incompatible.both_def_add_fact accu' br (b,target_l)
		      ) accu target_new_def
		  ) facts (!accu)
	      in
	      let simp_facts' = simplif_add_list simp_facts fact_accu in
	      let t' = apply_list Terms.copy_term target_new_def target_sv_brl sv_brl target_t in
	      let _ = simplif_add simp_facts' t' in
		(* The condition deflist' & t' does not imply a contradiction, I would need
		   a branch "deflist' & t' then ..." to be present in order to be able to 
		   merge the branches, so I raise Failed. *)
	      raise Failed
	    with Contradiction -> ()
		) (!remaining_source_vars_by_branches);

         (*
	     - Check that all branches_to_merge are "equal" modulo known equalities, i.e.
	       for each element of branches_to_merge except the target branch, 
	       rename target_b[target_l] to b[target_l] in target_branch 
               (use Terms.copy_term/binder/oprocess (Terms.Rename(target_l, target_b, b)))
	       where target_b[target_l] is an element of target_new_def and b is the variable
	       corresponding to target_b in the current branch (i.e. b = assq2 target_sv_brl sv_brl target_b). 
	       Check that, for the obtained branch,
	         def_list of branch is defined iff def_list of renamed_target_branch is defined;
	         when they are defined, the condition and process are equal (modulo known equalities)
	   *)
          List.iter (function sv_brl,_,(bl, def_list, t, p) ->
	    (* new_bl = target_bl = bl by the previous renaming *)
	    let new_def_list = List.map (apply_list Terms.copy_binder target_new_def target_sv_brl sv_brl) target_def_list in
	    let new_t = apply_list Terms.copy_term target_new_def target_sv_brl sv_brl target_t in
	    let target_new_def' = Terms.subst_def_list (List.map snd bl) (List.map (fun (b,_) -> Terms.term_from_binder b) bl) target_new_def in
	    let new_p = apply_list proc_rename target_new_def' target_sv_brl sv_brl target_p in
	    
	    begin
	      try
		let (_, new_def_list_implied) = Facts.def_vars_from_defined pps def_vars history new_def_list in
		if not (List.for_all (fun br -> Terms.mem_binderref br new_def_list_implied) def_list) then
		  raise Failed
	      with Contradiction -> ()
	    end;
	    begin
	      try
		let (facts, _, def_list_implied) = Facts.facts_from_defined pps def_vars history def_list in
		if not (List.for_all (fun br -> Terms.mem_binderref br def_list_implied) new_def_list) then
		  raise Failed;
		let simp_facts' = simplif_add_list simp_facts facts in
		if not (equal (equal_find_cond None) simp_facts' t new_t) then
		  raise Failed;
		let simp_facts'' = simplif_add simp_facts' t in
		let simp_facts'' = Terms.subst_simp_facts (List.map snd bl) (List.map (fun (b,_) -> Terms.term_from_binder b) bl) simp_facts'' in
		if not (equal proc_equal simp_facts'' p new_p) then
		  raise Failed
	      with Contradiction -> ()
	    end
	      ) branches_to_merge_remain';
	  
	  has_done_merge := true;
	  let l0' = target_branch :: (!branches_to_leave_unchanged) in
	  (* This transformation may reorder elements in the list of successful
	     branches and indices of find, hence we need to add eps_find. *)
	  let cur_array = 
	    match Incompatible.get_facts pp with
	      Some (cur_array, _, _, _, _, _, _) -> cur_array
	    | None -> Parsing_helper.internal_error "p_facts should have been defined"
	  in
	  Proba.add_proba_find cur_array l0' find_info;
	  l0'
	with Failed ->
	  match br_vars with
	    NoBranchVar -> raise Failed
	  | CreateBranchVar brl | CreateBranchVarAtProc(_,brl) | CreateBranchVarAtTerm(_,brl) ->
	      (* When the merging fails, we can still succeed by keeping each branch, 
		 adding a test defined(bi[l]) for each (b,l) in new_def_conditions_to_rename 
		 where bi is the variable of br_vars that corresponds to the element b of source_vars.
		 Then we rename the branch as other branches (bi will remain) *)
	      (List.map (fun (new_def, (bl, def_list, t, p)) ->
		(bl, (List.map (fun (b,l) -> 
		  let b' = assq2l source_to_target_list brl b in 
		  (b', Terms.lsuffix (List.length b'.args_at_creation) l)) new_def) @ def_list, t, p)
		  ) (!branches_to_merge)) @ (!branches_to_leave_unchanged)
      end
  in
  let p3' = proc_merge rename_instr p3 in
  let l0' = List.map (fun (bl, def_list, t, p) ->
    let bl' = List.map (fun (b,b') -> (rename_var rename_instr b, b')) bl in
    let def_list' = List.map (fun (b,l) -> (rename_var rename_instr b, 
					    List.map (merge_term rename_instr) l)) def_list in
    let p' = proc_merge rename_instr p in
    let t' = merge_find_cond rename_instr t in
    (bl', def_list', t', List.fold_left (proc_add_def_var rename_instr) p' (List.map fst bl))
      ) l0 
  in
  (l0',p3')
    
let rec merge_find_cond rename_instr t =
  let t' = 
  match t.t_desc with
    ResE(b,p) ->
      Terms.build_term t (ResE(rename_var rename_instr b, 
				add_def_var_find_cond rename_instr (merge_find_cond rename_instr p) b))
  | EventAbortE f ->
      Terms.build_term t (EventAbortE f)
  | EventE _ ->
      Parsing_helper.internal_error "events should not occur in find conditions in merge_find_cond"
  | GetE _ | InsertE _ ->
      Parsing_helper.internal_error "Get/Insert should not appear in Transf_merge.merge_find_cond"
  | TestE(t1,t2,t3) ->
      let t1' = merge_term rename_instr t1 in
      let t2' = merge_find_cond rename_instr t2 in
      let t3' = merge_find_cond rename_instr t3 in
      Terms.build_term t (TestE(t1',t2',t3'))
  | LetE(pat,t1,t2,topt) ->
      let pat' = merge_pat rename_instr pat in
      let t1' = merge_term rename_instr t1 in      
      let t2' = merge_find_cond rename_instr t2 in
      let topt' = 
	match topt with
	  None -> None
	| Some t3 -> Some (merge_find_cond rename_instr t3)
      in
      let pat_vars = Terms.vars_from_pat [] pat in
      Terms.build_term t (LetE(pat',t1', List.fold_left (add_def_var_find_cond rename_instr) t2' pat_vars,topt'))
  | FindE(l0,t3, find_info) ->
      begin
	try
	  let (l0', t3') = merge_find_branches Display.display_term 
	      Terms.subst3 Terms.copy_term (equal_find_cond None)
	      merge_find_cond add_def_var_find_cond merge_find_cond (DTerm t) rename_instr l0 t3 find_info
	  in
	  Terms.build_term t (FindE(l0',t3',find_info))
	with Contradiction ->
	  (* When there is a contradiction here, the Find is in fact unreachable *)
	  t3
      end
  | Var _ | FunApp _ | ReplIndex _ -> 
      merge_term rename_instr t 
  in
  let (_, br_vars) = rename_instr in
  match br_vars with
    CreateBranchVarAtTerm(tl,bl) ->
      begin
	try
	  let b = assq2 tl bl t in
	  Terms.build_term t (LetE(PatVar b, Stringmap.cst_for_type b.btype, t', None))
	with Not_found ->
	  t'
      end
  | _ -> t'


and merge_pat rename_instr = function
    PatVar b -> PatVar (rename_var rename_instr b)
  | PatTuple(f,l) -> PatTuple(f, List.map (merge_pat rename_instr) l)
  | PatEqual t -> PatEqual (merge_term rename_instr t)

let rec merge_i rename_instr p =
  let p_desc' =
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) ->
      Par(merge_i rename_instr p1,
	  merge_i rename_instr p2)
  | Repl(b,p) ->
      Repl(b, merge_i rename_instr p)
  | Input((c,tl),pat, p) ->
      let tl' = List.map (merge_term rename_instr) tl in 
      let pat' = merge_pat rename_instr pat in
      let p' = merge_o rename_instr p in
      let pat_vars = Terms.vars_from_pat [] pat in
      let p'' = List.fold_left (add_def_var_proc rename_instr) p' pat_vars in
      Input((c,tl'),pat',p'')
  in
  Terms.iproc_from_desc_loc p p_desc'

and merge_o rename_instr p =
  let p_desc' =
    match p.p_desc with
      Yield -> Yield
    | EventAbort f -> EventAbort f
    | Restr(b,p) ->
	Restr(rename_var rename_instr b, 
	      add_def_var_proc rename_instr (merge_o rename_instr p) b)
    | Test(t,p1,p2) ->
	let t' = merge_term rename_instr t in
	let p1' = merge_o rename_instr p1 in
	let p2' = merge_o rename_instr p2 in
	Test(t',p1',p2')
    | EventP(t,p) ->
	let t' = merge_term rename_instr t in
	let p' = merge_o rename_instr p in
	EventP(t',p')
    | Let(pat,t,p1,p2) ->
	let pat' = merge_pat rename_instr pat in
	let t' = merge_term rename_instr t in      
	let p1' = merge_o rename_instr p1 in
	let p2' = merge_o rename_instr p2 in
	let pat_vars = Terms.vars_from_pat [] pat in
	Let(pat',t', List.fold_left (add_def_var_proc rename_instr) p1' pat_vars,p2')
    | Find(l0,p3,find_info) ->
	begin
	  try
	    let (l0', p3') = merge_find_branches (Display.display_oprocess "  ") 
		Terms.subst_oprocess3 Terms.copy_oprocess (equal_oprocess None)
		merge_o add_def_var_proc merge_find_cond (DProcess p) rename_instr l0 p3 find_info
	    in
	    Find(l0',p3',find_info)
	  with Contradiction ->
	    (* When there is a contradiction here, the Find is in fact unreachable *)
	    Yield
	end
    | Output((c,tl),t,p) ->
	let tl' = List.map (merge_term rename_instr) tl in 
	let t' = merge_term rename_instr t in
	let p' = merge_i rename_instr p in
	Output((c,tl'),t',p')
    | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"
  in
  let p' = Terms.oproc_from_desc_loc p p_desc' in
  let (_, br_vars) = rename_instr in
  match br_vars with
    CreateBranchVarAtProc(pl,bl) ->
      begin
	try
	  let b = assq2 pl bl p in
	  Terms.oproc_from_desc (Let(PatVar b, Stringmap.cst_for_type b.btype, p', Terms.oproc_from_desc Yield))
	with Not_found ->
	  p'
      end
  | _ -> p'

let is_def_before (b1,_) (b,_) =
  match b.def with
    [n] -> List.memq b1 (Terms.add_def_vars_node [] n)
  | _ -> Parsing_helper.internal_error "Variable should have exactly one definition in Mergebranches.is_def_before"

let check_distinct_branch (b,ext) (b', ext') =
  try 
    ignore (Incompatible.incompatible_suffix_length_var_var b b')
  with Not_found -> 
    raise(Error("For merging arrays, variable " ^
		(Display.binder_to_string b) ^ 
		" should not be defined for the same indices as " ^ 
		(Display.binder_to_string b'), ext))

(*
merge_arrays merges arrays contained in bll. bll is a list of list of variables, say
bll = [[b11, ..., b1n],[b21, ..., b2n], ..., [bk1, ..., bkn]]
(Each list must contain the same number of variables; this MUST be checked before
calling merge_arrays.)

- each list [bi1,...,bin] corresponds to variables to merge together, they
are merged to bi1. Heuristic: the chances of success are probably higher if
bi1 comes from the "else" branch; indeed, the code of the various branches
is merged towards the code of the branch that contains bi1, and the code of 
the "else" branch is more generic because other branches can take advantage
of the tested conditions to use a different code.

- the variables bij for all i at the same position j in the various lists 
are expected to belong to the same branch. bij for i > 1 should preferably
be defined under the definition of b1j; this allows the algorithm to introduce
a new variable b'j defined when b1j is defined, and to use defined(b'j) to test
whether one is in branch j.

merge_arrays has several modes of operation, selected by the argument "mode":
- one in which br_vars are never introduced (MNoBranchVar)
- one in which br_vars may be introduced by the transformation at the point where
the first variable of each branch b1j is defined, if bij for i > 1 is 
defined under b1j (MCreateBranchVar)
- one in which br_vars are introduced at a program point specified in argument
(MCreateBranchVarAtProc / MCreateBranchVarAtTerm). The caller MUST make sure
bij for all i is defined under the j-th program point pj, and that these
program points cannot be executed for the same value of the replication indices.
So this mode can be used in advised instructions, but not for instructions
given by the user.

Note: if merge_arrays introduces new variables b'j to distinguish branches, and
later we could merge the branches that were still distinguished, we can
do that by calling merge_arrays again with argument the b'j.  
*)

let merge_arrays bll mode g =
  if not g.expanded then
    begin
      print_string "Does not support non-expanded games. ";
      (g,[],[])
    end
  else
    begin
  let g_proc = Terms.get_process g in
  whole_game := g;
  Array_ref.array_ref_process g_proc;
  Improved_def.improved_def_game None true g;
  Depanal.reset [] g;
  let old_merge_arrays = !Settings.merge_arrays in
  Settings.merge_arrays := false;
  has_done_merge := false;
  let cleanup() =
    Array_ref.cleanup_array_ref();
    Improved_def.empty_improved_def_game true g;
    Settings.merge_arrays := old_merge_arrays;
    whole_game := Terms.empty_game
  in
  begin
    try 
      List.iter (fun bl ->
	match bl with
	  [] -> Parsing_helper.internal_error "List of binder to merge should not be empty"
	| ((b1,ext1)::br) ->
	    List.iter (fun (b,ext) -> 
	      if b.btype != b1.btype then
		raise(Error("For merging arrays, variable " ^
			    (Display.binder_to_string b) ^ 
			    " should have the same type as " ^
			    (Display.binder_to_string b1), ext));
	      if not (Terms.equal_lists (==) b.args_at_creation b1.args_at_creation) then
		raise(Error("For merging arrays, variable " ^
			    (Display.binder_to_string b) ^ 
			    " should have the same indices as " ^
			    (Display.binder_to_string b1), ext))
		  ) br;
	    List.iter (fun (b, ext) -> 
	      if Settings.occurs_in_queries b (!whole_game).current_queries then
		raise(Error("For merging arrays, variable " ^
			    (Display.binder_to_string b) ^ 
			    " should not occur in queries", ext));
	      if b.count_def > 1 then
		raise(Error("For merging arrays, variable " ^
			    (Display.binder_to_string b) ^ 
			    " should have a single definition", ext));
	      if b.count_def = 0 then
		raise(Error("Variable " ^ (Display.binder_to_string b) ^ 
			    " should be defined", ext))
		  ) bl;
	    ) bll
    with (Error(mess, extent)) ->
      cleanup();
      raise (Error(mess, extent))
  end;
  let bll_br = swap_rows_columns bll in
  let rec check_pairwise_distinct_branches = function
      [] -> ()
    | bl::r ->
	check_pairwise_distinct_branches r;
	List.iter (fun b -> 
	  List.iter (List.iter (check_distinct_branch b)) r
	    ) bl
  in
  check_pairwise_distinct_branches bll_br;
  match bll with
    [] -> Parsing_helper.internal_error "List of list of binders to merge should not be empty"
  | bl1::blr ->
      let branch_vars =
	match mode with
	  MNoBranchVar -> NoBranchVar
	| MCreateBranchVar ->
	    if List.for_all (fun bl -> 
	      List.for_all2 is_def_before bl1 bl
		) blr then
	      CreateBranchVar (List.map (fun (b,_) -> Terms.new_binder b) bl1)
	    else
	      NoBranchVar
	| MCreateBranchVarAtProc(pl, cur_array) ->
	    CreateBranchVarAtProc(pl, List.map (fun (b,_) -> 
	      Terms.create_binder "br" b.btype cur_array) bl1)
	| MCreateBranchVarAtTerm(tl, cur_array) ->
	    CreateBranchVarAtTerm(tl, List.map (fun (b,_) -> 
	      Terms.create_binder "br" b.btype cur_array) bl1)
      in
      try
	let bll_no_ext = List.map (List.map fst) bll in
	let p' = merge_i (List.map (fun bl -> bl, List.hd bl) bll_no_ext, branch_vars) g_proc in
	(* If the variables have array references only at defined conditions,
	   and no real merge has been done, the transformation is useless: 
	   I would just use different variables to distinguish the branches. 
	   So in this case, I cancel the transformation. *)
	if (!has_done_merge) || (List.exists (fun bl ->
	  List.exists (fun (b,_) -> b.array_ref) bl
	    ) bll) then
	  begin
	    Settings.changed := true;
	    (* Display.display_process p'; *)
	    let proba = Depanal.final_add_proba () in
	    cleanup();
	    (Terms.build_transformed_game p' g, proba, [DMergeArrays(bll,mode)])
	  end
	else
	  begin
	    cleanup();
	    Depanal.final_empty_state();
	    (g, [], [])
	  end
      with 
	Failed ->
	  cleanup();
	  Depanal.final_empty_state();
	  (g, [], [])
      | Error(mess,ext) ->
	  cleanup();
	  Depanal.final_empty_state();
	  raise (Error(mess,ext))
    end
      
(* Merge as many branches of if/let/find as possible.
   Simplify already does a bit of this, but this function is more powerful
1st step: store the merges that may be done if array accesses are removed
2nd step: iterate, removing merges that cannot be done because the desired
array accesses cannot be removed
3rd step: 
   if some merges can be done, do them
   if some merges can be done and some have been excluded, iterate
   if no merges can be done, advise MergeBranches for the excluded merges.
 *)

(*
A merge is stored as
- the main process/term to merge (if/let/find)
- the list of branches to merge
  (these branches must be in the same order as the one output by
  form_advise, that is, else branch first, then the other branches in
  the same order as they appear in the process)
- the value of cur_array at that point
- the value of all_branches_var_list
- the list of variables that must have no array accesses for the 
  merge to be possible (!var_no_array_ref)
- a list of pairs (variables, number of array accesses to that 
  variable that can be removed by the merge)
*)

type merge_t =
    MergeFindCond of term * term list
  | MergeProcess of process * process list

type merge_tt = merge_t * repl_index list * (binder * binder) list list * binder list * (binder * int) list
    
let merges_to_do = ref ([] : merge_tt list)

let merges_cannot_be_done = ref ([] : merge_tt list)

let add_advice (merge_type, cur_array, all_branches_var_list, _, _) = 
  (* If I want to give an explicit location for variable creations, 
     I can give only one "MergeArrays" instruction, because after the first one,
     the location will no longer be up-to-date, and I should run it directly
     without giving it as advice, because if I give it as advice, I am not
     sure that it will be immediately executed, so the location may not be
     up-to-date when I execute it.

  let var_loc = 
    match merge_type with
      MergeFindCond(_, tl) -> MCreateBranchVarAtTerm(tl, cur_array)
    | MergeProcess(_,pl) -> MCreateBranchVarAtProc(pl, cur_array)
  in

     Furthermore, the advice is not always good! (r_362,r_404 in EKE)
     (when I advise MergeArrays in mode MCreateBranchVar).

     To avoid the risk of giving bad advice, I choose to advise
     MergeArrays in mode "MNoBranchVar", so that MergeArrays succeeds perhaps
     less often, but when MergeArrays succeeds, it has really simplified the game.
  *)
  if not (List.for_all (fun l -> l == []) all_branches_var_list) then
    try 
      Settings.advise := Terms.add_eq (MergeArrays(List.rev (form_advise all_branches_var_list), MNoBranchVar)) (!Settings.advise)
    with CannotFormAdvice -> 
      ()


(* First step *) 

let get_curarray_suffix cur_array curarray_suffix i =
  if List.memq i (!curarray_suffix) then () else
  let rec suffix_rec = function
      [] -> Parsing_helper.internal_error "Replication index not found in curarray"
    | (i'::l) as l' -> if i == i' then l' else suffix_rec l
  in
  curarray_suffix := suffix_rec cur_array

let rec get_curarray_suffix_t cur_array curarray_suffix t =
  match t.t_desc with
    Var(_,l) | FunApp(_,l) ->
      List.iter (get_curarray_suffix_t cur_array curarray_suffix) l
  | ReplIndex i -> get_curarray_suffix cur_array curarray_suffix i
  | EventAbortE _ -> ()
  | EventE _ | GetE _ | InsertE _ -> Parsing_helper.internal_error "EventE, GetE, InsertE should have been expanded"
  | ResE(_,t) -> get_curarray_suffix_t cur_array curarray_suffix t
  | TestE(t1,t2,t3) -> 
      get_curarray_suffix_t cur_array curarray_suffix t1;
      get_curarray_suffix_t cur_array curarray_suffix t2;
      get_curarray_suffix_t cur_array curarray_suffix t3
  | LetE(pat,t1,t2,t3opt) -> 
      get_curarray_suffix_pat cur_array curarray_suffix pat;
      get_curarray_suffix_t cur_array curarray_suffix t1;
      get_curarray_suffix_t cur_array curarray_suffix t2;
      (match t3opt with
	Some t3 -> get_curarray_suffix_t cur_array curarray_suffix t3
      |	None -> ())
  | FindE _ -> curarray_suffix := cur_array (* For simplicity *)

and get_curarray_suffix_pat cur_array curarray_suffix = function
    PatVar _ -> ()
  | PatTuple(_,l) -> List.iter (get_curarray_suffix_pat cur_array curarray_suffix) l
  | PatEqual t -> get_curarray_suffix_t cur_array curarray_suffix t

let get_curarray_suffix_term cur_array t =
  let curarray_suffix = ref [] in
  get_curarray_suffix_t cur_array curarray_suffix t;
  Some (!curarray_suffix)

let get_curarray_suffix_pat_term cur_array pat t = 
  let curarray_suffix = ref [] in
  get_curarray_suffix_pat cur_array curarray_suffix pat;
  get_curarray_suffix_t cur_array curarray_suffix t;
  Some (!curarray_suffix)
  
let rec collect_merges_find_cond cur_array t =
  match t.t_desc with
    Var _ | FunApp _ | ReplIndex _ | EventAbortE _ -> ()
  | EventE _ ->
      Parsing_helper.internal_error "events should not occur in find conditions in collect_merges_find_cond"
  | GetE _ | InsertE _ -> 
      Parsing_helper.internal_error "Get/Insert should not appear in Transf_merge.collect_merges_find_cond"
  | ResE(_,t) -> collect_merges_find_cond cur_array t
  | TestE(t1,t2,t3) ->
      begin
	try
	  all_branches_var_list := [];
	  cur_branch_var_list := [];
	  var_no_array_ref := [];
	  let (true_facts,_,_,_) = Facts.get_facts_at (DTerm t) in
	  let simp_facts = Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) true_facts in
	  if equal_store_arrays (equal_find_cond (get_curarray_suffix_term cur_array t1)) simp_facts t2 t3 then
	    begin
	      merges_to_do := (MergeFindCond(t, [t3;t2]), cur_array, !all_branches_var_list, !var_no_array_ref, []) :: (!merges_to_do);
	      var_no_array_ref := [];
	      all_branches_var_list := []
	    end;
	with Contradiction ->
	  (* The current program point is unreachable. I could in fact
	     perform the merge, but the most natural thing to do is to
	     use simplication to remove unreachable code.
	     No need to clean-up, because the contradiction occurs when computing
	     true_facts/simp_facts before storing anything in 
	     all_branches_var_list/cur_branch_var_list/var_no_array_ref.
	     Other contradictions are caught in 
	     equal_store_arrays *)
	  ()
      end;
      collect_merges_find_cond cur_array t2;
      collect_merges_find_cond cur_array t3
  | LetE(pat,t1,t2,topt) ->
      begin
	match topt with
	  None -> collect_merges_find_cond cur_array t2
	| Some t3 ->
	    begin
	      try 
		all_branches_var_list := [];
		cur_branch_var_list := [];
		var_no_array_ref := [];
		let (true_facts,_,_,_) = Facts.get_facts_at (DTerm t) in
		let simp_facts = Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) true_facts in
		let curarray_suffix = get_curarray_suffix_pat_term cur_array pat t in
		if equal_store_arrays (equal_find_cond curarray_suffix) simp_facts t2 t3 then
		  begin
		    merges_to_do := (MergeFindCond(t, [t3;t2]), cur_array, !all_branches_var_list, Terms.vars_from_pat (!var_no_array_ref) pat, []) :: (!merges_to_do);
		    var_no_array_ref := [];
		    all_branches_var_list := []
		  end;
	      with Contradiction ->
		()
	    end;
	    collect_merges_find_cond cur_array t2;
	    collect_merges_find_cond cur_array t3
      end
  | FindE(l0,t3,find_info) -> 
      collect_merges_find_cond cur_array t3;
      let (true_facts,_,_,_) = Facts.get_facts_at (DTerm t) in
      let simp_facts = Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) true_facts in
      if Terms.is_unique_no_abort (Some(!whole_game)) l0 find_info then
	begin
	  try
	    List.iter (fun ((bl, def_list, t1, t2) as br) ->
	      all_branches_var_list := [];
	      cur_branch_var_list := [];
	      var_no_array_ref := [];
	      let r = can_merge_one_branch_store_arrays (equal_find_cond (Some cur_array)) t.t_facts simp_facts br t3 in
	      if r then
		merges_to_do := (MergeFindCond(t, [t3;t2]), 
				 cur_array, !all_branches_var_list, !var_no_array_ref, 
				 List.map (fun b -> (b, b.count_exclude_array_ref)) (!Array_ref.all_vars_exclude))
		   :: (!merges_to_do);
	      var_no_array_ref := [];
	      all_branches_var_list := [];
	      Array_ref.cleanup_exclude_array_ref();
	      collect_merges_find_cond cur_array t2;
	      if not r then
		collect_merges_find_cond ((List.map snd bl) @ cur_array) t1
		  ) l0
	  with Contradiction ->
	    ()
	end
      else if Terms.is_not_unique_to_prove find_info then
	begin
	  try
	    all_branches_var_list := [];
	    cur_branch_var_list := [];
	    var_no_array_ref := [];
	    let r = can_merge_all_branches_store_arrays (equal_find_cond (Some cur_array)) t.t_facts simp_facts l0 t3 in
	    if r then
	      merges_to_do := (MergeFindCond(t, t3 :: List.map (fun (_,_,_,t2) -> t2) l0), 
			       cur_array, !all_branches_var_list, !var_no_array_ref, 
			       List.map (fun b -> (b, b.count_exclude_array_ref)) (!Array_ref.all_vars_exclude))
		 :: (!merges_to_do);
	    var_no_array_ref := [];
	    all_branches_var_list := [];
	    Array_ref.cleanup_exclude_array_ref();
	    List.iter (fun (_,_,_,t2) -> collect_merges_find_cond cur_array t2) l0;
	    if not r then
	      List.iter (fun (bl,_,t1,_) -> collect_merges_find_cond ((List.map snd bl) @ cur_array) t1) l0
	  with Contradiction ->
	    ()
	end
	    
let rec collect_merges_i cur_array p =
  match p.i_desc with
    Nil -> ()
  | Par(p1,p2) ->
      collect_merges_i cur_array p1;
      collect_merges_i cur_array p2
  | Repl(b,p) ->
      collect_merges_i (b::cur_array) p
  | Input(_,_, p) ->
      collect_merges_o cur_array p
    
and collect_merges_o cur_array p =
  match p.p_desc with
    Yield | EventAbort _ -> ()
  | Restr(b,p) ->
      collect_merges_o cur_array p
  | EventP(t,p) ->
      collect_merges_o cur_array p
  | Test(t,p1,p2) ->
      begin
	try
	  all_branches_var_list := [];
	  cur_branch_var_list := [];
	  var_no_array_ref := [];
	  let (true_facts,_,_,_) = Facts.get_facts_at (DProcess p) in
	  let simp_facts = Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) true_facts in
	  if equal_store_arrays (equal_oprocess (get_curarray_suffix_term cur_array t)) simp_facts p1 p2 then
	    begin
	      merges_to_do := (MergeProcess(p, [p2;p1]), cur_array, !all_branches_var_list, !var_no_array_ref, []) :: (!merges_to_do);
	      var_no_array_ref := [];
	      all_branches_var_list := []
	    end;
	with Contradiction ->
	  ()
      end;
      collect_merges_o cur_array p1;
      collect_merges_o cur_array p2
  | Let(pat,t,p1,p2) ->
      begin
	try
	  all_branches_var_list := [];
	  cur_branch_var_list := [];
	  var_no_array_ref := [];
	  let (true_facts,_,_,_) = Facts.get_facts_at (DProcess p) in
	  let simp_facts = Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) true_facts in
	  let curarray_suffix = get_curarray_suffix_pat_term cur_array pat t in
	  if equal_store_arrays (equal_oprocess curarray_suffix) simp_facts p1 p2 then
	    begin
	      merges_to_do := (MergeProcess(p, [p2;p1]), cur_array, !all_branches_var_list, Terms.vars_from_pat (!var_no_array_ref) pat, []) :: (!merges_to_do);
	      var_no_array_ref := [];
	      all_branches_var_list := []
	    end;
	with Contradiction ->
	  ()
      end;
      collect_merges_o cur_array p1;
      collect_merges_o cur_array p2
  | Find(l0,p3,find_info) ->
      collect_merges_o cur_array p3;
      let (true_facts,_,_,_) = Facts.get_facts_at (DProcess p) in
      let simp_facts = Facts.simplif_add_list Facts.no_dependency_anal ([],[],[]) true_facts in
      if Terms.is_unique_no_abort (Some(!whole_game)) l0 find_info then
	begin
	  try
	    List.iter (fun ((bl, def_list, t1, p2) as br) ->
	      all_branches_var_list := [];
	      cur_branch_var_list := [];
	      var_no_array_ref := [];
	      let r = can_merge_one_branch_store_arrays (equal_oprocess (Some cur_array)) p.p_facts simp_facts br p3 in
	      if r then
	      merges_to_do := (MergeProcess(p, [p3;p2]), 
			       cur_array, !all_branches_var_list, !var_no_array_ref, 
			       List.map (fun b -> (b, b.count_exclude_array_ref)) (!Array_ref.all_vars_exclude))
		 :: (!merges_to_do);
	      var_no_array_ref := [];
	      all_branches_var_list := [];
	      Array_ref.cleanup_exclude_array_ref();
	      collect_merges_o cur_array p2;
	      if not r then
		collect_merges_find_cond ((List.map snd bl) @ cur_array) t1
		  ) l0
	  with Contradiction -> 
	    ()
	end
      else if Terms.is_not_unique_to_prove find_info then
	begin
	  try 
	    all_branches_var_list := [];
	    cur_branch_var_list := [];
	    var_no_array_ref := [];
	    let r = can_merge_all_branches_store_arrays (equal_oprocess (Some cur_array)) p.p_facts simp_facts l0 p3 in
	    if r then
	      merges_to_do := (MergeProcess(p, p3 :: List.map (fun (_,_,_,p2) -> p2) l0), 
			       cur_array, !all_branches_var_list, !var_no_array_ref, 
			       List.map (fun b -> (b, b.count_exclude_array_ref)) (!Array_ref.all_vars_exclude))
		 :: (!merges_to_do);
	    var_no_array_ref := [];
	    all_branches_var_list := [];
	    Array_ref.cleanup_exclude_array_ref();
	    List.iter (fun (_,_,_,p2) -> collect_merges_o cur_array p2) l0;
	    if not r then
	      List.iter (fun (bl,_,t1,_) -> collect_merges_find_cond ((List.map snd bl) @ cur_array) t1) l0
	  with Contradiction ->
	    ()
	end
  | Output(_,_,p) ->
      collect_merges_i cur_array p
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

(* Second step *)

let rec remove_impossible_merges() =
  Array_ref.all_vars_exclude := [];
  List.iter (fun (_,_,_,_,l) ->
    List.iter (fun (b,n) -> 
      b.count_exclude_array_ref <- b.count_exclude_array_ref + n;
      Array_ref.all_vars_exclude := b :: (!Array_ref.all_vars_exclude)
				       ) l
      ) (!merges_to_do);
  let need_to_iterate = ref false in
  merges_to_do := List.filter (fun ((_,_,_,l,_) as merge) ->
    let r = List.exists has_array_ref l in
    if r then
      begin
	need_to_iterate := true;
	merges_cannot_be_done := merge :: (!merges_cannot_be_done)
      end;
    not r) (!merges_to_do);
  Array_ref.cleanup_exclude_array_ref();
  if !need_to_iterate then
    remove_impossible_merges()



(* Third step *)

let rec do_merges_find_cond t =
  match t.t_desc with
    Var _ | FunApp _ | ReplIndex _ | EventAbortE _ -> t
  | EventE _ ->
      Parsing_helper.internal_error "events should not occur in find conditions in collect_merges_find_cond"
  | GetE _ | InsertE _ -> 
      Parsing_helper.internal_error "Get/Insert should not appear in Transf_merge.collect_merges_find_cond"
  | ResE(b,t1) ->
      let t1' = do_merges_find_cond t1 in
      Terms.build_term t (ResE(b,t1'))
  | TestE(t1,t2,t3) ->
      if List.exists (function
	  (MergeFindCond(t',_),_,_,_,_) -> t' == t
	| _ -> false) (!merges_to_do)
      then
	(* Merge the test *)
	do_merges_find_cond t3
      else
	let t2' = do_merges_find_cond t2 in
	let t3' = do_merges_find_cond t3 in
	Terms.build_term t (TestE(t1,t2',t3'))
  | LetE(pat,t1,t2,topt) ->
      begin
	match topt with
	  None ->
	    let t2' = do_merges_find_cond t2 in
	    Terms.build_term t (LetE(pat,t1,t2',None))
	| Some t3 ->
	    if List.exists (function
		(MergeFindCond(t',_),_,_,_,_) -> t' == t
	      | _ -> false) (!merges_to_do)
	    then
	      (* Merge the let *)
	      do_merges_find_cond t3
	    else
	      let t2' = do_merges_find_cond t2 in
	      let t3' = do_merges_find_cond t3 in
	      Terms.build_term t (LetE(pat,t1,t2',Some t3'))
      end
  | FindE(l0,t3, find_info) ->
      let t3' = do_merges_find_cond t3 in
      if List.exists (function
	  (MergeFindCond(t',l),_,_,_,_) -> (t' == t) && (List.length l0 + 1 = List.length l)
	| _ -> false) (!merges_to_do)
      then
	(* Merge all branches of the find *)
	t3'
      else
	(* May merge some branches of the find
	   l0' = list with the merged branches removed *)
	let l0' = List.filter (fun (_,_,_,t2) ->
	  not (List.exists (function
	      (MergeFindCond(t',[t3';t2']),_,_,_,_) -> (t' == t) && (t3' == t3) && (t2' == t2)
	    | _ -> false) (!merges_to_do))) l0
	in
	if l0' == [] then
	  t3'
	else
	  let l0'' = List.map (fun (bl, def_list, t1, t2) ->
	    (bl, def_list, do_merges_find_cond t1, do_merges_find_cond t2)) l0' in
	  Terms.build_term t (FindE(l0'',t3',find_info))

let rec do_merges_i p =
  let p_desc' =
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) ->
      Par(do_merges_i p1,
	  do_merges_i p2)
  | Repl(b,p) ->
      Repl(b, do_merges_i p)
  | Input(ch,pat, p) ->
      Input(ch,pat,do_merges_o p)
  in
  Terms.iproc_from_desc_loc p p_desc'

and do_merges_o p =
  match p.p_desc with
    Yield | EventAbort _ -> p
  | Restr(b,p1) ->    
      Terms.oproc_from_desc_loc p (Restr(b, do_merges_o p1))
  | EventP(t,p1) ->
      Terms.oproc_from_desc_loc p (EventP(t, do_merges_o p1))
  | Test(t,p1,p2) ->
      if List.exists (function
	  (MergeProcess(p',_),_,_,_,_) -> p' == p
	| _ -> false) (!merges_to_do)
      then
	(* Merge the test *)
	do_merges_o p2
      else
	let p1' = do_merges_o p1 in
	let p2' = do_merges_o p2 in
	Terms.oproc_from_desc_loc p (Test(t,p1',p2'))
  | Let(pat,t,p1,p2) ->
      if List.exists (function
	  (MergeProcess(p',_),_,_,_,_) -> p' == p
	| _ -> false) (!merges_to_do)
      then
	(* Merge the let *)
	do_merges_o p2
      else
	let p1' = do_merges_o p1 in
	let p2' = do_merges_o p2 in
	Terms.oproc_from_desc_loc p (Let(pat, t,p1',p2'))
  | Find(l0,p3,find_info) ->
      let p3' = do_merges_o p3 in
      if List.exists (function
	  (MergeProcess(p',l),_,_,_,_) -> (p' == p) && (List.length l0 + 1 = List.length l)
	| _ -> false) (!merges_to_do)
      then
	(* Merge all branches of the find *)
	p3'
      else
	(* May merge some branches of the find
	   l0' = list with the merged branches removed *)
	let l0' = List.filter (fun (_,_,_,p2) ->
	  not (List.exists (function
	      (MergeProcess(p',[p3';p2']),_,_,_,_) -> (p' == p) && (p3' == p3) && (p2' == p2)
	    | _ -> false) (!merges_to_do))) l0
	in
	if l0' == [] then
	  p3'
	else
	  let l0'' = List.map (fun (bl, def_list, t1, p2) ->
	    (bl, def_list, do_merges_find_cond t1, do_merges_o p2)) l0' in
	  Terms.oproc_from_desc_loc p (Find(l0'',p3',find_info))
  | Output(ch,t,p1) ->
      Terms.oproc_from_desc_loc p (Output(ch, t, do_merges_i p1))
  | Get _ | Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

let display_merge = function
    (MergeProcess(p,l),_,_,_,_) ->
      print_string "Merging ";
      Display.display_oprocess "" p;
      print_string "Branches ";
      Display.display_list (fun p -> Display.display_oprocess "" p) l;
      print_newline()
  | (MergeFindCond(t,l),_,_,_,_) ->
      print_string "Merging ";
      Display.display_term t;
      print_string "Branches ";
      Display.display_list Display.display_term l;
      print_newline()
      

let merge_branches g =
  if not g.expanded then
    begin
      print_string "Does not support non-expanded games. ";
      (g,[],[])
    end
  else
    begin
      let g_proc = Terms.get_process g in
      whole_game := g;
      Array_ref.array_ref_process g_proc;
      Improved_def.improved_def_game None false g;
      Depanal.reset [] g;
      merges_to_do := [];
      merges_cannot_be_done := [];
      collect_merges_i [] g_proc;
      let result =
	if (!merges_to_do) == [] then
          (* No merge can be done *)
	  (g, [], [])
	else
	  begin
            (* See which merges can be done, if we remove enough array references *)
	    remove_impossible_merges();
            (* List.iter display_merge (!merges_to_do); *)
	    if (!merges_to_do) != [] then
            (* Perform the possible merges *)
	      let p' = do_merges_i g_proc in
	      Settings.changed := true;
        (* TO DO if (!merges_cannot_be_done) != [], I should iterate to get up-to-date advice *)
	      let done_transfos = 
		List.map (function
		    (MergeProcess(p,l),_,_,_,_) -> DMergeBranches(p,l)
		  | (MergeFindCond(t,l),_,_,_,_) -> DMergeBranchesE(t,l)) (!merges_to_do)
	      in
	      merges_to_do := [];
	      merges_cannot_be_done := [];
	      let proba = Depanal.final_add_proba () in
	      (Terms.build_transformed_game p' g, proba, done_transfos)
	    else
	      begin
	        (* No change, but may advise MergeArrays *)
		List.iter add_advice (!merges_cannot_be_done);
		merges_to_do := [];
		merges_cannot_be_done := [];
		Depanal.final_empty_state();
		(g, [], [])
	      end
	  end
      in
      Array_ref.cleanup_array_ref();
      Improved_def.empty_improved_def_game false g;
      whole_game := Terms.empty_game;
      result
    end
      
(**************** Test equality between two independent processes *****************)
(* Used for testing success of the equivalence query *)
    
let collect_good_vars_fullprocess p =
  let ok_vars = ref [] in
  collect_def_vars_process ok_vars p;
  List.map fst (!ok_vars)

let equal_games g1 g2 =
  (* Does not support non-expanded games *)
  if not (g1.expanded && g2.expanded) then (false, []) else
  let g1_proc = Terms.get_process g1 in
  let g2_proc = Terms.get_process g2 in
  whole_game := g1;
  (* We use [simp_facts_id] below since no fact holds at the beginning of the games.
     For this reason, we use no known facts, and the probability [proba] should always be 0 *)
  Array_ref.array_ref_process g1_proc;
  Array_ref.array_ref_process g2_proc;
  Depanal.reset [] g1;
  let r = 
    equal_store_arrays ~show_diff_reason:true (fun p p' ->
        ok_arrays_first_branch := collect_good_vars_fullprocess p;
        ok_arrays_second_branch := collect_good_vars_fullprocess p';
        equal_process ~show_diff_reason:true [] p p') Terms.simp_facts_id g1_proc g2_proc
  in
  let proba = Depanal.final_add_proba () in
  Array_ref.cleanup_array_ref();
  whole_game := Terms.empty_game;
  (r, proba)
