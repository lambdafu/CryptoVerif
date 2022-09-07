open Types

(* Expand term to term. Useful for conditions of find when they cannot be expanded to processes.
   Guarantees the invariant that if/let/find/res terms occur only in
   - conditions of find
   - at [ ] positions in TestE(t,[then],[else]), ResE(b,[...]), LetE(b,t,[in],[else]), 
     FindE((bl,def_list,[cond],[then]) list,[else])

   context = fun term -> C[term]
*)

let local_final_pseudo_expand g_opt t =

  let rec pseudo_expand_term t context =
    let pseudo_expand_term_rec t =
      pseudo_expand_term t context
    in
    match t.t_desc with
      Var(b,l) ->
	pseudo_expand_term_list l
	  (fun li ->
	    context (Terms.build_term t (Var(b,li))))
    | ReplIndex _ -> context t
    (* optimize the expansion of && and ||:
       when the first argument is false (resp. true), 
       I do not need to compute the other one. *)
    | FunApp(f, [t1;t2]) when f == Settings.f_and ->
	pseudo_expand_term t1 (fun t1' ->
          if Terms.is_false t1' && not (Terms.may_abort_counted g_opt t2) then
           (* If [t2] may abort, the following optimization is not sound,
              as [false && event_abort e] aborts. 
	      Similar observation for other calls to [Terms.may_abort_counted] below. *)
            context t1'
          else if Terms.is_true t1' then
            pseudo_expand_term_rec t2
          else
	    pseudo_expand_term t2 (fun t2' ->
              if Terms.is_false t2' && not (Terms.may_abort_counted g_opt t1') then
                context t2'
              else if Terms.is_true t2' then
                context t1'
              else
	        context (Terms.build_term t (FunApp(f,[t1';t2'])))))
    | FunApp(f, [t1;t2]) when f == Settings.f_or ->
	pseudo_expand_term t1 (fun t1' ->
          if Terms.is_true t1' && not (Terms.may_abort_counted g_opt t2) then
            context t1'
          else if Terms.is_false t1' then
            pseudo_expand_term_rec t2
          else
	    pseudo_expand_term t2 (fun t2' ->
              if Terms.is_true t2' && not (Terms.may_abort_counted g_opt t1') then
                context t2'
              else if Terms.is_false t2' then
                context t1'
              else
	        context (Terms.build_term t (FunApp(f,[t1';t2'])))))
    | FunApp(f,l) ->
	pseudo_expand_term_list l
	  (fun li ->
	    context (Terms.build_term t (FunApp(f,li))))
    | TestE(t1,t2,t3) ->
	pseudo_expand_term t1
	  (fun t1i ->
	    let t2' = pseudo_expand_term_rec t2 in
	    let t3' = pseudo_expand_term_rec t3 in
	    Terms.build_term_type (Terms.merge_types t2'.t_type t3'.t_type) (TestE(t1i, t2', t3')))
    | LetE(pat, t1, t2, topt) ->
	pseudo_expand_term t1 (fun t1i ->
	  pseudo_expand_pat pat (fun pati ->
	    let t2' = pseudo_expand_term_rec t2 in
	    let topt', ty =
	      match topt with
	      | None -> None, t2'.t_type
	      | Some t3 ->
		  let t3' = pseudo_expand_term_rec t3 in
		  Some t3', Terms.merge_types t2'.t_type t3'.t_type
	    in
	    Terms.build_term_type ty (LetE(pati, t1i, t2', topt'))))
    | FindE(l0, t3, find_info) ->
	let rec expand_cond_find_list l context =
	  match l with
	    [] -> context []
	  | ((bl, def_list, t1, t2)::restl) ->
                  (* I move something outside a condition of
                     "find" only when bl and def_list are empty.  
                     I could be more precise, I would need to
                     check not only that what I move out does not
                     refer to the indices of "find", but also that it
                     is does not refer to the variables in the
                     "defined" condition---otherwise, some variable
                     accesses may not be defined after the
                     transformation *)
              if bl != [] || def_list != [] || Terms.may_abort t1 then
		expand_cond_find_list restl (fun li ->
		  context ((bl, def_list, pseudo_expand_term t1 (fun t -> t), t2)::li))
	      else
		pseudo_expand_term t1 (fun t1i ->
		  expand_cond_find_list restl (fun li ->
		    context ((bl, def_list, t1i, t2)::li)))
	in
	expand_cond_find_list l0 (fun l1i ->
	  let l0' = List.map (fun (bl, def_list, t1, t2) ->
	    (bl, def_list, t1, pseudo_expand_term_rec t2)) l0 in
	  let t3' = pseudo_expand_term_rec t3 in
	  let rec get_type = function
	      [] -> t3'.t_type
	    | (_,_,_,t2')::rest ->
		Terms.merge_types t2'.t_type (get_type rest)
	  in
	  Terms.build_term_type (get_type l0') (FindE(l0', t3',find_info)))
    | ResE(b, t1) ->
	let t1' = pseudo_expand_term_rec t1 in
	Terms.build_term_type t1'.t_type (ResE(b, t1'))
    | EventAbortE f ->
	Terms.build_term_type t.t_type (EventAbortE f)
    | EventE _ | InsertE _ ->
	Parsing_helper.internal_error "Events and insert should not occur in conditions of find"
    | GetE _ ->
      (* We do not expand GetE, since anyway it will be ignored by [extract_sure] *)
	context t

  and pseudo_expand_term_list l context =
    match l with
      [] -> context []
    | (a::l) -> 
	pseudo_expand_term a (fun a' ->
	  pseudo_expand_term_list l (fun l' ->
	    context (a'::l')))

  and pseudo_expand_pat pat context =
    match pat with
      PatVar b -> context (PatVar b)
    | PatTuple (ft,l) ->
	pseudo_expand_pat_list l (fun li ->
	  context (PatTuple (ft,li)))
    | PatEqual t ->
	pseudo_expand_term t (fun ti ->
	  context (PatEqual ti))

  and pseudo_expand_pat_list l context =
    match l with
      [] -> context []
    | (a::l) -> 
	pseudo_expand_pat a (fun a' ->
	  pseudo_expand_pat_list l (fun l' ->
	    context (a'::l')))
	  
  in
  pseudo_expand_term t (fun t -> t)

(* Extract elsefind facts from a branch of find *)

(* From a term [t], we compute [or_i exists bl_i, defined(l_i) /\ tl_i] 
   that implies [t] represented as the list of [(bl_i, l_i,
   tl_i)], [tl_i] is a list of terms representing a conjonction.

   Then forall bl, not(defined(l) /\ t)
   implies forall bl, not(defined(l)) /\ /\_i forall bl_i, not(defined(l_i)) \/ not(tl_i)
   implies /\_i forall bl, bl_i, not(defined(l,l_i) /\ tl_i) *)


(* [make_or_efl f1 f2] computes [f1] or [f2], assuming [f1] and [f2]
   are of the form above. *)

let implies_ef (bl1,def_list1,tl1) (bl2,def_list2,tl2) =
  (List.length bl1 == List.length bl2) &&
  (List.iter2 (fun b1 b2 ->
    b1.ri_link <- TLink (Terms.term_from_repl_index b2)
	 ) bl1 bl2;
   let def_list1' = Terms.copy_def_list Links_RI def_list1 in
   let tl1' = List.map (Terms.copy_term Links_RI) tl1 in
   List.iter (fun ri -> ri.ri_link <- NoLink) bl1;
   List.for_all (fun br1 -> Terms.mem_binderref br1 def_list2) def_list1' && 
   List.for_all (fun t1 -> List.exists (Terms.equal_terms t1) tl2) tl1')

let make_or_efl f1 f2 =
  if List.length f1 > !Settings.max_efl then f1 else
  if List.length f2 > !Settings.max_efl then f2 else
  let f1_filtered =
    List.filter (fun ef1 ->
        not (List.exists (fun ef2 -> implies_ef ef2 ef1) f2)
      ) f1
  in
  let f2_filtered =
    List.filter (fun ef2 ->
        not (List.exists (fun ef1 -> implies_ef ef1 ef2) f1_filtered)
      ) f2
  in
  List.rev_append f1_filtered f2_filtered

let rec make_or_efl_list = function
    [] -> []
  | [a] -> a
  | a::l -> make_or_efl a (make_or_efl_list l)
                  
(* [make_and_efl f1 f2] computes [f1] and [f2], assuming [f1] and [f2]
   are of the form above. *)

let make_and_ef (bl1,def_list1,tl1) (bl2,def_list2,tl2) =
  (* when indices are common between [bl1] and [bl2], we rename them *)
  let ren_done = ref false in
  let bl1' = List.map (fun b1 ->
    if List.memq b1 bl2 then
      let b1' = Terms.create_repl_index "@ri" b1.ri_type in
      b1.ri_link <- (TLink (Terms.term_from_repl_index b1'));
      ren_done := true;
      b1'
    else
      b1
	) bl1
  in
  let def_list1' =
    if !ren_done then
      Terms.copy_def_list Links_RI def_list1
    else
      def_list1
  in
  let tl1' =
    if !ren_done then
      List.map (Terms.copy_term Links_RI) tl1
    else
      tl1
  in
  if !ren_done then
    List.iter (fun b1 -> b1.ri_link <- NoLink) bl1;
  (bl1' @ bl2, Terms.union_binderref def_list1' def_list2,
   Terms.union Terms.equal_terms tl1' tl2)
                               
let make_and_efl f1 f2 =
  let rec aux accu = function
      [] -> accu
    | (a::l) ->
	if List.length accu > !Settings.max_efl then accu else
	aux (make_or_efl (List.rev_map (make_and_ef a) f1) accu) l
  in
  aux [] f2
  
let rec make_and_efl_list = function
    [] -> [([], [], [])]
  | [a] -> a
  | a::l -> make_and_efl a (make_and_efl_list l)
    
(* [filter_efl var_list f] removes from [f] all references to variables in
   [var_list] *)

let refers_to_fact b (bl, def_list, tl) = 
  Terms.refers_to_def_list b def_list ||
  List.exists (Terms.refers_to b) tl
  
let filter_efl var_list f =
  let not_refers_to_var_list ef =
    not (List.exists (fun b -> refers_to_fact b ef) var_list)
  in
  List.filter not_refers_to_var_list f
    
    
(* From a term [t], [extract_efl_exp t] computes 
   [or_i exists bl_i, defined(l_i) /\ tl_i] that implies [t],
   represented as the list of [(bl_i, l_i, tl_i)], 
   [tl_i] is a list of terms representing a conjonction. 
   Applies when [t] is expanded *)
                    
let rec extract_efl_exp t =
  match t.t_desc with
  | _ when Terms.is_false t ->
     []
  | _ when Terms.is_true t ->
     [([],[],[])]
  | FunApp(f, [t1; t2]) when f == Settings.f_and ->
     make_and_efl (extract_efl_exp t1) (extract_efl_exp t2)
  | FunApp(f, [t1; t2]) when f == Settings.f_or ->
      make_or_efl (extract_efl_exp t1) (extract_efl_exp t2)
  (* TO DO should I simplify [not t] before computing the sure facts,
     to get a more precise result? *)
  | Var _ | FunApp _ | ReplIndex _ ->
     (* Since [t] is expanded, it is a simple term *)
     [([],[],[t])]
  | TestE(t1, t2, t3) ->
     (* Since [t] is expanded, [t1] is a simple term *)
     let f2 = extract_efl_exp t2 in
     let f3 = extract_efl_exp t3 in
     make_or_efl (make_and_efl [([],[],[t1])] f2)
                 (make_and_efl [([],[],[Terms.make_not t1])] f3)
  | FindE(l0,t3,_) ->
      let f3 =
	if List.for_all (fun (bl, def_list, t1, _) ->
	  bl == [] && def_list == [] && Terms.check_simple_term t1) l0 then
	  let else_find_efl =
	    [([],[],List.map (fun (_,_,t1,_) -> Terms.make_not t1) l0)]
	  in
	  make_and_efl else_find_efl (extract_efl_exp t3)
	else
	  (* We overapproximate with false, represented by an empty disjunction *)
	  []
      in
     let f0 =
       make_or_efl_list
         (List.map (fun (bl,def_list,t1,t2) ->
	   let vars = List.map fst bl in
	   let ris = List.map snd bl in
	   let f1 = extract_efl_exp t1 in
           let f2 = filter_efl vars (extract_efl_exp t2) in
           make_and_efl (List.map (fun (bl1, def_list1, t1') ->
	     ris @ bl1, Terms.union_binderref def_list def_list1, t1') f1) f2
             ) l0)
     in
     make_or_efl f0 f3
  | LetE(pat, t1, t2, topt) ->
     begin
       match pat with
       | PatVar b ->
	   (* Assumes there is no array access to [b], which is true
              when [t] is in a condition of find. *)
	   let t2' = Terms.copy_term (OneSubst(b, t1, ref false)) t2 in
	   extract_efl_exp t2'
       | _ ->
	   (* We overapproximate with false, represented by an empty disjunction *)
	   []
     end
  | ResE (b,t) ->
     filter_efl [b] (extract_efl_exp t)
  | EventAbortE _ ->
      (* In case of abortion, the else branch is not taken, like when t = true *)
      [([],[],[])]
  | GetE _ ->
     (* We overapproximate: false ==> t. The empty disjunction is false.

	[get] may appear because this function is called before the first 
	transformation of get/insert into find. Since it is removed 
	quickly, extracting information from [get] is not essential. *)
     []
  | EventE _ | InsertE _ ->
     Parsing_helper.internal_error "extract_efl_exp: event, insert should not occur in conditions of find"

(* Extract both the elsefind facts for when the else branch is taken *)

let rec extract_efl g_opt t =
  match t.t_desc with
  | _ when Terms.is_false t ->
     []
  | _ when Terms.is_true t ->
     [([],[],[])]
  | FunApp(f, [t1; t2]) when f == Settings.f_and ->
      make_and_efl (extract_efl g_opt t1) (extract_efl g_opt t2)
  | FunApp(f, [t1; t2]) when f == Settings.f_or ->
      make_or_efl (extract_efl g_opt t1) (extract_efl g_opt t2)
  | _ ->
      let t' = local_final_pseudo_expand g_opt t in
      extract_efl_exp t'

let final_extract_efl ris def_list efl =
  List.map (fun (bl1, def_list1, t1') ->
    ris @ bl1, Terms.union_binderref def_list def_list1, Terms.make_and_list t1') efl
    
let else_info_from_find_branch g_opt expanded (bl, def_list, t1, _) =
  (* [t1] must be expanded *)
  let ris = List.map snd bl in
  if Terms.check_simple_term t1 then
    [(ris,def_list,t1)]
  else
    if !Settings.max_efl > 0 then
      let extract_fun = if expanded then extract_efl_exp else extract_efl g_opt in
      final_extract_efl ris def_list (extract_fun t1)
    else
      []


let add_else_info_find g_opt expanded l0 =
  List.map (fun br ->
    (br, else_info_from_find_branch g_opt expanded br)
      ) l0

let extract_efl_exp t =
  if !Settings.max_efl > 0 then
    extract_efl_exp t
  else
    []

(* Facts *)
	
type fact_t =
  | FTerm of term
  | FDefined of binderref
  | FElseFind of elsefind_fact

let equal_facts f1 f2 =
  match (f1,f2) with
  | FTerm t1, FTerm t2 -> Terms.equal_terms t1 t2
  | FDefined br1, FDefined br2 -> Terms.equal_binderref br1 br2
  | FElseFind ef1, FElseFind ef2 -> Terms.equal_elsefind_facts ef1 ef2
  | _ -> false

(* We represent sure facts by
   [None] for [false]
   [Some l] for the list of facts [l] *)
	
(* [make_or_sure f1 f2] computes sure facts for [f1] or
   [f2], assuming [f1] and [f2] are sure facts. *)

let make_or_sure f1 f2 =
  match f1, f2 with
  | None, _ -> f2
  | _, None -> f1
  | Some l1, Some l2 ->
      Some (Terms.intersect equal_facts l1 l2)

let rec make_or_sure_list = function
    [] -> None
  | [a] -> a
  | a::l -> make_or_sure a (make_or_sure_list l)
                  
(* [make_and_sure f1 f2] computes sure facts for [f1] and
   [f2], assuming [f1] and [f2] are sure facts. *)

let make_and_sure f1 f2 =
  match f1, f2 with
  | None, _ | _, None -> None
  | Some l1, Some l2 ->
      Some (Terms.union equal_facts l1 l2)
  
let rec make_and_sure_list = function
    [] -> Some []
  | [a] -> a
  | a::l -> make_and_sure a (make_and_sure_list l)
                         
(* [filter_sure var_list f] removes from [f] all references to variables in
   [var_list] *)

let refers_to_fact b = function
  | FTerm t -> Terms.refers_to b t
  | FDefined br -> Terms.refers_to_br b br
  | FElseFind(bl, def_list, t) ->
      (Terms.refers_to_def_list b def_list) ||
      (Terms.refers_to b t)
	
let filter_sure var_list f =
  let not_refers_to_var_list t =
    not (List.exists (fun b -> refers_to_fact b t) var_list)
  in
  match f with
  | None -> None
  | Some l -> Some (List.filter not_refers_to_var_list l)

(* [filter_sure_ri ri_list f] removes from [f] all references to 
   replication indices in [ri_list] *)

let rec refers_to_ri ri0 t =
  (match t.t_desc with
  | ReplIndex ri -> 
      (ri == ri0) ||
      (match ri.ri_link with
	TLink t -> refers_to_ri ri t
      | _ -> false)
  | _ -> false) ||
  (Terms.exists_subterm (refers_to_ri ri0) (refers_to_ri_def_list ri0) (refers_to_ri_pat ri0) t)

and refers_to_ri_br ri0 (_,l) =
  List.exists (refers_to_ri ri0) l

and refers_to_ri_def_list ri0 def_list =
  List.exists (refers_to_ri_br ri0) def_list

and refers_to_ri_pat ri0 pat =
  Terms.exists_subpat (refers_to_ri ri0) (refers_to_ri_pat ri0) pat
      
let refers_to_ri_fact ri0 = function
  | FTerm t -> refers_to_ri ri0 t
  | FDefined br -> refers_to_ri_br ri0 br
  | FElseFind(bl, def_list, t) ->
      (refers_to_ri_def_list ri0 def_list) ||
      (refers_to_ri ri0 t)
	
let filter_sure_ri ri_list f =
  let not_refers_to_ri_list t =
    not (List.exists (fun b -> refers_to_ri_fact b t) ri_list)
  in
  match f with
  | None -> None
  | Some l -> Some (List.filter not_refers_to_ri_list l)

(* We cannot take the negation of the sure facts, because the sure facts are an 
   approximation: t implies the sure facts. If we take the negation,
   the approximation will be in the wrong direction.*)
    
(* [extract_sure_exp g_opt in_find t] derives facts implied by [t]. Applies when [t] is expanded *)
                    
let rec extract_sure_exp g_opt in_find t =
  match t.t_desc with
  | _ when Terms.is_false t ->
     None
  | _ when Terms.is_true t ->
     Some []
  | FunApp(f, [t1; t2]) when f == Settings.f_and ->
     make_and_sure (extract_sure_exp g_opt in_find t1) (extract_sure_exp g_opt in_find t2)
  | FunApp(f, [t1; t2]) when f == Settings.f_or ->
      make_or_sure (extract_sure_exp g_opt in_find t1) (extract_sure_exp g_opt in_find t2)
  (* TO DO should I simplify [not t] before computing the sure facts,
     to get a more precise result? *)
  | Var _ | FunApp _ ->
     (* Since [t] is expanded, it is a simple term *)
     Some [FTerm t]
  | ReplIndex _ -> Some [FTerm t]
  | TestE(t1, t2, t3) ->
     (* Since [t] is expanded, [t1] is a simple term *)
     let f2 = extract_sure_exp g_opt in_find t2 in
     let f3 = extract_sure_exp g_opt in_find t3 in
     make_or_sure (make_and_sure (Some [FTerm t1]) f2)
                 (make_and_sure (Some [FTerm (Terms.make_not t1)]) f3)
  | FindE(l0,t3,_) ->
      let else_find_sure =
	make_and_sure_list 
	  (List.map (function ((bl, def_list, _, _) as br) ->
	    if in_find then
	      let efl = else_info_from_find_branch g_opt true br in
	      Some (List.map (fun (bl, def_list, t) ->
		if bl == [] && def_list == [] then
		  FTerm (Terms.make_not t)
		else
		  FElseFind(bl, def_list, t)) efl)
	    else if bl == [] && def_list == [] then
	      let efl = else_info_from_find_branch g_opt true br in
	      Some (List.map (fun (_, _, t) -> FTerm (Terms.make_not t))
		      (List.filter (fun (bl, def_list, t) ->
			bl == [] && def_list == []) efl))
	    else
	      Some []
	      ) l0)
      in
     let f3 = make_and_sure else_find_sure (extract_sure_exp g_opt in_find t3) in
     let f0 =
       make_or_sure_list
         (List.map (fun (bl,def_list,t1,t2) ->
	   let vars = List.map fst bl in
	   let repl_indices = List.map snd bl in
           let f1 = filter_sure_ri repl_indices (extract_sure_exp g_opt in_find t1) in
           let f2 = filter_sure vars (extract_sure_exp g_opt in_find t2) in
           let accu = ref [] in
	   List.iter (Terms.close_def_subterm accu) def_list;
	   let def_list_subterms = !accu in
           let def_list_sure = filter_sure_ri repl_indices
             (Some (List.map (fun br -> FDefined br) def_list_subterms))
           in
           make_and_sure def_list_sure (make_and_sure f1 f2)
             ) l0)
     in
     make_or_sure f0 f3
  | LetE(pat, t1, t2, topt) ->
      (* Since [t] is expanded, [t1] and [pat] are simple *)
      begin
	match pat with
	| PatVar b when in_find ->
	   (* Assumes there is no array access to [b], which is true
              when [t] is in a condition of find. *)
	   let t2' = Terms.copy_term (OneSubst(b, t1, ref false)) t2 in
	   extract_sure_exp g_opt in_find t2'
	| _ ->
	    let vars = Terms.vars_from_pat [] pat in
	    let assign_sure = filter_sure vars (Some [FTerm (Terms.make_equal (Terms.term_from_pat pat) t1)]) in
	    let f2 = filter_sure vars (extract_sure_exp g_opt in_find t2) in
	    let in_branch_sure = make_and_sure assign_sure f2 in
	    begin
	      match pat with
	      | PatVar b -> in_branch_sure
	      | _ ->
		  match topt with
		    Some t3 ->
		      let f3 = extract_sure_exp g_opt in_find t3 in
		      let else_branch_sure =
			try
			  make_and_sure (Some [FTerm (Terms.make_for_all_diff (Terms.gen_term_from_pat pat) t1)]) f3
			with Terms.NonLinearPattern -> f3
		      in
		      make_or_sure in_branch_sure else_branch_sure
		  | None -> Parsing_helper.internal_error "else branch of let missing"
	    end
      end
  | ResE (b,t) ->
     filter_sure [b] (extract_sure_exp g_opt in_find t)
  | EventAbortE _ ->
     (* We consider that [EventAbort e] implies false.
	In transf_expand.ml and transf_simplify.ml, in case the test may
	abort, we do not remove the branch of find, because evaluating
	the condition is needed for executing [EventAbort e].
	Instead, we replace the [then] branch with empty code 
	(constant for terms, Yield for processes) *)
      None
  | GetE _ ->
      (* [get] may appear because this function is called before the first 
	 transformation of get/insert into find. Since it is removed 
	 quickly, extracting information from [get] is not essential. *)
      Some []
  | EventE(_,t) | InsertE(_,_,t) ->
      if in_find then
	Parsing_helper.internal_error "extract_sure_exp: event, insert should not occur in conditions of find";
      extract_sure_exp g_opt in_find t

(* [extract_sure g_opt in_find t] derives a logical formula in disjunctive
   normal form that is implied by [t] *)

let rec extract_sure g_opt in_find t =
  match t.t_desc with
  | _ when Terms.is_false t ->
     None
  | _ when Terms.is_true t ->
     Some []
  | FunApp(f, [t1; t2]) when f == Settings.f_and ->
     make_and_sure (extract_sure g_opt in_find t1) (extract_sure g_opt in_find t2)
  | FunApp(f, [t1; t2]) when f == Settings.f_or ->
     make_or_sure (extract_sure g_opt in_find t1) (extract_sure g_opt in_find t2)
  | _ ->
      let t' = local_final_pseudo_expand g_opt t in
      extract_sure_exp g_opt in_find t'
      
(* [def_vars_and_facts_from_term g_opt expanded in_find t] extracts a list of defined 
   variables and a list of facts implied by [t]

   [expanded] is true when [t] is for sure already expanded.
   (Otherwise, it will be expanded internally.)

   When [in_find = true], it assumes that [t] is a condition
   of [find]: it collects [elsefind] facts without caring about variables
   defined inside [t]. That's ok because variables defined in conditions
   of [find] never appear in [defined] conditions.
   It also substitutes variables bound by [let] with their value.
   That's ok since there are no array accesses on these variables.
   When [in_find = false], it does not make such assumptions.
   It does not collect [elsefind] facts. (If we wanted to collect them,
   we might have to update them for variables defined above them.) *)

let partition_facts l =
  List.fold_left (fun accu fact ->
    let (facts, def_list, elsefind) = accu in
    match fact with
    | FTerm t -> (t::facts, def_list, elsefind)
    | FDefined br -> (facts, br::def_list, elsefind)
    | FElseFind ef -> (facts, def_list, ef::elsefind)) ([],[],[]) l

let final_extract_sure = function
  | Some sure_facts ->
      partition_facts sure_facts
  | None ->
      ([Terms.make_false()], [], [])
    
let def_vars_and_facts_from_term g_opt expanded in_find t =
  if Terms.check_simple_term t then
    ([t],[],[])
  else
    let extract_fun = if expanded then extract_sure_exp g_opt else extract_sure g_opt in
    final_extract_sure (extract_fun in_find t)

(* Extract both the sure facts when the then branch is taken and
   the elsefind facts for when the else branch is taken *)

let rec extract_sure_efl g_opt t =
  match t.t_desc with
  | _ when Terms.is_false t ->
     None, []
  | _ when Terms.is_true t ->
     Some [], [([],[],[])]
  | FunApp(f, [t1; t2]) when f == Settings.f_and ->
      let (sure1, efl1) = extract_sure_efl g_opt t1 in
      let (sure2, efl2) = extract_sure_efl g_opt t2 in
      make_and_sure sure1 sure2,
      make_and_efl efl1 efl2
  | FunApp(f, [t1; t2]) when f == Settings.f_or ->
      let (sure1, efl1) = extract_sure_efl g_opt t1 in
      let (sure2, efl2) = extract_sure_efl g_opt t2 in
      make_or_sure sure1 sure2,
      make_or_efl efl1 efl2
  | _ ->
      let t' = local_final_pseudo_expand g_opt t in
      extract_sure_exp g_opt true t',
      extract_efl_exp t'

(* [info_from_find_branch g_opt expanded br] returns a pair of
   information certainly true when the condition of find in the branch [br]
   succeeds (facts, defined variables, elsefind facts)
   and information certainly true when this condition fails
   (elsefind facts) *) 

let info_from_find_branch g_opt expanded (bl, def_list, t1, _) =
  let ris = List.map snd bl in
  if Terms.check_simple_term t1 then
    ([t1],[],[]), [(ris,def_list,t1)]
  else
    let (sure1, efl1) =
      if expanded then
        extract_sure_exp g_opt true t1,
        extract_efl_exp t1
      else
	extract_sure_efl g_opt t1 
    in
    (final_extract_sure sure1,
     final_extract_efl ris def_list efl1)

(* [add_info_find expanded g_opt l0] adds information collected 
   by [info_from_find_branch] to each branch of find in [l0] *)
let add_info_find g_opt expanded l0 =
  List.map (fun br ->
    (br, info_from_find_branch g_opt expanded br)
      ) l0
