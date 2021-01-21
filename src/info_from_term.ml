open Types

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

(* [make_or_dnf f1 f2] computes the disjunctive normal form of [f1] or
   [f2], assuming [f1] and [f2] are already in disjunctive normal
   form. *)

let includes l1 l2 =
  List.for_all (fun a1 ->
      List.exists (equal_facts a1) l2
    ) l1
       
let make_or_dnf f1 f2 =
  let f1_filtered =
    List.filter (fun l1 ->
        not (List.exists (fun l2 -> includes l2 l1) f2)
      ) f1
  in
  let f2_filtered =
    List.filter (fun l2 ->
        not (List.exists (fun l1 -> includes l1 l2) f1_filtered)
      ) f2
  in
  List.rev_append f1_filtered f2_filtered

let rec make_or_dnf_list = function
    [] -> []
  | [a] -> a
  | a::l -> make_or_dnf a (make_or_dnf_list l)
                  
(* [make_and_dnf f1 f2] computes the disjunctive normal form of [f1] and
   [f2], assuming [f1] and [f2] are already in disjunctive normal
   form. *)

let make_and_conj_list l1 l2 =
  let rec aux accu = function
      [] -> accu
    | (a::l) ->
       if List.exists (equal_facts a) l2 then aux accu l else aux (a::accu) l
  in
  aux l2 l1
                               
let make_and_dnf f1 f2 =
  let rec aux accu = function
      [] -> accu
    | (a::l) ->
       aux (make_or_dnf (List.rev_map (make_and_conj_list a) f1) accu) l
  in
  aux [] f2
  
let rec make_and_dnf_list = function
    [] -> [[]]
  | [a] -> a
  | a::l -> make_and_dnf a (make_and_dnf_list l)
                         
(* [filter_dnf var_list f] removes from [f] all references to variables in
   [var_list] *)

let refers_to_fact b = function
  | FTerm t -> Terms.refers_to b t
  | FDefined br -> Terms.refers_to_br b br
  | FElseFind(bl, def_list, t) ->
      (List.exists (Terms.refers_to_br b) def_list) ||
      (Terms.refers_to b t)
	
let filter_dnf var_list f =
  let not_refers_to_var_list t =
    not (List.exists (fun b -> refers_to_fact b t) var_list)
  in
  make_or_dnf_list
    (List.map (fun and_f ->
        [List.filter not_refers_to_var_list and_f]) f)

(* [filter_dnf_ri ri_list f] removes from [f] all references to 
   replication indices in [ri_list] *)

let rec refers_to_ri ri0 t =
  (match t.t_desc with
  | ReplIndex ri -> 
      (ri == ri0) ||
      (match ri.ri_link with
	TLink t -> refers_to_ri ri t
      | _ -> false)
  | _ -> false) ||
  (Terms.exists_subterm (refers_to_ri ri0) (refers_to_ri_br ri0) (refers_to_ri_pat ri0) t)

and refers_to_ri_br ri0 (_,l) =
  List.exists (refers_to_ri ri0) l

and refers_to_ri_pat ri0 pat =
  Terms.exists_subpat (refers_to_ri ri0) (refers_to_ri_pat ri0) pat
      
let refers_to_ri_fact ri0 = function
  | FTerm t -> refers_to_ri ri0 t
  | FDefined br -> refers_to_ri_br ri0 br
  | FElseFind(bl, def_list, t) ->
      (List.exists (refers_to_ri_br ri0) def_list) ||
      (refers_to_ri ri0 t)
	
let filter_dnf_ri ri_list f =
  let not_refers_to_ri_list t =
    not (List.exists (fun b -> refers_to_ri_fact b t) ri_list)
  in
  make_or_dnf_list
    (List.map (fun and_f ->
        [List.filter not_refers_to_ri_list and_f]) f)

(* [make_not_dnf t] returns the negation of [t] in disjunctive normal
form, assuming [t] is already in disjunctive normal
form. Very inefficient in general, but hopefully we are not often
in this case. *)

let rec make_not_fact = function
  | FTerm t -> [[FTerm (Terms.make_not t)]]
  | FDefined br1 -> [[FElseFind([], [br1], Terms.make_true())]]
  | FElseFind(bl, def_list,t) ->
      let accu = ref [] in
      List.iter (Terms.close_def_subterm accu) def_list;
      let def_list_subterms = !accu in
      let def_list_dnf = filter_dnf_ri bl
	  [List.map (fun br -> FDefined(br)) def_list_subterms]
      in
      let t_dnf = filter_dnf_ri bl (extract_dnf t) in
      make_and_dnf t_dnf def_list_dnf
	
and make_not_dnf f =
  make_and_dnf_list
    (List.map (fun l ->
         make_or_dnf_list (List.map make_not_fact l)
       ) f)

(* [extract_dnf t] derives a logical formula in disjunctive
   normal form that is implied by [t] *)
                    
and extract_dnf t =
  match t.t_desc with
  | _ when Terms.is_false t ->
     []
  | _ when Terms.is_true t ->
     [[]]
  | FunApp(f, [t1; t2]) when f == Settings.f_and ->
     make_and_dnf (extract_dnf t1) (extract_dnf t2)
  | FunApp(f, [t1; t2]) when f == Settings.f_or ->
     make_or_dnf (extract_dnf t1) (extract_dnf t2)
  | FunApp(f, [t1]) when f == Settings.f_not ->
     make_not_dnf (extract_dnf t1)
  | Var(_,l) | FunApp(_,l) ->
     if (List.for_all Terms.check_simple_term l) then [[FTerm t]] else [[]]
  | ReplIndex _ -> [[FTerm t]]
  | TestE(t1, t2, t3) ->
     let f1 = extract_dnf t1 in
     let f2 = extract_dnf t2 in
     let f3 = extract_dnf t3 in
     make_or_dnf (make_and_dnf f1 f2) (make_and_dnf (make_not_dnf f1) f3)
  | FindE(l0,t3,_) ->
      let else_find_dnf =
	make_and_dnf_list 
	  (List.map (fun (bl, def_list, t1, _) ->
	    if bl == [] && def_list == [] then
	      make_not_dnf (extract_dnf t1)
	    else if Terms.check_simple_term t1 then
	      [[FElseFind(List.map snd bl, def_list, t1)]]
	    else
	      [[]]) l0)
      in
     let f3 = make_and_dnf else_find_dnf (extract_dnf t3) in
     let f0 =
       make_or_dnf_list
         (List.map (fun (bl,def_list,t1,t2) ->
	   let vars = List.map fst bl in
	   let repl_indices = List.map snd bl in
           let f1 = filter_dnf_ri repl_indices (extract_dnf t1) in
           let f2 = filter_dnf vars (extract_dnf t2) in
           let accu = ref [] in
	   List.iter (Terms.close_def_subterm accu) def_list;
	   let def_list_subterms = !accu in
           let def_list_dnf = filter_dnf_ri repl_indices
             [List.map (fun br -> FDefined br) def_list_subterms]
           in
           make_and_dnf def_list_dnf (make_and_dnf f1 f2)
             ) l0)
     in
     make_or_dnf f0 f3
  | LetE(pat, t1, t2, topt) ->
     let vars = Terms.vars_from_pat [] pat in
     let assign_dnf = filter_dnf vars [[FTerm (Terms.make_equal (Terms.term_from_pat pat) t1)]] in
     let f2 = filter_dnf vars (extract_dnf t2) in
     let in_branch_dnf = make_and_dnf assign_dnf f2 in
     begin
       match pat with
       | PatVar b -> in_branch_dnf
       | _ ->
          match topt with
            Some t3 -> make_or_dnf in_branch_dnf (extract_dnf t3)
          | None -> Parsing_helper.internal_error "else branch of let missing"
     end
  | ResE (b,t) ->
     filter_dnf [b] (extract_dnf t)
  | EventAbortE _ | GetE _ ->
     (* Considering that [EventAbort e] implies false would not be correct
	in transf_expand.ml and transf_simplify.ml, because it leads to 
	removing the branch, including the condition, while evaluating
	the condition is needed for executing [EventAbort e].

	[get] may appear because this function is called before the first 
	transformation of get/insert into find. Since it is removed 
	quickly, extracting information from [get] is not essential. *)
     [[]]
  | EventE _ | InsertE _ ->
     Parsing_helper.internal_error "extract_dnf: event, insert should not occur in conditions of find"

(* [def_vars_and_facts_from_term t] extracts a list of defined variables and a
   list of facts implied by [t]

   [def_vars_and_facts_from_term] must be used only when [t] is a condition
   of [find]: it collects [elsefind] facts without caring about variables
   defined inside [t]. That's ok because variables defined in conditions
   of [find] never appear in [defined] conditions.
   If [def_vars_and_facts_from_term] were used for other terms, we might
   have to update some of these [elsefind] facts. *)

let partition_facts l =
  List.fold_left (fun accu fact ->
    let (facts, def_list, elsefind) = accu in
    match fact with
    | FTerm t -> (t::facts, def_list, elsefind)
    | FDefined br -> (facts, br::def_list, elsefind)
    | FElseFind ef -> (facts, def_list, ef::elsefind)) ([],[],[]) l
	       
let def_vars_and_facts_from_term t =
  try 
    let sure_facts = Terms.intersect_list equal_facts (extract_dnf t) in
    partition_facts sure_facts
  with Contradiction ->
    ([Terms.make_false()], [], [])

