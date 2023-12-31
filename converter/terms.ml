open Types
open Parsing_helper

let map_empty = Occ_map.empty

let simp_facts_id = ([],[],[])
let try_no_var_id t = t

(* Returns a list containing n times element x *)

let rec repeat n x =
  if n = 0 then [] else x :: (repeat (n-1) x)

(* Returns l without its n first elements *)

let rec skip n l = 
  try
    if n = 0 then l else skip (n-1) (List.tl l)
  with Failure _ ->
    failwith "Terms.skip"

(* Split l into two lists, first its n first elements, second
   the remaining of l *)

let rec split n l = 
  if n = 0 then ([],l) else
  match l with
    [] -> Parsing_helper.internal_error "split"
  | (a::l') -> let l1,l2 = split (n-1) l' in (a::l1,l2)


(* Find x in list l and return its position *)

let rec find_in_list x = function
    [] -> raise Not_found
  | (a::l) -> if x == a then 0 else 1 + find_in_list x l

(* Take a suffix of length n *)

let lsuffix n l =
  try
    skip (List.length l - n) l
  with Failure _ ->
    failwith "Terms.lsuffix"

(* Remove a suffix of length n *)

let remove_suffix n l =
  let (res, _) = split (List.length l - n) l in
  res

(* Compute intersections *)

let mem eqtest a l = List.exists (eqtest a) l

let intersect eqtest l1 l2 = List.filter (fun a2 -> mem eqtest a2 l1) l2

let rec intersect_list eqtest = function
    [] -> raise Contradiction
  | [a] -> a
  | (a::l) -> intersect eqtest a (intersect_list eqtest l)

(* union eqtest l1 l2 = l1 union l2 *)

let rec union eqtest l1 = function
    [] -> l1
  | (a::l) -> 
      if List.exists (eqtest a) l1 then
	union eqtest l1 l
      else
	a::(union eqtest l1 l)
	  
(* [map_union eqtest f l] = union of all [f a] for [a] in [l] *)

let rec map_union eqtest f = function
    [] -> []
  | (a::l) -> union eqtest (f a) (map_union eqtest f l)

(* Iterators *)

(* Exists *)
	
let rec exists_subterm f f_br f_pat t =
  match t.t_desc with
    Var(_,tl) | FunApp(_,tl) ->
      List.exists f tl
  | ReplIndex _ -> false
  | TestE(t1,t2,t3) ->
      (f t1) ||
      (f t2) ||
      (f t3)
  | FindE(l,t3,_) ->
      (f t3) ||
      (List.exists (fun (_,def_list,t1,t2) ->
	(List.exists f_br def_list) || (f t1)|| (f t2)) l)
  | LetE(pat,t1,t2,topt) ->
      (f_pat pat) ||
      (f t1) ||
      (f t2) ||
      (match topt with
	None -> false
      | Some t3 -> f t3)
  | ResE(_,t1) -> f t1
  | EventAbortE _ -> false
  | EventE(t1,p) ->
      (f t1) ||
      (f p)
  | InsertE(_,tl,p) ->
      (List.exists f tl) ||
      (f p)
  | GetE(_, patl, topt, p1, p2) ->
      (List.exists f_pat patl) ||
      (match topt with
	  None -> false
	| Some t -> f t) ||
      (f p1) ||
      (f p2)

let exists_subpat f f_pat = function
    PatVar _ -> false
  | PatTuple(_,l) -> List.exists f_pat l
  | PatEqual t -> f t

let exists_subiproc f f_input p =
  match p.i_desc with
    Nil -> false
  | Par(p1,p2) -> (f p1) || (f p2)
  | Repl(b,p) -> f p
  | Input((c,tl),pat,p) -> 
      f_input (c,tl) pat p

let exists_suboproc f f_term f_br f_pat f_iproc p =
  match p.p_desc with
    Yield | EventAbort _ -> false
  | Restr(_,p) -> f p
  | Test(t,p1,p2) -> (f_term t) || (f p1) ||
    (f p2)
  | Find(l0,p2, find_info) ->
      (List.exists (fun (bl,def_list,t,p1) ->
	(List.exists f_br def_list) ||
        (f_term t) || (f p1)) l0) || 
      (f p2)
  | Output((c,tl),t2,p) ->
      (List.exists f_term tl) || (f_term t2) || (f_iproc p)
  | EventP(t,p) ->
      (f_term t) || (f p)
  | Let(pat,t,p1,p2) ->
      (f_term t) || (f_pat pat) || 
      (f p1) ||(f p2)
  | Get(tbl,patl,topt,p1,p2) ->
      (List.exists f_pat patl) || 
      (match topt with None -> false | Some t -> f_term t) || 
      (f p1) ||(f p2)
  | Insert(tbl,tl,p) ->
      (List.exists f_term tl) || (f p)

	
(* Equality tests *)

let equal_lists eq l1 l2 =
  (List.length l1 == List.length l2) && 
  (List.for_all2 eq l1 l2)

let equal_mset mset1 mset2 =
  match (mset1, mset2) with
    (MOneBinder b1, MOneBinder b2) -> b1 == b2
  | x, y -> x == y

let equal_rset rset1 rset2 =
  match (rset1, rset2) with
    (All, All) | (Minimal, Minimal) | (FindCond, FindCond) -> true
  | (OneBinder b1, OneBinder b2) -> b1 == b2
  | _ -> false

let equal_merge_mode m1 m2 =
  match (m1,m2) with
    (MNoBranchVar, MNoBranchVar) | (MCreateBranchVar, MCreateBranchVar) -> true
  | (MCreateBranchVarAtProc (pl1, cur_array1), MCreateBranchVarAtProc (pl2, cur_array2)) ->
      (equal_lists (==) pl1 pl2) && (equal_lists (==) cur_array1 cur_array2)
  | (MCreateBranchVarAtTerm (tl1, cur_array1), MCreateBranchVarAtTerm (tl2, cur_array2)) ->
      (equal_lists (==) tl1 tl2) && (equal_lists (==) cur_array1 cur_array2)
  | _ -> false

let equal_query q1 q2 =
  match (q1,q2) with
    (QSecret (b1,l1), QSecret (b2,l2)) -> (b1 == b2) && (equal_lists (==) l1 l2)
  | (QSecret1 (b1,l1), QSecret1 (b2,l2)) -> (b1 == b2) && (equal_lists (==) l1 l2)
  | _ -> false

let eq_pair (a1,b1) (a2,b2) =
  a1 == a2 && b1 == b2
	
let equal_user_info i1 i2 =
  match i1,i2 with
    VarList(bl1,b1),VarList(bl2,b2) -> (equal_lists (==) bl1 bl2) && (b1 == b2)
  | Detailed(vmopt1,tmopt1), Detailed(vmopt2,tmopt2) ->
     (match vmopt1, vmopt2 with
       None, None -> true
     | Some(ml1,l1,b1), Some(ml2,l2,b2) ->
	 (equal_lists eq_pair ml1 ml2) && (equal_lists (==) l1 l2) && (b1 == b2)
     | _ -> false) &&
      (match tmopt1, tmopt2 with
	None, None -> true
      | Some(ml1,b1), Some(ml2,b2) ->
	  (equal_lists eq_pair ml1 ml2) && (b1 == b2)
      | _ -> false)
  | _ -> false
	
let equal_instruct i1 i2 =
  match i1,i2 with
    (ExpandIfFindGetInsert, ExpandIfFindGetInsert) -> true
  | (Simplify l1, Simplify l2) -> equal_lists (=) l1 l2
  | (GlobalDepAnal (b1,l1), GlobalDepAnal (b2,l2)) -> (b1 == b2) && (equal_lists (=) l1 l2)
  | (RemoveAssign rset1, RemoveAssign rset2) -> equal_rset rset1 rset2
  | (SArenaming b1, SArenaming b2) -> b1 == b2
  | (MoveNewLet mset1, MoveNewLet mset2) -> equal_mset mset1 mset2
  | (CryptoTransf (eq1, bl1), CryptoTransf (eq2, bl2)) -> 
      (eq1 == eq2) && (equal_user_info bl1 bl2)
  | (InsertEvent(s1,n1), InsertEvent(s2,n2)) ->
      (s1 = s2) && (n1 == n2)
  | (InsertInstruct(s1,_,n1,_), InsertInstruct(s2,_,n2,_)) ->
      (s1 = s2) && (n1 == n2)
  | (ReplaceTerm(s1,_,n1,_), ReplaceTerm(s2,_,n2,_)) ->
      (s1 = s2) && (n1 == n2)
  | (MergeArrays(bl1,m1), MergeArrays(bl2,m2)) ->
      (equal_lists (equal_lists (fun (b1,ext1) (b2, ext2) -> (b1 == b2) && (ext1 = ext2))) bl1 bl2) &&
      (equal_merge_mode m1 m2)
  | (MergeBranches, MergeBranches) -> true
  | (Proof ql1, Proof ql2) ->
      equal_lists (fun ((q1,n1),p1) ((q2,n2),p2) -> (equal_query q1 q2) && (n1 = n2) && (p1 = p2)) ql1 ql2
  | _ -> false

let add_eq a l =
  if List.exists (equal_instruct a) l then l else a::l

(* Create an interval type from a parameter *)

let type_for_param_table = Hashtbl.create 7

let type_for_param p =
  try 
    Hashtbl.find type_for_param_table p 
  with Not_found ->
    let t = { tname = "[1," ^ p.pname ^"]";
	      tcat = Interv p;
	      toptions = Settings.tyopt_BOUNDED;
	      tsize = 0;
              timplsize = None;
              tpredicate = None;
              timplname = None;
              tserial = None;
              trandom = None }
    in
    Hashtbl.add type_for_param_table p t;
    t

(* Get a parameter from an interval type *)

let param_from_type t =
  match t.tcat with
    Interv p -> p
  | _ -> internal_error "Interval type expected"

(* New occurrence *)

let occ = ref 0
let max_occ = ref 100

let new_occ() =
  incr occ;
  if !occ > !max_occ then max_occ := !occ;
  !occ

(* Get the else branch of let for terms *)

let get_else = function
    None -> Parsing_helper.internal_error "missing else branch of let"
  | Some t -> t
    
(* Binder from term *)

let binder_from_term t =
  match t.t_desc with
    Var(b,_) -> b
  | _ -> internal_error "Binder term expected"

let binderref_from_term t =
  match t.t_desc with
    Var(b,l) -> (b,l)
  | _ -> internal_error "Binder term expected"

let repl_index_from_term t =
  match t.t_desc with
    ReplIndex(b) -> b
  | _ -> internal_error "Replication index term expected"

let build_term t desc =
  { t_desc = desc;
    t_type = t.t_type;
    t_occ = new_occ(); 
    t_max_occ = 0;
    t_loc = Parsing_helper.dummy_ext;
    t_incompatible = map_empty;
    t_facts = None }

(* build_term2 is the same as build_term, except that it keeps the
   occurrence of t. This is useful in particular so that occurrences
   are kept in term manipulations by simplification, to be able to
   designate a term by occurrence *)

let build_term2 t desc =
  { t_desc = desc;
    t_type = t.t_type;
    t_occ = t.t_occ;
    t_max_occ = 0;
    t_loc = t.t_loc;
    t_incompatible = map_empty;
    t_facts = None }

let build_term3 t desc =
  { t_desc = desc;
    t_type = t.t_type;
    t_occ = new_occ();
    t_max_occ = 0;
    t_loc = t.t_loc;
    t_incompatible = map_empty;
    t_facts = None }

let build_term_type ty desc =
  { t_desc = desc;
    t_type = ty;
    t_occ = new_occ();
    t_max_occ = 0;
    t_loc = Parsing_helper.dummy_ext;
    t_incompatible = map_empty;
    t_facts = None }

let new_term ty ext desc =
  { t_desc = desc;
    t_type = ty;
    t_occ = new_occ();
    t_max_occ = 0;
    t_loc = ext;
    t_incompatible = map_empty;
    t_facts = None }  
    
let term_from_repl_index b =
  build_term_type b.ri_type (ReplIndex b)

let term_from_binder b =
  build_term_type b.btype (Var(b, List.map term_from_repl_index b.args_at_creation))

let term_from_binderref (b,l) =
  build_term_type b.btype (Var(b, l))

let binderref_from_binder b =
  (b, List.map term_from_repl_index b.args_at_creation)

let is_args_at_creation b l =
  List.for_all2 (fun ri t -> 
    match t.t_desc with
      ReplIndex ri' -> ri == ri'
    | _ -> false) b.args_at_creation l

let app f l =
  build_term_type (snd f.f_type) (FunApp(f,l)) 

(* Process from desc *)

let iproc_from_desc d = { i_desc = d; i_occ = new_occ(); i_max_occ = 0; 
			  i_incompatible = map_empty; i_facts = None }

let oproc_from_desc d = { p_desc = d; p_occ = new_occ(); p_max_occ = 0;
			  p_incompatible = map_empty; p_facts = None }

let iproc_from_desc2 p d = { i_desc = d; i_occ = p.i_occ; i_max_occ = 0; 
			     i_incompatible = p.i_incompatible; 
			     i_facts = p.i_facts }

let oproc_from_desc2 p d = { p_desc = d; p_occ = p.p_occ; p_max_occ = 0;
			     p_incompatible = p.p_incompatible; 
			     p_facts = p.p_facts }

let iproc_from_desc3 p d = { i_desc = d; i_occ = p.i_occ; i_max_occ = 0; 
			     i_incompatible = map_empty; i_facts = None }

let oproc_from_desc3 p d = { p_desc = d; p_occ = p.p_occ; p_max_occ = 0;
			     p_incompatible = map_empty; p_facts = None }

let empty_game = { proc = iproc_from_desc Nil; game_number = -1; current_queries = [] }
    
(* Constant for each type *)

module HashedType =
  struct
    type t = Types.typet
    let equal = (==)
    (* The hash function must use only parts that are not modified,
       otherwise, we may have the same element with several different hashes *)
    let hash t = Hashtbl.hash t.tname
  end

module TypeHashtbl = Hashtbl.Make(HashedType)

let cst_for_type_table = TypeHashtbl.create 7

let cst_for_type ty =
  let f = 
    try
      TypeHashtbl.find cst_for_type_table ty
    with Not_found ->
      let r = { f_name = "cst_" ^ ty.tname;
		f_type = [],ty;
		f_cat = Std;
		f_options = 0;
		f_statements = [];
		f_collisions = [];
		f_eq_theories = NoEq;
                f_impl = No_impl;
                f_impl_inv = None }
      in
      TypeHashtbl.add cst_for_type_table ty r;
      r
  in
  build_term_type ty (FunApp(f,[]))

(* Is a variable defined by a restriction ? *)

let is_restr b =
  (* if b.def == [] then
    print_string ("Warning: is_restr with empty def " ^ b.sname ^ "_" ^ (string_of_int b.vname) ^ "\n"); *)
  List.for_all (function 
      { definition = DProcess { p_desc = Restr _} } -> true
    | { definition = DTerm ({ t_desc = ResE _}) } -> true
    | { definition = DFunRestr } -> true
    | _ -> false) b.def

(* Is a variable defined by an assignment ? *)

let is_assign b =
  List.for_all (function 
      { definition = DProcess { p_desc = Let _} } -> true
    | { definition = DTerm { t_desc = LetE _ }} -> true
    | _ -> false) b.def

(* Links *)

let current_bound_vars = ref []

let link v l =
  current_bound_vars := v :: (!current_bound_vars);
  v.link <- l

let cleanup () =
  List.iter (fun v -> v.link <- NoLink) (!current_bound_vars);
  current_bound_vars := []

let auto_cleanup f =
  let tmp_bound_vars = !current_bound_vars in
  current_bound_vars := [];
  try
    let r = f () in
    List.iter (fun v -> v.link <- NoLink) (!current_bound_vars);
    current_bound_vars := tmp_bound_vars;
    r
  with x ->
    List.iter (fun v -> v.link <- NoLink) (!current_bound_vars);
    current_bound_vars := tmp_bound_vars;
    raise x

(* Equality *)

(* [compute_inv try_no_var reduced (f, inv, n) t] returns a term equal to 
   [inv(t)]. 
   [(f, inv,n)] is supposed to be a group, with product [f],
   inverse function [inv], and neutral element [n]. 
   [reduced] is set to true when a simplification occurred
   during the computation. 
   [try_no_var] is explained in the function [simp_main_fun]. *)

let rec compute_inv try_no_var reduced (f, inv, n) t =
  let t_no_var = try_no_var t in
  match t_no_var.t_desc with
    FunApp(inv', [t']) when inv' == inv -> 
      (* inv(inv(x)) = x *)
      reduced := true;
      t'
  | FunApp(f', [t1;t2]) when f' == f ->
      (* inv(x.y) = inv(y).inv(x) *)
      reduced := true;
      build_term t (FunApp(f, [compute_inv try_no_var reduced (f,inv,n) t2; compute_inv try_no_var reduced (f,inv,n) t1]))
  | FunApp(n', []) when n' == n ->
      (* inv(n) = n *)
      reduced := true;
      t_no_var
  | _ ->
      build_term t (FunApp(inv, [t]))

(* Simplification function:
   [simp_main_fun try_no_var reduced f t] simplifies term [t].
   [f] is a binary function with an equational theory. 
   [simp_main_fun] returns a list of terms [l], such that [t] is equal to
   the product of the elements of [l] by function [f].
   [reduced] is set to true when [t] has really been simplified.
   [try_no_var] is a function from terms to terms that tries to replace
   variables with their values. It leaves non-variable terms unchanged.
   It can be the identity when we do not have information on the values
   of variables.
   ([simp_main_fun] does not consider cancellations between terms in
   ACUN or group equational theories, which are considered below by
   function [simp_prod].) *)

let rec simp_main_fun try_no_var reduced f t =
  match f.f_eq_theories, (try_no_var t).t_desc with
    (Assoc | AssocN _ | AssocCommut | AssocCommutN _ | ACUN _ | 
     Group _ | CommutGroup _), FunApp(f', [t1;t2]) when f == f' -> 
      (simp_main_fun try_no_var reduced f t1) @ 
      (simp_main_fun try_no_var reduced f t2)
  | (Group(f'',inv,n) | CommutGroup(f'',inv,n)), FunApp(inv', [t1]) when inv' == inv ->
      let reduced' = ref false in
      let t' = compute_inv try_no_var reduced' (f'',inv,n) t1 in
      if !reduced' then
	begin
	  reduced := true;
	  simp_main_fun try_no_var reduced f t'
	end
      else
	[t]
  | (AssocN(_,n) | AssocCommutN(_,n) | ACUN(_,n) | Group(_,_,n) | 
     CommutGroup(_,_,n)), FunApp(n', []) when n == n' ->
      (* Eliminate the neutral element *)
      reduced := true;
      []
  | _ -> [t]

(* [remove_elem sub_eq a l] returns list [l] with one
   occurrence of element [a] removed. Function [sub_eq]
   is used to test equality between elements.
   When [l] does not contain [a], raises [Not_found]. *)

let rec remove_elem sub_eq a = function
    [] -> raise Not_found 
  | (a'::l) ->
      if sub_eq a a' then l else a'::(remove_elem sub_eq a l)

(* [remove_duplicates reduced sub_eq l] returns list [l]
   after removing duplicate elements. Function [sub_eq]
   is used to test equality between elements.
   [reduced] is set to true when some elements have been removed. *)

let rec remove_duplicates reduced sub_eq = function
    [] -> []
  | (a::l) ->
      try 
	let l' = remove_elem sub_eq a l in
	reduced := true;
	remove_duplicates reduced sub_eq l'
      with Not_found ->
	a::(remove_duplicates reduced sub_eq l)

(* [equal_up_to_order sub_eq l1 l2] returns true when the
   lists [l1] and [l2] are equal up to the ordering of their
   elements. 
   The function [sub_eq] is used to test equality between elements. *)

let rec equal_up_to_order sub_eq l1 l2 =
  match l1,l2 with
    [],[] -> true
  | [],_ | _,[] -> false
  | (a::l,_) ->
      try
	let l2' = remove_elem sub_eq a l2 in
	equal_up_to_order sub_eq l l2'
      with Not_found ->
	false

(* [equal_up_to_roll sub_eq l1 l2] returns true when [l1]
   contains the same elements as [l2], in the same order,
   but the lists may be rotated, that is,
   l1 = [t1;...;tn] and l2 = [tk;...;tn;t1;...;t_{k-1}].
   Function [sub_eq] is used to test equality between elements. *)

let rec equal_up_to_roll_rec sub_eq l1 seen2 rest2 =
  (List.for_all2 sub_eq l1 (rest2 @ (List.rev seen2))) ||
  (match rest2 with
    [] -> false
  | (a::rest2') ->
      equal_up_to_roll_rec sub_eq l1 (a::seen2) rest2'
	)

let equal_up_to_roll sub_eq l1 l2 =
  (List.length l1 == List.length l2) && 
  (equal_up_to_roll_rec sub_eq l1 [] l2)

(* [get_neutral f] returns the neutral element of the equational
   theory of the function symbol [f]. *)

let get_neutral f =
  match f.f_eq_theories with
    ACUN(_,n) | Group(_,_,n) | CommutGroup(_,_,n) | AssocN(_,n) | AssocCommutN(_,n) -> n
  | _ -> Parsing_helper.internal_error "equational theory has no neutral element in Terms.get_neutral"

(* [get_prod try_no_var t] returns the equational theory of the root
   function symbol of term [t], when it is a product
   in a group or xor. *)

let get_prod try_no_var t =
  match (try_no_var t).t_desc with
    FunApp(f,[_;_]) ->
      begin
	match f.f_eq_theories with
	  Group(prod,_,_) | CommutGroup(prod,_,_) 
	| ACUN(prod,_) when prod == f -> 
	    f.f_eq_theories
	| _ -> NoEq
      end
  | _ -> NoEq

(* [get_prod_list try_no_var l] returns the equational theory of the root
   function symbol of a term in [l], when it is a product
   in a group or xor. *)

let rec get_prod_list try_no_var = function
    [] -> NoEq
  | t::l ->
      match (try_no_var t).t_desc with
	FunApp(f,[_;_]) ->
	  begin
	  match f.f_eq_theories with
	    Group(prod,_,_) | CommutGroup(prod,_,_) 
	  | ACUN(prod,_) when prod == f -> 
	      f.f_eq_theories
	  | _ -> get_prod_list try_no_var l
	  end
      |	_ -> get_prod_list try_no_var l

(* [remove_inverse_ends simp_facts reduced group_th l] removes the
   inverse elements at the two ends of the list [l]. In a non-commutative group,
   the product of the elements [l] is the neutral element if and only if the
   product of the resulting list is: x * t * x^-1 = e iff t = e by multiplying
   on the left by x^-1 and on the right by x. 
   [simp_facts] collects the rewrite rules corresponding to known equalities
   and other known facts, which we use in order to replace variables with their values and
   to test equality between terms.
   [group_th = (f, inv,n)] is supposed to be a group, with product [f],
   inverse function [inv], and neutral element [n].    
   [reduced] is set to true when some elements have been removed. *)

let rec cut_list n accu l = 
  if n = 0 then (accu, l) else
  match l with
    [] -> (accu, [])
  | a::l' -> cut_list (n-1) (a::accu) l'

let rec remove_inverse_prefix simp_facts reduced group_th l1 l2 =
  match l1, l2 with
    t1::r1, t2::r2 when simp_equal_terms simp_facts true t1 (compute_inv (try_no_var simp_facts) (ref false) group_th t2) -> 
      reduced := true;
      remove_inverse_prefix simp_facts reduced group_th r1 r2
  | _ -> (l1,l2)    

and remove_inverse_ends simp_facts reduced group_th l = 
  let n = (List.length l) / 2 in
  let half1, half2 = cut_list n [] l in
  let half1', half2' = remove_inverse_prefix simp_facts reduced group_th half1 half2 in
  List.rev_append half1' half2'

(* [remove_inverse simp_facts reduced group_th l] returns list [l]
   after removing elements that are inverse of one another. 
   [simp_facts], [reduced], and [group_th] are as above. *)

and remove_inverse simp_facts reduced group_th = function
    [] -> []
  | (a::l) ->
      try 
	let a_inv = compute_inv (try_no_var simp_facts) (ref false) group_th a in
	let l' = remove_elem (simp_equal_terms simp_facts true) a_inv l in
	reduced := true;
	remove_inverse simp_facts reduced group_th l'
      with Not_found ->
	a::(remove_inverse simp_facts reduced group_th l)

(* [remove_consecutive_inverse simp_facts reduced group_th seen_l l]
   removes consecutive elements of [l] that are inverses of one another.
   [seen_l] corresponds to the part of [l] already examined by the algorithm,
   in reverse order. The algorithm always tries to eliminate the first
   element of [seen_l] and the first element of [l].
   [simp_facts], [reduced], and [group_th] are as above. *)

and remove_consecutive_inverse simp_facts reduced group_th seen_l l = 
  match (seen_l, l) with
    [],[] -> []
  | [],a::l' -> remove_consecutive_inverse simp_facts reduced group_th [a] l'
  | _ ,[] -> List.rev seen_l
  | a::seen_l', a'::l' ->
      let a_inv = compute_inv (try_no_var simp_facts) (ref false) group_th a in
      if simp_equal_terms simp_facts true a_inv a' then
	begin
	  reduced := true;
	  remove_consecutive_inverse simp_facts reduced group_th seen_l' l'
	end
      else
	remove_consecutive_inverse simp_facts reduced group_th (a'::seen_l) l'


(* Simplification function:
   [simp_prod simp_facts reduced f t] simplifies term [t].
   [f] is a binary function with an equational theory. 
   [simp_prod] returns a list of terms [l], such that [t] is equal to
   the product of the elements of [l] by function [f].
   [simp_facts] collects the rewrite rules corresponding to known equalities
   and other known facts, which we use in order to replace variables with their values and
   to test equality between terms.
   [reduced] is set to true when [t] has really been simplified. *)

and simp_prod simp_facts reduced f t =
  let l = simp_main_fun (try_no_var simp_facts) reduced f t in
  match f.f_eq_theories with
    ACUN _ -> 
      (* Remove duplicates from the list, since they cancel out *)
      remove_duplicates reduced (simp_equal_terms simp_facts true) l
  | Group(f',inv,n) ->
      (* Remove pairs formed of an element immediately followed by its inverse,
	 since they cancel out. *)
      remove_consecutive_inverse simp_facts reduced (f',inv,n) [] l
  | CommutGroup(f',inv,n) ->
      (* Remove pairs of an element and its inverse since they cancel out *)
      remove_inverse simp_facts reduced (f',inv,n) l
  | _ -> l


(* [try_no_var simp_facts t] returns [t] unchanged when it
   is a function application and tries to replace it with its value
   using the rewrite rules in [simp_facts] when it is a variable.
   See facts.ml for additional information on [simp_facts].

   The functions [apply_subst_list] and [normalize_var] are helper functions
   to define [try_no_var].

   [apply_subst_list t subst] applies a rewrite rule in [subst]
   to the term [t] (only at the root of [t]) and returns the reduced
   term, if possible. Otherwise, it just returns [t] itself. *)

and apply_subst_list t = function
    [] -> t
  | tsubst::rest -> 
     match tsubst.t_desc with
       FunApp(f,[redl;redr]) when f.f_cat == Equal || f.f_cat == LetEqual ->
         begin
           if equal_terms t redl then 
	     redr
           else
	     apply_subst_list t rest
         end
     | _ -> Parsing_helper.internal_error "substitutions should be Equal or LetEqual terms"

(* [normalize_var subst t] normalizes the term [t] (which must contain
   only variables and replication indices) using the rewrite rules
   in [subst].
   Since the RHS of rewrite rules is already normalized,
   it is enough to apply rewrite rules once at each variable 
   symbol from the inside to the outside to normalize the term. *)

and normalize_var subst2 t =
  match t.t_desc with
    Var(b,l) ->
      let l' = List.map (normalize_var subst2) l in
      let t' = build_term2 t (Var(b,l')) in
      apply_subst_list t' subst2
  | ReplIndex _ -> 
      apply_subst_list t subst2
  | FunApp _ ->
      (* This property requires variables not to contain functions.
	 This is true now, but may change in the future. *)
      Parsing_helper.internal_error "FunApp should not occur in normalize_var"
  | TestE _ | FindE _ | LetE _ | ResE _ | EventAbortE _ | EventE _ | GetE _ | InsertE _ -> 
      Parsing_helper.internal_error "If, find, let, and new should not occur in normalize_var"

and try_no_var (subst2, _, _) t =
  if subst2 == [] then t else
  match t.t_desc with
    Var _ | ReplIndex _ -> 
      normalize_var subst2 t
  | _ -> t

(* Equality test *)

(* [simp_equal_terms simp_facts normalize_root t1 t2] returns true when
   the terms [t1] and [t2] are equal. It uses the rewrite rules in
   [simp_facts] to reduce the terms in order to infer more equalities.
   When [normalize_root] is false, the rewrite rules in [simp_facts]
   are not applied at the root of the terms [t1] and [t2]. *)

and simp_equal_terms simp_facts normalize_root t1 t2 = 
  if (simp_facts == simp_facts_id) || (not normalize_root) then
    simp_equal_terms1 simp_facts t1 t2
  else
    (simp_equal_terms1 simp_facts_id t1 t2) ||
    (let t1' = normalize simp_facts t1 in
    let t2' = normalize simp_facts t2 in
    simp_equal_terms1 simp_facts t1' t2')

and simp_equal_terms1 simp_facts t1 t2 =
  match (t1.t_desc, t2.t_desc) with
    Var(b1,l1),Var(b2,l2) ->
      (b1 == b2) && (List.for_all2 equal_terms l1 l2)
  | ReplIndex b1, ReplIndex b2 -> b1 == b2
  | FunApp(f1, [t1;t1']), FunApp(f2, [t2;t2']) when 
      f1 == f2 && (f1.f_cat == Equal || f1.f_cat == Diff) ->
	(* It is important to test this case before the commutative
	   function symbols: = and <> are also commutative function
	   symbols. *)
	begin
	  (* In a group, when t1/t1' = t2/t2', we have t1 = t1' if and only if t2 = t2'.
	     With xor, when t1 xor t1' = t2 xor t2', we have t1 = t1' if and only if t2 = t2'. *)
	  match get_prod_list (try_no_var simp_facts) [t1;t1';t2;t2'] with
	    ACUN(xor,_) ->
	      simp_equal_terms simp_facts true (app xor [t1;t1']) (app xor [t2;t2'])
	  | CommutGroup(prod,inv,_) ->
	      (simp_equal_terms simp_facts true (app prod [t1; app inv [t1']])
		(app prod [t2; app inv [t2']])) ||
	      (simp_equal_terms simp_facts true (app prod [t1; app inv [t1']]) 
		(app prod [t2'; app inv [t2]]))
	  | Group(prod,inv,neut) ->
	      (* For non-commutative groups, I can still commute a term
		 and its inverse, so I try all possibilities. 
		 t1 = t1' iff t1/t1' = neut iff the product of the elements of [l1] is neut 
		          iff the product of the elements of [l1'] is neut 
		 Similarly, t2 = t2' iff the product of the elements of [l2'] is neut.
		 The product of the elements of [l2''] is the inverse of 
		 the product of the elements of [l2'],
		 so one is neut iff the other is.
		 *)
	      let l1 = simp_prod simp_facts (ref false) prod (app prod [t1; app inv [t1']]) in
	      let l1' = remove_inverse_ends simp_facts (ref false) (prod, inv, neut) l1 in
	      let l2 = simp_prod simp_facts (ref false) prod (app prod [t2; app inv [t2']]) in
	      let l2' = remove_inverse_ends simp_facts (ref false) (prod, inv, neut) l2 in
	      (equal_up_to_roll (simp_equal_terms simp_facts true) l1' l2') || 
	      (let l2'' = List.rev (List.map (compute_inv (try_no_var simp_facts) (ref false) (prod, inv, neut)) l2') in
	      equal_up_to_roll (simp_equal_terms simp_facts true) l1' l2'')
	  | _ -> 
	      ((simp_equal_terms simp_facts true t1 t2) && (simp_equal_terms simp_facts true t1' t2')) ||
	      ((simp_equal_terms simp_facts true t1 t2') && (simp_equal_terms simp_facts true t1' t2))
	end
  | FunApp(f1,[t1;t1']),FunApp(f2,[t2;t2']) when f1 == f2 && f1.f_eq_theories = Commut ->
      (* Commutative function symbols *)
      ((simp_equal_terms simp_facts true t1 t2) && (simp_equal_terms simp_facts true t1' t2')) ||
      ((simp_equal_terms simp_facts true t1 t2') && (simp_equal_terms simp_facts true t1' t2))
  | FunApp({f_eq_theories = (Group(f,inv',n) | CommutGroup(f,inv',n)) } as inv, [t1']), _ when inv' == inv ->
      (* inv is an inverse function *)
      let reduced = ref false in
      let t1_simp = compute_inv (try_no_var simp_facts) reduced (f,inv',n) t1' in
      if !reduced then simp_equal_terms simp_facts true t1_simp t2 else 
      begin
        match t2.t_desc with
          FunApp({f_eq_theories = (Group(f2,inv2',n2) | CommutGroup(f2,inv2',n2)) } as inv2, [t2']) when inv2' == inv2 ->
            (* inv2 is an inverse function *)
            let reduced = ref false in
            let t2_simp = compute_inv (try_no_var simp_facts) reduced (f2,inv2',n2) t2' in
            if !reduced then simp_equal_terms simp_facts true t1 t2_simp else 
            (inv == inv2) && (simp_equal_terms simp_facts true t1' t2')
        | FunApp(f2, [_;_]) when f2.f_eq_theories != NoEq && f2.f_eq_theories != Commut ->
            (* f2 is a binary function with an equational theory that is
	       not commutativity nor inverse -> it is a product-like function *)
            let l2 = simp_prod simp_facts (ref false) f2 t2 in
            begin
	      match l2 with
	        [] -> simp_equal_terms simp_facts true t1 (build_term t2 (FunApp(get_neutral f2, [])))
	      | [t] -> simp_equal_terms simp_facts true t1 t
	      | _ -> (* t2 is a product and t1 is not (it is an inverse), so they cannot be equal *)
	         false
            end
        | _ -> (* t2 is not an inverse nor a product, it cannot be equal to t1 *) false
      end
  | FunApp(f1,[_;_]),_ when f1.f_eq_theories != NoEq && f1.f_eq_theories != Commut ->
      (* f1 is a binary function with an equational theory that is
	 not commutativity nor inverse -> it is a product-like function *)
      let l1 = simp_prod simp_facts (ref false) f1 t1 in
      begin
	match l1 with
	  [] -> simp_equal_terms simp_facts true (build_term t1 (FunApp(get_neutral f1, []))) t2
	| [t] -> simp_equal_terms simp_facts true t t2
	| _ -> 
	    let l2 = simp_prod simp_facts (ref false) f1 t2 in
	    match f1.f_eq_theories with
	      NoEq | Commut -> Parsing_helper.internal_error "equal_terms: cases NoEq, Commut should have been eliminated"
	    | AssocCommut | AssocCommutN _ | CommutGroup _ | ACUN _ ->
		(* Commutative equational theories: test equality up to ordering *)
		(List.length l1 == List.length l2) &&
		(equal_up_to_order (simp_equal_terms simp_facts true) l1 l2)
	    | Assoc | AssocN _ | Group _ -> 
		(* Non-commutative equational theories: test equality in the same order *)
		equal_lists (simp_equal_terms simp_facts true) l1 l2		
      end
  | _, FunApp({f_eq_theories = (Group(f,inv',n) | CommutGroup(f,inv',n)) } as inv, [t2']) when inv == inv' ->
      (* inv is an inverse function *)
      let reduced = ref false in
      let t2_simp = compute_inv (try_no_var simp_facts) reduced (f,inv',n) t2' in
      if !reduced then simp_equal_terms simp_facts true t1 t2_simp else 
      (* t1 is not a product nor an inverse, otherwise the previous cases 
         would have been triggered, so t1 cannot be equal to t2 *)
      false
  | _, FunApp(f2, [_;_]) when f2.f_eq_theories != NoEq && f2.f_eq_theories != Commut ->
      (* f2 is a binary function with an equational theory that is
	 not commutativity nor inverse -> it is a product-like function *)
      let l2 = simp_prod simp_facts (ref false) f2 t2 in
      begin
	match l2 with
	  [] -> simp_equal_terms simp_facts true t1 (build_term t2 (FunApp(get_neutral f2, [])))
	| [t] -> simp_equal_terms simp_facts true t1 t
	| _ -> (* t2 is a product and t1 is not (otherwise the previous case
		  would have been triggered), so they cannot be equal *)
	    false
      end
  | FunApp(f1,l1),FunApp(f2,l2) ->
      (f1 == f2) && (List.for_all2 (simp_equal_terms simp_facts true) l1 l2)
  | TestE(t1,t2,t3), TestE(t1',t2',t3') ->
      (simp_equal_terms simp_facts true t1 t1') && (simp_equal_terms simp_facts true t2 t2') && (simp_equal_terms simp_facts true t3 t3')
  | FindE(l,t3,find_info),FindE(l',t3',find_info') ->
      (* Could do modulo renaming of bl and bl'! *)
      (equal_lists (fun (bl,def_list,t1,t2) (bl',def_list',t1',t2') ->
	(equal_lists (fun (b1,b2) (b1', b2') -> (b1 == b1') && (b2 == b2')) bl bl') && 
	(equal_def_lists def_list def_list') && 
	(simp_equal_terms simp_facts true t1 t1') && (simp_equal_terms simp_facts true t2 t2')) l l') && 
      (simp_equal_terms simp_facts true t3 t3') &&
      (find_info == find_info')
  | LetE(pat, t1, t2, topt), LetE(pat', t1', t2', topt') ->
      (equal_pats simp_facts pat pat') &&
      (simp_equal_terms simp_facts true t1 t1') &&
      (simp_equal_terms simp_facts true t2 t2') &&
      (match topt, topt' with
	None, None -> true
      | Some t3, Some t3' -> simp_equal_terms simp_facts true t3 t3'
      | _ -> false)
  | ResE(b,t), ResE(b',t') ->
      (b == b') && (simp_equal_terms simp_facts true t t')
  | EventAbortE(f), EventAbortE(f') -> 
      f == f'
  | EventE(t,p), EventE(t',p') ->
      (simp_equal_terms simp_facts true t t') &&
      (simp_equal_terms simp_facts true p p')
  | (GetE _, GetE _) | (InsertE _, InsertE _) ->
      Parsing_helper.internal_error "get and insert should not occur in simp_equal_terms"
  | _ -> false

and equal_terms t1 t2 = simp_equal_terms1 simp_facts_id t1 t2

and equal_def_lists def_list def_list' =
  equal_lists equal_binderref def_list def_list'

and equal_binderref (b,l) (b',l') =
  (b == b') && (List.for_all2 equal_terms l l')

and equal_pats simp_facts p1 p2 =
  match p1,p2 with
    PatVar b, PatVar b' -> b == b'
  | PatTuple (f,l), PatTuple (f',l') -> (f == f') && (List.for_all2 (equal_pats simp_facts) l l')
  | PatEqual t, PatEqual t' -> simp_equal_terms simp_facts true t t'
  | _ -> false



(* [apply_subst_list_fun simp_facts t subst] applies a 
   rewrite rule [subst] to the term [t] (only at the root)
   and returns the reduced term, if possible. Otherwise,
   it just returns [t] itself.
   It uses the equalities in [simp_facts] to help establishing
   that [t] is equal to the left-hand side of a rewrite rule.
   The equalities in [simp_facts] are applied only to strict 
   subterms of [t] and of the LHS of a rewrite rule, because
   applying them at the root of [t]  would mean applying another 
   rewrite rule, and applying them at the root of the LHS of a
   rewrite rule is impossible since the root of rewrite rules
   is already normalized.
 *)

and apply_subst_list_fun simp_facts t seen = function
    [] -> t
  | tsubst::rest -> 
     match tsubst.t_desc with
       FunApp(f,[redl;redr]) when f.f_cat == Equal || f.f_cat == LetEqual ->
         begin
	   (* Excluding the rewrite rule redl->redr that we want to test
              from the rules that can be used to test equality between t and redl.
              This avoids an infinite loop.
	      For instance, when t = H(M') and redl = H(H(M)),
	      normalizing t calls simp_equal_terms [...] false H(M') H(H(M)),
	      which calls normalize on H(M). If the rewrite rule redl->redr
	      with redl = H(H(M)) is still present, it will call 
	      simp_equal_terms [...] false H(M) H(H(M)),
	      which again calls normalize on H(M). *)
	   let (_,facts,elsefind) = simp_facts in
	   let simp_facts' = (List.rev_append seen rest, facts,elsefind) in
           if simp_equal_terms simp_facts' false t redl then 
	     redr
           else
	     apply_subst_list_fun simp_facts t (tsubst::seen) rest
         end
     | _ -> Parsing_helper.internal_error "substitutions should be Equal or LetEqual terms"

(* [normalize simp_facts t] normalizes the term [t]
   using the rewrite rules in [simp_facts]. 
   The root of [t] is guaranteed to be normalized.
   Rewrite rules of [simp_facts] may still be applicable
   to strict subterms of the result. 
   When [t] is a variable, we use [normalize_var].
   When it is a function symbol, we apply a rewrite rule of
   [simp_facts] once at the root (possibly applying rewrite rules
   of [simp_facts] to strict subterms to allow this rewriting),
   if possible. This is enough because the RHS of rewrite rules is 
   already normalized at the root. *)
	   
and normalize ((subst2, _, _) as simp_facts) t =
  match t.t_desc with
    FunApp(f,l) ->
      apply_subst_list_fun simp_facts t [] subst2
  | Var _ | ReplIndex _ -> 
      normalize_var subst2 t 
  | TestE _ | FindE _ | LetE _ | ResE _ | EventAbortE _ | EventE _ | GetE _ | InsertE _ -> 
      t

let equal_term_lists l1 l2 =
  equal_lists equal_terms l1 l2

let equal_action a1 a2 =
  match a1, a2 with
    AFunApp f, AFunApp f' -> f == f'
  | APatFunApp f, APatFunApp f' -> f == f'
  | AReplIndex, AReplIndex -> true
  | AArrayAccess n, AArrayAccess n' -> n == n'
  | ANew t, ANew t' -> t == t'
  | ANewChannel, ANewChannel -> true
  | AIf, AIf -> true
  | AFind n, AFind n' -> n == n'
  | AOut(tl,t), AOut(tl',t') -> (t == t') && (equal_lists (==) tl tl')
  | AIn n, AIn n' -> n == n'
  | _ -> false
  
let rec equal_probaf p1 p2 =
  match p1, p2 with
    Proba(p, l), Proba(p',l') -> (p == p') && (equal_lists equal_probaf l l')
  | Count p, Count p' -> p == p'
  | OCount c, OCount c' -> c == c'
  | Cst f, Cst f' -> f = f'
  | Zero, Zero -> true
  | Card t, Card t' -> t == t'
  | AttTime, AttTime -> true
  | Time (n,p), Time (n',p') -> (n == n') && (equal_probaf p p')
  | ActTime(a,l), ActTime(a',l') -> (equal_action a a') && (equal_lists equal_probaf l l')
  | Add(p1,p2), Add(p1',p2') -> (equal_probaf p1 p1') && (equal_probaf p2 p2')
  | Mul(p1,p2), Mul(p1',p2') -> (equal_probaf p1 p1') && (equal_probaf p2 p2')
  | Sub(p1,p2), Sub(p1',p2') -> (equal_probaf p1 p1') && (equal_probaf p2 p2')
  | Div(p1,p2), Div(p1',p2') -> (equal_probaf p1 p1') && (equal_probaf p2 p2')
  | Max l, Max l' -> equal_lists equal_probaf l l'
  | Maxlength(n,t),Maxlength(n',t') -> (n == n') && (equal_terms t t')
  | TypeMaxlength(t),TypeMaxlength(t') -> t == t'
  | Length(f,l), Length(f',l') -> (f == f') && (equal_lists equal_probaf l l')
  | EpsFind, EpsFind -> true
  | EpsRand t, EpsRand t' -> t == t'
  | PColl1Rand t, PColl1Rand t' -> t == t'
  | PColl2Rand t, PColl2Rand t' -> t == t'
  | _ -> false

let equal_elsefind_facts (bl1,def_list1,t1) (bl2,def_list2,t2) =
  equal_lists (==) bl1 bl2 && 
  equal_def_lists def_list1 def_list2 && 
  equal_terms t1 t2

(* syntactic equality, possibly modulo associativity and commutativity,
   but no other equations *)

let rec dec_prod f t =
  match t.t_desc with
    FunApp(f',[t1;t2]) when f' == f ->
      (dec_prod f t1) @ (dec_prod f t2)
  | _ -> [t]

let rec synt_equal_terms t1 t2 =
  match (t1.t_desc, t2.t_desc) with
    Var(b1,l1),Var(b2,l2) ->
      (b1 == b2) && (List.for_all2 equal_terms l1 l2)
  | ReplIndex b1, ReplIndex b2 -> b1 == b2
  | FunApp(f1,[t1;t1']),FunApp(f2,[t2;t2']) when f1 == f2 && f1.f_eq_theories = Commut ->
      (* Commutative function symbols *)
      ((synt_equal_terms t1 t2) && (synt_equal_terms t1' t2')) ||
      ((synt_equal_terms t1 t2') && (synt_equal_terms t1' t2))
  | FunApp(f1,[_;_]),FunApp(f2,[_;_]) when f1 == f2 && 
      f1.f_eq_theories != NoEq && f1.f_eq_theories != Commut ->
      (* f1 is a binary function with an equational theory that is
	 not commutativity nor inverse -> it is a product-like function *)
	begin
	  let l1 = dec_prod f1 t1 in
	  let l2 = dec_prod f1 t2 in
	  match f1.f_eq_theories with 
	    NoEq | Commut -> Parsing_helper.internal_error "Terms.synt_equal_terms: cases NoEq, Commut should have been eliminated"
	  | AssocCommut | AssocCommutN _ | CommutGroup _ | ACUN _ ->
	      (* Commutative equational theories: test equality up to ordering *)
	      (List.length l1 == List.length l2) &&
	      (equal_up_to_order synt_equal_terms l1 l2)
	  | Assoc | AssocN _ | Group _  ->
	      (* Non-commutative equational theories: test equality in the same order *)
	      equal_lists synt_equal_terms l1 l2		
	end
  | FunApp(f1,l1),FunApp(f2,l2) ->
      (f1 == f2) && (List.for_all2 synt_equal_terms l1 l2)
  | TestE(t1,t2,t3), TestE(t1',t2',t3') ->
      (synt_equal_terms t1 t1') && (synt_equal_terms t2 t2') && (synt_equal_terms t3 t3')
  | FindE(l,t3,find_info),FindE(l',t3',find_info') ->
      (* Could do modulo renaming of bl and bl'! *)
      (equal_lists (fun (bl,def_list,t1,t2) (bl',def_list',t1',t2') ->
	(equal_lists (fun (b1,b2) (b1', b2') -> (b1 == b1') && (b2 == b2')) bl bl') && 
	(equal_def_lists def_list def_list') && 
	(synt_equal_terms t1 t1') && (synt_equal_terms t2 t2')) l l') && 
      (synt_equal_terms t3 t3') &&
      (find_info == find_info')
  | LetE(pat, t1, t2, topt), LetE(pat', t1', t2', topt') ->
      (synt_equal_pats pat pat') &&
      (synt_equal_terms t1 t1') &&
      (synt_equal_terms t2 t2') &&
      (match topt, topt' with
	None, None -> true
      |	Some t3, Some t3' -> synt_equal_terms t3 t3'
      |	_ -> false)
  | ResE(b,t), ResE(b',t') ->
      (b == b') && (synt_equal_terms t t')
  | EventAbortE(f), EventAbortE(f') -> 
      f == f'
  | EventE(t,p), EventE(t',p') ->
      (synt_equal_terms t t') &&
      (synt_equal_terms p p')
  | (GetE _, GetE _) | (InsertE _, InsertE _) ->
      Parsing_helper.internal_error "get and insert should not occur in synt_equal_terms"
  | _ -> false

and synt_equal_pats p1 p2 =
  match p1,p2 with
    PatVar b, PatVar b' -> b == b'
  | PatTuple (f,l), PatTuple (f',l') -> (f == f') && (List.for_all2 synt_equal_pats l l')
  | PatEqual t, PatEqual t' -> synt_equal_terms t t'
  | _ -> false


(* Compute a product *)

let rec make_prod prod = function
    [] -> 
      begin
	(* Look for the neutral element of the product *)
	match prod.f_eq_theories with
	  Group(_,_,n) | CommutGroup(_,_,n) | AssocN(_,n) 
	| AssocCommutN(_,n) | ACUN(_,n) -> 
	    build_term_type (snd n.f_type) (FunApp(n, []))
	| _ -> 
	    Parsing_helper.internal_error "Empty product impossible without a neutral element"
      end
  | [t] -> t
  | t::l -> build_term_type t.t_type (FunApp(prod, [t; make_prod prod l]))
  
(* [make_inv_prod eq_th l1 t l2] computes the product 
   inv (product (List.rev l1)) * t * inv(product l2) *)

let make_inv_prod eq_th l1 t l2 =
  match eq_th with
    ACUN(prod, neut) ->
      make_prod prod (l1 @ (t::l2))
  | Group(prod, inv, neut) | CommutGroup(prod, inv, neut) ->
      let compute_inv = compute_inv try_no_var_id (ref false) (prod, inv, neut) in
      let inv_rev_l1 = List.map compute_inv l1 in
      let inv_l2 = List.map compute_inv (List.rev l2) in
      make_prod prod (inv_rev_l1 @ (t :: inv_l2))
  | _ -> Parsing_helper.internal_error "No product in make_inv_prod"


(* [is_subterm t1 t2] returns [true] when [t1] is a subterm of [t2] *)

let rec is_subterm t1 t2 =
  if equal_terms t1 t2 then true else
  match t2.t_desc with
    Var(_,l) | FunApp(_,l) -> List.exists (is_subterm t1) l
  | ReplIndex _ -> false
  | _ -> Parsing_helper.internal_error "is_subterm only for Var/FunApp/ReplIndex terms"

(* Compute the length of the longest common prefix *)

let rec len_common_prefix l1 l2 =
  match (l1, l2) with
    [], _ | _, [] -> 0
  | (a1::l1,a2::l2) ->
      if equal_terms a1 a2 then 1 + len_common_prefix l1 l2 else 0

(* Compute the length of the longest common suffix *)

let len_common_suffix l1 l2 =
  len_common_prefix (List.rev l1) (List.rev l2)

(* Term from pattern *)

let rec term_from_pat = function
    PatVar b -> term_from_binder b
  | PatTuple (f,l) -> 
      build_term_type (snd f.f_type) (FunApp(f, List.map term_from_pat l))
  | PatEqual t -> t

(* Type of a pattern *)

let get_type_for_pattern = function
    PatVar b -> b.btype
  | PatTuple(f,_) -> snd f.f_type
  | PatEqual t -> t.t_type

(* Count the number of variables in a term *)

let rec list_add f = function
    [] -> 0
  | a::l -> f a + list_add f l

let rec count_var t =
  match t.t_desc with
    FunApp(f,l) -> list_add count_var l
  | Var _ -> 1
  | ReplIndex _ -> 0
  | _ -> Parsing_helper.internal_error "Only Var/FunApp/ReplIndex expected in count_var"

let rec size t =
  match t.t_desc with
    FunApp(_,l) | Var(_,l) -> list_add size l
  | ReplIndex _ -> 1
  | _ -> Parsing_helper.internal_error "Only Var/FunApp/ReplIndex expected in size"

(* New variable name *)

(* These functions are used to guarantee the freshness of new identifiers 
   Each identifier is represented by a pair (s,n):
   - if n = 0, then (s,n) is displayed s
   - otherwise, (s,n) is displayed s_n
   Invariant: n has at most 9 digits (supports one billion of variables);
   when n = 0, s is never of the form N_xxx where xxx is a non-zero
   number of at most 9 digits. 
   This guarantees that for each identifier, (s,n) is unique.
   We guarantee the freshness by changing the value of n
*)

(* [get_id_n s] converts [s] into a pair [(s',n)] displayed [s] *)

let get_id_n s =
  let l = String.length s in
  if '0' <= s.[l-1] && s.[l-1] <= '9' then
    let rec underscore_number n = 
      if (n > 0) && (l-n<=10) then
        if s.[n] = '_' then
	  n 
        else if '0' <= s.[n] && s.[n] <= '9' then
	  underscore_number (n-1)
	else
	  raise Not_found
      else
	raise Not_found
    in
    try 
      let pos_underscore = underscore_number (l-2) in
      if s.[pos_underscore+1] = '0' then raise Not_found;
      let n' = int_of_string (String.sub s (pos_underscore+1) (l-pos_underscore-1)) in
      let s' = String.sub s 0 pos_underscore in
      (* print_string (s ^ " split into " ^ s' ^ "  " ^ (string_of_int n') ^ "\n"); *)
      (s',n')
    with Not_found ->
      (* s does not end with _xxx *)
      (s,0)
  else
    (s,0)

(* Counter incremented to generate fresh variable names.
   We use a different counter for each string name,
   stored in a hash table. *)
let vcounter = ref (Hashtbl.create 7)

type var_num_state = (string, int) Hashtbl.t

let get_var_num_state() = Hashtbl.copy (!vcounter)

let set_var_num_state x =
  vcounter := x
    
(* The maximum xxx such N_xxx occurs and xxx does not come from vcounter *)
let max_source_idx = ref 0

(* Set of pairs (s,n) used, stored in a hash table. 
   All pairs (s,n) where 0 < n <= !vcounter(s) are considered as always used,
   so we need not add them to the hash table.
   All pairs (s,n) in [used_ids] satisfy [n <= !max_source_idx] *)
let used_ids = Hashtbl.create 7

(* [record_id s ext] records the identifier [s] so that it will not be reused elsewhere.
   [record_id] must be called only before calls to [fresh_id] or [new_var_name], so that
   [s] cannot collide with an identifier generated by [fresh_id] or [new_var_name].
   Moreover, !vcounter(s) = 0, there are no pairs (s,n) with 0 < n <= !vcounter(s),
   so the used pairs are exactly those in the hash table used_ids. *)

let record_id s ext =
  let (_,n) as s_n = get_id_n s in
  if n > !max_source_idx then max_source_idx := n;
  if Hashtbl.mem used_ids s_n then
    ()
  else
    Hashtbl.add used_ids s_n ()
    
(* [new_var_name s] creates a fresh pair [(s,n)] using [!vcounter(s)]. *) 

let rec new_var_name_counter counter s =
  let n = counter+1 in
  if (n <= !max_source_idx) && (Hashtbl.mem used_ids (s,n)) then
    new_var_name_counter n s
  else
    n

let new_var_name s =
  let counter = (try Hashtbl.find (!vcounter) s with Not_found -> 0) in
  let counter' = new_var_name_counter counter s in
  Hashtbl.replace (!vcounter) s counter';
  (s, counter')
       
(* [fresh_id s] creates a fresh identifier [s'] corresponding to
   identifier [s], preferably [s] itself. If [s] is already used,
   create a fresh identifier by changing the number suffix of [s], or
   adding a number suffix to [s] if there is none, using [new_var_name] *)

let fresh_id s =
  let ((s',n) as s_n) = get_id_n s in
  let counter = (try Hashtbl.find (!vcounter) s' with Not_found -> 0) in
  if ((n != 0) && (n <= counter)) || (Hashtbl.mem used_ids s_n) then
    let n' = new_var_name_counter counter s' in
    Hashtbl.replace (!vcounter) s' n';
    s' ^ "_" ^ (string_of_int n')
  else
    begin
      if n > !max_source_idx then max_source_idx := n;
      Hashtbl.add used_ids s_n ();
      s
    end

(* [fresh_id_keep_s s] creates a fresh pair [(s,n)] corresponding to 
   identifier [s], preferably the pair [(s,0)], which displays exactly as [s],
   if possible, that is, if [s] does not end with _number and this pair is
   not already used. Otherwise, create a fresh pair using [new_var_name] *) 

let fresh_id_keep_s s =
  let ((s',n) as s_n) = get_id_n s in
  if (n != 0) || (Hashtbl.mem used_ids s_n) then 
    new_var_name s'
  else
    begin
      (* n = 0, so no need to increase max_source_idx, it is already >= n *)
      Hashtbl.add used_ids s_n ();
      s_n
    end

let new_binder b0 =
  (* Invariant: 
     if vname = 0, then sname never contains N_xxx where xxx is a non-zero 
     number of at most 9 digits. As a consequence, we don't need to split 
     v.sname using fresh_id_n. *)
  let (s, n) = new_var_name b0.sname in
  { sname = s;
    vname = n;
    btype = b0.btype;
    args_at_creation = b0.args_at_creation;
    def = b0.def;
    link = NoLink;
    count_def = 0;
    root_def_array_ref = false;
    root_def_std_ref = false;
    array_ref = false;
    std_ref = false;
    count_array_ref = 0;
    count_exclude_array_ref = 0;
    priority = 0 }

let new_repl_index b0 =
  let (s, n) = new_var_name b0.ri_sname in
  { ri_sname = s;
    ri_vname = n;
    ri_type = b0.ri_type;
    ri_link = NoLink }

let create_binder_internal s n t a =
  { sname = s;
    vname = n;
    btype = t;
    args_at_creation = a;
    def = [];
    link = NoLink;
    count_def = 0;
    root_def_array_ref = false;
    root_def_std_ref = false;
    array_ref = false;
    std_ref = false;
    count_array_ref = 0;
    count_exclude_array_ref = 0;
    priority = 0 }

let create_binder s t a =
  let (s', n) = fresh_id_keep_s s in
  create_binder_internal s' n t a

let create_binder0 s t a =
  let (s', n) = get_id_n s in
  create_binder_internal s' n t a

let create_repl_index s t =
  let (s', n) = fresh_id_keep_s s in  
  { ri_sname = s';
    ri_vname = n;
    ri_type = t;
    ri_link = NoLink }

(* Create a term containing general variables that corresponds to a pattern *)

exception NonLinearPattern

let gvar_name = "?x"

let create_gvar b = 
  let b' = create_binder gvar_name b.btype [] in
  let rec st_node = { above_node = st_node; 
		      binders = []; 
		      true_facts_at_def = []; 
		      def_vars_at_def = []; 
		      elsefind_facts_at_def = [];
		      future_binders = []; future_true_facts = []; 
		      definition = DGenVar;
		      definition_success = DGenVar} 
  in
  b'.def <- [st_node];
  b'

let gen_term_from_pat pat = 
  let rec gterm_from_pat = function
      PatVar b ->
	let b' = create_gvar b in
	if b.link != NoLink then raise NonLinearPattern;
	let bt = term_from_binder b' in
	link b (TLink bt);
	bt
    | PatTuple (f,l) -> 
	build_term_type (snd f.f_type) (FunApp(f, List.map gterm_from_pat l))
    | PatEqual t -> t
  in
  auto_cleanup (fun () -> gterm_from_pat pat)

let rec single_occ_gvar seen_list t = 
  match t.t_desc with
    Var (b,l) -> 
      if b.sname == gvar_name then
	begin
	  if List.memq b (!seen_list) then false else
	  begin
	    seen_list := b :: (!seen_list);
	    true
	  end
	end
      else
	List.for_all (single_occ_gvar seen_list) l
  | ReplIndex _ -> true
  | FunApp(_,l) -> List.for_all (single_occ_gvar seen_list) l
  | _ -> Parsing_helper.internal_error "Only Var/FunApp/ReplIndex expected in single_occ_gvar"



(* Find out whether a term is a conjunction of "defined(...)" conditions *)

let mem_binderref br l = List.exists (equal_binderref br) l

let add_binderref a accu =
  if mem_binderref a (!accu) then () else accu := a :: (!accu)

let setminus_binderref s1 s2 =
  List.filter (fun br -> not (mem_binderref br s2)) s1

let inter_binderref s1 s2 =
  List.filter (fun br -> mem_binderref br s2) s1

let union_binderref s1 s2 = 
  s2 @ (setminus_binderref s1 s2)

(* get def_list subterms *)

let rec get_deflist_subterms accu t =
  match t.t_desc with
    Var(b,l) -> add_binderref (b,l) accu
  | ReplIndex i -> ()
  | FunApp(f,l) -> List.iter (get_deflist_subterms accu) l
	(* The cases TestE, FindE, LetE, RestE, EventAbortE are probably not used *)
  | TestE(t1,t2,t3) -> 
      get_deflist_subterms accu t1;
      get_deflist_subterms accu t2;
      get_deflist_subterms accu t3
  | FindE(l0,t3, find_info) ->
      List.iter (fun (bl, def_list, t, t1) ->
	get_deflist_subterms accu t;
	get_deflist_subterms accu t1
	) l0;
      get_deflist_subterms accu t3
  | LetE(pat,t1,t2,topt) ->
      get_def_list_pat accu pat;
      get_deflist_subterms accu t1;
      get_deflist_subterms accu t2;
      begin
	match topt with
	  None -> ()
	| Some t3 -> get_deflist_subterms accu t3
      end
  | ResE(b,t) -> get_deflist_subterms accu t
  | EventAbortE f -> ()
  | EventE _ | InsertE _ | GetE _ ->
      Parsing_helper.internal_error "event, get, and insert should not occur in get_deflist_subterms"

and get_def_list_pat accu = function
    PatVar _ -> ()
  | PatTuple(f,l) -> List.iter (get_def_list_pat accu) l
  | PatEqual t -> get_deflist_subterms accu t

(* Change the occurrences and make sure nodes associated with Find
   are distinct for different occurrences of Find *)

let rec move_occ_term t = 
  let x_occ = new_occ() in
  let desc = 
    match t.t_desc with
	Var(b,l) -> Var(b, List.map move_occ_term l)
      |	ReplIndex i -> ReplIndex i
      |	FunApp(f,l) -> FunApp(f, List.map move_occ_term l)
      |	TestE(t1,t2,t3) -> 
	  let t1' = move_occ_term t1 in
	  let t2' = move_occ_term t2 in
	  let t3' = move_occ_term t3 in 
	  TestE(t1', t2', t3')
      |	FindE(l0,t3, find_info) -> 
	  let l0' = List.map (fun (bl,def_list,t1,t2) ->
	    let def_list' = List.map move_occ_br def_list in
	    let t1' = move_occ_term t1 in
	    let t2' = move_occ_term t2 in
	    (bl, def_list', t1', t2')) l0
	  in
	  let t3' = move_occ_term t3 in
	  FindE(l0', t3', find_info)
      |	LetE(pat, t1, t2, topt) ->
	  let pat' = move_occ_pat pat in
	  let t1' = move_occ_term t1 in
	  let t2' = move_occ_term t2 in
	  let topt' = match topt with
		 None -> None
	       | Some t3 -> Some (move_occ_term t3)
	  in
	  LetE(pat', t1', t2', topt')
      |	ResE(b,t) ->
	  ResE(b, move_occ_term t)
      |	EventAbortE f -> EventAbortE f 
      | EventE(t,p) ->
	  let t' = move_occ_term t in
	  let p' = move_occ_term p in
	  EventE(t', p')
      | GetE(tbl,patl,topt,p1,p2) -> 
	  let patl' = List.map move_occ_pat patl in
	  let topt' = 
	    match topt with 
	      Some t -> Some (move_occ_term t) 
	    | None -> None
	  in
	  let p1' = move_occ_term p1 in
	  let p2' = move_occ_term p2 in	  
          GetE(tbl,patl',topt',p1', p2')
      | InsertE (tbl,tl,p) -> 
	  let tl' = List.map move_occ_term tl in
	  let p' = move_occ_term p in
          InsertE(tbl, tl', p')
  in
  { t_desc = desc;
    t_type = t.t_type;
    t_occ = x_occ;
    t_max_occ = !occ;
    t_loc = Parsing_helper.dummy_ext;
    t_incompatible = map_empty;
    t_facts = None }

and move_occ_pat = function
    PatVar b -> PatVar b
  | PatTuple (f,l) -> PatTuple(f,List.map move_occ_pat l)
  | PatEqual t -> PatEqual(move_occ_term t)

and move_occ_br (b,l) = (b, List.map move_occ_term l)

let rec move_occ_process p = 
  let x_occ = new_occ() in
  let desc = 
    match p.i_desc with
	Nil -> Nil
      | Par(p1,p2) -> 
	  let p1' = move_occ_process p1 in
	  let p2' = move_occ_process p2 in
	  Par(p1', p2')
      | Repl(b,p) -> Repl(b, move_occ_process p)
      | Input((c,tl),pat,p) ->
	  let tl' = List.map move_occ_term tl in
	  let pat' = move_occ_pat pat in
	  let p' = move_occ_oprocess p in
	  Input((c, tl'), pat', p')
  in
  { i_desc = desc;
    i_occ = x_occ; 
    i_max_occ = !occ;
    i_incompatible = map_empty; 
    i_facts = None }

and move_occ_oprocess p =
  let x_occ = new_occ() in
  let desc = 
    match p.p_desc with
	Yield -> Yield
      |	EventAbort f -> EventAbort f
      | Restr(b,p) -> Restr(b, move_occ_oprocess p)
      | Test(t,p1,p2) -> 
	  let t' = move_occ_term t in
	  let p1' = move_occ_oprocess p1 in
	  let p2' = move_occ_oprocess p2 in
	  Test(t', p1', p2')
      | Find(l0, p2, find_info) -> 
	  let l0' = List.map (fun (bl, def_list, t, p1) -> 
	    let def_list' = List.map move_occ_br def_list in
	    let t' = move_occ_term t in
	    let p1' = move_occ_oprocess p1 in
	    (bl, def_list', t', p1')) l0
	  in
	  let p2' = move_occ_oprocess p2 in
	  Find(l0', p2', find_info)
      | Let(pat,t,p1,p2) ->
	  let pat' = move_occ_pat pat in
	  let t' = move_occ_term t in
	  let p1' = move_occ_oprocess p1 in
	  let p2' = move_occ_oprocess p2 in	  
	  Let(pat', t', p1', p2')
      | Output((c,tl),t2,p) ->
	  let tl' = List.map move_occ_term tl in
	  let t2' = move_occ_term t2 in
	  let p' = move_occ_process p in
	  Output((c, tl'), t2', p')
      | EventP(t,p) ->
	  let t' = move_occ_term t in
	  let p' = move_occ_oprocess p in
	  EventP(t', p')
      | Get(tbl,patl,topt,p1,p2) -> 
	  let patl' = List.map move_occ_pat patl in
	  let topt' = 
	    match topt with 
	      Some t -> Some (move_occ_term t) 
	    | None -> None
	  in
	  let p1' = move_occ_oprocess p1 in
	  let p2' = move_occ_oprocess p2 in	  
          Get(tbl,patl',topt',p1', p2')
      | Insert (tbl,tl,p) -> 
	  let tl' = List.map move_occ_term tl in
	  let p' = move_occ_oprocess p in
          Insert(tbl, tl', p')
  in
  { p_desc = desc;
    p_occ = x_occ;
    p_max_occ = !occ;
    p_incompatible = map_empty; 
    p_facts = None }

let move_occ_process p =
  occ := 0;
  move_occ_process p

(* Copy a term
   Preserves occurrences of the original term. This is useful so that
   we can designate variables by occurrences in simplify coll_elim;
   otherwise, occurrences would be modified before they are tested.

   Several transformations are possible
 *)

type copy_transf =
    Links_RI (* Substitutes replication indices that are linked *)
  | Links_Vars 
     (* Substitutes variables that are linked, when their arguments are args_at_creation
	The linked variables are supposed to be defined above the copied terms/processes *)
  | Links_RI_Vars (* Combines Links_RI and Links_Vars *)
  | OneSubst of binder * term * bool ref 
     (* OneSubst(b,t,changed) substituted b[b.args_at_creation] with t.
	Sets changed to true when such a substitution has been done.
	b is assumed to be defined above the copied terms/processes *) 
  | OneSubstArgs of binderref * term 
     (* OneSubstArgs(br,t) substitutes t for the accesses br.
	It is assumed that br and t are already guaranteed to be defined,
	so br is removed from defined conditions if it occurs. *)
  | Rename of term list * binder * binder
     (* Rename(args, b, b') replaces array accesses b[args] with b'[args] *)
  | Links_Vars_Args of (binder * binder) list
     (* Links_Vars_Args(replacement_def_list) substitutes variables that are 
	linked, for any arguments: if b is linked to M, b[l] is
	replaced with M{l/b.args_at_creation}. replacement_def_list defines
	variable replacements to do in defined conditions. *)

(* Helper function for copy_def_list in case Links_Vars_Args *)

let rec get_remassign_subterms accu (b,l) =
  List.iter (get_remassign_terms accu) l;
  match b.link with
    NoLink -> ()
  | TLink _ -> add_binderref (b,l) accu

and get_remassign_terms accu t =
  match t.t_desc with
    Var(b,l) -> get_remassign_subterms accu (b,l)
  | ReplIndex(b) -> ()
  | FunApp(f,l) -> List.iter (get_remassign_terms accu) l
  | _ -> Parsing_helper.internal_error "if/let/find forbidden in defined conditions of find"

(* Copy functions *)

let rec copy_binder transf (b,l) =
  match transf with
    Rename(cur_array, b0, b0') ->
      let l' = List.map (copy_term transf) l in
      if (b == b0) && (List.for_all2 equal_terms l cur_array) then
	(b0', l')
      else
	(b,l')
  | _ -> 
      Parsing_helper.internal_error "copy_binder allowed only with transformation Rename"

and copy_term transf t = 
  match t.t_desc with
    ReplIndex b -> 
      begin
	match transf with
	  Links_Vars | OneSubst _ | OneSubstArgs _ | Rename _ | Links_Vars_Args _ -> t
	| Links_RI | Links_RI_Vars -> 
	    match b.ri_link with
	      NoLink -> t
	    | TLink t' -> move_occ_term t' (* Same comment as in case OneSubst *)
      end
  | Var(b,l) ->
      begin
        match transf with
          OneSubst(b',t',changed) ->
            if (b == b') && (is_args_at_creation b l) then
	      begin
		changed := true;
                move_occ_term t' (* This just makes a copy of the same term -- This is needed
				    to make sure that all terms are physically distinct,
				    which is needed to store facts correctly in
				    [Terms.build_def_process]. *)
	      end
            else
	      build_term2 t (Var(b,List.map (copy_term transf) l))
	| OneSubstArgs((b',l'), t') ->
	    if (b == b') && (List.for_all2 equal_terms l l') then
	      move_occ_term t' (* Same comment as in case OneSubst *)
	    else
	      build_term2 t (Var(b,List.map (copy_term transf) l))
	| Rename _ ->
	    let (b',l') = copy_binder transf (b,l) in
	    build_term2 t (Var(b',l'))
	| Links_Vars_Args _ -> 
	    begin
	      let l' = List.map (copy_term transf) l in
	      match b.link with
		NoLink -> build_term2 t (Var(b,l'))
	      | TLink t ->
		  let t = copy_term transf t in
                  (* Rename array indices *)
		  subst b.args_at_creation l' t
	    end
	| Links_RI ->  build_term2 t (Var(b,List.map (copy_term transf) l))
	| Links_Vars | Links_RI_Vars ->
	    match b.link with
	      TLink t' when is_args_at_creation b l -> move_occ_term t' (* Same comment as in case OneSubst *)
	    | _ -> build_term2 t (Var(b,List.map (copy_term transf) l))
      end
  | FunApp(f,l) ->
      build_term2 t (FunApp(f, List.map (copy_term transf) l))
  | TestE(t1,t2,t3) ->
      build_term2 t (TestE(copy_term transf t1,
				 copy_term transf t2, 
				 copy_term transf t3))
  | LetE(pat, t1, t2, topt) ->
      let pat' = copy_pat transf pat in
      let t1' = copy_term transf t1 in
      let t2' = copy_term transf t2 in
      let topt' = match topt with
	None -> None
      |	Some t3 -> Some (copy_term transf t3)
      in
      build_term2 t (LetE(pat', t1', t2', topt'))
  | FindE(l0, t3, find_info) -> 
      let l0' = List.map (fun (bl, def_list, t1, t2) ->
	(bl,
	 copy_def_list transf def_list,
	 copy_term transf t1,
	 copy_term transf t2)) l0
      in
      build_term2 t (FindE(l0', copy_term transf t3, find_info))
  | ResE(b,t1) ->
      build_term2 t (ResE(b, copy_term transf t1))
  | EventAbortE(f) ->
      build_term2 t (EventAbortE(f))
  | EventE(t1,p) ->
      build_term2 t (EventE(copy_term transf t1, 
			    copy_term transf p))
  | GetE(tbl, patl, topt, p1, p2) ->
      let topt' =
	match topt with
	  None -> None
	| Some t -> Some (copy_term transf t)
      in
      build_term2 t (GetE(tbl, List.map (copy_pat transf) patl,
			  topt',
			  copy_term transf p1,
			  copy_term transf p2))
  | InsertE(tbl,tl,p) ->
      build_term2 t (InsertE(tbl, List.map (copy_term transf) tl,
			     copy_term transf p))

and copy_def_list transf def_list =
  match transf with
    OneSubst(b',t',changed) ->
      (* When removing assignments in_scope_only, and I am removing
         assignments on b, I know that b is in scope, so
         b[b.args_at_creation] is always defined, and I can remove that
         defined condition *)
      List.map (fun (b,l) ->
        (b, List.map (copy_term transf) l)) 
       (List.filter (fun (b,l) ->
          not ((b == b') && (is_args_at_creation b l))) def_list)
  | OneSubstArgs((b',l'), t') ->
      List.map (fun (b,l) ->
        (b, List.map (copy_term transf) l)) 
       (List.filter (fun (b,l) ->
          not ((b == b') && (List.for_all2 equal_terms l l'))) def_list)
  | Rename _ ->
      List.map (copy_binder transf) def_list
  | Links_Vars_Args(replacement_def_list) ->
      (* Update def_list, following removal of assignments *)
      (* 1: root_remassign = subterms of def_list whose root is
         a variable on which we remove assignments *)
      let root_remassign = ref [] in
      List.iter (get_remassign_subterms root_remassign) def_list;
      (* 2: not_root_remassign = elements of def_list whose root is
         not a variable on which we remove assignments *)
      let not_root_remassign =
	List.filter (fun (b,l) ->
	  match b.link with
	    NoLink -> true
	  | TLink _ -> false
	      ) def_list 
      in
      (* 3: compute the new def_list *)
      let accu = ref 
	  (List.map (fun (b,l) -> (b, List.map (copy_term transf) l)) 
	     ((!root_remassign) @ not_root_remassign))
      in
      List.iter (fun br -> get_deflist_subterms accu
	(copy_term transf (term_from_binderref br))) (!root_remassign);
      (* 4: replace defined(b) with defined(b') when b was used
	 only in defined conditions and it is defined when b' is defined *)
      List.map (fun (b,l) ->
	try 
	  (List.assq b replacement_def_list, l)
	with Not_found ->
	  (b,l)) (!accu)
  | Links_RI -> List.map (fun (b,l) -> (b, List.map (copy_term transf) l)) def_list
  | Links_Vars | Links_RI_Vars ->
      (* When we substitute b (b.link != NoLink), we know that b is in scope, so
	 we can remove the condition that b is defined. *)
      List.map (fun (b,l) ->
        (b, List.map (copy_term transf) l)) 
       (List.filter (fun (b,l) ->
          not ((b.link != NoLink) && (is_args_at_creation b l))) def_list)
      
and copy_pat transf = function
  PatVar b -> PatVar b
| PatTuple (f,l) -> PatTuple(f,List.map (copy_pat transf) l)
| PatEqual t -> PatEqual(copy_term transf t)

(* Compute term { l / cur_array } *)

and subst cur_array l term =
  List.iter2 (fun b t -> b.ri_link <- (TLink t)) cur_array l;
  let term' = copy_term Links_RI term in
  List.iter (fun b -> b.ri_link <- NoLink) cur_array;
  term'

let copy_elsefind (bl, def_vars, t) = 
  (bl, copy_def_list Links_RI def_vars, copy_term Links_RI t)

let rec copy_process transf p = 
  iproc_from_desc3 p (
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) ->
      Par(copy_process transf p1,
	  copy_process transf p2)
  | Repl(b,p) ->
      Repl(b, copy_process transf p)
  | Input((c,tl), pat, p) ->
      Input((c, List.map (copy_term transf) tl),
	    copy_pat transf pat,
	    copy_oprocess transf p))

and copy_oprocess transf p =
  oproc_from_desc3 p (
  match p.p_desc with
    Yield -> Yield
  | EventAbort f -> EventAbort f
  | Restr(b, p) ->
      Restr(b, copy_oprocess transf p)
  | Test(t,p1,p2) ->
      Test(copy_term transf t, 
	   copy_oprocess transf p1,
           copy_oprocess transf p2)
  | Let(pat, t, p1, p2) ->
      Let(copy_pat transf pat, 
	  copy_term transf t, 
	  copy_oprocess transf p1,
          copy_oprocess transf p2)
  | Output((c,tl),t2,p) ->
      Output((c, List.map (copy_term transf) tl),
	     copy_term transf t2,
	     copy_process transf p)
  | Find(l0, p2, find_info) ->
      let l0' = List.map (fun (bl, def_list, t, p1) ->
	(bl, 
	 copy_def_list transf def_list, 
	 copy_term transf t,
	 copy_oprocess transf p1)) l0 in
      Find(l0', copy_oprocess transf p2, find_info)
  | EventP(t,p) ->
      EventP(copy_term transf t, 
	     copy_oprocess transf p)
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear in Terms.copy_oprocess"
  )

(* Compute element{l/cur_array}, where element is def_list, simp_facts
   Similar to what subst does for terms. *)

let subst_def_list cur_array l def_list =
  List.iter2 (fun b t -> b.ri_link <- (TLink t)) cur_array l;
  let def_list' = copy_def_list Links_RI def_list in
  List.iter (fun b -> b.ri_link <- NoLink) cur_array;
  def_list'

let subst_else_find cur_array l ((bl, _, _) as elsefind_fact) =
  List.iter2 (fun b t -> if not (List.memq b bl) then b.ri_link <- (TLink t)) cur_array l;
  let elsefind_fact' = copy_elsefind elsefind_fact in
  List.iter (fun b -> if not (List.memq b bl) then b.ri_link <- NoLink) cur_array;
  elsefind_fact'

let subst_simp_facts cur_array l (substs, facts, elsefind) =
  List.iter2 (fun b t -> b.ri_link <- (TLink t)) cur_array l;
  let substs' = List.map (copy_term Links_RI) substs in
  let facts' = List.map (copy_term Links_RI) facts in
  List.iter (fun b -> b.ri_link <- NoLink) cur_array;
  (substs', facts', List.map (subst_else_find cur_array l) elsefind)


(* Substitution of v[v.args_at_creation] only
   Preserves occurrences of the original term. This is useful so that
   we can designate variables by occurrences in simplify coll_elim;
   otherwise, occurrences would be modified before they are tested. *)

let subst3 subst t =
  auto_cleanup (fun () ->
    List.iter (fun (b,t') -> link b (TLink t')) subst;
    copy_term Links_Vars t)

let subst_def_list3 subst def_list =
  auto_cleanup (fun () ->
    List.iter (fun (b,t') -> link b (TLink t')) subst;
    copy_def_list Links_Vars def_list)

let subst_oprocess3 subst p =
  auto_cleanup (fun () ->
    List.iter (fun (b,t') -> link b (TLink t')) subst;
    copy_oprocess Links_Vars p)

(* [find_some f l] returns [f a] for the first element
   [a] of the list [l] such that [f a <> None].
   It returns [None] if [f a = None] for all [a] in [l]. *)

let rec find_some f = function
    [] -> None
  | a::l ->
      match f a with
	None -> find_some f l
      |	x -> x

(* [replace l1 l0 t] replaces all terms in [l1] with the 
   corresponding term in [l0] inside [t] *)

let rec assoc l1 l0 t =
  match l1, l0 with
    [], [] -> raise Not_found
  | a1::l1, a0::l0 ->
      if equal_terms a1 t then a0 else assoc l1 l0 t
  | _ ->
      Parsing_helper.internal_error "Lists should have the same length in Terms.assoc"
    
let rec replace l1 l0 t =
  try
    assoc l1 l0 t
  with Not_found ->
    match t.t_desc with
      FunApp(f,l) ->
	build_term2 t (FunApp(f, List.map (replace l1 l0) l))
    | ReplIndex _ -> t
    | Var(b,l) ->
	build_term2 t (Var(b, List.map (replace l1 l0) l))
    | _ -> Parsing_helper.internal_error "Var/Fun/ReplIndex expected in Terms.replace"

(* Check whether a term t refers to a binder b0 *)

let no_def = ref false

let rec refers_to b0 t = 
  (match t.t_desc with
    Var (b,l) -> 
      (b == b0) ||
      (match b.link with
	 TLink t -> refers_to b0 t
      | _ -> false)
  | _ -> false) ||
  (exists_subterm (refers_to b0) (refers_to_br b0) (refers_to_pat b0) t)

and refers_to_br b0 (b,l) =
  ((not (!no_def)) && (b == b0)) || List.exists (refers_to b0) l

and refers_to_pat b0 pat =
  exists_subpat (refers_to b0) (refers_to_pat b0) pat

let rec refers_to_process b0 p =
  exists_subiproc (refers_to_process b0) (fun (c,tl) pat p ->
    (List.exists (refers_to b0) tl) || (refers_to_pat b0 pat) ||
    (refers_to_oprocess b0 p)
      ) p

and refers_to_oprocess b0 p =
  exists_suboproc (refers_to_oprocess b0) (refers_to b0) (refers_to_br b0)
    (refers_to_pat b0) (refers_to_process b0) p

let rec refers_to_fungroup b = function
    ReplRestr(_,_,funlist) ->
      List.exists (refers_to_fungroup b) funlist
  | Fun(_,_,res,_) -> refers_to b res

let refers_to_nodef b0 t =
  no_def := true;
  let res = refers_to b0 t in
  no_def := false;
  res

let refers_to_process_nodef b0 p =
  no_def := true;
  let res = refers_to_oprocess b0 p in
  no_def := false;
  res

(* Extract defined variables from a pattern *)

let rec vars_from_pat accu = function
    PatVar b -> b::accu
  | PatEqual t -> accu
  | PatTuple (f,l) -> vars_from_pat_list accu l

and vars_from_pat_list accu = function
    [] -> accu
  | (a::l) -> vars_from_pat_list (vars_from_pat accu a) l


(* Test if a variable occurs in a pattern *)

let rec occurs_in_pat b = function
    PatVar b' -> b' == b
  | PatTuple (f,l) -> List.exists (occurs_in_pat b) l
  | PatEqual t -> false

(* Testing boolean values *)

let is_true t =
  match t.t_desc with
    FunApp(f,[]) when f == Settings.c_true -> true
  | _ -> false

let is_false t =
  match t.t_desc with
    FunApp(f,[]) when f == Settings.c_false -> true
  | _ -> false

(* Applying boolean functions *)

let make_true () =
  build_term_type Settings.t_bool (FunApp(Settings.c_true, []))
  
let make_false () =
  build_term_type Settings.t_bool (FunApp(Settings.c_false, []))

let make_and_ext ext t t' =
  if (is_true t) || (is_false t') then t' else
  if (is_true t') || (is_false t) then t else
  new_term Settings.t_bool ext (FunApp(Settings.f_and, [t;t']))

let make_and t t' =  make_and_ext Parsing_helper.dummy_ext t t'

let make_or_ext ext t t' =
  if (is_false t) || (is_true t') then t' else
  if (is_false t') || (is_true t) then t else
  new_term Settings.t_bool ext (FunApp(Settings.f_or, [t;t']))

let make_or t t' =  make_or_ext Parsing_helper.dummy_ext t t'

let make_and_list = function
    [] -> make_true()
  | [a] -> a
  | (a::l) -> List.fold_left make_and a l

let rec split_and accu t = 
  match t.t_desc with
    FunApp(f, [t1;t2]) when f == Settings.f_and ->
      split_and (split_and accu t1) t2
  | _ -> 
      if List.exists (fun t' -> equal_terms t t') accu then
	accu
      else
	t::accu

let make_and_list l =
  let l' = List.fold_left split_and [] l in
  make_and_list l'

let make_or_list = function
    [] -> make_false()
  | [a] -> a
  | (a::l) -> List.fold_left make_or a l

let rec split_or accu t = 
  match t.t_desc with
    FunApp(f, [t1;t2]) when f == Settings.f_or ->
      split_or (split_or accu t1) t2
  | _ -> 
      if List.exists (fun t' -> equal_terms t t') accu then
	accu
      else
	t::accu

let make_or_list l =
  let l' = List.fold_left split_or [] l in
  make_or_list l'

let make_not t =
  build_term_type Settings.t_bool (FunApp(Settings.f_not, [t]))
  
let make_equal_ext ext t t' =
  new_term Settings.t_bool ext
    (FunApp(Settings.f_comp Equal t.t_type t'.t_type, [t;t']))

let make_equal t t' = make_equal_ext Parsing_helper.dummy_ext t t'

let make_let_equal t t' =
  begin
    match t.t_desc with
      Var _ -> ()
    | _ -> Parsing_helper.internal_error "make_let_equal:  LetEqual terms should have a variable in the left-hand side"
  end;
  build_term_type Settings.t_bool (FunApp(Settings.f_comp LetEqual t.t_type t'.t_type, [t;t']))

let make_diff_ext ext t t' =
  new_term Settings.t_bool ext
    (FunApp(Settings.f_comp Diff t.t_type t'.t_type, [t;t']))

let make_diff t t' = make_diff_ext Parsing_helper.dummy_ext t t'

let make_for_all_diff t t' =
  build_term_type Settings.t_bool (FunApp(Settings.f_comp ForAllDiff t.t_type t'.t_type, [t;t']))

(* Put a term in the form or (and (...)) *)

let rec get_or t =
  match t.t_desc with
    FunApp(f, [t1;t2]) when f == Settings.f_or ->
      (get_or t1) @ (get_or t2)
  | _ -> [t]

let rec make_and1 a = function
    [] -> Parsing_helper.internal_error "make_and1 empty"
  | [b] -> make_and b a
  | (b::l2) -> make_or (make_and a b) (make_and1 a l2)

let rec make_and2 l1 = function
    [] -> Parsing_helper.internal_error "make_and2 empty"
  | [a] -> make_and1 a l1
  | (a::l2) -> make_or (make_and1 a l1) (make_and2 l1 l2)

let make_and_distr t1 t2 =
  if (is_false t1) || (is_false t2) then make_false() else
  if is_true t1 then t2 else
  if is_true t2 then t1 else
  (* If t1 or t2 is "or", distribute *)
  make_and2 (get_or t1) (get_or t2)

let rec or_and_form t =
  match t.t_desc with
    FunApp(f, [t1;t2]) when f == Settings.f_and ->
      make_and_distr (or_and_form t1) (or_and_form t2)
  | FunApp(f, [t1;t2]) when f == Settings.f_or ->
      make_or (or_and_form t1) (or_and_form t2)
  | _ -> t

(* Test for tuples *)

let is_tuple t =
  match t.t_desc with
    FunApp(f, _) when (f.f_options land Settings.fopt_COMPOS) != 0 -> true
  | _ -> false

let is_pat_tuple = function
    PatTuple (f,_) -> true
  | _ -> false

(* Building lets *)

let rec put_lets l p1 p2 = 
  match l with
    [] -> p1
  | ((PatVar b) as a1,a2)::lr ->
      oproc_from_desc (Let(a1, a2, put_lets lr p1 p2, oproc_from_desc Yield))
  | (a1,a2)::lr ->
      oproc_from_desc (Let(a1, a2, put_lets lr p1 p2, p2))

let rec put_lets_term l p1 p2 = 
  match l with
    [] -> p1
  | ((PatVar b) as a1,a2)::lr ->
      build_term_type p1.t_type (LetE(a1, a2, put_lets_term lr p1 p2, None))
  | (a1,a2)::lr ->
      build_term_type p1.t_type (LetE(a1, a2, put_lets_term lr p1 p2, p2))
	
(* [simplify_let_tuple pat t] serves to simplify "let pat = t in ..."
   when pat is a tuple.
   It returns 
   - the list of performed transformations
   - a term [t] meant to be transformed into a test "if t then ... else ..." 
   before the following [let]s (no test should be generated when [t] is true)
   - a list [(pat1, t1);...;(patn, tn)] meant to
   be transformed into "let pat1 = t1 in ... let patn = tn in ...".
   It makes sure that, when the initial pattern matching fails,
   none of the variables of pat is defined in the transformed let.
   It raises the exception [Impossible] when the initial pattern 
   matching always fails. *)
	
exception Impossible

let rec split_term f0 t = 
  match t.t_desc with
    Var(_,_) -> 
      (* TO DO when the variable is created by a restriction,
         it is different from a tuple with high probability *)
      raise Not_found
  | ReplIndex i -> 
      (* A replication index cannot occur because the split term must be of a bitstring type *)
      Parsing_helper.internal_error "A replication index should not occur in Terms.split_term"
  | FunApp(f,l) when f == f0 -> l
  | FunApp(f,l) -> 
      if f0.f_cat == Tuple && (f.f_cat == Tuple || (f.f_cat == Std && l == [] && (!Settings.constants_not_tuple))) then
	raise Impossible
      else
	raise Not_found
  | TestE _ | FindE _ | LetE _ | ResE _ | EventAbortE _ | EventE _ | GetE _ | InsertE _ ->
      Parsing_helper.internal_error "If, find, let, new, get, insert, event, and event_abort should have been expanded (Simplify)"

let rec rename_var_pat rename_accu = function
    (PatEqual t) as pat -> pat
  | PatTuple(f,l) -> PatTuple(f, List.map (rename_var_pat rename_accu) l)
  | PatVar b ->
      let b' = new_binder b in
      b'.count_def <- 1;
      rename_accu := (PatVar b, term_from_binder b') :: (!rename_accu);
      PatVar b'
	
let rec rename_var_except_last rename_accu = function
    [] -> []
  | [a] -> [a]
  | (pat,t)::l -> (rename_var_pat rename_accu pat, t) :: (rename_var_except_last rename_accu l)
	
let rec simplify_let_tuple_aux get_tuple transfo_accu accu pat t =
  match pat with
    PatTuple(f, l) ->
      begin
      try 
	let l' = split_term f (get_tuple t) in
	simplify_let_tuple_aux_list get_tuple ((pat, DExpandTuple)::transfo_accu) accu l l'
      with Not_found ->
	transfo_accu, (pat, t) :: accu
      end
  | _ -> transfo_accu, (pat, t) :: accu
				   
and simplify_let_tuple_aux_list get_tuple transfo_accu accu patl tl =
  match patl, tl with
    [], [] -> transfo_accu, accu
  | (pat::patr, t::tr) ->
      let transfo_accu', accu' = 
	simplify_let_tuple_aux get_tuple transfo_accu accu pat t
      in
      simplify_let_tuple_aux_list get_tuple transfo_accu' accu' patr tr
  | _ -> Parsing_helper.internal_error "simplify_let_tuple_aux_list: lists should have same length"
	
let simplify_let_tuple get_tuple pat t =
  let transfo_accu, lbind =
    simplify_let_tuple_aux get_tuple [] [] pat t
  in
  let lbind_eq = List.filter (function (PatEqual _, _) -> true | _ -> false) lbind in
  let lbind_tup = List.filter (function (PatTuple _, _) -> true | _ -> false) lbind in
  let lbind_var = List.filter (function (PatVar _, _) -> true | _ -> false) lbind in
  let rename_accu = ref [] in
  let renamed_lbind_tup = rename_var_except_last rename_accu lbind_tup in
  let pat_remaining = List.rev_append renamed_lbind_tup (List.rev_append (!rename_accu) lbind_var) in
  let transfo_accu = (List.map (fun (pat, t') -> (pat, DEqTest)) lbind_eq) @ transfo_accu in
  let test =
    make_and_list (List.map (function
      | (PatEqual t, t') -> make_equal t t'
      | _ -> Parsing_helper.internal_error "Should have PatEqual") lbind_eq)
  in
  transfo_accu, test, pat_remaining
  
    
(* Empty tree of definition dependances 
   The treatment of TestE/FindE/LetE/ResE is necessary: build_def_process
   is called in check.ml.
*)


let rec empty_def_term t =
  t.t_facts <- None;
  match t.t_desc with
    Var(b,l) ->
      b.def <- [];
      empty_def_term_list l
  | ReplIndex _ -> ()
  | FunApp(_,l) ->
      empty_def_term_list l
  | TestE(t1,t2,t3) ->
      empty_def_term t2;
      empty_def_term t3;
      empty_def_term t1
  | FindE(l0,t3,_) ->
      List.iter (fun (bl,def_list,t1,t2) ->
	List.iter (fun (b1,b2) -> b1.def <- []) bl;
	empty_def_term_def_list def_list;
	empty_def_term t1;
	empty_def_term t2) l0;
      empty_def_term t3;
  | LetE(pat, t1, t2, topt) ->
      empty_def_pattern pat;
      empty_def_term t1;
      empty_def_term t2;
      begin
	match topt with
	  None -> ()
	| Some t3 -> empty_def_term t3
      end
  | ResE(b,t) -> b.def <- []; empty_def_term t
  | EventAbortE _ -> ()
  | EventE(t,p) ->
      empty_def_term t;
      empty_def_term p
  | GetE(tbl,patl,topt,p1,p2) ->
      List.iter empty_def_pattern patl;
      (match topt with None -> () | Some t -> empty_def_term t);
      empty_def_term p1;
      empty_def_term p2
  | InsertE(tbl,tl,p) -> 
      List.iter empty_def_term tl;
      empty_def_term p

and empty_def_term_list l = List.iter empty_def_term l

and empty_def_br (b,l) = b.def <- []; empty_def_term_list l

and empty_def_term_def_list def_list = 
  List.iter empty_def_br def_list

and empty_def_pattern = function
    PatVar b -> b.def <- []
  | PatTuple (f,l) -> List.iter empty_def_pattern l
  | PatEqual t -> empty_def_term t

let rec empty_def_process p = 
  p.i_facts <- None;
  match p.i_desc with
    Nil -> ()
  | Par(p1,p2) -> 
      empty_def_process p1;
      empty_def_process p2
  | Repl(b,p) ->
      empty_def_process p
  | Input((c,tl),pat,p) ->
      List.iter empty_def_term tl;
      empty_def_pattern pat;
      empty_def_oprocess p

and empty_def_oprocess p = 
  p.p_facts <- None;
  match p.p_desc with
    Yield | EventAbort _ -> ()
  | Restr(b,p) ->
      b.def <- [];
      empty_def_oprocess p
  | Test(t,p1,p2) ->
      empty_def_term t;
      empty_def_oprocess p1;
      empty_def_oprocess p2
  | Find(l0,p2,_) ->
      List.iter (fun (bl,def_list,t,p1) ->
	List.iter (fun (b1,b2) -> b1.def <- []) bl;
	empty_def_term_def_list def_list;
	empty_def_term t;
	empty_def_oprocess p1) l0;
      empty_def_oprocess p2
  | Output((c,tl),t',p) ->
      List.iter empty_def_term tl;
      empty_def_term t';
      empty_def_process p
  | Let(pat,t,p1,p2) ->
      empty_def_term t;
      empty_def_pattern pat;
      empty_def_oprocess p1;
      empty_def_oprocess p2
  | EventP(t,p) ->
      empty_def_term t;
      empty_def_oprocess p
  | Get(tbl,patl,topt,p1,p2) ->
      List.iter empty_def_pattern patl;
      (match topt with None -> () | Some t -> empty_def_term t);
      empty_def_oprocess p1;
      empty_def_oprocess p2
  | Insert(tbl,tl,p) -> 
      List.iter empty_def_term tl;
      empty_def_oprocess p

(* Functions used for updating elsefind facts when a new variable
   is defined.

If we have the elsefind fact "for all j, not (defined(x[j]...) && cond)"
and we define the variable x[i], we transform the elsefind fact into
"for all j, not (defined(x[j]...) && cond && i <> j)"
Indeed:
For i = j, i<>j is false, so defined(x[j]...) && cond && i <> j is
   false, so not (defined(x[j]...) && cond && i <> j) is true.
For i<>j, not (defined(x[j]...) && cond && i <> j) is equivalent to
   not (defined(x[j]...) && cond) so it is true because it was true
   before the definition of x[i]. 

[collect_ineq_def_list bl def_list] generates the inequalities
[i <> j] where [i] is the current replication indices, the
indices at which the variables in [bl] are newly defined,
and [j] is the indices with which variables in [bl] occur in [def_list].

[update_elsefind_with_def bl elsefind] updates the [elsefind] fact
as outlined above, where the newly defined variables (x above)
are the variables in [bl].
*)


let collect_ineq_def_list bl def_list =
  (* all variables in [bl] have the same [args_at_creation],
     corresponding to the current replication indices *)
  let args_at_creation = (List.hd bl).args_at_creation in

  let rec collect_ineq_term accu t =
    match t.t_desc with
      Var(b,l) ->
	collect_ineq_br accu (b,l)
    | FunApp(f,l) ->
	List.fold_left collect_ineq_term accu l
    | ReplIndex _ -> accu
    | _ -> Parsing_helper.internal_error "if/let/find/new should not occur in defined conditions"

  and collect_ineq_br accu (b,l) =
    if List.memq b bl then  
      let new_fact = make_or_list (List.map2 (fun i t -> make_diff (term_from_repl_index i) t) args_at_creation l) in
      List.fold_left collect_ineq_term (new_fact::accu) l
    else
      List.fold_left collect_ineq_term accu l
  
  in
  List.fold_left collect_ineq_br [] def_list
  
let update_elsefind_with_def bl ((bl',def_list,t) as elsefind) =
  if bl == [] then elsefind else
  let new_facts = collect_ineq_def_list bl def_list in
  if new_facts == [] then
    elsefind
  else
    (bl', def_list, make_and_list (t::new_facts))

(* Check that a term is a basic term (no if/let/find/new/event/get/insert) *)

let rec check_simple_term t =
  match t.t_desc with
    Var(_,l) | FunApp(_,l) ->
      List.for_all check_simple_term l
  | ReplIndex _ -> true
  | TestE _ | FindE _ | LetE _ | ResE _ | EventAbortE _ | EventE _ | GetE _ | InsertE _ ->
      false

let find_list_to_elsefind accu l =
  List.fold_left (fun ((fact_accu, else_find_accu) as accu) ((bl, def_list, t1,_):'a findbranch) ->
    if check_simple_term t1 then
      if bl == [] && def_list == [] then
	((make_not t1)::fact_accu, else_find_accu)
      else
	(fact_accu, (List.map snd bl, def_list, t1)::else_find_accu)
    else
      accu) accu l

(* Build tree of definition dependences
   The treatment of TestE/FindE/LetE/ResE is necessary: build_def_process
   is called in check.ml.

   The value of elsefind_facts is correct even if the game has not been expanded:
   we correctly discard elsefind_facts when their defined condition refers
   to a variable defined in a term.
   *)

let rec close_def_subterm accu (b,l) =
  add_binderref (b,l) accu;
  List.iter (close_def_term accu) l

and close_def_term accu t =
  match t.t_desc with
    Var(b,l) -> close_def_subterm accu (b,l)
  | ReplIndex i -> ()
  | FunApp(f,l) -> List.iter (close_def_term accu) l
  | _ -> Parsing_helper.input_error "if/find/let/new/event/get/insert forbidden in defined conditions of find" t.t_loc

let defined_refs_find bl def_list defined_refs =
  (* Compute the defined references in the condition *)
  let accu = ref defined_refs in
  List.iter (close_def_subterm accu) def_list;
  let defined_refs_cond = !accu in
  (* Compute the defined references in the then branch *)
  let vars = List.map fst bl in
  let repl_indices = List.map snd bl in
  let def_list' = subst_def_list repl_indices (List.map term_from_binder vars) def_list in
  let accu = ref ((List.map binderref_from_binder vars) @ defined_refs) in
  List.iter (close_def_subterm accu) def_list';
  let defined_refs_branch = !accu in
  (defined_refs_cond, defined_refs_branch)

let add_var accu b =
  if List.memq b accu then accu else b::accu

let rec unionq l1 = function
    [] -> l1
  | (a::l) -> 
      if List.memq a l1 then unionq l1 l else
      a::(unionq l1 l)

let rec add_vars_from_pat accu = function
    PatVar b -> add_var accu b
  | PatEqual t -> accu
  | PatTuple (f,l) -> add_vars_from_pat_list accu l

and add_vars_from_pat_list accu = function
    [] -> accu
  | (a::l) -> add_vars_from_pat_list (add_vars_from_pat accu a) l

let rec def_vars_term accu t = 
  match t.t_desc with
    Var(_,l) | FunApp(_,l) -> def_vars_term_list accu l
  | ReplIndex i -> accu
  | TestE(t1,t2,t3) -> 
      def_vars_term (def_vars_term (def_vars_term accu t1) t2) t3
  | FindE(l0, t3, _) ->
      let accu = ref (def_vars_term accu t3) in
      List.iter (fun (bl, def_list, t1, t2) ->
	(*Nothing to do for def_list: it contains only
          Var and Fun*)
	accu := unionq (List.map fst bl) (def_vars_term (def_vars_term (!accu) t1) t2)
	     ) l0;
      !accu
  | LetE(pat, t1, t2, topt) ->
      let accu' = match topt with
	None -> accu
      |	Some t3 -> def_vars_term accu t3 
      in
      def_vars_term (def_vars_pat (add_vars_from_pat (def_vars_term accu' t2) pat) pat) t1
  | ResE(b,t) ->
      add_var (def_vars_term accu t) b
  | EventAbortE _ -> accu
  | EventE(t,p) ->
      def_vars_term (def_vars_term accu p) t
  | GetE(tbl,patl,topt,p1,p2) ->
      let accu' = match topt with
	None -> accu
      |	Some t -> def_vars_term accu t
      in
      def_vars_term (def_vars_term (def_vars_pat_list (add_vars_from_pat_list accu' patl) patl) p1) p2
  | InsertE(tbl,tl,p) ->
      def_vars_term_list (def_vars_term accu p) tl
      
and def_vars_term_list accu = function
    [] -> accu
  | (a::l) -> def_vars_term (def_vars_term_list accu l) a

and def_vars_pat accu = function
    PatVar b -> accu 
  | PatTuple (f,l) -> def_vars_pat_list accu l
  | PatEqual t -> def_vars_term accu t

and def_vars_pat_list accu = function
    [] -> accu
  | (a::l) -> def_vars_pat (def_vars_pat_list accu l) a

(* def_term is always called with  above_node.def_vars_at_def \subseteq def_vars
def_term returns a node n'. In this node n', we always have n'.def_vars_at_def \subseteq def_vars
Same property for def_term_list, def_term_def_list, def_pattern, def_pattern_list.
By induction. 
In cases ReplIndex, FindE, n' = above_node. 
In the other cases, we use the induction hypothesis. *)

let rec def_term event_accu cur_array above_node true_facts def_vars elsefind_facts t =
  if (t.t_facts != None) then
    Parsing_helper.internal_error "Two terms physically equal: cannot compute facts correctly";
  t.t_facts <- Some (cur_array, true_facts, elsefind_facts, def_vars, above_node);
  match t.t_desc with
    Var(_,l) | FunApp(_,l) ->
      let (above_node', _) = def_term_list_ef event_accu cur_array above_node true_facts def_vars elsefind_facts l in
      above_node'
  | ReplIndex i -> above_node
  | TestE(t1,t2,t3) ->
      let true_facts' = t1 :: true_facts in
      let true_facts'' = (make_not t1) :: true_facts in
      let (above_node', elsefind_facts') = def_term_ef event_accu cur_array above_node true_facts def_vars elsefind_facts t1 in
      ignore(def_term event_accu cur_array above_node' true_facts' def_vars elsefind_facts' t2);
      ignore(def_term event_accu cur_array above_node' true_facts'' def_vars elsefind_facts' t3);
      above_node'
  | FindE(l0,t3,_) ->
      let (true_facts_else, elsefind_facts_else) = 
	find_list_to_elsefind (true_facts, elsefind_facts) l0
      in
      List.iter (fun (bl,def_list,t1,t2) ->
	let vars = List.map fst bl in
	let repl_indices = List.map snd bl in
        (* The variables defined in t are variables defined in conditions of find,
	   one cannot make array accesses to them, nor test their definition,
	   so they will not appear in defined conditions of elsefind_facts.
	   We need not take them into account to update elsefind_facts. *)
	let elsefind_facts'' = List.map (update_elsefind_with_def vars) elsefind_facts in
	let t1' = subst repl_indices (List.map term_from_binder vars) t1 in
	let true_facts' =  t1' :: true_facts in
	let accu = ref [] in
	List.iter (close_def_subterm accu) def_list;
	let def_list_subterms = !accu in 
	let def_vars_t1 = def_list_subterms @ def_vars in
       	let def_vars' = (subst_def_list repl_indices (List.map term_from_binder vars) def_list_subterms) @ def_vars in
	let above_node' = { above_node = above_node; binders = vars; 
			    true_facts_at_def = true_facts'; 
			    def_vars_at_def = def_vars';
			    elsefind_facts_at_def = elsefind_facts;
			    future_binders = []; future_true_facts = []; 
			    definition = DTerm t;
			    definition_success = DTerm t2 } 
	in
	List.iter (fun b -> b.def <- above_node' :: b.def) vars;
	ignore(def_term event_accu (repl_indices @ cur_array) 
		 (def_term_def_list event_accu cur_array above_node true_facts def_vars elsefind_facts'' def_list)
		 true_facts def_vars_t1 elsefind_facts'' t1);
	ignore(def_term event_accu cur_array above_node' true_facts' def_vars' elsefind_facts'' t2)) l0;
      ignore(def_term event_accu cur_array above_node true_facts_else def_vars elsefind_facts_else t3);
      above_node
  | LetE(pat, t1, t2, topt) ->
      let (above_node', elsefind_facts') = def_term_ef event_accu cur_array above_node true_facts def_vars elsefind_facts t1 in
      let accu = ref [] in
      let (above_node'', elsefind_facts'') = def_pattern_ef accu event_accu cur_array above_node' true_facts def_vars elsefind_facts' pat in
      let true_facts' = ((match pat with PatVar _ -> make_let_equal | _ -> make_equal) (term_from_pat pat) t1) :: true_facts in
      let above_node''' = { above_node = above_node''; binders = !accu; 
			    true_facts_at_def = true_facts'; 
			    def_vars_at_def = def_vars;
			    elsefind_facts_at_def = elsefind_facts'';
			    future_binders = []; future_true_facts = []; 
			    definition = DTerm t;
			    definition_success = DTerm t2 } 
      in
      let elsefind_facts''' = List.map (update_elsefind_with_def (!accu)) elsefind_facts'' in
      List.iter (fun b -> b.def <- above_node''' :: b.def) (!accu);
      ignore (def_term event_accu cur_array above_node''' true_facts' def_vars elsefind_facts''' t2);
      begin
	match topt with
	  None -> ()
	| Some t3 -> 
	    let true_facts' = 
	      try
		(make_for_all_diff (gen_term_from_pat pat) t1) :: true_facts
	      with NonLinearPattern -> true_facts
	    in
	    ignore(def_term event_accu cur_array above_node' true_facts' def_vars elsefind_facts'' t3)
      end;
      above_node'
  | ResE(b, t') ->
      let elsefind_facts' = List.map (update_elsefind_with_def [b]) elsefind_facts in
      let above_node' = { above_node = above_node; binders = [b]; 
			  true_facts_at_def = true_facts; 
			  def_vars_at_def = def_vars;
			  elsefind_facts_at_def = elsefind_facts;
			  future_binders = []; future_true_facts = []; 
			  definition = DTerm t;
			  definition_success = DTerm t' } 
      in
      b.def <- above_node' :: b.def;
      def_term event_accu cur_array above_node' true_facts def_vars elsefind_facts' t'
  | EventAbortE f ->
      begin
	match event_accu with
	  None -> ()
	| Some accu -> 
	    let idx = build_term_type Settings.t_bitstring (FunApp(Settings.get_tuple_fun [], [])) in
	    let t' = build_term_type Settings.t_bool (FunApp(f, [idx])) in
	    accu := (t', DTerm t) :: (!accu)
      end;
      above_node
  | EventE(t1,p) ->
      begin
	match event_accu with
	  None -> ()
	| Some accu -> accu := (t1, DTerm t) :: (!accu)
      end;
      let (above_node', elsefind_facts') = def_term_ef event_accu cur_array above_node true_facts def_vars elsefind_facts t1 in
      def_term event_accu cur_array above_node' (t1 :: true_facts) def_vars elsefind_facts' p

  | GetE(tbl,patl,topt,p1,p2) ->
      let accu = ref [] in
      let above_node' = def_pattern_list accu event_accu cur_array above_node true_facts def_vars elsefind_facts patl in
      let above_node'' = 
        match topt with 
          Some t -> def_term event_accu cur_array above_node' true_facts def_vars elsefind_facts t
        | None -> above_node'
      in
      (* The variables defined in patl, topt are variables defined in conditions of find,
	 one cannot make array accesses to them, nor test their definition,
	 so they will not appear in defined conditions of elsefind_facts.
	 We need not update elsefind_facts. *)
      let elsefind_facts' = List.map (update_elsefind_with_def (!accu)) elsefind_facts in
      ignore (def_term event_accu cur_array above_node'' true_facts def_vars elsefind_facts' p1);
      ignore (def_term event_accu cur_array above_node true_facts def_vars elsefind_facts p2);
      above_node
        
  | InsertE(tbl,tl,p) ->
      let (above_node', elsefind_facts') = def_term_list_ef event_accu cur_array above_node true_facts def_vars elsefind_facts tl in
      def_term event_accu cur_array above_node' true_facts def_vars elsefind_facts' p

	
(* same as [def_term] but additionally updates elsefind_facts to take into account
   the variables defined in [t] *) 
and def_term_ef event_accu cur_array above_node true_facts def_vars elsefind_facts t =
  let above_node' = def_term event_accu cur_array above_node true_facts def_vars elsefind_facts t in
  let vars_t = def_vars_term [] t in
  let elsefind_facts' = List.map (update_elsefind_with_def vars_t) elsefind_facts in
  (above_node', elsefind_facts')

(* [def_term_list_ef] also updates elsefind_facts to take into account
   the variables defined in the considered list of terms *)
and def_term_list_ef event_accu cur_array above_node true_facts def_vars elsefind_facts = function
    [] -> (above_node, elsefind_facts)
  | (a::l) -> 
      let (above_node', elsefind_facts') = def_term_ef event_accu cur_array above_node true_facts def_vars elsefind_facts a in
      def_term_list_ef event_accu cur_array above_node' true_facts def_vars elsefind_facts' l

and def_term_def_list event_accu cur_array above_node true_facts def_vars elsefind_facts = function
    [] -> above_node
  | (b,l)::l' -> 
      let (above_node', elsefind_facts') = def_term_list_ef event_accu cur_array above_node true_facts def_vars elsefind_facts l in
      def_term_def_list event_accu cur_array above_node' true_facts def_vars elsefind_facts' l'

and def_pattern accu event_accu cur_array above_node true_facts def_vars elsefind_facts = function
    PatVar b -> accu := b :: (!accu); above_node
  | PatTuple (f,l) -> def_pattern_list accu event_accu cur_array above_node true_facts def_vars elsefind_facts l
  | PatEqual t -> def_term event_accu cur_array above_node true_facts def_vars elsefind_facts t

(* same as [def_pattern] but additionally updates elsefind_facts to take into account
   the variables defined in [pat] *) 
and def_pattern_ef accu event_accu cur_array above_node true_facts def_vars elsefind_facts pat = 
  let above_node' = def_pattern accu event_accu cur_array above_node true_facts def_vars elsefind_facts pat in
  let vars_pat = def_vars_pat [] pat in
  let elsefind_facts' = List.map (update_elsefind_with_def vars_pat) elsefind_facts in
  (above_node', elsefind_facts')

and def_pattern_list accu event_accu cur_array above_node true_facts def_vars elsefind_facts = function
    [] -> above_node 
  | (a::l) -> 
      let (above_node', elsefind_facts') = def_pattern_ef accu event_accu cur_array above_node true_facts def_vars elsefind_facts a in
      def_pattern_list accu event_accu cur_array above_node' true_facts def_vars elsefind_facts' l

(* def_process is always called with above_node.def_vars_at_def \subseteq def_vars
   By induction, also using the properties of def_term, ...
   One case in which the two values are different is in the condition of find:
   def_vars contains the def_list, which is not included in above_node.def_vars_at_def. *)

let rec def_process event_accu cur_array above_node true_facts def_vars p' =
  if p'.i_facts != None then
    Parsing_helper.internal_error "Two processes physically equal: cannot compute facts correctly";
  p'.i_facts <- Some (cur_array, true_facts, [], def_vars, above_node);
  match p'.i_desc with
    Nil -> ()
  | Par(p1,p2) -> 
      def_process event_accu cur_array above_node true_facts def_vars p1;
      def_process event_accu cur_array above_node true_facts def_vars p2
  | Repl(b,p) ->
      (* A node is needed here, even if the replication defines no
	 binders, because I rely on the node to locate the
	 replication in Simplify.CompatibleDefs.check_compatible *)
      let above_node' = { above_node = above_node; binders = [];
                          true_facts_at_def = true_facts;
                          def_vars_at_def = def_vars;
                          elsefind_facts_at_def = [];
                          future_binders = []; future_true_facts = []; 
                          definition = DInputProcess p';
			  definition_success = DInputProcess p }
      in
      def_process event_accu (b::cur_array) above_node' true_facts def_vars p
  | Input((c,tl),pat,p) ->
      let (above_node',_) = def_term_list_ef event_accu cur_array above_node true_facts def_vars [] tl in
      let accu = ref [] in
      let above_node'' = def_pattern accu event_accu cur_array above_node' true_facts def_vars [] pat in
      (* is_find_unique uses this node to test whether two variables are defined
	 in the same input/output block, so it's important to generate this
	 node even if the pattern pat defines no variable. *)
      let above_node''' = { above_node = above_node''; binders = !accu; 
			    true_facts_at_def = true_facts; 
			    def_vars_at_def = def_vars;
			    elsefind_facts_at_def = [];
			    future_binders = []; future_true_facts = []; 
			    definition = DInputProcess p';
			    definition_success = DProcess p } 
      in
      List.iter (fun b -> b.def <- above_node''' :: b.def) (!accu);
      let (fut_binders, fut_true_facts) = 
	def_oprocess event_accu cur_array above_node''' true_facts def_vars [] p
      in
      above_node'''.future_binders <- fut_binders;
      above_node'''.future_true_facts <- fut_true_facts

and def_oprocess event_accu cur_array above_node true_facts def_vars elsefind_facts p' =
  if p'.p_facts != None then
    Parsing_helper.internal_error "Two processes physically equal: cannot compute facts correctly";
  p'.p_facts <- Some (cur_array, true_facts, elsefind_facts, def_vars, above_node);
  match p'.p_desc with
    Yield -> 
      ([],[])
  | EventAbort f -> 
      begin
	match event_accu with
	  None -> ()
	| Some accu -> 
	    let idx = build_term_type Settings.t_bitstring (FunApp(Settings.get_tuple_fun [], [])) in
	    let t = build_term_type Settings.t_bool (FunApp(f, [idx])) in
	    accu := (t, DProcess p') :: (!accu)
      end;
      ([],[])
  | Restr(b,p) ->
      let elsefind_facts' = List.map (update_elsefind_with_def [b]) elsefind_facts in
      let above_node' = { above_node = above_node; binders = [b]; 
			  true_facts_at_def = true_facts; 
			  def_vars_at_def = def_vars;
			  elsefind_facts_at_def = elsefind_facts;
			  future_binders = []; future_true_facts = []; 
			  definition = DProcess p';
			  definition_success = DProcess p } 
      in
      b.def <- above_node' :: b.def;
      let (fut_binders, fut_true_facts) = 
	def_oprocess event_accu cur_array above_node' true_facts def_vars elsefind_facts' p
      in
      above_node'.future_binders <- fut_binders;
      above_node'.future_true_facts <- fut_true_facts;
      (b::fut_binders, fut_true_facts)
  | Test(t,p1,p2) ->
      let (above_node', elsefind_facts') = def_term_ef event_accu cur_array above_node true_facts def_vars elsefind_facts t in
      let true_facts' = t :: true_facts in
      let true_facts'' = (make_not t) :: true_facts in
      let (fut_binders1, fut_true_facts1) = 
	def_oprocess event_accu cur_array above_node' true_facts' def_vars elsefind_facts' p1
      in
      let (fut_binders2, fut_true_facts2) = 
	def_oprocess event_accu cur_array above_node' true_facts'' def_vars elsefind_facts' p2
      in
      (intersect (==) fut_binders1 fut_binders2, 
       intersect equal_terms fut_true_facts1 fut_true_facts2)
  | Find(l0,p2,_) ->
      let (true_facts', elsefind_facts') = 
	find_list_to_elsefind (true_facts, elsefind_facts) l0
      in
      let (fut_binders2, fut_true_facts2) = 
	def_oprocess event_accu cur_array above_node true_facts' def_vars elsefind_facts' p2
      in
      let rec find_l = function
	  [] -> (fut_binders2, fut_true_facts2)
	| (bl,def_list,t,p1)::l ->
	    let (fut_bindersl, fut_true_factsl) = find_l l in
	    let vars = List.map fst bl in
	    let repl_indices = List.map snd bl in
            (* The variables defined in t are variables defined in conditions of find,
	       one cannot make array accesses to them, nor test their definition,
	       so they will not appear in defined conditions of elsefind_facts.
	       We need not take them into account to update elsefind_facts. *)
	    let elsefind_facts'' = List.map (update_elsefind_with_def vars) elsefind_facts in
	    let t' = subst repl_indices (List.map term_from_binder vars) t in
	    let true_facts' = t' :: true_facts in
	    let accu = ref [] in
	    List.iter (close_def_subterm accu) def_list;
	    let def_list_subterms = !accu in 
	    let def_vars_t = def_list_subterms @ def_vars in
       	    let def_vars' = (subst_def_list repl_indices (List.map term_from_binder vars) def_list_subterms) @ def_vars in
	    let above_node' = { above_node = above_node; binders = vars; 
				true_facts_at_def = true_facts'; 
				def_vars_at_def = def_vars';
				elsefind_facts_at_def = elsefind_facts;
				future_binders = []; future_true_facts = []; 
				definition = DProcess p';
			        definition_success = DProcess p1 } 
	    in
	    List.iter (fun b -> b.def <- above_node' :: b.def) vars;
	    ignore(def_term event_accu (repl_indices @ cur_array) 
		     (def_term_def_list event_accu cur_array above_node true_facts def_vars elsefind_facts'' def_list)
		     true_facts def_vars_t elsefind_facts'' t);
	    let (fut_binders1, fut_true_facts1) = 
	      def_oprocess event_accu cur_array above_node' true_facts' def_vars' elsefind_facts'' p1
	    in
	    above_node'.future_binders <- fut_binders1;
	    above_node'.future_true_facts <- fut_true_facts1;
	    (intersect (==) (vars @ fut_binders1) fut_bindersl,
	     intersect equal_terms fut_true_facts1 fut_true_factsl)
      in
      find_l l0
  | Output((c,tl),t',p) ->
      let (above_node', elsefind_facts') = def_term_list_ef event_accu cur_array above_node true_facts def_vars elsefind_facts tl in
      let above_node'' = def_term event_accu cur_array above_node' true_facts def_vars elsefind_facts' t' in
      def_process event_accu cur_array above_node'' true_facts def_vars p;
      ([],[])
  | Let(pat,t,p1,p2) ->
      let (above_node', elsefind_facts') = def_term_ef event_accu cur_array above_node true_facts def_vars elsefind_facts t in
      let accu = ref [] in
      let (above_node'', elsefind_facts'') = def_pattern_ef accu event_accu cur_array above_node' true_facts def_vars elsefind_facts' pat in
      let new_fact = (match pat with PatVar _ -> make_let_equal | _ -> make_equal) (term_from_pat pat) t in
      let true_facts' = new_fact :: true_facts in
      let elsefind_facts''' = List.map (update_elsefind_with_def (!accu)) elsefind_facts'' in
      let above_node''' = { above_node = above_node''; binders = !accu; 
			    true_facts_at_def = true_facts'; 
			    def_vars_at_def = def_vars;
			    elsefind_facts_at_def = elsefind_facts'';
			    future_binders = []; future_true_facts = []; 
			    definition = DProcess p';
			    definition_success = DProcess p1 } 
      in
      List.iter (fun b -> b.def <- above_node''' :: b.def) (!accu);
      let (fut_binders1, fut_true_facts1) = 
	def_oprocess event_accu cur_array above_node''' true_facts' def_vars elsefind_facts''' p1
      in
      above_node'''.future_binders <- fut_binders1;
      above_node'''.future_true_facts <- fut_true_facts1;
      begin
	match pat, p2.p_desc with
	  PatVar _, Yield -> 
	    ((!accu) @ fut_binders1, new_fact :: fut_true_facts1)
	| _ -> 
	    let true_facts' = 
	      try
		(make_for_all_diff (gen_term_from_pat pat) t) :: true_facts
	      with NonLinearPattern -> true_facts
	    in
	    let (fut_binders2, fut_true_facts2) = 
	      def_oprocess event_accu cur_array above_node' true_facts' def_vars elsefind_facts'' p2
	    in
	    (intersect (==) ((!accu) @ fut_binders1) fut_binders2,
	     intersect equal_terms (new_fact :: fut_true_facts1) fut_true_facts2)
      end
  | EventP(t,p) ->
      begin
	match event_accu with
	  None -> ()
	| Some accu -> accu := (t, DProcess p') :: (!accu)
      end;
      let (above_node', elsefind_facts') = def_term_ef event_accu cur_array above_node true_facts def_vars elsefind_facts t in
      let (fut_binders, fut_true_facts) = 
	def_oprocess event_accu cur_array above_node' (t :: true_facts) def_vars elsefind_facts' p
      in
      (fut_binders, t::fut_true_facts)
  | Get(tbl,patl,topt,p1,p2) ->
      let accu = ref [] in
      let above_node' = def_pattern_list accu event_accu cur_array above_node true_facts def_vars elsefind_facts patl in
      let above_node'' = 
        match topt with 
          Some t -> def_term event_accu cur_array above_node' true_facts def_vars elsefind_facts t
        | None -> above_node'
      in
      (* The variables defined in patl, topt are variables defined in conditions of find,
	 one cannot make array accesses to them, nor test their definition,
	 so they will not appear in defined conditions of elsefind_facts.
	 We need not update elsefind_facts. *)
      let elsefind_facts' = List.map (update_elsefind_with_def (!accu)) elsefind_facts in
      let (fut_binders1, fut_true_facts1) = 
	def_oprocess event_accu cur_array above_node'' true_facts def_vars elsefind_facts' p1
      in
      let (fut_binders2, fut_true_facts2) = 
	def_oprocess event_accu cur_array above_node true_facts def_vars elsefind_facts p2
      in
      (intersect (==) fut_binders1 fut_binders2, 
       intersect equal_terms fut_true_facts1 fut_true_facts2)
        
  | Insert(tbl,tl,p) ->
      let (above_node', elsefind_facts') = def_term_list_ef event_accu cur_array above_node true_facts def_vars elsefind_facts tl in
      def_oprocess event_accu cur_array above_node' true_facts def_vars elsefind_facts' p

let build_def_process event_accu p =
  empty_def_process p;
  let rec st_node = { above_node = st_node; 
		      binders = []; 
		      true_facts_at_def = []; 
		      def_vars_at_def = []; 
		      elsefind_facts_at_def = [];
		      future_binders = []; future_true_facts = []; 
		      definition = DNone;
		      definition_success = DNone } 
  in
  def_process event_accu [] st_node [] [] p

(* Add to [accu] the variables defined above the node [n] *)

let rec add_def_vars_node accu n =
  let accu' = n.binders @ accu in
  if n.above_node != n then
    add_def_vars_node accu' n.above_node
  else
    accu'


(* array_ref_* stores in the binders the kind of accesses made to the binder:
    - b.count_def: number of definitions of the binder b
    - b.std_ref: true when b has standard references (references to b 
      in its scope with the array indices at its definition)
    - b.array_ref: true when b has array references (references to b
      outside its scope or with explicit array indices that use the value of b)
    - b.root_def_std_ref: true when b is referenced at the root of a "defined"
      condition, in its scope with the array indices at its definition.
    - b.root_def_array_ref: true when b is referenced at the root of a "defined"
      condition, in an array reference. 
      If references at the root of defined conditions are the only ones, 
      the definition point of b is important, but not its value.

   It also stores the binders in all_vars, so that cleanup_array_ref
   can cleanup the binders; cleanup_array_ref should be called when
   the reference information is no longer needed.

   The treatment of TestE/FindE/LetE/ResE is necessary: array_ref_eqside
   is called in check.ml.
*)

let all_vars = ref []

let add b =
  if not (List.memq b (!all_vars)) then
    all_vars := b :: (!all_vars)

let rec array_ref_term in_scope t = 
  match t.t_desc with
    Var(b, l) -> 
      if is_args_at_creation b l &&
	List.memq b in_scope then
	b.std_ref <- true
      else
	begin
	  b.array_ref <- true;
      	  b.count_array_ref <- b.count_array_ref + 1
	end;
      add b;
      List.iter (array_ref_term in_scope) l
  | ReplIndex i -> ()
  | FunApp(_,l) ->
      List.iter (array_ref_term in_scope)  l
  | TestE(t1,t2,t3) ->
      array_ref_term in_scope t1;
      array_ref_term in_scope t2;
      array_ref_term in_scope t3
  | LetE(pat, t1, t2, topt) ->
      array_ref_pattern in_scope pat;
      array_ref_term in_scope t1;
      array_ref_term (vars_from_pat in_scope pat) t2;
      begin
	match topt with
	  None -> ()
	| Some t3 -> array_ref_term in_scope t3
      end
  | FindE(l0,t3,_) ->
      List.iter (fun (bl,def_list, t1,t2) ->
	List.iter (fun (b,_) -> add b; b.count_def <- b.count_def + 1) bl;
	let in_scope' = (List.map fst bl) @ in_scope in
	array_ref_def_list in_scope def_list;
	array_ref_term in_scope t1;
	array_ref_term in_scope' t2) l0;
      array_ref_term in_scope t3
  | ResE(b,t) ->
      add b;
      b.count_def <- b.count_def + 1;
      array_ref_term (b::in_scope) t
  | EventAbortE _ -> ()
  | EventE(t,p) ->
      array_ref_term in_scope t;
      array_ref_term in_scope p
  | GetE(tbl,patl,topt,p1,p2) ->
      List.iter (array_ref_pattern in_scope) patl;
      let in_scope' = vars_from_pat_list in_scope patl in
      (match topt with 
         | Some t -> array_ref_term in_scope' t
         | None -> ());
      array_ref_term in_scope' p1;
      array_ref_term in_scope p2
  | InsertE(tbl,tl,p) ->
      List.iter (array_ref_term in_scope) tl;
      array_ref_term in_scope p

and array_ref_pattern in_scope = function
    PatVar b -> 
      add b;
      b.count_def <- b.count_def + 1
  | PatTuple (f,l) -> List.iter (array_ref_pattern in_scope) l
  | PatEqual t -> array_ref_term in_scope t

and array_ref_def_list in_scope' def_list =
  List.iter (fun (b,l) -> 
    List.iter (array_ref_term in_scope') l;
    if is_args_at_creation b l &&
      List.memq b in_scope' then
      b.root_def_std_ref <- true
    else
      begin
	b.root_def_array_ref <- true;
	b.count_array_ref <- b.count_array_ref + 1
      end;
    add b) def_list

let rec array_ref_process in_scope p =
  match p.i_desc with
    Nil -> ()
  | Par(p1,p2) -> 
      array_ref_process in_scope p1;
      array_ref_process in_scope p2
  | Repl(b,p) ->
      array_ref_process in_scope p
  | Input((_,tl),pat,p) ->
      List.iter (array_ref_term in_scope) tl;      
      array_ref_pattern in_scope pat;
      array_ref_oprocess (vars_from_pat in_scope pat) p

and array_ref_oprocess in_scope p = 
  match p.p_desc with
    Yield | EventAbort _ -> ()
  | Restr(b,p) ->
      add b;
      b.count_def <- b.count_def + 1;
      array_ref_oprocess (b::in_scope) p
  | Test(t,p1,p2) ->
      array_ref_term in_scope t;      
      array_ref_oprocess in_scope p1;
      array_ref_oprocess in_scope p2
  | Find(l0,p2,_) ->
      List.iter (fun (bl,def_list,t,p1) ->
	List.iter (fun (b,_) -> add b; b.count_def <- b.count_def + 1) bl;
	let in_scope' = (List.map fst bl) @ in_scope in
	array_ref_def_list in_scope def_list;
	array_ref_term in_scope t;      
	array_ref_oprocess in_scope' p1) l0;
      array_ref_oprocess in_scope p2
  | Output((_,tl),t2,p) ->
      List.iter (array_ref_term in_scope) tl;      
      array_ref_term in_scope t2;
      array_ref_process in_scope p
  | Let(pat, t, p1, p2) ->
      array_ref_pattern in_scope pat;
      array_ref_term in_scope t;      
      array_ref_oprocess (vars_from_pat in_scope pat) p1;
      array_ref_oprocess in_scope p2
  | EventP(t,p) ->
      array_ref_term in_scope t;      
      array_ref_oprocess in_scope p
  | Get(tbl,patl,topt,p1,p2) ->
      List.iter (array_ref_pattern in_scope) patl;
      let in_scope' = vars_from_pat_list in_scope patl in
      (match topt with 
         | Some t -> array_ref_term in_scope' t
         | None -> ());
      array_ref_oprocess in_scope' p1;
      array_ref_oprocess in_scope p2
  | Insert(tbl,tl,p) ->
      List.iter (array_ref_term in_scope) tl;
      array_ref_oprocess in_scope p


let rec array_ref_fungroup in_scope = function
    ReplRestr(repl, restr, funlist) ->
      List.iter (array_ref_fungroup ((List.map fst restr) @ in_scope)) funlist
  | Fun(ch, args, res, priority) ->
      array_ref_term (args @ in_scope) res
      
let cleanup_array_ref() =
  List.iter (fun b ->
    b.count_def <- 0;
    b.root_def_array_ref <- false;
    b.root_def_std_ref <- false;
    b.array_ref <- false;
    b.std_ref <- false;
    b.count_array_ref <- 0;
    b.count_exclude_array_ref <- 0) (!all_vars);
  all_vars := []

let array_ref_process p =
  cleanup_array_ref();
  array_ref_process [] p

let array_ref_eqside rm =
  cleanup_array_ref();
  List.iter (fun (fg, _) -> array_ref_fungroup [] fg) rm

let has_array_ref b =
  b.root_def_array_ref || b.array_ref

let has_array_ref_q b =
  (has_array_ref b) || (Settings.occurs_in_queries b)

(* Functions that compute count_exclude_array_ref.
   The goal is to be able to easily determine if a variable has array
   references in the game outside a certain expression.
   One first computes array references in the full game, then
   one calls exclude_array_ref_term/exclude_array_ref_def_list on the
   part to exclude. 
   b has an array reference in the remaining part iff
   b.count_array_ref > b.count_exclude_array_ref *)

let all_vars_exclude = ref []

let add_exclude b =
  if not (List.memq b (!all_vars_exclude)) then
    all_vars_exclude := b :: (!all_vars_exclude)

let rec exclude_array_ref_term in_scope t = 
  match t.t_desc with
    Var(b, l) -> 
      if not (is_args_at_creation b l &&
	List.memq b in_scope) then
	begin
      	  b.count_exclude_array_ref <- b.count_exclude_array_ref + 1;
	  add_exclude b
	end;
      List.iter (exclude_array_ref_term in_scope) l
  | ReplIndex i -> ()
  | FunApp(_,l) ->
      List.iter (exclude_array_ref_term in_scope)  l
  | TestE(t1,t2,t3) ->
      exclude_array_ref_term in_scope t1;
      exclude_array_ref_term in_scope t2;
      exclude_array_ref_term in_scope t3
  | LetE(pat, t1, t2, topt) ->
      exclude_array_ref_pattern in_scope pat;
      exclude_array_ref_term in_scope t1;
      exclude_array_ref_term (vars_from_pat in_scope pat) t2;
      begin
	match topt with
	  None -> ()
	| Some t3 -> exclude_array_ref_term in_scope t3
      end
  | FindE(l0,t3,_) ->
      List.iter (fun (bl,def_list,t1,t2) ->
	let in_scope' = (List.map fst bl) @ in_scope in
	exclude_array_ref_def_list in_scope def_list;
	exclude_array_ref_term in_scope t1;
	exclude_array_ref_term in_scope' t2) l0;
      exclude_array_ref_term in_scope t3
  | ResE(b,t) ->
      exclude_array_ref_term (b::in_scope) t
  | EventAbortE _ -> ()
  | EventE(t,p) ->
      exclude_array_ref_term in_scope t;
      exclude_array_ref_term in_scope p
  | GetE(tbl,patl,topt,p1,p2) -> 
      List.iter (exclude_array_ref_pattern in_scope) patl;
      let in_scope' = vars_from_pat_list in_scope patl in
      begin
	match topt with
	  None -> ()
	| Some t -> exclude_array_ref_term in_scope' t
      end;
      exclude_array_ref_term in_scope' p1;
      exclude_array_ref_term in_scope p2
  | InsertE(tbl,tl,p) ->
      List.iter (exclude_array_ref_term in_scope) tl;
      exclude_array_ref_term in_scope p

and exclude_array_ref_pattern in_scope = function
    PatVar b -> ()
  | PatTuple (f,l) -> List.iter (exclude_array_ref_pattern in_scope) l
  | PatEqual t -> exclude_array_ref_term in_scope t

and exclude_array_ref_def_list in_scope' def_list = 
  List.iter (fun (b,l) -> 
    List.iter (exclude_array_ref_term in_scope') l;
    if not (is_args_at_creation b l &&
	    List.memq b in_scope') then
      begin
	b.count_exclude_array_ref <- b.count_exclude_array_ref + 1;
        add_exclude b
      end) def_list

let cleanup_exclude_array_ref() =
  List.iter (fun b ->
    b.count_exclude_array_ref <- 0) (!all_vars_exclude);
  all_vars_exclude := []

let has_array_ref_non_exclude b =
  b.count_array_ref > b.count_exclude_array_ref

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
  t.t_incompatible <- map_empty;
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
  | GetE(tbl,patl,topt,p1,p2) -> 
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
  p.i_incompatible <- map_empty;
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
  p.p_incompatible <- map_empty;
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
  | Get(tbl,patl,topt,p1,p2) -> 
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
  | GetE(_,_,_,_,_) | InsertE (_,_,_) -> 
      internal_error "Get/Insert should have been reduced at this point"

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
  | Get(_,_,_,_,_) | Insert (_,_,_) -> 
      internal_error "Get/Insert should have been reduced at this point"


let build_compatible_defs p = 
  compatible_def_process 0 map_empty p

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

(* [both_pp_add_fact fact_accu (args, pp) (args', pp')] 
   adds to [fact_accu] a fact inferred from the execution of both
   program point [pp] with indices [args] and 
   program point [pp'] with indices [args'], if any.*)
	
let both_pp_add_fact fact_accu (args, pp) (args', pp') =
  try
    let suffix_l = incompatible_suffix_length_pp pp pp' in
    let args_skip = lsuffix suffix_l args in
    let args_skip' = lsuffix suffix_l args' in
    (make_or_list (List.map2 make_diff args_skip args_skip')) :: fact_accu
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
    let args_skip = lsuffix suffix_l args in
    let args_skip' = lsuffix suffix_l args' in
    (not (List.for_all2 equal_terms args_skip args_skip'))
  with Not_found -> true)

(* [is_compatible_node (b,args) n (b',args')] returns true when
   [b[args]] and [b'[args']] may both be defined, with [b[args]]
   defined at node [n]. *)

let is_compatible_node (b,args) n (b',args') =
  (b == b') || 
  (try
    let suffix_l = incompatible_suffix_length_onepp n.definition_success b' in
    (*print_string ("incompatible_suffix_length 1 " ^ b.sname ^ "_" ^ (string_of_int b.vname) ^ " " ^ b'.sname ^ "_" ^ (string_of_int b'.vname) ^ " = "); print_int suffix_l; print_newline(); *)
    let args_skip = lsuffix suffix_l args in
    let args_skip' = lsuffix suffix_l args' in
    (not (List.for_all2 equal_terms args_skip args_skip'))
  with Not_found -> true)

(* [both_def_add_fact fact_accu (b,args) (b',args')]
   adds to [fact_accu] a fact that always holds when
   [b[args]] and [b'[args']] are both defined, if any. *)

let both_def_add_fact fact_accu (b,args) (b',args') =
  if b != b' then 
    try
      let suffix_l = incompatible_suffix_length b b' in
      let args_skip = lsuffix suffix_l args in
      let args_skip' = lsuffix suffix_l args' in
      (make_or_list (List.map2 make_diff args_skip args_skip')) :: fact_accu
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
  let new_def_list = List.filter (fun br -> not (mem_binderref br old_def_list)) def_list in
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
    let args_skip = lsuffix suffix_l args in
    let args_skip' = lsuffix suffix_l args' in
    (make_or_list (List.map2 make_diff args_skip args_skip')) :: fact_accu
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
  if n.above_node == n then
    (* n is the initial node *)
    n.definition
  else
    match n.definition with
      DInputProcess({ i_desc = Input _}) as pp -> pp
    | _ -> get_start_block_pp n.above_node

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
    | Some(cur_array,_,_,_,_) -> cur_array
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

(* [incompatible_nodelist_different_block_suffix_length (nl, args) n]
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
    let args_skip = lsuffix suffix_l args in
    let args_skip' = lsuffix suffix_l history.cur_array in
    (not (List.for_all2 equal_terms args_skip args_skip'))
  with Not_found -> true) &&
  (List.for_all (fun (nl',args') ->
    try
      let suffix_l = incompatible_nodelist_different_block_suffix_length (nl', args') n in
      let args_skip = lsuffix suffix_l args in
      let args_skip' = lsuffix suffix_l args' in
      (not (List.for_all2 equal_terms args_skip args_skip'))
    with Not_found -> true
	) history.def_vars_in_different_blocks) && 
  (List.for_all (fun (nl',args') ->
    try
      let suffix_l = incompatible_nodelist_same_block_suffix_length (nl', args') n in
      let args_skip = lsuffix suffix_l args in
      let args_skip' = lsuffix suffix_l args' in
      (not (List.for_all2 equal_terms args_skip args_skip'))
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
      let args_skip = lsuffix suffix_l args in
      let args_skip' = lsuffix suffix_l history.cur_array in
      (make_or_list (List.map2 make_diff args_skip args_skip')) :: fact_accu
    with Not_found -> fact_accu
  in
  let fact_accu2 =
    List.fold_left (fun fact_accu (nl',args') ->
      try
	let suffix_l = map_max (incompatible_nodelist_different_block_suffix_length (nl', args')) nl in
	let args_skip = lsuffix suffix_l args in
	let args_skip' = lsuffix suffix_l args' in
	(make_or_list (List.map2 make_diff args_skip args_skip')) :: fact_accu
    with Not_found -> fact_accu
	) fact_accu1 history.def_vars_in_different_blocks
  in
  List.fold_left (fun fact_accu (nl',args') ->
    try
      let suffix_l = map_max (incompatible_nodelist_same_block_suffix_length (nl', args')) nl in
      let args_skip = lsuffix suffix_l args in
      let args_skip' = lsuffix suffix_l args' in
      (make_or_list (List.map2 make_diff args_skip args_skip')) :: fact_accu
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
    let args_skip = lsuffix suffix_l args in
    let args_skip' = lsuffix suffix_l args' in
    (make_or_list (List.map2 make_diff args_skip args_skip')) :: fact_accu
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
   [b[args]] may be defined before [b'[args']] *)

let may_def_before (b,args) (b',args') = 
  (b == b') || 
  (try
    let length_cur_array_b' = List.length args' in
    let suffix_l = map_max (fun n -> not_after_suffix_length_one_pp n.definition_success length_cur_array_b' b) b'.def in
    let args_skip = lsuffix suffix_l args in
    let args_skip' = lsuffix suffix_l args' in
    (not (List.for_all2 equal_terms args_skip args_skip'))
  with Not_found -> true)

(* Update args_at_creation: since variables in conditions of find have
as args_at_creation the indices of the find, transformations of the
find may lead to changes in these indices.  This function updates
these indices. It relies on the invariant that variables in conditions
of find have no array accesses, and that new/event do not occur in
conditions of find. It creates fresh variables for all variables
defined in the condition of the find. *)

let rec update_args_at_creation cur_array t =
  match t.t_desc with
    Var(b,l) ->
      begin
      match b.link with
	NoLink -> build_term2 t (Var(b, List.map (update_args_at_creation cur_array) l))
      |	TLink t' -> 
	  (* Variable b is defined in the current find condition, 
             it has no array accesses *)
	  t'
      end
  | ReplIndex b -> t
  | FunApp(f,l) -> build_term2 t (FunApp(f, List.map (update_args_at_creation cur_array) l))
  | ResE _ | EventAbortE _ | EventE _ | GetE _ | InsertE _ ->
      Parsing_helper.internal_error "new/event/event_abort/get/insert should not occur as term in find condition" 
  | TestE(t1,t2,t3) ->
       build_term2 t (TestE(update_args_at_creation cur_array t1,
			    update_args_at_creation cur_array t2,
			    update_args_at_creation cur_array t3))
  | FindE(l0,t3,find_info) ->
      let l0' = 
	List.map (fun (bl, def_list, t1, t2) ->
	  let repl_indices = List.map snd bl in
	  let cur_array_cond = repl_indices @ cur_array in
	  let def_list' = List.map (update_args_at_creation_br cur_array_cond) def_list in
	  let t1' = update_args_at_creation cur_array_cond t1 in
	  let bl' = List.map (fun (b,b') ->
	    let b1 = create_binder b.sname b.btype cur_array in
	    link b (TLink (term_from_binder b1));
	    (b1, b')) bl 
	  in
	  let t2' = update_args_at_creation cur_array t2 in
	  (bl', def_list', t1', t2')
	  ) l0
      in
      build_term2 t (FindE(l0',
				 update_args_at_creation cur_array t3,
				 find_info))
  | LetE(pat, t1, t2, topt) ->
      let t1' = update_args_at_creation cur_array t1 in
      let pat' = update_args_at_creation_pat cur_array pat in
      let t2' = update_args_at_creation cur_array t2 in
      let topt' = 
	match topt with
	  None -> None
	| Some t3 -> Some (update_args_at_creation cur_array t3)
      in
      build_term2 t (LetE(pat', t1', t2', topt'))

and update_args_at_creation_br cur_array (b,l) =
  begin
    match b.link with
      NoLink -> (b, List.map (update_args_at_creation cur_array) l)
    | TLink t' -> 
        (* Variable b is defined in the current find condition, 
           it has no array accesses *)
	binderref_from_term t'
  end

and update_args_at_creation_pat cur_array = function
    PatVar b ->
      let b' = create_binder b.sname b.btype cur_array in
      link b (TLink (term_from_binder b'));
      PatVar b'
  | PatTuple(f,l) ->
      PatTuple(f, List.map (update_args_at_creation_pat cur_array) l)
  | PatEqual t ->
      PatEqual (update_args_at_creation cur_array t)
      

let update_args_at_creation cur_array t =
  auto_cleanup (fun () ->
    update_args_at_creation cur_array t)

(* get needed def_list elements *)

let rec get_needed_deflist_term defined accu t =
  match t.t_desc with
    Var(b,l) -> 
      let br = (b,l) in
      if not (mem_binderref br defined) then
	add_binderref br accu
  | ReplIndex i -> ()
  | FunApp(f,l) -> List.iter (get_needed_deflist_term defined accu) l
  | TestE(t1,t2,t3) -> 
      get_needed_deflist_term defined accu t1;
      get_needed_deflist_term defined accu t2;
      get_needed_deflist_term defined accu t3
  | FindE(l0,t3, find_info) ->
      List.iter (fun (bl, def_list, t, t1) ->
	let (defined_t, defined_t1) = defined_refs_find bl def_list defined in
	get_needed_deflist_term defined_t accu t;
	get_needed_deflist_term defined_t1 accu t1
	) l0;
      get_needed_deflist_term defined accu t3
  | LetE(pat,t1,t2,topt) ->
      get_needed_deflist_pat defined accu pat;
      get_needed_deflist_term defined accu t1;
      let bpat = vars_from_pat [] pat in
      let defs = List.map binderref_from_binder bpat in
      get_needed_deflist_term (defs @ defined) accu t2;
      begin
	match topt with
	  None -> ()
	| Some t3 -> get_needed_deflist_term defined accu t3
      end
  | ResE(b,t) -> get_needed_deflist_term ((binderref_from_binder b)::defined) accu t
  | EventAbortE f -> ()
  | EventE(t,p) ->
      get_needed_deflist_term defined accu t;
      get_needed_deflist_term defined accu p
  | GetE(tbl,patl,topt,p1,p2) ->
      List.iter (get_needed_deflist_pat defined accu) patl;
      let bpat = List.fold_left vars_from_pat [] patl in
      let defs = (List.map binderref_from_binder bpat) @ defined in
      (match topt with None -> () | Some t -> get_needed_deflist_term defs accu t);
      get_needed_deflist_term defs accu p1;
      get_needed_deflist_term defined accu p2
  | InsertE(tbl,tl,p) ->
      List.iter (get_needed_deflist_term defined accu) tl;
      get_needed_deflist_term defined accu p

and get_needed_deflist_pat defined accu = function
    PatVar _ -> ()
  | PatTuple(f,l) -> List.iter (get_needed_deflist_pat defined accu) l
  | PatEqual t -> get_needed_deflist_term defined accu t

let rec get_needed_deflist_process defined accu p = 
  match p.i_desc with
    Nil -> ()
  | Par(p1,p2) -> get_needed_deflist_process defined accu p1;
      get_needed_deflist_process defined accu p2
  | Repl(b,p) -> get_needed_deflist_process defined accu p
  | Input((c,tl),pat,p) ->
      List.iter (get_needed_deflist_term defined accu) tl;
      get_needed_deflist_pat defined accu pat;
      let bpat = vars_from_pat [] pat in
      let defs = List.map binderref_from_binder bpat in
      get_needed_deflist_oprocess (defs @ defined) accu p

and get_needed_deflist_oprocess defined accu p =
  match p.p_desc with
    Yield | EventAbort _ -> ()
  | Restr(b,p) -> get_needed_deflist_oprocess ((binderref_from_binder b)::defined) accu p
  | Test(t,p1,p2) -> 
      get_needed_deflist_term defined accu t;
      get_needed_deflist_oprocess defined accu p1;
      get_needed_deflist_oprocess defined accu p2
  | Find(l0,p2, find_info) ->
      List.iter (fun (bl, def_list, t, p1) ->
	let (defined_t, defined_p1) = defined_refs_find bl def_list defined in
	get_needed_deflist_term defined_t accu t;
	get_needed_deflist_oprocess defined_p1 accu p1
	) l0;
      get_needed_deflist_oprocess defined accu p2
  | Let(pat,t,p1,p2) ->
      get_needed_deflist_pat defined accu pat;
      get_needed_deflist_term defined accu t;
      let bpat = vars_from_pat [] pat in
      let defs = List.map binderref_from_binder bpat in
      get_needed_deflist_oprocess (defs @ defined) accu p1;
      get_needed_deflist_oprocess defined accu p2
  | Output((c,tl),t2,p) ->
      List.iter (get_needed_deflist_term defined accu) tl;
      get_needed_deflist_term defined accu t2;
      get_needed_deflist_process defined accu p
  | EventP(t,p) ->
      get_needed_deflist_term defined accu t;
      get_needed_deflist_oprocess defined accu p
  | Get(tbl,patl,topt,p1,p2) ->
      List.iter (get_needed_deflist_pat defined accu) patl;
      let bpat = List.fold_left vars_from_pat [] patl in
      let defs = (List.map binderref_from_binder bpat) @ defined in
      (match topt with None -> () | Some t -> get_needed_deflist_term defs accu t);
      get_needed_deflist_oprocess defs accu p1;
      get_needed_deflist_oprocess defined accu p2
  | Insert(tbl,tl,p) ->
      List.iter (get_needed_deflist_term defined accu) tl;
      get_needed_deflist_oprocess defined accu p

(********** Use the equational theory to simplify a term *************)

(* Remark: applying remove_consecutive_inverse and remove_inverse_ends
to t1 * inv(t2) does the same job as applying 
- remove_consecutive_inverse to t1 and to t2, 
- remove_common_prefix and remove_common_suffix to the obtained t1 t2, 
- and remove_inverse_ends to t1 in case t2 is the neutral element and conversely.
We do the latter below. (One advantage is that the form of the simplified
term is then closer to the initial term.) *)

let rec remove_common_prefix simp_facts reduced l1 l2 = 
  match (l1,l2) with
    t1::r1, t2::r2 when simp_equal_terms simp_facts true t1 t2 -> 
      reduced := true;
      remove_common_prefix simp_facts reduced r1 r2
  | _ -> (l1,l2)
      
let remove_common_suffix simp_facts reduced l1 l2 = 
  let l1rev = List.rev l1 in
  let l2rev = List.rev l2 in
  let (l1rev',l2rev') = remove_common_prefix simp_facts reduced l1rev l2rev in
  (List.rev l1rev', List.rev l2rev')

let is_fun f t =
  match t.t_desc with
    FunApp(f',_) -> f == f' 
  | _ -> false

(* collect_first_inverses inv [] [inv(t1); ... inv(tn); rest] 
   is ([tn; ...; t1], rest) *)

let rec collect_first_inverses inv accu = function
    [] -> (accu, [])
  | (t::l) ->
      match t.t_desc with
	FunApp(f,[tinv]) when f == inv -> 
	  collect_first_inverses inv (tinv::accu) l
      |	_ -> (accu, t::l)

(* when l = inv(t1) * ... * inv(tn) * rest' * inv(t'_n') * ... * inv(t'_1),
   collect_first_and_last_inverses is
   (l1',l2') = (tn * ... * t1 * l1 * t'_1 * ... * t'_n', rest)
   so that l = l1 is equivalent to l1' = l2'.
   (Lists represent products.) *)

let collect_first_and_last_inverses reduced inv l1 l =
  let (first_inv, rest) = collect_first_inverses inv [] l in
  (* first_inv = tn * ... * t1, rest = rest' * inv(t'_n') * ... * inv(t'_1) *)
  let rest_rev = List.rev rest in
  (* rest_rev = inv(t'_1) * ... * inv(t'_n') * List.rev rest' *)
  let (last_inv_rev, rest_rev') = collect_first_inverses inv [] rest_rev in
  (* last_inv_rev = t'_n' * ... * t'_1, rest_rev' = List.rev rest' *)
  if first_inv != [] || last_inv_rev != [] then reduced := true;
  (first_inv @ l1 @ (List.rev last_inv_rev), List.rev rest_rev')

(* apply_eq_reds implements reduction rules coming from the
   equational theories, as well as
     not (x = y) -> x != y
     not (x != y) -> x = y
     x = x -> true
     x != x -> false
     ?x != t -> false where ?x is a general variable (universally quantified)
(These rules cannot be stored in file default, because there are several
functions for = and for !=, one for each type.)
*)

let rec apply_eq_reds simp_facts reduced t =
  match t.t_desc with
(* not (x = y) -> x != y
   not (x != y) -> x = y *)
    FunApp(fnot, [t']) when fnot == Settings.f_not ->
      begin
      let t' = try_no_var simp_facts t' in
      match t'.t_desc with
	FunApp(feq, [t1;t2]) when feq.f_cat == Equal ->
	  reduced := true;
	  apply_eq_reds simp_facts reduced (make_diff t1 t2)
      |	FunApp(fdiff, [t1;t2]) when fdiff.f_cat == Diff ->
	  reduced := true;
	  apply_eq_reds simp_facts reduced (make_equal t1 t2)
      |	_ -> make_not (apply_eq_reds simp_facts reduced t')
      end

(* simplify inv(M): inv(neut) -> neut; inv(inv(M)) -> M; inv(M * M') -> inv(M') * inv(M) *)
  | FunApp({f_eq_theories = (Group(f,inv',n) | CommutGroup(f,inv',n)) } as inv, [t']) when inv' == inv ->
      (* inv is an inverse function *)
      let t' = apply_eq_reds simp_facts reduced t' in
      compute_inv (try_no_var simp_facts) reduced (f,inv',n) t'

(* Simplify and/or when one side is known to be true/false
   It is important that this case is tested before the more general case below. *)
  | FunApp(f,[t1;t2]) when f == Settings.f_and ->
      let t1' = apply_eq_reds simp_facts reduced t1 in
      let t2' = apply_eq_reds simp_facts reduced t2 in
      if (is_true t1') || (is_false t2') then
	begin
	  reduced := true; t2'
	end
      else if (is_true t2') || (is_false t1') then
	begin
	  reduced := true; t1'
	end
      else
	build_term2 t (FunApp(f, [t1';t2']))
  | FunApp(f,[t1;t2]) when f == Settings.f_or ->
      let t1' = apply_eq_reds simp_facts reduced t1 in
      let t2' = apply_eq_reds simp_facts reduced t2 in
      if (is_false t1') || (is_true t2') then
	begin
	  reduced := true; t2'
	end
      else if (is_false t2') || (is_true t1') then
	begin
	  reduced := true; t1'
	end
      else
	build_term2 t (FunApp(f, [t1';t2']))

(* simplify products: eliminate factors that cancel out *)
  | FunApp(f,[t1;t2]) when f.f_eq_theories != NoEq && f.f_eq_theories != Commut &&
    f.f_eq_theories != Assoc && f.f_eq_theories != AssocCommut ->
      (* f is a binary function with an equational theory that is
	 not commutativity nor inverse -> it is a product-like function *)
      begin
	match f.f_eq_theories with
	  NoEq | Commut | Assoc | AssocCommut -> 
	    Parsing_helper.internal_error "Terms.apply_eq_reds: cases NoEq, Commut, Assoc, AssocCommut should have been eliminated"
	| AssocN(_, neut) | AssocCommutN(_, neut) -> 
	    (* eliminate the neutral element *)
	    if is_fun neut t1 then 
	      begin
		reduced := true;
		apply_eq_reds simp_facts reduced t2
	      end
	    else if is_fun neut t2 then
	      begin
		reduced := true;
		apply_eq_reds simp_facts reduced t1
	      end
	    else
	      build_term2 t (FunApp(f, [ apply_eq_reds simp_facts reduced t1;
					 apply_eq_reds simp_facts reduced t2 ]))	      
	| Group _ | CommutGroup _ | ACUN _ ->
	    (* eliminate factors that cancel out and the neutral element *)
	    let reduced' = ref false in
	    let l1 = simp_prod simp_facts reduced' f t in
	    if !reduced' then
	      begin
		reduced := true;
		let l1 = List.map (apply_eq_reds simp_facts reduced) l1 in
		make_prod f l1
	      end
	    else
	      build_term2 t (FunApp(f, [ apply_eq_reds simp_facts reduced t1;
					 apply_eq_reds simp_facts reduced t2 ]))
      end

(* simplify equalities and inequalities:
     x = x -> true
     x != x -> false
as well as equalities between products *)
  | FunApp(f, [t1;t2]) when (f.f_cat == Equal || f.f_cat == Diff) ->
      begin
	if simp_equal_terms simp_facts true t1 t2 then
	  begin
	    reduced := true;
	    match f.f_cat with
	      Equal -> make_true()
	    | Diff -> make_false()
	    | _ -> assert false
	  end
	else
	match get_prod_list (try_no_var simp_facts) [t1;t2] with
	  ACUN(xor,neut) ->
	    let reduced' = ref false in
	    let l1 = simp_prod simp_facts reduced' xor (app xor [t1;t2]) in
	    if !reduced' then
	      begin
		reduced := true;
		let l1 = List.map (apply_eq_reds simp_facts reduced) l1 in
		match l1 with
		  [] -> 
		    begin
		      match f.f_cat with
			Equal -> make_true()
		      | Diff -> make_false()
		      | _ -> assert false
		    end
		| t1::l -> build_term2 t (FunApp(f,[t1;make_prod xor l]))
		      (* The number of terms that appear here is always strictly
			 less than the initial number of terms:
			 the number of terms in l1 is strictly less than the number of terms
			 in t1 plus t2; make_prod introduces an additional neutral
			 term when l = []; in this case, we have two terms 
			 in the final result, and at least 3 in the initial t1 = t2,
			 since the side that contains the XOR symbol returned by get_prod_list
			 contains at least two terms. 
			 Hence, we always really simplify the term. *)
	      end
	    else
	      build_term2 t (FunApp(f, [ apply_eq_reds simp_facts reduced t1;
					 apply_eq_reds simp_facts reduced t2 ]))
	| CommutGroup(prod,inv,neut) ->
	    let reduced' = ref false in
	    let lmix =
	      if is_fun neut t1 then
		let l2 = simp_main_fun (try_no_var simp_facts) reduced' prod t2 in
		reduced' := (!reduced') || (List.exists (is_fun inv) l2);
		l2
	      else if is_fun neut t2 then
		let l1 = simp_main_fun (try_no_var simp_facts) reduced' prod t1 in
		reduced' := (!reduced') || (List.exists (is_fun inv) l1);
		l1
	      else
		let l1 = simp_main_fun (try_no_var simp_facts) reduced' prod t1 in
		let l2 = simp_main_fun (try_no_var simp_facts) reduced' prod t2 in
		reduced' := (!reduced') || (List.exists (is_fun inv) l1) ||
		  (List.exists (is_fun inv) l2);
		l1 @ (List.map (compute_inv (try_no_var simp_facts) reduced' (prod, inv, neut)) l2)
	        (* t2 = t1 is equivalent to t1 * t2^-1 = neut *)

	      (* It is important to treat the cases t1 or t2 neutral specially above.
		 Otherwise, we would leave M1 * M2 = neut unchanged, while still setting
		 reduced to true because simp_prod eliminates neut.

		 reduced' is set when t1 or t2 contains an inverse,
		 since this inverse will be removed by the final
		 building of the result below. *)
	    in
	    let l1 = remove_inverse simp_facts reduced' (prod,inv,neut) lmix in
	    if !reduced' then
	      begin
		reduced := true;
		let l1 = List.map (apply_eq_reds simp_facts reduced) l1 in
		match l1 with
		  [] -> 
		    begin
		      match f.f_cat with
			Equal -> make_true()
		      | Diff -> make_false()
		      | _ -> assert false
		    end
		| l -> 
		    let linv, lno_inv = List.partition (is_fun inv) l in
		    let linv_removed = List.map (function { t_desc = FunApp(f,[t]) } when f == inv -> t | _ -> assert false) linv in
		    build_term2 t (FunApp(f, [ make_prod prod lno_inv; 
					       make_prod prod linv_removed ]))
	      end
	    else
	      build_term2 t (FunApp(f, [ apply_eq_reds simp_facts reduced t1;
					 apply_eq_reds simp_facts reduced t2 ]))
	| Group(prod,inv,neut) ->
	    let reduced' = ref false in
	    let l1 = 
	      (* When t1 is the neutral element, applying simp_prod would
		 set reduced' to true, so one would iterate simplification.
		 However, the neutral element will be reintroduced by
		 make_prod below, so that could lead to a loop. 
		 We detect this special case, and avoid setting reduced'
		 in this case. *)
	      if is_fun neut t1 then [] else
	      simp_prod simp_facts reduced' prod t1 
	    in
	    let l2 = 
	      if is_fun neut t2 then [] else
	      simp_prod simp_facts reduced' prod t2 
	    in
	    let (l1',l2') = remove_common_prefix simp_facts reduced' l1 l2 in
	    let (l1'',l2'') = remove_common_suffix simp_facts reduced' l1' l2' in
	    let l1'' = if l2'' == [] then remove_inverse_ends simp_facts reduced' (prod, inv, neut) l1'' else l1'' in
	    let l2'' = if l1'' == [] then remove_inverse_ends simp_facts reduced' (prod, inv, neut) l2'' else l2'' in
	    let (l1'', l2'') = collect_first_and_last_inverses reduced' inv l1'' l2'' in
	    let (l1'', l2'') = collect_first_and_last_inverses reduced' inv l2'' l1'' in
	    if !reduced' then
	      begin
		reduced := true;
		let l1 = List.map (apply_eq_reds simp_facts reduced) l1'' in
		let l2 = List.map (apply_eq_reds simp_facts reduced) l2'' in
		match l1,l2 with
		  [],[] -> 
		    begin
		      match f.f_cat with
			Equal -> make_true()
		      | Diff -> make_false()
		      | _ -> assert false
		    end
		| _ -> 
		    build_term2 t (FunApp(f, [ make_prod prod l1; 
					       make_prod prod l2 ]))
	      end
	    else
	      build_term2 t (FunApp(f, [ apply_eq_reds simp_facts reduced t1;
					 apply_eq_reds simp_facts reduced t2 ]))
	| _ -> 
	    build_term2 t (FunApp(f, [ apply_eq_reds simp_facts reduced t1;
				       apply_eq_reds simp_facts reduced t2 ]))
      end

(* ?x <> t is always false when ?x is a general variable (universally quantified) *)
  | FunApp(f,[{t_desc = Var(b,[])};t2]) when f.f_cat == ForAllDiff && 
    b.sname == gvar_name && not (refers_to b t2) -> 
      reduced := true;
      make_false()      
  | FunApp(f,[t2;{t_desc = Var(b,[])}]) when f.f_cat == ForAllDiff && 
    b.sname == gvar_name && not (refers_to b t2) -> 
      reduced := true;
      make_false()      

(* Simplify subterms *)
  | FunApp(f,l) ->
      build_term2 t (FunApp(f, List.map (apply_eq_reds simp_facts reduced) l))
  | _ -> t


