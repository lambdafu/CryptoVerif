open Types
open Parsing_helper

(* Returns a list containing n times element x *)

let rec repeat n x =
  if n = 0 then [] else x :: (repeat (n-1) x)

(* Returns l without its n first elements *)

let rec skip n l = 
  try
    if n = 0 then l else skip (n-1) (List.tl l)
  with Failure "tl" ->
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
  with Failure "Terms.skip" ->
    failwith "Terms.lsuffix"

(* Remove a suffix of length n *)

let remove_suffix n l =
  let (res, _) = split (List.length l - n) l in
  res

(* [map_concat f l] applied f to each element of l,
   and concatenates the result. Duplicate elements in the result
   are removed. *)

let equal_mset mset1 mset2 =
  match (mset1, mset2) with
    (MAll, MAll) -> true
  | (MOneBinder b1, MOneBinder b2) -> b1 == b2
  | _ -> false

let equal_rset rset1 rset2 =
  match (rset1, rset2) with
    (All, All) | (Minimal, Minimal) -> true
  | (OneBinder b1, OneBinder b2) -> b1 == b2
  | (SubstOneBinder (b1,occ1), SubstOneBinder (b2, occ2)) -> (b1 == b2) && (occ1 == occ2)
  | _ -> false

let equal_query q1 q2 =
  match (q1,q2) with
    (QSecret b1, QSecret b2) -> b1 == b2
  | (QSecret1 b1, QSecret1 b2) -> b1 == b2
  | _ -> false

let equal_instruct i1 i2 =
  match i1,i2 with
    (ExpandIfFind, ExpandIfFind) | (Simplify, Simplify) -> true
  | (RemoveAssign rset1, RemoveAssign rset2) -> equal_rset rset1 rset2
  | (SArenaming b1, SArenaming b2) -> b1 == b2
  | (MoveNew mset1, MoveNew mset2) -> equal_mset mset1 mset2
  | (CryptoTransf (eq1, bl1), CryptoTransf (eq2, bl2)) -> (eq1 == eq2) && 
      (List.length bl1 == List.length bl2) && (List.for_all2 (==) bl1 bl2)
  | (Proof ql1, Proof ql2) ->
      (List.length ql1 == List.length ql2) && (List.for_all2 (fun (q1,p1) (q2,p2) -> (equal_query q1 q2) && (p1 = p2)) ql1 ql2)
  | _ -> false

let add_eq a l =
  if List.exists (equal_instruct a) l then l else a::l

let rec union_eq l1 = function
    [] -> l1
  | (a::l) ->
      if List.exists (equal_instruct a) l1 then union_eq l1 l else
      a::(union_eq l1 l)

let rec map_concat f = function
    [] -> []
  | (a::l) -> union_eq (f a) (map_concat f l)
      
(* Create an interval type from a parameter *)

let type_for_param_table = Hashtbl.create 7

let type_for_param p =
  try 
    Hashtbl.find type_for_param_table p 
  with Not_found ->
    let t = { tname = "[1," ^ p.pname ^"]";
	      tcat = Interv p;
	      toptions = Settings.tyopt_BOUNDED }
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

let new_occ() =
  incr occ;
  !occ

(* Binder from term *)

let binder_from_term t =
  match t.t_desc with
    Var(b,_) -> b
  | _ -> internal_error "Binder term expected"

let term_from_binder b =
  { t_desc = Var(b, b.args_at_creation);
    t_type = b.btype;
    t_occ = new_occ() }

let term_from_binderref (b,l) =
  { t_desc = Var(b, l);
    t_type = b.btype;
    t_occ = new_occ() }

(* Constant for each type *)

let cst_for_type_table = Hashtbl.create 7

let cst_for_type ty =
  try
    Hashtbl.find cst_for_type_table ty
  with Not_found ->
    let r = { t_desc = FunApp({ f_name = "cst_" ^ ty.tname;
				f_type = [],ty;
				f_cat = Std;
				f_options = 0 },[]);
	      t_type = ty;
	      t_occ = -1 }
    in
    Hashtbl.add cst_for_type_table ty r;
    r

(* Is a type large? (i.e. the inverse of its cardinal is negligible) *)

let is_large t =
  (t.toptions land Settings.tyopt_LARGE) != 0

(* Is a variable defined by a restriction ? *)

let is_restr b =
  List.for_all (function 
      { definition = DProcess (Restr _) } -> true
    | { definition = DTerm ({ t_desc = ResE _}) } -> true
    | { definition = DFunRestr } -> true
    | _ -> false) b.def

let is_repl b =
  List.for_all (function 
      { definition = DInputProcess (Repl _) } -> true
    | { definition = DFunRepl } -> true
    | _ -> false) b.def

let is_assign b =
  List.for_all (function 
      { definition = DProcess (Let _) } -> true
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

let rec equal_terms t1 t2 = 
  match (t1.t_desc, t2.t_desc) with
    Var(b1,l1),Var(b2,l2) ->
      (b1 == b2) && (List.for_all2 equal_terms l1 l2)
  | FunApp(f1,[t1;t1']),FunApp(f2,[t2;t2']) when f1 == f2 && f1.f_options land Settings.fopt_COMMUT != 0 ->
      (* Commutative function symbols *)
      ((equal_terms t1 t2) && (equal_terms t1' t2')) ||
      ((equal_terms t1 t2') && (equal_terms t1' t2))
  | FunApp(f1,l1),FunApp(f2,l2) ->
      (f1 == f2) && (List.for_all2 equal_terms l1 l2)
  | TestE(t1,t2,t3), TestE(t1',t2',t3') ->
      (equal_terms t1 t1') && (equal_terms t2 t2') && (equal_terms t3 t3')
  | FindE(l,t3,_),FindE(l',t3',_) ->
      (* Could do modulo renaming of bl and bl'! *)
      (List.length l == List.length l') &&
      (List.for_all2 (fun (bl,def_list,otheruses_list,t1,t2) (bl',def_list',otheruses_list',t1',t2') ->
	(List.for_all2 (==) bl bl') && 
	(equal_def_lists def_list def_list') && 
	(equal_def_lists otheruses_list otheruses_list') &&
	(equal_terms t1 t1') && (equal_terms t2 t2')) l l') && 
      (equal_terms t3 t3')
  | LetE(pat, t1, t2, topt), LetE(pat', t1', t2', topt') ->
      (equal_pats pat pat') &&
      (equal_terms t1 t1') &&
      (equal_terms t2 t2') &&
      (match topt, topt' with
	None, None -> true
      |	Some t3, Some t3' -> equal_terms t3 t3'
      |	_ -> false)
  | ResE(b,t), ResE(b',t') ->
      (b == b') && (equal_terms t t')
  | _ -> false

and equal_def_lists def_list def_list' =
  (List.length def_list == List.length def_list') &&
  (List.for_all2 (fun (b,l) (b',l') -> (b == b') && 
    (List.for_all2 equal_terms l l')) def_list def_list')

and equal_pats p1 p2 =
  match p1,p2 with
    PatVar b, PatVar b' -> b == b'
  | PatTuple (f,l), PatTuple (f',l') -> (f == f') && (List.for_all2 equal_pats l l')
  | PatEqual t, PatEqual t' -> equal_terms t t'
  | _ -> false

let equal_term_lists l1 l2 =
  (List.length l1 == List.length l2) &&
  (List.for_all2 equal_terms l1 l2)

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
  | AOut(tl,t), AOut(tl',t') -> (t == t') && (List.length tl == List.length tl') && (List.for_all2 (==) tl tl')
  | AIn n, AIn n' -> n == n'
  | _ -> false
  
let rec equal_probaf p1 p2 =
  match p1, p2 with
    Proba(p, l), Proba(p',l') -> (p == p') && (List.length l == List.length l') && (List.for_all2 equal_probaf l l')
  | Count p, Count p' -> p == p'
  | Cst f, Cst f' -> f = f'
  | Zero, Zero -> true
  | Card t, Card t' -> t == t'
  | AttTime, AttTime -> true
  | Time (n,p), Time (n',p') -> (n == n') && (equal_probaf p p')
  | ActTime(a,l), ActTime(a',l') -> (equal_action a a') && (List.length l == List.length l') && (List.for_all2 equal_probaf l l')
  | Add(p1,p2), Add(p1',p2') -> (equal_probaf p1 p1') && (equal_probaf p2 p2')
  | Mul(p1,p2), Mul(p1',p2') -> (equal_probaf p1 p1') && (equal_probaf p2 p2')
  | Sub(p1,p2), Sub(p1',p2') -> (equal_probaf p1 p1') && (equal_probaf p2 p2')
  | Div(p1,p2), Div(p1',p2') -> (equal_probaf p1 p1') && (equal_probaf p2 p2')
  | Max l, Max l' -> (List.length l == List.length l') && (List.for_all2 equal_probaf l l')
  | Maxlength(n,t),Maxlength(n',t') -> (n == n') && (equal_terms t t')
  | Length(f,l), Length(f',l') -> (f == f') && (List.length l == List.length l') && (List.for_all2 equal_probaf l l')
  | _ -> false

(* Compute the length of the longest common prefix *)

let rec len_common_prefix l1 l2 =
  match (l1, l2) with
    [], _ | _, [] -> 0
  | (a1::l1,a2::l2) ->
      if equal_terms a1 a2 then 1 + len_common_prefix l1 l2 else 0

(* Compute the length of the longest common suffix *)

let len_common_suffix l1 l2 =
  len_common_prefix (List.rev l1) (List.rev l2)

(* Copy term, following one level of links *)

(* NOTE: cases TestE/LetE/FindE/ResE may be removed *)
let rec copy_term t = 
  match t.t_desc with
    Var(b,l) ->
      begin
	match b.link with
	  NoLink -> 
	  { t_desc = Var(b,List.map copy_term l);
	    t_type = t.t_type;
	    t_occ = new_occ() }
	| TLink t -> t
      end
  | FunApp(f,l) ->
      { t_desc = FunApp(f, List.map copy_term l);
	t_type = t.t_type;
	t_occ = new_occ() }	
  | TestE(t1,t2,t3) ->
      { t_desc = TestE(copy_term t1, copy_term t2, copy_term t3);
	t_type = t.t_type;
	t_occ = new_occ() }
  | LetE(pat, t1, t2, topt) ->
      let topt' = match topt with
	None -> None
      |	Some t3 -> Some (copy_term t3)
      in
      { t_desc = LetE(copy_pat pat, copy_term t1, copy_term t2, topt');
	t_type = t.t_type;
	t_occ = new_occ() }
  | FindE(l, t3, def_node_opt) -> 
      let l' = List.map (fun (bl, def_list, otheruses_list, t1, t2) -> 
	let def_list' = List.map (fun (b,l) ->
	  (b, List.map copy_term l)) def_list in
	let otheruses_list' = List.map (fun (b,l) ->
	  (b, List.map copy_term l)) otheruses_list in
	(bl, def_list', otheruses_list', copy_term t1, copy_term t2)) l 
      in
      { t_desc = FindE(l', copy_term t3, def_node_opt);
	t_type = t.t_type;
	t_occ = new_occ() }
  | ResE(b,t) ->
      { t_desc = ResE(b, copy_term t);
	t_type = t.t_type;
	t_occ = new_occ() }	
      

and copy_pat = function
  PatVar b -> PatVar b
| PatTuple (f,l) -> PatTuple(f,List.map copy_pat l)
| PatEqual t -> PatEqual(copy_term t)

(* Compute term { l / cur_array } *)

let subst cur_array l term =
  List.iter2 (fun b t -> link b (TLink t)) cur_array l;
  let term' = copy_term term in
  cleanup();
  term'


(* Substitution taking into account array indexes *)

(* The code of copy_term2 requires that linked values do not
   contain themselves links to other terms, at the call site of
   copy_term2 *)

(* NOTE: cases TestE/LetE/FindE/ResE may be removed *)
let rec copy_term2 t = 
  match t.t_desc with
    Var(b,l) ->
      let l' = List.map copy_term2 l in
      begin
	match b.link with
	  NoLink -> 
	    { t_desc = Var(b,l');
	      t_type = t.t_type;
	      t_occ = new_occ() }
	| TLink t ->
            auto_cleanup (fun () ->
	        (* rename array indexes *)
              List.iter2 (fun tb ti ->
                let bi = binder_from_term tb in
                match ti.t_desc with
                  Var(bi',[]) when bi == bi' -> ()
                | _ -> 
                    match bi.link with
                      NoLink -> link bi (TLink ti)
                    | _ -> Parsing_helper.internal_error "Cyclic assignment! Should never happen."
			  ) b.args_at_creation l';
	      copy_term t)
      end
  | FunApp(f,l) ->
      { t_desc = FunApp(f, List.map copy_term2 l);
	t_type = t.t_type;
	t_occ = new_occ() }	
  | TestE(t1,t2,t3) ->
      { t_desc = TestE(copy_term2 t1, copy_term2 t2, copy_term2 t3);
	t_type = t.t_type;
	t_occ = new_occ() }
  | LetE(pat, t1, t2, topt) ->
      let topt' = match topt with
	None -> None
      |	Some t3 -> Some (copy_term2 t3)
      in
      { t_desc = LetE(copy_pat2 pat, copy_term2 t1, copy_term2 t2, topt');
	t_type = t.t_type;
	t_occ = new_occ() }
  | FindE(l, t3, def_node_opt) -> 
      let l' = List.map (fun (bl, def_list, otheruses_list, t1, t2) ->
	let def_list' = List.map (fun (b,l) ->
	  (b, List.map copy_term2 l)) def_list in
	let otheruses_list' = List.map (fun (b,l) ->
	  (b, List.map copy_term2 l)) otheruses_list in
	(bl, def_list', otheruses_list', copy_term2 t1, copy_term2 t2)) l
      in
      { t_desc = FindE(l', copy_term2 t3, def_node_opt);
	t_type = t.t_type;
	t_occ = new_occ() }
  | ResE(b,t) ->
      { t_desc = ResE(b, copy_term2 t);
	t_type = t.t_type;
	t_occ = new_occ() }
      
	
and copy_pat2 = function
  PatVar b -> PatVar b
| PatTuple (f,l) -> PatTuple(f,List.map copy_pat2 l)
| PatEqual t -> PatEqual(copy_term2 t)

(* subst is a list (b,t) of binders and their image by the substitution.
   The image must not contain binders in the domain of the substitution *)

let subst2 subst t =
  auto_cleanup (fun () ->
    List.iter (fun (b,t') -> link b (TLink t')) subst;
    copy_term2 t)


(* Substitution of v[v.args_at_creation] only *)

(* NOTE: cases TestE/LetE/FindE/ResE may be removed *)
let rec copy_term3 t = 
  match t.t_desc with
    Var(b,l) ->
      begin
	match b.link with
	  TLink t when List.for_all2 equal_terms l b.args_at_creation ->
	    t
	| _ -> 
	    { t_desc = Var(b,List.map copy_term3 l);
	      t_type = t.t_type;
	      t_occ = new_occ() }
      end
  | FunApp(f,l) ->
      { t_desc = FunApp(f, List.map copy_term3 l);
	t_type = t.t_type;
	t_occ = new_occ() }	
  | TestE(t1,t2,t3) ->
      { t_desc = TestE(copy_term3 t1, copy_term3 t2, copy_term3 t3);
	t_type = t.t_type;
	t_occ = new_occ() }
  | LetE(pat, t1, t2, topt) ->
      let topt' = match topt with
	None -> None
      |	Some t3 -> Some (copy_term3 t3)
      in
      { t_desc = LetE(copy_pat3 pat, copy_term3 t1, copy_term3 t2, topt');
	t_type = t.t_type;
	t_occ = new_occ() }
  | FindE(l, t3, def_node_opt) -> 
      let l' = List.map (fun (bl, def_list, otheruses_list, t1, t2) ->
	let def_list' = List.map (fun (b,l) ->
	  (b, List.map copy_term3 l)) def_list in
	let otheruses_list' = List.map (fun (b,l) ->
	  (b, List.map copy_term3 l)) otheruses_list in
	(bl, def_list', otheruses_list', copy_term3 t1, copy_term3 t2)) l
      in
      { t_desc = FindE(l', copy_term3 t3, def_node_opt);
	t_type = t.t_type;
	t_occ = new_occ() }
  | ResE(b,t) ->
      { t_desc = ResE(b, copy_term3 t);
	t_type = t.t_type;
	t_occ = new_occ() }
      
	
and copy_pat3 = function
  PatVar b -> PatVar b
| PatTuple (f,l) -> PatTuple(f,List.map copy_pat3 l)
| PatEqual t -> PatEqual(copy_term3 t)


  
(* Term from pattern *)

let rec term_from_pat = function
    PatVar b -> term_from_binder b
  | PatTuple (f,l) -> 
      { t_desc = FunApp(f, List.map term_from_pat l);
	t_type = snd f.f_type;
	t_occ = new_occ() }
  | PatEqual t -> t

(* New variable name *)

let vcounter = ref 0

let new_vname() =
  incr vcounter;
  !vcounter

let new_binder b0 =
  { sname = b0.sname;
    vname = new_vname();
    btype = b0.btype;
    args_at_creation = b0.args_at_creation;
    def = b0.def;
    link = NoLink }

(* Find out whether a term is a conjunction of "defined(...)" conditions *)

type binderref = binder * term list

let equal_binderref (b,l) (b',l') =
  (b == b') && (List.for_all2 equal_terms l l')

let rec mem_binderref br = function
    [] -> false
  | (a::l) -> (equal_binderref br a) || (mem_binderref br l)

let add_binderref a accu =
  if mem_binderref a (!accu) then () else accu := a :: (!accu)

let setminus_binderref s1 s2 =
  List.filter (fun br -> not (mem_binderref br s2)) s1

let inter_binderref s1 s2 =
  List.filter (fun br -> mem_binderref br s2) s1

(* get def_list subterms *)

let rec get_deflist_subterms accu t =
  match t.t_desc with
    Var(b,l) -> add_binderref (b,l) accu
  | FunApp(f,l) -> List.iter (get_deflist_subterms accu) l
  | _ -> Parsing_helper.internal_error "if/let/find forbidden in defined conditions of find"

let rec get_def_list_pat accu = function
    PatVar _ -> ()
  | PatTuple(f,l) -> List.iter (get_def_list_pat accu) l
  | PatEqual t -> get_deflist_subterms accu t

let rec get_deflist_process accu = function
    Nil -> ()
  | Par(p1,p2) -> get_deflist_process accu p1;
      get_deflist_process accu p2
  | Repl(b,p) -> get_deflist_process accu p
  | Input((c,tl),pat,p) ->
      List.iter (get_deflist_subterms accu) tl;
      get_def_list_pat accu pat;
      get_deflist_oprocess accu p

and get_deflist_oprocess accu = function
    Yield -> ()
  | Restr(b,p) -> get_deflist_oprocess accu p
  | Test(t,p1,p2) -> 
      get_deflist_subterms accu t;
      get_deflist_oprocess accu p1;
      get_deflist_oprocess accu p2
  | Find(l0,p2,_) ->
      List.iter (fun (bl, def_list, otheruses_list, t, p1) ->
	get_deflist_subterms accu t;
	get_deflist_oprocess accu p1
	) l0;
      get_deflist_oprocess accu p2
  | Let(pat,t,p1,p2) ->
      get_def_list_pat accu pat;
      get_deflist_subterms accu t;
      get_deflist_oprocess accu p1;
      get_deflist_oprocess accu p2
  | Output((c,tl),t2,p) ->
       List.iter (get_deflist_subterms accu) tl;
      get_deflist_subterms accu t2;
      get_deflist_process accu p
  | EventP(t,p) ->
      get_deflist_subterms accu t;
      get_deflist_oprocess accu p
      

(* Check whether a term t refers to a binder b0 *)

let no_def = ref false

let rec refers_to b0 t = 
  match t.t_desc with
    Var (b,l) -> 
      (b == b0) || (List.exists (refers_to b0) l) ||
      (match b.link with
	 TLink t -> refers_to b0 t
       | _ -> false)
  | FunApp(f,l) -> List.exists (refers_to b0) l
  | TestE(t1,t2,t3) -> (refers_to b0 t1) || (refers_to b0 t2) || (refers_to b0 t3)
  | ResE(b,t) -> refers_to b0 t
  | FindE(l0,t3,_) -> 
      (List.exists (fun (bl,def_list,otheruses_list,t1,t2) ->
	(List.exists (fun (b, l) -> ((not (!no_def)) && (b == b0)) || 
                                     List.exists (refers_to b0) l) def_list) ||
	(List.exists (fun (b, l) -> ((not (!no_def)) && (b == b0)) || 
                                     List.exists (refers_to b0) l) otheruses_list) ||
	(refers_to b0 t1) || (refers_to b0 t2)) l0) || 
      (refers_to b0 t3)
  | LetE(pat, t1, t2, topt) ->
      (refers_to_pat b0 pat) ||
      (refers_to b0 t1) || (refers_to b0 t2) ||
      (match topt with
	None -> false
      |	Some t3 -> refers_to b0 t3)

and refers_to_pat b0 = function
    PatVar b -> false
  | PatTuple (f,l) -> List.exists (refers_to_pat b0) l
  | PatEqual t -> refers_to b0 t 

let rec refers_to_process b0 = function
    Nil -> false
  | Par(p1,p2) -> (refers_to_process b0 p1) || (refers_to_process b0 p2)
  | Repl(b,p) -> refers_to_process b0 p
  | Input((c,tl),pat,p) -> 
      (List.exists (refers_to b0) tl) || (refers_to_pat b0 pat) || (refers_to_oprocess b0 p)

and refers_to_oprocess b0 = function
    Yield -> false
  | Restr(b,p) -> refers_to_oprocess b0 p
  | Test(t,p1,p2) -> (refers_to b0 t) || (refers_to_oprocess b0 p1) ||
    (refers_to_oprocess b0 p2)
  | Find(l0,p2,_) ->
      (List.exists (fun (bl,def_list,otheruses_list,t,p1) ->
	(List.exists (fun (b, l) -> ((not (!no_def)) && (b == b0)) || 
                                     List.exists (refers_to b0) l) def_list) ||
	(List.exists (fun (b, l) -> ((not (!no_def)) && (b == b0)) || 
                                     List.exists (refers_to b0) l) otheruses_list) ||
        (refers_to b0 t) || (refers_to_oprocess b0 p1)) l0) || 
      (refers_to_oprocess b0 p2)
  | Output((c,tl),t2,p) ->
      (List.exists (refers_to b0) tl) || (refers_to b0 t2) || (refers_to_process b0 p)
  | EventP(t,p) ->
      (refers_to b0 t) || (refers_to_oprocess b0 p)
  | Let(pat,t,p1,p2) ->
      (refers_to b0 t) || (refers_to_pat b0 pat) || 
      (refers_to_oprocess b0 p1) ||(refers_to_oprocess b0 p2)

let rec refers_to_fungroup b = function
    ReplRestr(_,_,funlist) ->
      List.exists (refers_to_fungroup b) funlist
  | Fun(_,res) -> refers_to b res

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
  { t_desc = FunApp(Settings.c_true, []);
    t_type = Settings.t_bool;
    t_occ = new_occ() }
  
let make_false () =
  { t_desc = FunApp(Settings.c_false, []);
    t_type = Settings.t_bool;
    t_occ = new_occ() }

let make_and t t' =
  if (is_false t) || (is_false t') then make_false() else
  if is_true t then t' else
  if is_true t' then t else
  { t_desc = FunApp(Settings.f_and, [t;t']);
    t_type = Settings.t_bool;
    t_occ = new_occ() }

let make_or t t' =
  if (is_true t) || (is_true t') then make_true() else
  if is_false t then t' else
  if is_false t' then t else
  { t_desc = FunApp(Settings.f_or, [t;t']);
    t_type = Settings.t_bool;
    t_occ = new_occ() }

let rec make_and_list = function
    [] -> make_true()
  | [a] -> a
  | (a::l) -> make_and a (make_and_list l)

let rec make_or_list = function
    [] -> make_false()
  | [a] -> a
  | (a::l) -> make_or a (make_or_list l)

let make_not t =
  { t_desc = FunApp(Settings.f_not, [t]);
    t_type = Settings.t_bool;
    t_occ = new_occ() }
  
let make_equal t t' =
  { t_desc = FunApp(Settings.f_comp Equal t.t_type t'.t_type, [t;t']);
    t_type = Settings.t_bool;
    t_occ = new_occ() }

let make_let_equal t t' =
  { t_desc = FunApp(Settings.f_comp LetEqual t.t_type t'.t_type, [t;t']);
    t_type = Settings.t_bool;
    t_occ = new_occ() }

let make_diff t t' =
  { t_desc = FunApp(Settings.f_comp Diff t.t_type t'.t_type, [t;t']);
    t_type = Settings.t_bool;
    t_occ = new_occ() }

(* Compute intersections *)

let rec intersect eqtest l = function
    [] -> []
  | (a'::l') -> 
      let l'' = intersect eqtest l l' in
      if List.exists (eqtest a') l then 
	a'::l'' 
      else
	l''

let rec intersect_list eqtest = function
    [] -> Parsing_helper.internal_error "Intersection of nothing"
  | [a] -> a
  | (a::l) -> intersect eqtest a (intersect_list eqtest l)

(* Building tests / lets *)

let make_let_proc pat t p1 p2 =
  Let(pat, t, p1, p2)

let make_let_term ty pat t1 t2 topt =
  { t_desc = LetE(pat, t1, t2, topt);
    t_type = ty;
    t_occ = new_occ() }

let make_test_proc t p1 p2 =
  Test(t,p1,p2)

let make_test_term ty t1 t2 topt =
  match topt with
    Some t3 ->
      { t_desc = TestE(t1, t2, t3);
	t_type = ty;
	t_occ = new_occ() }
  | None -> 
      Parsing_helper.internal_error "Missing else in letE"
  
let rec put_lets make_let l1 l2 p1 p2 = 
  match (l1,l2) with
    [],[] -> p1
  | (a1::l1),(a2::l2) ->
      make_let a1 a2 (put_lets make_let l1 l2 p1 p2) p2
  | _ -> Parsing_helper.internal_error "Different lengths in put_lets"

exception Impossible

let rec split_term f0 t = 
  match t.t_desc with
    Var(_,_) -> 
      (* TO DO when the variable is created by a restriction,
         it is different from a tuple with high probability *)
      raise Not_found
  | FunApp(f,l) when f == f0 -> l
  | FunApp(f,l) -> 
      if f0.f_cat == Tuple && (f.f_cat == Tuple || (f.f_cat == Std && l == [] && (!Settings.constants_not_tuple))) then
	raise Impossible
      else
	raise Not_found
  | TestE _ | FindE _ | LetE _ | ResE _ ->
      Parsing_helper.internal_error "If, find, and let should have been expanded (Simplify)"


  
(* Change the occurrences *)

let rec move_occ_term t = 
  { t_desc = 
    begin
      match t.t_desc with
	Var(b,l) -> Var(b, List.map move_occ_term l)
      |	FunApp(f,l) -> FunApp(f, List.map move_occ_term l)
      |	TestE(t1,t2,t3) -> TestE(move_occ_term t1, 
				 move_occ_term t2, 
				 move_occ_term t3)
      |	FindE(l0,t3,def_node_opt) -> 
	  FindE(List.map (fun (bl,def_list,otheruses_list,t1,t2) ->
	          (bl, 
		   List.map (fun (b,l) -> (b, List.map move_occ_term l)) def_list,
		   List.map (fun (b,l) -> (b, List.map move_occ_term l)) otheruses_list,
		   move_occ_term t1,
		   move_occ_term t2)) l0,
		move_occ_term t3, def_node_opt)
      |	LetE(pat, t1, t2, topt) ->
	  LetE(move_occ_pat pat, move_occ_term t1, 
	       move_occ_term t2, 
	       match topt with
		 None -> None
	       | Some t3 -> Some (move_occ_term t3))
      |	ResE(b,t) ->
	  ResE(b, move_occ_term t)
    end;
    t_type = t.t_type;
    t_occ = new_occ() }

and move_occ_pat = function
    PatVar b -> PatVar b
  | PatTuple (f,l) -> PatTuple(f,List.map move_occ_pat l)
  | PatEqual t -> PatEqual(move_occ_term t)

let rec move_occ_process = function
    Nil -> Nil
  | Par(p1,p2) -> Par(move_occ_process p1, move_occ_process p2)
  | Repl(b,p) -> Repl(b, move_occ_process p)
  | Input((c,tl),pat,p) ->
      Input((c, List.map move_occ_term tl), move_occ_pat pat, move_occ_oprocess p)

and move_occ_oprocess = function
    Yield -> Yield
  | Restr(b,p) -> Restr(b, move_occ_oprocess p)
  | Test(t,p1,p2) -> Test(move_occ_term t, move_occ_oprocess p1,
			  move_occ_oprocess p2)
  | Find(l0, p2, def_node_opt) -> 
      Find(List.map (fun (bl, def_list, otheruses_list, t, p1) -> 
	     (bl, 
	      List.map (fun (b,l) -> (b, List.map move_occ_term l)) def_list,
	      List.map (fun (b,l) -> (b, List.map move_occ_term l)) otheruses_list,
	      move_occ_term t,
	      move_occ_oprocess p1)) l0,
           move_occ_oprocess p2, def_node_opt)
  | Let(pat,t,p1,p2) ->
      Let(move_occ_pat pat, move_occ_term t,
	  move_occ_oprocess p1,
	  move_occ_oprocess p2)
  | Output((c,tl),t2,p) ->
      Output((c, List.map move_occ_term tl), move_occ_term t2, move_occ_process p)
  | EventP(t,p) ->
      EventP(move_occ_term t, move_occ_oprocess p)

(* Empty tree of definition dependances *)


let rec empty_def_term t =
  match t.t_desc with
    Var(b,l) ->
      b.def <- [];
      empty_def_term_list l
  | FunApp(_,l) ->
      empty_def_term_list l
  | TestE(t1,t2,t3) ->
      empty_def_term t2;
      empty_def_term t3;
      empty_def_term t1
  | FindE(l0,t3,def_node_opt) ->
      def_node_opt := None;
      List.iter (fun (bl,def_list,otheruses_list,t1,t2) ->
	List.iter (fun b -> b.def <- []) bl;
	empty_def_term_def_list def_list;
	empty_def_term_def_list otheruses_list;
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

and empty_def_term_list l = List.iter empty_def_term l

and empty_def_term_def_list def_list = 
  List.iter (fun (b,l) -> b.def <- []; empty_def_term_list l) def_list

and empty_def_pattern = function
    PatVar b -> b.def <- []
  | PatTuple (f,l) -> List.iter empty_def_pattern l
  | PatEqual t -> empty_def_term t

let rec empty_def_process = function
    Nil -> ()
  | Par(p1,p2) -> 
      empty_def_process p1;
      empty_def_process p2
  | Repl(b,p) ->
      b.def <- [];
      empty_def_process p
  | Input((c,tl),pat,p) ->
      List.iter empty_def_term tl;
      empty_def_pattern pat;
      empty_def_oprocess p

and empty_def_oprocess = function
    Yield -> ()
  | Restr(b,p) ->
      b.def <- [];
      empty_def_oprocess p
  | Test(t,p1,p2) ->
      empty_def_term t;
      empty_def_oprocess p1;
      empty_def_oprocess p2
  | Find(l0,p2, def_node_opt) ->
      def_node_opt := None;
      List.iter (fun (bl,def_list,otheruses_list,t,p1) ->
	List.iter (fun b -> b.def <- []) bl;
	empty_def_term_def_list def_list;
	empty_def_term_def_list otheruses_list;
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

(* Build tree of definition dependences *)

let rec close_def_subterm accu (b,l) =
  accu := (b,l) :: (!accu);
  List.iter (close_def_term accu) l

and close_def_term accu t =
  match t.t_desc with
    Var(b,l) -> close_def_subterm accu (b,l)
  | FunApp(f,l) -> List.iter (close_def_term accu) l
  | _ -> Parsing_helper.user_error "if/find/let forbidden in defined conditions of find"

let rec def_term above_node true_facts def_vars t =
  match t.t_desc with
    Var(b,l) ->
      def_term_list above_node true_facts def_vars l
  | FunApp(_,l) ->
      def_term_list above_node true_facts def_vars l
  | TestE(t1,t2,t3) ->
      let true_facts' = t1 :: true_facts in
      let true_facts'' = (make_not t1) :: true_facts in
      ignore(def_term above_node true_facts' def_vars t2);
      ignore(def_term above_node true_facts'' def_vars t3);
      def_term above_node true_facts def_vars t1
  | FindE(l0,t3,def_node_opt) ->
      def_node_opt := Some above_node;
      List.iter (fun (bl,def_list,otheruses_list,t1,t2) ->
	let true_facts' =  t1 :: true_facts in
	let accu = ref def_vars in
	List.iter (close_def_subterm accu) def_list;
	(*Nothing to do for otheruses_list (it does not define anything;
          it contains only Var and Fun)*)
	let def_vars' = !accu in
	let above_node' = { above_node = above_node; binders = bl; 
			    true_facts_at_def = true_facts'; 
			    def_vars_at_def = def_vars';
			    future_binders = []; future_true_facts = [];
			    future_def_vars = [];
			    definition = DTerm t } 
	in
	List.iter (fun b -> b.def <- above_node' :: b.def) bl;
	let above_node'' = def_term (def_term_def_list above_node' true_facts' def_vars' def_list) true_facts' def_vars' t1 in
	ignore(def_term above_node'' true_facts' def_vars' t2)) l0;
      ignore(def_term above_node true_facts def_vars t3);
      above_node
  | LetE(pat, t1, t2, topt) ->
      let above_node' = def_term above_node true_facts def_vars t1 in
      let accu = ref [] in
      let above_node'' = def_pattern accu above_node' true_facts def_vars pat in
      let true_facts' = ((match pat with PatVar _ -> make_let_equal | _ -> make_equal) (term_from_pat pat) t1) :: true_facts in
      let above_node''' = { above_node = above_node''; binders = !accu; 
			    true_facts_at_def = true_facts'; 
			    def_vars_at_def = def_vars;
			    future_binders = []; future_true_facts = [];
			    future_def_vars = [];
			    definition = DTerm t } 
      in
      List.iter (fun b -> b.def <- above_node''' :: b.def) (!accu);
      ignore (def_term above_node''' true_facts' def_vars t2);
      begin
	match topt with
	  None -> ()
	| Some t3 -> ignore(def_term above_node' true_facts def_vars t3)
      end;
      above_node'
  | ResE(b, t') ->
      let above_node' = { above_node = above_node; binders = [b]; 
			  true_facts_at_def = true_facts; 
			  def_vars_at_def = def_vars;
			  future_binders = []; future_true_facts = [];
			  future_def_vars = [];
			  definition = DTerm t } 
      in
      b.def <- above_node' :: b.def;
      def_term above_node' true_facts def_vars t'
      

and def_term_list above_node true_facts def_vars = function
    [] -> above_node
  | (a::l) -> def_term_list (def_term above_node true_facts def_vars a) true_facts def_vars l

and def_term_def_list above_node true_facts def_vars = function
    [] -> above_node
  | (b,l)::l' -> def_term_def_list (def_term_list above_node true_facts def_vars l) true_facts def_vars l'

and def_pattern accu above_node true_facts def_vars = function
    PatVar b -> accu := b :: (!accu); above_node
  | PatTuple (f,l) -> def_pattern_list accu above_node true_facts def_vars l
  | PatEqual t -> def_term above_node true_facts def_vars t

and def_pattern_list accu above_node true_facts def_vars = function
    [] -> above_node 
  | (a::l) -> def_pattern_list accu (def_pattern accu above_node true_facts def_vars a) true_facts def_vars l

let rec def_process event_accu above_node true_facts def_vars = function
    Nil -> ()
  | Par(p1,p2) -> 
      def_process event_accu above_node true_facts def_vars p1;
      def_process event_accu above_node true_facts def_vars p2
  | (Repl(b,p)) as p' ->
      let above_node' = { above_node = above_node; binders = [b]; 
			  true_facts_at_def = true_facts;
			  def_vars_at_def = def_vars;
			  future_binders = []; future_true_facts = [];
			  future_def_vars = [];
			  definition = DInputProcess p' } 
      in
      b.def <- above_node' :: b.def;
      def_process event_accu above_node' true_facts def_vars p
  | (Input((c,tl),pat,p)) as p' ->
      let above_node' = def_term_list above_node true_facts def_vars tl in
      let accu = ref [] in
      let above_node'' = def_pattern accu above_node' true_facts def_vars pat in
      let above_node''' = { above_node = above_node''; binders = !accu; 
			    true_facts_at_def = true_facts; 
			    def_vars_at_def = def_vars;
			    future_binders = []; future_true_facts = [];
			    future_def_vars = [];
			    definition = DInputProcess p' } 
      in
      List.iter (fun b -> b.def <- above_node''' :: b.def) (!accu);
      let (fut_binders, fut_true_facts, fut_def_vars) = 
	def_oprocess event_accu above_node''' true_facts def_vars p
      in
      above_node'''.future_binders <- fut_binders;
      above_node'''.future_true_facts <- fut_true_facts;
      above_node'''.future_def_vars <- fut_def_vars

and def_oprocess event_accu above_node true_facts def_vars = function
    Yield -> 
      ([],[],[])
  | (Restr(b,p)) as p' ->
      let above_node' = { above_node = above_node; binders = [b]; 
			  true_facts_at_def = true_facts; 
			  def_vars_at_def = def_vars;
			  future_binders = []; future_true_facts = [];
			  future_def_vars = [];
			  definition = DProcess p' } 
      in
      b.def <- above_node' :: b.def;
      let (fut_binders, fut_true_facts, fut_def_vars) = 
	def_oprocess event_accu above_node' true_facts def_vars p
      in
      above_node'.future_binders <- fut_binders;
      above_node'.future_true_facts <- fut_true_facts;
      above_node'.future_def_vars <- fut_def_vars;
      (b::fut_binders, fut_true_facts, fut_def_vars)
  | Test(t,p1,p2) ->
      let above_node' = def_term above_node true_facts def_vars t in
      let true_facts' = t :: true_facts in
      let true_facts'' = (make_not t) :: true_facts in
      let (fut_binders1, fut_true_facts1, fut_def_vars1) = 
	def_oprocess event_accu above_node' true_facts' def_vars p1
      in
      let (fut_binders2, fut_true_facts2, fut_def_vars2) = 
	def_oprocess event_accu above_node' true_facts'' def_vars p2
      in
      (intersect (==) fut_binders1 fut_binders2, 
       intersect equal_terms fut_true_facts1 fut_true_facts2,
       intersect equal_binderref fut_def_vars1 fut_def_vars2)
  | (Find(l0,p2,def_node_opt)) as p' ->
      def_node_opt := Some above_node;
      let (fut_binders2, fut_true_facts2, fut_def_vars2) = 
	def_oprocess event_accu above_node true_facts def_vars p2
      in
      let rec find_l = function
	  [] -> (fut_binders2, fut_true_facts2, fut_def_vars2)
	| (bl,def_list,otheruses_list,t,p1)::l ->
	    let (fut_bindersl, fut_true_factsl, fut_def_varsl) = find_l l in
	    let true_facts' = t :: true_facts in
	    let accu = ref [] in
	    List.iter (close_def_subterm accu) def_list;
	(*Nothing to do for otheruses_list (it does not define anything;
          it contains only Var and Fun) *)
	    let def_vars' = (!accu) @ def_vars in
	    let above_node' = { above_node = above_node; binders = bl; 
				true_facts_at_def = true_facts'; 
				def_vars_at_def = def_vars';
				future_binders = []; future_true_facts = [];
				future_def_vars = [];
				definition = DProcess p' } 
	    in
	    List.iter (fun b -> b.def <- above_node' :: b.def) bl;
	    let above_node'' = def_term (def_term_def_list above_node' true_facts' def_vars' def_list) true_facts' def_vars' t in
	    let (fut_binders1, fut_true_facts1, fut_def_vars1) = 
	      def_oprocess event_accu above_node'' true_facts' def_vars' p1
	    in
	    above_node'.future_binders <- fut_binders1;
	    above_node'.future_true_facts <- fut_true_facts1;
	    above_node'.future_def_vars <- fut_def_vars1;
	    (intersect (==) (bl @ fut_binders1) fut_bindersl,
	     intersect equal_terms (t::fut_true_facts1) fut_true_factsl,
	     intersect equal_binderref ((!accu) @ fut_def_vars1) fut_def_varsl)
      in
      find_l l0
  | Output((c,tl),t',p) ->
      let above_node' = def_term_list above_node true_facts def_vars  tl in
      let above_node'' = def_term above_node' true_facts def_vars t' in
      def_process event_accu above_node'' true_facts def_vars p;
      ([],[],[])
  | (Let(pat,t,p1,p2)) as p' ->
      let above_node' = def_term above_node true_facts def_vars t in
      let accu = ref [] in
      let above_node'' = def_pattern accu above_node' true_facts def_vars pat in
      let new_fact = (match pat with PatVar _ -> make_let_equal | _ -> make_equal) (term_from_pat pat) t in
      let true_facts' = new_fact :: true_facts in
      let above_node''' = { above_node = above_node''; binders = !accu; 
			    true_facts_at_def = true_facts'; 
			    def_vars_at_def = def_vars;
			    future_binders = []; future_true_facts = [];
			    future_def_vars = [];
			    definition = DProcess p' } 
      in
      List.iter (fun b -> b.def <- above_node''' :: b.def) (!accu);
      let (fut_binders1, fut_true_facts1, fut_def_vars1) = 
	def_oprocess event_accu above_node''' true_facts' def_vars p1
      in
      above_node'''.future_binders <- fut_binders1;
      above_node'''.future_true_facts <- fut_true_facts1;
      above_node'''.future_def_vars <- fut_def_vars1;
      begin
	match pat, p2 with
	  PatVar _, Yield -> 
	    ((!accu) @ fut_binders1, new_fact :: fut_true_facts1, fut_def_vars1)
	| _ -> 
	    let (fut_binders2, fut_true_facts2, fut_def_vars2) = 
	      def_oprocess event_accu above_node' true_facts def_vars p2
	    in
	    (intersect (==) ((!accu) @ fut_binders1) fut_binders2,
	     intersect equal_terms (new_fact :: fut_true_facts1) fut_true_facts2,
	     intersect equal_binderref fut_def_vars1 fut_def_vars2)
      end
  | EventP(t,p) ->
      begin
	match event_accu with
	  None -> ()
	| Some accu -> accu := (t, true_facts, above_node) :: (!accu)
      end;
      let above_node' = def_term above_node true_facts def_vars t in
      let (fut_binders, fut_true_facts, fut_def_vars) = 
	def_oprocess event_accu above_node' (t :: true_facts) def_vars p
      in
      (fut_binders, t::fut_true_facts, fut_def_vars)

let build_def_process event_accu p =
  empty_def_process p;
  let rec st_node = { above_node = st_node; 
		      binders = []; 
		      true_facts_at_def = []; 
		      def_vars_at_def = []; 
		      future_binders = []; future_true_facts = [];
		      future_def_vars = [];
		      definition = DNone } 
  in
  def_process event_accu st_node [] [] p

      
(* Build list of compatible binder definitions
   i.e. pairs of binders that can be simultaneously defined with
   the same array indexes *)

let rec union l1 = function
    [] -> l1
  | (a::l) -> 
      if List.memq a l1 then union l1 l else
      a::(union l1 l)

let compatible = ref []

let add_compatible l1 l2 =
  List.iter (fun a ->
    List.iter (fun b ->
      if a == b then
	Parsing_helper.internal_error "Same binder may be defined several times";
      compatible := (a,b):: (!compatible)) l2) l1

let rec compatible_def_term t = 
  match t.t_desc with
    Var(b,l) -> compatible_def_term_list l
  | FunApp(f,l) -> compatible_def_term_list l
  | TestE(t1,t2,t3) -> 
      let def1 = compatible_def_term t1 in
      let def2 = compatible_def_term t2 in
      let def3 = compatible_def_term t3 in
      add_compatible def1 def2;
      add_compatible def1 def3;
      union def1 (union def2 def3)
  | FindE(l0, t3,_) ->
      let def3 = compatible_def_term t3 in
      let accu = ref def3 in
      List.iter (fun (bl, def_list, otheruses_list, t1, t2) ->
	(*Nothing to for def_list and otheruses_list: they contain only
          Var and Fun*)
	let def1 = compatible_def_term t1 in
	let def2 = compatible_def_term t2 in
	add_compatible bl def1;
	add_compatible bl def2;
	add_compatible def1 def2;
	accu := union bl (union def1 (union def2 (!accu)))) l0;
      !accu
  | LetE(pat, t1, t2, topt) ->
      let accu = ref [] in
      let def1 = compatible_def_term t1 in
      let def2 = compatible_def_pat accu pat in
      let def3 = compatible_def_term t2 in
      let def4 = match topt with
	None -> []
      |	Some t3 -> compatible_def_term t3 
      in
      add_compatible (!accu) def1;
      add_compatible (!accu) def2;
      add_compatible (!accu) def3;
      add_compatible def1 def2;
      add_compatible def1 def3;
      add_compatible def2 def3;
      add_compatible def1 def4;
      add_compatible def2 def4;
      union (!accu) (union def1 (union def2 (union def3 def4)))
  | ResE(b,t) ->
      let def = compatible_def_term t in
      add_compatible def [b];
      union def [b]
      
      
and compatible_def_term_list = function
    [] -> []
  | (a::l) -> 
      let defl = compatible_def_term_list l in
      let defa = compatible_def_term a in
      add_compatible defl defa;
      union defa defl

and compatible_def_list = function
    [] -> []
  | ((b,l)::l') ->
      let defl = compatible_def_term_list l in
      let defl' = compatible_def_list l' in
      add_compatible defl defl';
      union defl' defl
      
and compatible_def_pat accu = function
    PatVar b -> accu := b :: (!accu); []
  | PatTuple (f,l) -> compatible_def_pat_list accu l
  | PatEqual t -> compatible_def_term t

and compatible_def_pat_list accu = function
    [] -> []
  | (a::l) -> 
      let defl = compatible_def_pat_list accu l in
      let defa = compatible_def_pat accu a in
      add_compatible defl defa;
      union defa defl

let rec compatible_def_process = function
    Nil -> []
  | Par(p1,p2) ->
      let def1 = compatible_def_process p1 in
      let def2 = compatible_def_process p2 in
      add_compatible def1 def2;
      union def1 def2
  | Repl(b,p) ->
      let def = compatible_def_process p in
      add_compatible def [b];
      union def [b]
  | Input((c,tl),pat,p) ->
      let accu = ref [] in
      let def1 = compatible_def_term_list tl in
      let def2 = compatible_def_pat accu pat in
      let def3 = compatible_def_oprocess p in
      add_compatible (!accu) def1;
      add_compatible (!accu) def2;
      add_compatible (!accu) def3;
      add_compatible def1 def2;
      add_compatible def1 def3;
      add_compatible def2 def3;
      union (!accu) (union def1 (union def2 def3))

and compatible_def_oprocess = function
    Yield -> []
  | Restr(b, p) ->
      let def = compatible_def_oprocess p in
      add_compatible def [b];
      union def [b]
  | Test(t,p1,p2) ->
      let def1 = compatible_def_term t in
      let def2 = compatible_def_oprocess p1 in
      let def3 = compatible_def_oprocess p2 in
      add_compatible def1 def2;
      add_compatible def1 def3;
      union def1 (union def2 def3)
  | Find(l0, p2,_) ->
      let def3 = compatible_def_oprocess p2 in
      let accu = ref def3 in
      List.iter (fun (bl, def_list, otheruses_list, t, p1) ->
	(*Nothing to for def_list and otheruses_list: they contain only
          Var and Fun*)
	let def1 = compatible_def_term t in
	let def2 = compatible_def_oprocess p1 in
	add_compatible bl def1;
	add_compatible bl def2;
	add_compatible def1 def2;
	accu := union bl (union def1 (union def2 (!accu)))) l0;
      !accu
  | Output((c,tl),t2,p) ->
      let def1 = compatible_def_term_list tl in
      let def2 = compatible_def_term t2 in
      let def3 = compatible_def_process p in
      add_compatible def1 def2;
      add_compatible def1 def3;
      add_compatible def2 def3;
      union def1 (union def2 def3)
  | Let(pat,t,p1,p2) ->
      let accu = ref [] in
      let def1 = compatible_def_term t in
      let def2 = compatible_def_pat accu pat in
      let def3 = compatible_def_oprocess p1 in
      let def4 = compatible_def_oprocess p2 in
      add_compatible (!accu) def1;
      add_compatible (!accu) def2;
      add_compatible (!accu) def3;
      add_compatible def1 def2;
      add_compatible def1 def3;
      add_compatible def2 def3;
      add_compatible def1 def4;
      add_compatible def2 def4;
      union (!accu) (union def1 (union def2 (union def3 def4)))
  | EventP(t,p) ->
      let def1 = compatible_def_term t in
      let def2 = compatible_def_oprocess p in
      add_compatible def1 def2;
      union def1 def2

let compatible_defs p = 
  compatible := [];
  ignore (compatible_def_process p);
  !compatible

(* Finds terms that can certainly not be evaluated in the same
   session (because they are in different branches of if/find/let) *)

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
  | TestE(t1,t2,t3) -> 
      let def1 = incompatible_def_term t1 in
      let def2 = incompatible_def_term t2 in
      let def3 = incompatible_def_term t3 in
      add_incompatible def2 def3;
      t::(def1 @ (def2 @ def3))
  | FindE(l0, t3,_) ->
      let def3 = incompatible_def_term t3 in
      let accu = ref def3 in
      List.iter (fun (bl, def_list, otheruses_list, t1, t2) ->
	let def = (incompatible_def_list def_list) 
	    @ (incompatible_def_list otheruses_list) 
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


let rec incompatible_def_process = function
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

and incompatible_def_oprocess = function
    Yield -> []
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
      List.iter (fun (bl, def_list, otheruses_list, t, p1) ->
	let def = (incompatible_def_list def_list) @
	  (incompatible_def_list otheruses_list) @
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

let incompatible_defs p = 
  incompatible_terms := [];
  ignore (incompatible_def_process p);
  !incompatible_terms
