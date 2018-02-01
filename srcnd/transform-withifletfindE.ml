open Types

let debug = false
let debug_print s = ()
  (* print_string s;
  print_newline() *)

(* Set when a game is modified *)

let changed = ref false

(* Instructions are added in advise when an instruction I cannot be fully
   performed. The added instructions correspond to suggestions of instructions
   to apply before I so that instruction I can be better performed. *)

let advise = ref ([] : instruct list)

(***************************************************************************)

let queries = ref []

let occurs_in_queries b =
  List.exists (function 
      QSecret b' -> b == b'
    | QSecret1 b' -> b == b'
    | QEventQ _ -> false) (!queries)

(***************************************************************************)

let statements = ref []

let collisions = ref []

let equivs = ref []

(***************************************************************************)


(* Expand all if, let, and find in expressions, so that they occur only in 
   processes. 

expand_term returns either
  None: the term is unchanged
  Some(f,l): a function f that takes a list of processes (of the same
  length as l) as argument and a list of terms l. 

expand_term_list returns either
  None: the list of terms is unchanged
  Some(f,l): a function f that takes a list of processes (of the same
  length as l) as argument and a list of lists of terms l. 

After expansion, if/let/find have disappeared from terms.
*)

exception CannotExpand

let rec cross_product l1 = function
    [] -> []
  | (a::l) -> (List.map (fun l1i -> (l1i,a)) l1) @ (cross_product l1 l)

let rec split_every n = function
    [] -> []
  | l ->
      let (l1,l2) = Terms.split n l in
      l1 :: (split_every n l2)

let rec check_no_ifletfindres t =
  match t.t_desc with
    Var(_,l) | FunApp(_,l) ->
      List.for_all check_no_ifletfindres l
  | TestE _ | FindE _ | LetE _ | ResE _ ->
      false

let check_no_ifletfind t =
  if not (check_no_ifletfindres t) then
    Parsing_helper.user_error "I cannot handle if, let, find, new inside the definition condition of a find. Sorry.\n"


(* Expand term to process *)

let pairing_expand a l aex lex =
  match aex, lex with
    None, None -> None
  | Some(fa,la),None -> Some(fa, List.map (fun lai -> (lai,l)) la)
  | None,Some(fl,ll) -> Some(fl, List.map (fun lli -> (a,lli)) ll)
  | Some(fa,la),Some(fl,ll) ->
      let len = List.length la in
      Some((fun l -> let l' = split_every len l in
                     fl (List.map fa l')), cross_product la ll)

let always_some t = function
    None -> ((fun [p] -> p), [t])
  | Some(f,l) -> (f,l)

let rec expand_term t = 
  match t.t_desc with
    Var(b,l) ->
      begin
        match expand_term_list l with
          None -> None
        | Some(f,l') ->
            Some(f, List.map (fun li -> { t_desc = Var(b,li); t_type = t.t_type; t_occ = Terms.new_occ() }) l')
      end  
  | FunApp(f,l) ->
      begin
        match expand_term_list l with
          None -> None
        | Some(f',l') -> Some(f', List.map (fun li -> { t_desc = FunApp(f,li); t_type = t.t_type; t_occ = Terms.new_occ() }) l')
      end
  | TestE(t1,t2,t3) ->
      (* I always expand this test *)
      let (f2, l2) = always_some t2 (expand_term t2) in
      let (f3, l3) = always_some t3 (expand_term t3) in
      let (f1, l1) = always_some t1 (expand_term t1) in
      let len2 = List.length l2 in
      Some((fun l -> 
	let (l2part, l3part) = Terms.split len2 l in
	f1 (List.map (fun t1i -> Test(t1i, f2 l2part, f3 l3part)) l1)), l2 @ l3)
  | LetE(pat, t1, t2, topt) ->
      let (fpat,lpat) = always_some pat (expand_pat pat) in
      let (f1,l1) = always_some t1 (expand_term t1) in
      let (f2,l2) = always_some t2 (expand_term t2) in
      begin
	match topt with
	  None ->
	    Some ((fun l -> 
	      f1 (List.map (fun t1i -> 
		fpat (List.map (fun pati ->
		  Let(pati, t1i, f2 l, Yield)) lpat)) l1)), l2)
	| Some t3 ->
	    let (f3,l3) = always_some t3 (expand_term t3) in
	    let len2 = List.length l2 in
	    Some ((fun l -> 
	      let (l2part, l3part) = Terms.split len2 l in
	      f1 (List.map (fun t1i -> 
		fpat (List.map (fun pati ->
		  Let(pati, t1i, f2 l2part, f3 l3part)) lpat)) l1)), l2 @ l3)
      end
  | FindE(l0, t3,_) ->
      let rec expand_find_list = function
	  [] -> ((fun l -> []), [])
	| ((bl, def_list, otheruses_list, t1, t2)::restl) ->
	    let (frestl, lrestl) = expand_find_list restl in
	    List.iter (fun (_,l) -> List.iter check_no_ifletfind l) def_list;
	    List.iter (fun (_,l) -> List.iter check_no_ifletfind l) otheruses_list;
            check_no_ifletfind t1;
	    let (f2, l2) = always_some t2 (expand_term t2) in
	    let len2 = List.length l2 in
	    ((fun l -> 
	      let (l2part, l3part) = Terms.split len2 l in
	      (bl, def_list, otheruses_list, t1, f2 l2part) :: (frestl l3part)),
	     l2 @ lrestl)
      in 
      let (f2, l2) = expand_find_list l0 in
      let (f3, l3) = always_some t3 (expand_term t3) in
      let len3 = List.length l3 in
      Some((fun l -> 
	let (l3part, l2part) = Terms.split len3 l in
        Find(f2 l2part, f3 l3part, ref None)), l3 @ l2)
  | ResE(b, t) ->
      let (f,l) = always_some t (expand_term t) in
      Some((fun l -> Restr(b, f l)), l)

and expand_term_list = function
  [] -> None
| (a::l) -> 
    let aex = expand_term a in
    let lex = expand_term_list l in
    match pairing_expand a l aex lex with
      None -> None
    | Some(f,l') -> Some(f, List.map (fun (a,l'') -> a::l'') l')

and expand_pat = function
    PatVar b -> None
  | PatTuple (ft,l) -> 
      begin
	match expand_pat_list l with
	  None -> None
	| Some(f,l') -> Some(f, List.map (fun li -> PatTuple (ft,li)) l')
      end 
  | PatEqual t -> 
      begin
	match expand_term t with
	  None -> None
	| Some(f,l) -> Some (f, List.map (fun ti -> PatEqual ti) l)
      end

and expand_pat_list = function
  [] -> None
| (a::l) -> 
    let aex = expand_pat a in
    let lex = expand_pat_list l in
    match pairing_expand a l aex lex with
      None -> None
    | Some(f,l') -> Some(f, List.map (fun (a,l'') -> a::l'') l')

(* Expand process to process *)

let rec expand_process cur_array = function
    Nil -> Nil
  | Par(p1,p2) -> Par(expand_process cur_array p1,
		      expand_process cur_array p2)
  | Repl(b,p) -> Repl(b, expand_process ((Terms.term_from_binder b)::cur_array) p)
  | Input((c,tl),pat,p) ->
      List.iter check_no_ifletfind tl;
      begin
	let patex = expand_pat pat in
	match patex with
	  None -> Input((c,tl),pat, expand_oprocess cur_array p)
	| Some(f,l) -> 
	    changed := true;
	    let b = { sname = "patv"; vname = Terms.new_vname();
		      btype = Settings.t_bitstring; 
		      args_at_creation = cur_array;
		      def = []; link = NoLink }
	    in
	    Input((c,tl),PatVar b, 
	      f (List.map (fun pati -> Let(pati,
		   { t_desc = Var(b, b.args_at_creation);
		     t_type = b.btype;
		     t_occ = Terms.new_occ() },
		 expand_oprocess cur_array p, Yield)) l))
      end

and expand_oprocess cur_array = function
    Yield -> Yield
  | Restr(b,p) -> Restr(b, expand_oprocess cur_array p)
  | Test(t,p1,p2) ->
	begin
	  match expand_term t with
	    None -> Test(t,expand_oprocess cur_array p1,
			 expand_oprocess cur_array p2)
	  | Some(f,l) ->
	      changed := true;
	      f (List.map (fun ti ->
		   Test(ti,expand_oprocess cur_array p1,
		        expand_oprocess cur_array p2)) l)
	end
  | Find(l0, p2, _) ->
      let rec expand_find_list next_f = function
	  [] -> next_f []
	| ((bl, def_list, otheruses_list, t, p1)::rest_l) ->
	    List.iter (fun (_,l) -> List.iter check_no_ifletfind l) def_list;
	    List.iter (fun (_,l) -> List.iter check_no_ifletfind l) otheruses_list;
	    let ex1 = expand_term t in
	    let ex1' = match ex1 with
	      None -> None
	    | Some(f,l) ->
		let fNil = f (List.map (fun _ -> Yield) l) in
		if List.exists (fun b -> Terms.refers_to_oprocess b fNil) bl then
		  raise CannotExpand
		else
		  ex1
	    in
	    match ex1' with
	      None -> 
		expand_find_list (fun rest_l' ->
		  next_f ((bl, def_list, otheruses_list, t, expand_oprocess cur_array p1)::rest_l')) rest_l
	    | Some(f,l) ->
		changed := true;
		f (List.map (fun ti -> expand_find_list (fun rest_l' ->
		  next_f ((bl, def_list, otheruses_list, ti, expand_oprocess cur_array p1)::rest_l')) rest_l) l)
      in
      expand_find_list (fun l0' -> Find(l0', expand_oprocess cur_array p2, ref None)) l0
  | Output((c,tl),t2,p) ->
      begin
	let tlex = expand_term_list tl in
	let t2ex = expand_term t2 in
	match pairing_expand tl t2 tlex t2ex with
	  None -> Output((c,tl),t2, expand_process cur_array p)
	| Some(f,l) -> 
	    changed := true;
	    f (List.map (fun (t1i,t2i) -> Output((c,t1i),t2i,expand_process cur_array p)) l)
      end
  | Let(pat,t,p1,p2) ->
      begin
	let tex = expand_term t in
	let patex = expand_pat pat in
	match pairing_expand t pat tex patex with
	  None -> Let(pat, t, expand_oprocess cur_array p1, 
		      expand_oprocess cur_array p2)
	| Some(f,l) -> 
	    changed := true;
	    f (List.map (fun (ti,pati) -> Let(pati,ti,expand_oprocess cur_array p1, expand_oprocess cur_array p2)) l)
      end
  | EventP(t,p) ->
      begin
	let tex = expand_term t in
	match tex with
	  None -> EventP(t, expand_oprocess cur_array p)
	| Some(f,l) ->
	    changed := true;
	    f (List.map (fun ti -> EventP(ti, expand_oprocess cur_array p)) l)
      end

(* Main function for expansion of if and find
   Call move_occ after expand_process, so that occurrences have distinct 
   numbers *)

let expand_process p =
  Terms.move_occ_process (expand_process [] p) 

(****************************************************************************)

(* When variable x is assigned at several places, 
   rename variable x into x1, ..., xn and duplicate code if necessary 

This transformation is programmed assuming that there are no FindE
in expressions! If FindE where present in expressions, we may need
to rename variables defined at those FindE.

*)

(* rename_term cur_array b0 b0' t renames b0[cur_array] into b0'[cur_array] *)


let rec rename_binder cur_array b0 b0' (b,l) =
  let l' = List.map (rename_term cur_array b0 b0') l in
  if (b == b0) && (List.for_all2 Terms.equal_terms l cur_array) then
    (b0', l')
  else
    (b,l')

(* NOTE: cases TestE/LetE/FindE/ResE may be removed *)
and rename_term cur_array b0 b0' t =
  { t_desc = 
    begin
      match t.t_desc with
	Var(b,l) ->
	  let (b',l') = rename_binder cur_array b0 b0' (b,l) in
	  Var(b',l')
      | FunApp(f,l) ->
	  FunApp(f, List.map (rename_term cur_array b0 b0') l)
      | TestE(t1,t2,t3) ->
          TestE(rename_term cur_array b0 b0' t1,
		rename_term cur_array b0 b0' t2,
		rename_term cur_array b0 b0' t3)
      | FindE(l0,t3, _) ->
          FindE(List.map (fun (bl, def_list, otheruses_list, t1,t2) ->
	          (bl, List.map (rename_binder cur_array b0 b0') def_list,
		   List.map (rename_binder cur_array b0 b0') otheruses_list,
		   rename_term cur_array b0 b0' t1,
		   rename_term cur_array b0 b0' t2)) l0,
		rename_term cur_array b0 b0' t3, ref None)
      | LetE(pat, t1, t2, topt) ->
	  LetE(rename_pat cur_array b0 b0' pat,
	       rename_term cur_array b0 b0' t1,
	       rename_term cur_array b0 b0' t2,
	       match topt with
		 Some t3 -> Some (rename_term cur_array b0 b0' t3)
	       | None -> None)
      |	ResE(b,t) ->
	  ResE(b,rename_term cur_array b0 b0' t)
    end;
    t_type = t.t_type;
    t_occ = t.t_occ }

and rename_pat cur_array b0 b0' = function
    PatVar b -> 
      (* if b == b0 then Parsing_helper.internal_error "rename_pat"; *)
      PatVar b
  | PatTuple (f,l) -> PatTuple (f,List.map (rename_pat cur_array b0 b0') l)
  | PatEqual t -> PatEqual (rename_term cur_array b0 b0' t)

let rec rename_process cur_array b0 b0' = function
    Nil -> Nil
  | Par(p1,p2) -> Par(rename_process cur_array b0 b0' p1, 
		      rename_process cur_array b0 b0' p2)
  | Repl(b,p) ->
      (* if b == b0 then Parsing_helper.internal_error "rename_process2"; *)
      Repl(b, rename_process cur_array b0 b0' p)
  | Input((c,tl),pat,p) ->
      Input((c, List.map (rename_term cur_array b0 b0') tl),
	    rename_pat cur_array b0 b0' pat,
	    rename_oprocess cur_array b0 b0' p)

and rename_oprocess cur_array b0 b0' = function
    Yield -> Yield
  | Restr(b,p) ->
      (* if b == b0 then Parsing_helper.internal_error "rename_oprocess1"; *)
      Restr(b, rename_oprocess cur_array b0 b0' p)
  | Test(t,p1,p2) ->
      Test(rename_term cur_array b0 b0' t,
	   rename_oprocess cur_array b0 b0' p1,
	   rename_oprocess cur_array b0 b0' p2)
  | Find(l0, p2,_) ->
      (* if List.memq b0 bl then Parsing_helper.internal_error "rename_oprocess3"; *)
      Find(List.map (fun (bl, def_list, otheruses_list, t, p1) ->
	     (bl, List.map (rename_binder cur_array b0 b0') def_list,
	      List.map (rename_binder cur_array b0 b0') otheruses_list,
	      rename_term cur_array b0 b0' t,
	      rename_oprocess cur_array b0 b0' p1)) l0,
	   rename_oprocess cur_array b0 b0' p2, ref None)
  | Let(pat,t,p1,p2) ->
      Let(rename_pat cur_array b0 b0' pat,
	  rename_term cur_array b0 b0' t,
	  rename_oprocess cur_array b0 b0' p1,
	  rename_oprocess cur_array b0 b0' p2)
  | Output((c,tl),t2,p) ->
      Output((c, List.map (rename_term cur_array b0 b0') tl),
	     rename_term cur_array b0 b0' t2,
	     rename_process cur_array b0 b0' p)
  | EventP(t,p) ->
      EventP(rename_term cur_array b0 b0' t,
	     rename_oprocess cur_array b0 b0' p)

(* - First pass: look for assignments to x, give a new name to each of them,
   and rename the in-scope references to x with current session identifiers *)
   
let image_name_list = ref []

(* NOTE: when TestE/LetE/FindE/ResE are forbidden, sa_term is the identity *)
let rec sa_term cur_array b0 t =
  { t_desc =
    begin
      match t.t_desc with
	Var(b,l) ->
          Var(b, List.map (sa_term cur_array b0) l)
      | FunApp(f,l) ->
          FunApp(f, List.map (sa_term cur_array b0) l)
      | TestE(t1,t2,t3) ->
          TestE(sa_term cur_array b0 t1,
		sa_term cur_array b0 t2,
		sa_term cur_array b0 t3)
      | FindE(l0,t3,_) ->
	  let l0' = List.map (fun (bl, def_list, otheruses_list, t1, t2) ->
            if List.memq b0 bl then
              let b0' = Terms.new_binder b0 in
              image_name_list := b0' :: (!image_name_list);
              (List.map (fun b -> if b == b0 then b0' else b) bl,
               List.map (fun (b,l) -> (b, List.map (rename_term cur_array b0 b0') l)) def_list,
               List.map (fun (b,l) -> (b, List.map (rename_term cur_array b0 b0') l)) otheruses_list,
               rename_term cur_array b0 b0' t1,
               rename_term cur_array b0 b0' t2)
            else
              (bl, List.map (fun (b,l) -> (b, List.map (sa_term cur_array b0) l)) def_list,
	       List.map (fun (b,l) -> (b, List.map (sa_term cur_array b0) l)) otheruses_list,
               sa_term cur_array b0 t1,
               sa_term cur_array b0 t2)) l0
	  in
	  FindE(l0', sa_term cur_array b0 t3, ref None)
      |	LetE(pat, t1, t2, topt) ->
	  let target_name = ref b0 in
	  let pat' = sa_pat cur_array b0 target_name pat in
	  if !target_name == b0 then
	  (* b0 not defined in pat *)
	    LetE(pat', t1, 
		sa_term cur_array b0 t2, 
		match topt with
		  Some t3 -> Some (sa_term cur_array b0 t3)
		| None -> None)
	  else
	    (* b0 defined in pat and renamed to !target_name *)
	    LetE(pat', t1, 
		rename_term cur_array b0 (!target_name) t2, 
		match topt with
		  Some t3 -> Some (sa_term cur_array b0 t3)
		| None -> None)
      |	ResE(b,t) ->
	  if b == b0 then
	    let b0' = Terms.new_binder b0 in
	    image_name_list := b0' :: (!image_name_list);
	    ResE(b0', rename_term cur_array b0 b0' t)
	  else
	    ResE(b, sa_term cur_array b0 t)
    end;
    t_type = t.t_type;
    t_occ = t.t_occ }

and sa_pat cur_array b0 target_name = function
    PatVar b -> 
      if b == b0 then
	let b0' = Terms.new_binder b0 in
	image_name_list := b0' :: (!image_name_list);
	if (!target_name) != b0 then 
	  Parsing_helper.internal_error "target name already assigned in sa_pat";
	target_name := b0';
	PatVar b0'
      else
	PatVar b
  | PatTuple (f,l) -> PatTuple (f,List.map (sa_pat cur_array b0 target_name) l)
  | PatEqual t -> PatEqual t

let rec sa_process cur_array b0 = function
    Nil -> Nil
  | Par(p1,p2) -> Par(sa_process cur_array b0 p1,
		      sa_process cur_array b0 p2)
  | Repl(b,p) ->
      let bt = Terms.term_from_binder b in
      if b == b0 then
	(* b cannot have outscope references, so no need to store it in
	   image_name_list for future renaming of outscope references *)
	let b0' = Terms.new_binder b0 in
	Repl(b0', rename_process (bt::cur_array) b0 b0' p)
      else
	Repl(b, sa_process (bt::cur_array) b0 p)
  | Input((c,tl),pat,p) ->
      let target_name = ref b0 in
      let pat' = sa_pat cur_array b0 target_name pat in
      if !target_name == b0 then
	(* b0 not defined in pat *)
	Input((c,List.map (sa_term cur_array b0) tl), pat', 
	      sa_oprocess cur_array b0 p)
      else
	(* b0 defined in pat and renamed to !target_name *)
	Input((c,List.map (sa_term cur_array b0) tl), pat', 
	      rename_oprocess cur_array b0 (!target_name) p)

and sa_oprocess cur_array b0 = function
    Yield -> Yield
  | Restr(b,p) ->
      if b == b0 then
	let b0' = Terms.new_binder b0 in
	image_name_list := b0' :: (!image_name_list);
	Restr(b0', rename_oprocess cur_array b0 b0' p)
      else
	Restr(b, sa_oprocess cur_array b0 p)
  | Test(t,p1,p2) ->
      Test(sa_term cur_array b0 t, 
	   sa_oprocess cur_array b0 p1,
	   sa_oprocess cur_array b0 p2)
  | Find(l0, p2, _) -> 
      let l0' = List.map (fun (bl, def_list, otheruses_list, t, p1) ->
	if List.memq b0 bl then
	  let b0' = Terms.new_binder b0 in
	  image_name_list := b0' :: (!image_name_list);
	  (List.map (fun b -> if b == b0 then b0' else b) bl, 
	   List.map (fun (b,l) -> (b, List.map (rename_term cur_array b0 b0') l)) def_list,
	   List.map (fun (b,l) -> (b, List.map (rename_term cur_array b0 b0') l)) otheruses_list,
	   rename_term cur_array b0 b0' t,
	   rename_oprocess cur_array b0 b0' p1)
	else
	  (bl, List.map (fun (b,l) -> (b, List.map (sa_term cur_array b0) l)) def_list,
	   List.map (fun (b,l) -> (b, List.map (sa_term cur_array b0) l)) otheruses_list,
           sa_term cur_array b0 t,
	   sa_oprocess cur_array b0 p1)) l0
      in
      Find(l0', sa_oprocess cur_array b0 p2, ref None)
  | Output((c,tl),t2,p) ->
      Output((c, List.map (sa_term cur_array b0) tl), 
	     sa_term cur_array b0 t2,
	     sa_process cur_array b0 p)
  | Let(pat,t,p1,p2) ->
      let target_name = ref b0 in
      let pat' = sa_pat cur_array b0 target_name pat in
      if !target_name == b0 then
	(* b0 not defined in pat *)
	Let(pat', t, 
	    sa_oprocess cur_array b0 p1, 
	    sa_oprocess cur_array b0 p2)
      else
	(* b0 defined in pat and renamed to !target_name *)
	Let(pat', t, 
	    rename_oprocess cur_array b0 (!target_name) p1, 
	    sa_oprocess cur_array b0 p2)
  | EventP(t,p) ->
      EventP(sa_term cur_array b0 t,
	     sa_oprocess cur_array b0 p)

(* - Second pass: empty b.def 
	          compute new value of b.def
     See terms.ml *)
      
(* - Third pass: rename the out-scope array references to x
   A find or if defined(...) should be split if
      - either it contains defined(x[...])
           defined(x[...]) becomes defined(x1[...]), ..., defined(xn[...]) in the different cases
      - or it contains defined(y[...]), x is defined syntactically before y,
        and the then part refers to x[...]
           add defined(x1[...]), ..., defined(xn[...]) in the different cases
   If due to other defined conditions, only some of the xi can be defined
   then consider only these xi cases: collect all "defined" conditions up to the
   current point. On the other hand, collect the variables defined in the same 
   branch as xi. The case xi needs to be considered only when all "defined" 
   conditions up to the current point that have session identifiers prefix or 
   suffix of those of xi are variables defined in the same branch as xi.
   Use Terms.compatible_defs to test whether two variables are in the
   same branch.
 *)

(*
let rec defined_after_node n blist =
  (List.exists (fun b1 ->
    List.exists (fun b2 -> b1 == b2) blist) n.binders) ||
    ((n.above_node != n) && (defined_after_node n.above_node blist))

let defined_after b blist =
  List.for_all (fun n -> defined_after_node n blist) b.def

let implies_def b0 def_list =
  let accu = ref [] in
  List.iter (fun (b,l) ->
    if ((b == b0) || (defined_after b (!image_name_list))) &&
       (* Do not add duplicates in accu *)
       (not (List.exists (fun l' -> List.for_all2 Terms.equal_terms l l') (!accu)))
    then
      accu := l :: (!accu)) def_list;
  !accu
*)

let rec implies_def_subterm b0 accu (b,l) =
  if (b == b0) && 
    (* Do not add duplicates in accu *)
    (not (List.exists (fun l' -> List.for_all2 Terms.equal_terms l l') (!accu))) then
    accu := l :: (!accu);
  List.iter (implies_def_term b0 accu) l

and implies_def_term b0 accu t =
  match t.t_desc with
    Var(b,l) -> implies_def_subterm b0 accu (b,l)
  | FunApp(f,l) -> List.iter (implies_def_term b0 accu) l
  | _ -> Parsing_helper.internal_error "if/let/find forbidden in defined conditions of find"
    
let implies_def b0 def_list =
  let accu = ref [] in
  List.iter (implies_def_subterm b0 accu) def_list;
  !accu

let compatible_defs = ref [] 

let is_compatible b0 (b,args) (b',args') =
  (b == b') || (b0 == b') || 
  (
  let l = List.length args in
  let l' = List.length args' in
  let min = if l > l' then l' else l in
  let args_skip = Terms.skip (l-min) args in
  let args_skip' = Terms.skip (l'-min) args' in
  (not (List.for_all2 Terms.equal_terms args_skip args_skip')) ||
  (List.exists (fun (b1,b1') ->
      ((b == b1) && (b' == b1')) || ((b == b1') && (b' == b1))) (!compatible_defs))
      )

let rec rename_find p1rename b0 image_list args accu ((bl,def_list,otheruses_list,t,p1) as p) =
  match image_list with
    [] -> accu
  | (b::l) ->
      let accu' = 
	if List.for_all (is_compatible b0 (b,args)) def_list then
	  let def_list' = List.map (rename_binder args b0 b) def_list in
	  let def_list'' = 
	    if not (List.exists (fun (b',l') -> (b' == b0) && (List.for_all2 Terms.equal_terms l' args)) def_list) then
	      (b,args)::def_list'
	    else
	      def_list'
	  in
	  (bl, def_list'',
	   List.map (rename_binder args b0 b) otheruses_list,
	   rename_term args b0 b t, 
	   p1rename args b0 b p1) :: accu
	else
          accu
      in
      rename_find p1rename b0 l args accu' p

let rec rename_finds p1rename b0 image_list args_list accu p =
  match args_list with
    [] ->  accu 
  | (args::args_list) ->
      rename_finds p1rename b0 image_list args_list (rename_find p1rename b0 image_list args accu p) p

(* NOTE: when TestE/LetE/FindE/ResE are forbidden,
   ren_out_term and ren_out_pat are the identity *)
let rec ren_out_term b0 t = 
  { t_desc =
    begin
      match t.t_desc with
	Var(b,l) -> 
	  Var(b, List.map (ren_out_term b0) l)
      | FunApp(f,l) ->  
	  FunApp(f, List.map (ren_out_term b0) l)
      | TestE(t1,t2,t3) ->
	  TestE(ren_out_term b0 t1,
		ren_out_term b0 t2,
		ren_out_term b0 t3)
      | LetE(pat, t1, t2, topt) ->
	  LetE(ren_out_pat b0 pat,
	       ren_out_term b0 t1,
	       ren_out_term b0 t2,
	       match topt with
		 Some t3 -> Some (ren_out_term b0 t3)
	       | None -> None)
      | FindE(l0, t3, _) ->
	  let rec ren_out_list = function
	      [] -> []
	    | (bl,def_list, otheruses_list, t1, t2)::l1 ->
		let l1' = ren_out_list l1 in
		let t1' = ren_out_term b0 t1 in
		let t2' = ren_out_term b0 t2 in
		let to_rename = implies_def b0 def_list in
                (* renamings of b0 *)	
		if to_rename = [] then
		  (bl, def_list, otheruses_list, t1', t2')::l1'
		else
		  rename_finds rename_term b0 (!image_name_list) to_rename l1' (bl, def_list, otheruses_list, t1', t2')
	  in
	  FindE(ren_out_list l0, ren_out_term b0 t3, ref None)
      |	ResE(b,t) ->
	  ResE(b, ren_out_term b0 t)
    end;
    t_type = t.t_type;
    t_occ = t.t_occ }
    
and ren_out_pat b0 = function
    PatVar b -> PatVar b 
  | PatTuple (f,l) -> PatTuple (f,List.map (ren_out_pat b0) l)
  | PatEqual t -> PatEqual (ren_out_term b0 t)

let rec ren_out_process b0 = function
    Nil -> Nil
  | Par(p1,p2) -> Par(ren_out_process b0 p1,
		      ren_out_process b0 p2)
  | Repl(b,p) -> Repl(b, ren_out_process b0 p)
  | Input((c,tl),pat,p) ->
      Input((c, List.map (ren_out_term b0) tl), 
	    ren_out_pat b0 pat, ren_out_oprocess b0 p)

and ren_out_oprocess b0 = function
    Yield -> Yield
  | Restr(b,p) -> Restr(b, ren_out_oprocess b0 p)
  | Test(t,p1,p2) -> 
      Test(ren_out_term b0 t,
	   ren_out_oprocess b0 p1,
	   ren_out_oprocess b0 p2)
  | Find(l0, p2, _) ->
      let rec ren_out_list = function
	  [] -> []
	| (bl,def_list, otheruses_list, t, p1)::l1 ->
	    let l1' = ren_out_list l1 in
	    let t' = ren_out_term b0 t in
	    let p1' = ren_out_oprocess b0 p1 in
	    let to_rename = implies_def b0 def_list in
            (* renamings of b0 *)	
	    if to_rename = [] then
	      (bl, def_list, otheruses_list, t', p1')::l1'
	    else
	      rename_finds rename_oprocess b0 (!image_name_list) to_rename l1' (bl, def_list, otheruses_list, t', p1')
      in
      Find(ren_out_list l0, ren_out_oprocess b0 p2, ref None)
  | Output((c,tl),t2,p) ->
      Output((c, List.map (ren_out_term b0) tl),
	     ren_out_term b0 t2,ren_out_process b0 p)
  | Let(pat,t,p1,p2) ->
      Let(ren_out_pat b0 pat, ren_out_term b0 t, ren_out_oprocess b0 p1,
	  ren_out_oprocess b0 p2)
  | EventP(t,p) ->
      EventP(ren_out_term b0 t, ren_out_oprocess b0 p)

(* Main function for variable renaming into sa *)

let sa_rename b0 p =
  (* cannot rename if b0 occurs in queries! 
     TO DO in fact, I could replace b0 = M with b' = M; b0 = b',
     replace all references to b0 with b', and apply sa_rename on b' *)
  if occurs_in_queries b0 then p else
  begin
  image_name_list := [];
  let p' = sa_process [] b0 p in
  if List.length (!image_name_list) >= 2 then
    begin
      changed := true;
      Terms.build_def_process None p';
      compatible_defs := Terms.compatible_defs p';
      let p'' = ren_out_process b0 p' in
      image_name_list := [];
      compatible_defs := [];
      p''
    end
  else
    begin
      image_name_list := [];
      p
    end
  end

(****************************************************************************)

(* Remove assignments 

This transformation is programmed assuming there are no LetE or FindE in
let expressions or in patterns! Otherwise, we should verify for each expression that we copy
that it does not contain LetE or FindE: if we copy a LetE or FindE, we may 
break the invariant that each variable is assigned at most once.

Be careful of variables defined at several places!  *)

(* - First pass: Finds binders that have definition tests, and store them in accu;
                 Finds binders that have out-of-scope array accesses and store them in accu1 *)

let add accu b =
  if not (List.memq b (!accu)) then
    accu := b :: (!accu)

let rec add_subterms accu t = 
  match t.t_desc with
    Var(b,l) ->
      add accu b; List.iter (add_subterms accu) l
  | FunApp(f,l) -> List.iter (add_subterms accu) l
  | _ -> Parsing_helper.internal_error "if/find/let forbidden in defined conditions of find"

let rec array_ref_term in_scope accu accu1 t = 
  match t.t_desc with
    Var(b, l) -> 
      if not (List.for_all2 Terms.equal_terms l b.args_at_creation &&
	      List.memq b in_scope) then
	add accu1 b;
      List.iter (array_ref_term in_scope accu accu1) l
  | FunApp(_,l) ->
      List.iter (array_ref_term in_scope accu accu1) l
  | TestE(t1,t2,t3) ->
      array_ref_term in_scope accu accu1 t1;
      array_ref_term in_scope accu accu1 t2;
      array_ref_term in_scope accu accu1 t3
  | LetE(pat, t1, t2, topt) ->
      array_ref_pattern in_scope accu accu1 pat;
      array_ref_term in_scope accu accu1 t1;
      array_ref_term (Terms.vars_from_pat in_scope pat) accu accu1 t2;
      begin
	match topt with
	  None -> ()
	| Some t3 -> array_ref_term in_scope accu accu1 t3
      end
  | FindE(l0,t3, _) ->
      List.iter (fun (bl,def_list,otheruses_list, t1,t2) ->
	let in_scope' = bl @ in_scope in
	List.iter (fun (b,l) -> 
	  List.iter (array_ref_term in_scope' accu accu1) l;
	  add accu b;
	  List.iter (add_subterms accu) l) def_list;
	List.iter (fun (b,l) -> 
	  if not (List.for_all2 Terms.equal_terms l b.args_at_creation &&
		  List.memq b in_scope') then
	    add accu1 b;
	  List.iter (array_ref_term in_scope' accu accu1) l) otheruses_list;
	array_ref_term in_scope' accu accu1 t1;
	array_ref_term in_scope' accu accu1 t2) l0;
      array_ref_term in_scope accu accu1 t3
  | ResE(b,t) ->
      array_ref_term (b::in_scope) accu accu1 t

and array_ref_pattern in_scope accu accu1 = function
    PatVar b -> ()
  | PatTuple (f,l) -> List.iter (array_ref_pattern in_scope accu accu1) l
  | PatEqual t -> array_ref_term in_scope accu accu1 t

let rec array_ref_process in_scope accu accu1 = function
    Nil -> ()
  | Par(p1,p2) -> 
      array_ref_process in_scope accu accu1 p1;
      array_ref_process in_scope accu accu1 p2
  | Repl(b,p) ->
      array_ref_process (b::in_scope) accu accu1 p
  | Input((_,tl),pat,p) ->
      List.iter (array_ref_term in_scope accu accu1) tl;      
      array_ref_pattern in_scope accu accu1 pat;
      array_ref_oprocess (Terms.vars_from_pat in_scope pat) accu accu1 p

and array_ref_oprocess in_scope accu accu1 = function
    Yield -> ()
  | Restr(b,p) ->
      array_ref_oprocess (b::in_scope) accu accu1 p
  | Test(t,p1,p2) ->
      array_ref_term in_scope accu accu1 t;      
      array_ref_oprocess in_scope accu accu1 p1;
      array_ref_oprocess in_scope accu accu1 p2
  | Find(l0,p2, _) ->
      List.iter (fun (bl,def_list,otheruses_list,t,p1) ->
	let in_scope' = bl @ in_scope in
	List.iter (fun (b,l) -> 
	  List.iter (array_ref_term in_scope' accu accu1) l;
	  add accu b) def_list;
	List.iter (fun (b,l) -> 
	  if not (List.for_all2 Terms.equal_terms l b.args_at_creation &&
		  List.memq b in_scope') then
	    add accu1 b;
	  List.iter (array_ref_term in_scope' accu accu1) l) otheruses_list;
	array_ref_term in_scope' accu accu1 t;      
	array_ref_oprocess in_scope' accu accu1 p1) l0;
      array_ref_oprocess in_scope accu accu1 p2
  | Output((_,tl),t2,p) ->
      List.iter (array_ref_term in_scope accu accu1) tl;      
      array_ref_term in_scope accu accu1 t2;
      array_ref_process in_scope accu accu1 p
  | Let(pat, t, p1, p2) ->
      array_ref_pattern in_scope accu accu1 pat;
      array_ref_term in_scope accu accu1 t;      
      array_ref_oprocess (Terms.vars_from_pat in_scope pat) accu accu1 p1;
      array_ref_oprocess in_scope accu accu1 p2
  | EventP(t,p) ->
      array_ref_term in_scope accu accu1 t;      
      array_ref_oprocess in_scope accu accu1 p

(* - Third pass: copy the process following the links.
     Be careful for array references: update the indexes properly  *)

let in_scope_only = ref false

let rec get_remassign_subterms accu (b,l) =
  List.iter (get_remassign_terms accu) l;
  match b.link with
    NoLink -> ()
  | TLink _ -> Terms.add_binderref (b,l) accu

and get_remassign_terms accu t =
  match t.t_desc with
    Var(b,l) -> get_remassign_subterms accu (b,l)
  | FunApp(f,l) -> List.iter (get_remassign_terms accu) l
  | _ -> Parsing_helper.internal_error "if/let/find forbidden in defined conditions of find"

let rec copy_term remove_set t = 
  match t.t_desc with
    Var(b,l) ->
      begin
	let l' = List.map (copy_term remove_set) l in
	let default() = 
	  { t_desc = Var(b,l');
	    t_type = t.t_type;
	    t_occ = Terms.new_occ() }
	in
	let do_copy() = 
	  match b.link with
	    NoLink -> default()
	  | TLink t ->
	      let t = copy_term remove_set t in
              if !in_scope_only then
                if List.for_all2 Terms.equal_terms l b.args_at_creation then
		  begin
		    changed := true;
                    t
		  end
                else
		  default()
              else
		Terms.auto_cleanup (fun () ->
	        (* rename array indexes *)
		  List.iter2 (fun tb ti ->
                    let bi = Terms.binder_from_term tb in
                    match ti.t_desc with
                      Var(bi',[]) when bi == bi' -> ()
                    | _ -> 
			match bi.link with
			  NoLink -> Terms.link bi (TLink ti)
			| _ -> Parsing_helper.internal_error "Cyclic assignment! Should never happen."
			      ) b.args_at_creation l';
		  changed := true;
		  Terms.copy_term t)
	in
	match remove_set with
	  SubstOneBinder(b',occ) -> 
	    if (b' == b) && (occ = t.t_occ) then do_copy() else 
	    default()
	| _ -> do_copy()
      end
  | FunApp(f,l) ->
      { t_desc = FunApp(f, List.map (copy_term remove_set) l);
	t_type = t.t_type;
	t_occ = Terms.new_occ() }	
  | TestE(t1,t2,t3) ->
      { t_desc = TestE(copy_term remove_set t1,
		       copy_term remove_set t2, 
		       copy_term remove_set t3);
	t_type = t.t_type;
	t_occ = Terms.new_occ() }
  | LetE(pat, t1, t2, topt) ->
      let pat' = copy_pat remove_set pat in
      let t1' = copy_term remove_set t1 in
      let t2' = copy_term remove_set t2 in
      let topt' = match topt with
	None -> None
      |	Some t3 -> Some (copy_term remove_set t3)
      in
      { t_desc = LetE(pat', t1', t2', topt');
	t_type = t.t_type;
	t_occ = Terms.new_occ() }
  | FindE(l0, t3, _) -> 
      let l0' = List.map (fun (bl, def_list, otheruses_list, t1, t2) ->
	(bl,
	 copy_def_list remove_set def_list, 
	 List.map (fun (b,l) ->
	   if b.link != NoLink then
	     Parsing_helper.internal_error "A variable with \"otheruses\" condition should be defined only by restrictions.";
	   (b, List.map (copy_term remove_set) l)) otheruses_list,
	 copy_term remove_set t1,
	 copy_term remove_set t2)) l0
      in
      { t_desc = FindE(l0', copy_term remove_set t3, ref None);
	t_type = t.t_type;
	t_occ = Terms.new_occ() }
  | ResE(b,t) ->
      { t_desc = ResE(b, copy_term remove_set t);
	t_type = t.t_type;
	t_occ = Terms.new_occ() }
      

and copy_def_list remove_set def_list =
  if !in_scope_only then
    List.map (fun (b,l) ->
      (b, List.map (copy_term remove_set) l)) def_list
  else
    begin
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
	  (List.map (fun (b,l) -> (b, List.map (copy_term remove_set) l)) 
	     ((!root_remassign) @ not_root_remassign))
      in
      List.iter (fun (b,l) -> Terms.get_deflist_subterms accu
	(copy_term remove_set { t_desc = Var(b,l); t_type = b.btype; 
				t_occ = Terms.new_occ() })) (!root_remassign);
      !accu
    end

and copy_pat remove_set = function
  PatVar b -> PatVar b
| PatTuple (f,l) -> PatTuple(f,List.map (copy_pat remove_set) l)
| PatEqual t -> PatEqual(copy_term remove_set t)

let rec copy_process remove_set = function
    Nil -> Nil
  | Par(p1,p2) ->
      Par(copy_process remove_set p1,
	  copy_process remove_set p2)
  | Repl(b,p) ->
      Repl(b, copy_process remove_set p)
  | Input((c,tl), pat, p) ->
      Input((c, List.map (copy_term remove_set) tl),
	    copy_pat remove_set pat,
	    copy_oprocess remove_set p)

and copy_oprocess remove_set = function
    Yield -> Yield
  | Restr(b, p) ->
      Restr(b, copy_oprocess remove_set p)
  | Test(t,p1,p2) ->
      Test(copy_term remove_set t, 
	   copy_oprocess remove_set p1,
           copy_oprocess remove_set p2)
  | Let(pat, t, p1, p2) ->
      Let(copy_pat remove_set pat, 
	  copy_term remove_set t, 
	  copy_oprocess remove_set p1,
          copy_oprocess remove_set p2)
  | Output((c,tl),t2,p) ->
      Output((c, List.map (copy_term remove_set) tl),
	     copy_term remove_set t2,
	     copy_process remove_set p)
  | Find(l0, p2, _) ->
      let l0' = List.map (fun (bl, def_list, otheruses_list, t, p1) ->
	(bl, 
	 copy_def_list remove_set def_list, 
	 List.map (fun (b,l) ->
	   if b.link != NoLink then
	     Parsing_helper.internal_error "A variable with \"otheruses\" condition should be defined only by restrictions.";
	   (b, List.map (copy_term remove_set) l)) otheruses_list,
	 copy_term remove_set t,
	 copy_oprocess remove_set p1)) l0 in
      Find(l0', copy_oprocess remove_set p2, ref None)
  | EventP(t,p) ->
      EventP(copy_term remove_set t, 
	     copy_oprocess remove_set p)

(* - Second pass: put links; split assignments of tuples if possible *)

(* Function for assignment expansion that works both for terms
   and processes *)

(* p1: 'a          rec_simplif1 : 'a -> 'a
   p2: 'b not2: 'b rec_simplif2 : 'b -> 'b 
                   rec_simplif2bis : 'b -> 'a
*)

let expand_assign make_test make_let copy1 refers_to1 not2 
    arrays_refs arrays_out_refs remove_set
    rec_simplif1 rec_simplif2 rec_simplif2bis pat t p1 p2 =
  match pat with
    PatEqual t' -> 
      changed := true;
      make_test (Terms.make_equal t t') (rec_simplif1 p1) (rec_simplif2 p2)
  | PatTuple (f,l) -> 
      (* try to split *)
      begin
	try 
	  let res = rec_simplif1
	      (Terms.put_lets make_let l (Terms.split_term f t) p1 p2)
	  in
	  changed := true;
	  res
	with Not_found -> 
	  make_let pat  t (rec_simplif1 p1) (rec_simplif2 p2)
	| Terms.Impossible -> 
	    changed := true;
	    rec_simplif2bis p2
      end
  | PatVar b ->
      let put_link do_advise =
	if Terms.refers_to b t then
	  (* Cannot replace cyclic assignment *)
	  make_let pat  t (rec_simplif1 p1) not2
	else 
	  match b.def with
	    [] -> Parsing_helper.internal_error "Should have at least one definition"
	  | [d] -> (* There is a single definition *)
	      begin
		(* All references to binder b will be removed *)
		Terms.link b (TLink t);
		if occurs_in_queries b then
		  (* if b occurs in queries then leave as it is *)
		  make_let pat t (rec_simplif1 p1) not2
		else if List.memq b arrays_refs then
		  (* We may keep calls to defined(b), so keep a definition of b
		     but its value does not matter *)
		  let t' = Terms.cst_for_type t.t_type in
		  if not (Terms.equal_terms t t') then changed := true;
		  make_let pat  t' (rec_simplif1 p1) not2
		else
		  begin
                    (* b will completely disappear *)
                    changed := true;
		    rec_simplif1 p1
		  end
	      end
	  | _ -> (* There are several definitions.
		    I can remove in-scope requests, but out-of-scope array accesses will remain *)
              begin
		b.link <- (TLink t);
                in_scope_only := true;
                let p1' = copy1 p1 in
                b.link <- NoLink;
                in_scope_only := false;
                let p1'' = rec_simplif1 p1' in
                if List.memq b arrays_out_refs then
		  begin
                    (* suggest to use "sa_rename b" before removing assignments *)
		    if do_advise then advise := Terms.add_eq (SArenaming b) (!advise);
                    (* Keep the definition so that out-of-scope array accesses are correct *)
                    make_let pat t p1'' not2
		  end
		else if occurs_in_queries b then
		  (* Cannot change definition if b occurs in queries *)
		  make_let pat t p1'' not2
                else if List.memq b arrays_refs then
		  (* We may keep calls to defined(b), so keep a definition of b
		     but its value does not matter *)
		  let t' = Terms.cst_for_type t.t_type in
		  if not (Terms.equal_terms t t') then changed := true;
		  make_let pat t' p1'' not2
		else
                  (* b will completely disappear *)
		  begin
		    changed := true;
		    p1''
		  end
              end
      in
      if (check_no_ifletfindres t) then
	begin
	  if (not (refers_to1 b p1)) &&
	    (not (List.memq b arrays_out_refs)) &&
	    (not (occurs_in_queries b)) then
	    begin
	      (* Value of the variable is useless *)
	      if not (List.memq b arrays_refs) then
	        (* Variable is useless *)
		begin
		  changed := true;
		  rec_simplif1 p1
		end
	      else
		begin
	          (* We may keep calls to defined(b), so keep a definition of b
		     but its value does not matter *)
		  let t' = Terms.cst_for_type t.t_type in
		  if not (Terms.equal_terms t t') then changed := true;
		  make_let pat t' (rec_simplif1 p1) not2
		end
	    end
	  else
	    match remove_set with
	      SubstOneBinder(b0,occ) when b == b0 ->
	        (* Cannot replace cyclic assignment *)
		if not (Terms.refers_to b t) then
		  Terms.link b (TLink t);
		make_let pat t (rec_simplif1 p1) not2
	    | All -> put_link true
	    | OneBinder b0 when b == b0 -> put_link true
	    | _ -> 
		match t.t_desc with
		  Var _ when !Settings.expand_letxy -> 
	            (* Always expand assignments let x = x', if possible,
                       but don't do a lot of work for that, so don't apply advises *)
		    put_link false
		| _ ->
		    make_let pat t (rec_simplif1 p1) not2
	end
      else
	(* NOTE Useless if TestE/LetE/FindE/ResE are forbidden *)
	begin
	  begin
	    match remove_set with
	      All -> advise := Terms.add_eq ExpandIfFind (!advise)
	    | OneBinder b0 when b == b0 -> 
		advise := Terms.add_eq ExpandIfFind (!advise)
	    | SubstOneBinder(b0,occ) when b == b0 -> 
		advise := Terms.add_eq ExpandIfFind (!advise)
	    | _ -> ()
	  end;
	  make_let pat t (rec_simplif1 p1) not2
	end

let several_def b =
  match b.def with
    [] | [_] -> false
  | _::_::_ -> true
      
(* NOTE: when TestE/LetE/FindE/ResE are forbidden,
   remove_assignments_term is the identity;
   then expand_assign can be specialized to processes *)
let rec remove_assignments_term arrays_refs arrays_out_refs remove_set t =
  match t.t_desc with
    Var(b,l) ->
      { t_desc = Var(b, List.map (remove_assignments_term arrays_refs arrays_out_refs remove_set) l);
	t_type = t.t_type;
	t_occ = t.t_occ }
  | FunApp(f,l) ->
      { t_desc = FunApp(f, List.map (remove_assignments_term arrays_refs arrays_out_refs remove_set) l);
	t_type = t.t_type;
	t_occ = t.t_occ }
  | TestE(t1,t2,t3) ->
      { t_desc = TestE(remove_assignments_term arrays_refs arrays_out_refs remove_set t1,
		       remove_assignments_term arrays_refs arrays_out_refs remove_set t2,
		       remove_assignments_term arrays_refs arrays_out_refs remove_set t3);
	t_type = t.t_type;
	t_occ = t.t_occ }
  | FindE(l0, t3, _) ->
      { t_desc = FindE(List.map (fun (bl, def_list, otheruses_list, t1, t2) ->
	                 (bl, List.map (fun (b,l) -> (b, List.map (remove_assignments_term arrays_refs arrays_out_refs remove_set) l)) def_list,
			  List.map (fun (b,l) -> (b, List.map (remove_assignments_term arrays_refs arrays_out_refs remove_set) l)) otheruses_list,
			  remove_assignments_term arrays_refs arrays_out_refs remove_set t1,
			  remove_assignments_term arrays_refs arrays_out_refs remove_set t2)) l0,
		       remove_assignments_term arrays_refs arrays_out_refs remove_set t3, ref None);
	t_type = t.t_type;
	t_occ = t.t_occ }
  | LetE(pat,t1,t2,topt) ->
      expand_assign (Terms.make_test_term t.t_type) (Terms.make_let_term t.t_type) 
	(copy_term remove_set) Terms.refers_to_nodef None
	arrays_refs arrays_out_refs remove_set
	(remove_assignments_term arrays_refs arrays_out_refs remove_set)
	(function
	    None -> None
	  | Some t -> Some (remove_assignments_term arrays_refs arrays_out_refs remove_set t))
	(function
	    None -> Parsing_helper.internal_error "Missing else part of let"
	  | Some t -> remove_assignments_term arrays_refs arrays_out_refs remove_set t)
	pat t1 t2 topt
  | ResE(b,t) ->
      { t_desc = ResE(b, remove_assignments_term arrays_refs arrays_out_refs remove_set t);
	t_type = t.t_type;
	t_occ = t.t_occ }

let rec remove_assignments_rec arrays_refs arrays_out_refs remove_set = function
    Nil -> Nil
  | Par(p1,p2) -> 
      Par(remove_assignments_rec arrays_refs arrays_out_refs remove_set p1,
	  remove_assignments_rec arrays_refs arrays_out_refs remove_set p2)
  | Repl(b,p) ->
      Repl(b,remove_assignments_rec arrays_refs arrays_out_refs remove_set p)
  | Input((c,tl),pat,p) ->
      Input((c, List.map (remove_assignments_term arrays_refs arrays_out_refs remove_set) tl),pat, 
	    remove_assignments_reco arrays_refs arrays_out_refs remove_set p)

and remove_assignments_reco arrays_refs arrays_out_refs remove_set = function
    Yield -> Yield
  | Restr(b,p) ->
      if (!Settings.auto_sa_rename) && (several_def b) && (not (List.memq b arrays_refs)) && (not (List.memq b arrays_out_refs)) && (not (occurs_in_queries b)) then
	begin
	  let b' = Terms.new_binder b in
	  let p' = 
	    Terms.auto_cleanup (fun () ->
	      Terms.link b (TLink { t_desc = Var(b', b.args_at_creation); t_type = b.btype; t_occ = Terms.new_occ() });
	      copy_oprocess remove_set p)
	  in
	  Restr(b',remove_assignments_reco arrays_refs arrays_out_refs remove_set p')
	end
      else
	Restr(b,remove_assignments_reco arrays_refs arrays_out_refs remove_set p)
  | Test(t,p1,p2) ->
      Test(remove_assignments_term arrays_refs arrays_out_refs remove_set t, 
	   remove_assignments_reco arrays_refs arrays_out_refs remove_set p1,
	   remove_assignments_reco arrays_refs arrays_out_refs remove_set p2)
  | Find(l0,p2, _) ->
      Find(List.map (fun (bl,def_list,otheruses_list, t,p1) ->
	     (bl, List.map (fun (b,l) -> (b, List.map (remove_assignments_term arrays_refs arrays_out_refs remove_set) l)) def_list,
	      List.map (fun (b,l) -> (b, List.map (remove_assignments_term arrays_refs arrays_out_refs remove_set) l)) otheruses_list,
	      remove_assignments_term arrays_refs arrays_out_refs remove_set t,
	      remove_assignments_reco arrays_refs arrays_out_refs remove_set p1)) l0,
	   remove_assignments_reco arrays_refs arrays_out_refs remove_set p2, ref None)
  | Output((c,tl),t2,p) ->
      Output((c, List.map (remove_assignments_term arrays_refs arrays_out_refs remove_set) tl),
	     remove_assignments_term arrays_refs arrays_out_refs remove_set t2,
	     remove_assignments_rec arrays_refs arrays_out_refs remove_set p)
  | Let(pat, t, p1, p2) ->
      let rec_simplif = remove_assignments_reco arrays_refs arrays_out_refs remove_set in
      expand_assign Terms.make_test_proc Terms.make_let_proc (copy_oprocess remove_set)
	Terms.refers_to_process_nodef Yield arrays_refs arrays_out_refs remove_set
	rec_simplif rec_simplif rec_simplif pat t p1 p2
  | EventP(t,p) ->
      EventP(remove_assignments_term arrays_refs arrays_out_refs remove_set t,
	     remove_assignments_reco arrays_refs arrays_out_refs remove_set p)

(* - Main function for assignment removal *)

let remove_assignments remove_set p =
  Terms.build_def_process None p;
  if !Terms.current_bound_vars != [] then
    Parsing_helper.internal_error "bound vars should be cleaned up (transf1)";
  let array_refs = ref [] in
  let array_out_refs = ref [] in
  array_ref_process [] array_refs array_out_refs p;
  let p' = remove_assignments_rec (!array_refs) (!array_out_refs) remove_set p in
  let p'' = copy_process remove_set p' in
  Terms.cleanup();
  p''

let rec remove_assignments_repeat n remove_set p =
  let tmp_changed = !changed in
  changed := false;
  let p' = remove_assignments remove_set p in
  if n != 1 && !changed then
    remove_assignments_repeat (n-1) remove_set p'
  else
    begin
      changed := tmp_changed;
      p'
    end

let remove_assignments remove_set p =
  if remove_set == Minimal then
    remove_assignments_repeat (!Settings.max_iter_removeuselessassign) remove_set p
  else
    remove_assignments remove_set p

(**********************************************************************)

(* Move new:
   when a restriction has no array references, but has several uses
   under different branches of if/find, move it down under if/find.
   It will be later SA renamed, which can allow to distinguish
   cases easily.
   *)

let rec move_a_new b = function
    Nil -> 
      changed := true;
      Nil
  | Par(p1,p2) ->
      let r1 = Terms.refers_to_process b p1 in
      let r2 = Terms.refers_to_process b p2 in
      if r1 && r2 then
	raise Not_found
      else 
	begin
	  changed := true;
	  if r1 then
	    Par(move_a_new b p1,p2)
	  else if r2 then
	    Par(p1, move_a_new b p2)
	  else
	    Par(p1,p2)
	end
  | Repl(b',p) -> raise Not_found
  | Input((c,tl), pat, p) ->
      if (List.exists (Terms.refers_to b) tl) || (Terms.refers_to_pat b pat) then
	raise Not_found
      else
	Input((c,tl), pat, move_a_newo b p)

and move_a_newo b = function
    Yield -> Yield
  | Restr(b',p) -> 
      changed := true;
      Restr(b', move_a_newo b p)
  | Test(t,p1,p2) ->
      if Terms.refers_to b t then
	Restr(b,Test(t,p1,p2))
      else
	begin
	  changed:= true;
	  Test(t, move_a_newo b p1, move_a_newo b p2)
	end
  | Find(l0,p,_) ->
      if List.exists (fun (bl, def_list, otheruses_list, t, _) ->
	(List.exists (fun (b',l) -> b == b' || List.exists (Terms.refers_to b) l) def_list) ||
	(List.exists (fun (b',l) -> b == b' || List.exists (Terms.refers_to b) l) otheruses_list) ||
	Terms.refers_to b t) l0 then
	Restr(b, Find(l0,p,ref None))
      else
	begin
	  changed := true;
	  Find(List.map (fun (bl, def_list, otheruses_list, t, p1) ->
	    (bl, def_list, otheruses_list, t, move_a_newo b p1)) l0,
	       move_a_newo b p, ref None)
	end
  | Output((c,tl),t2,p) ->
      if (List.exists (Terms.refers_to b) tl) || (Terms.refers_to b t2) then
	Restr(b, Output((c,tl),t2,p))
      else
	begin
	  try
	    let p' = move_a_new b p in
	    changed := true;
	    Output((c,tl), t2, p')
	  with Not_found ->
	    Restr(b, Output((c,tl),t2,p))
	end
  | Let(pat, t, p1, p2) ->
      if (Terms.refers_to b t) || (Terms.refers_to_pat b pat) then
	Restr(b, Let(pat, t, p1, p2))
      else
	begin
	  changed := true;
	  Let(pat, t, move_a_newo b p1, move_a_newo b p2)
	end
  | EventP(t,p) ->
      if Terms.refers_to b t then
	Restr(b, EventP(t,p))
      else
	begin
	  changed := true;
	  EventP(t, move_a_newo b p)
	end

let do_move move_set b =
  match move_set with
    MAll -> true
  | MOneBinder b' -> b == b'

let rec move_new_rec move_set array_refs array_out_refs = function
    Nil -> Nil
  | Par(p1,p2) -> Par(move_new_rec move_set array_refs array_out_refs p1,
		      move_new_rec move_set array_refs array_out_refs p2)
  | Repl(b,p) -> Repl(b,move_new_rec move_set array_refs array_out_refs p)
  | Input(t, pat, p) ->
      Input(t, pat, move_new_reco move_set array_refs array_out_refs p)

and move_new_reco move_set array_refs array_out_refs = function
    Yield -> Yield
  | Restr(b,p) ->
      if (not (do_move move_set b)) || (List.memq b array_refs) || (List.memq b array_out_refs) then
	Restr(b, move_new_reco move_set array_refs array_out_refs p)
      else
	move_a_newo b (move_new_reco move_set array_refs array_out_refs p)
  | Test(t,p1,p2) -> Test(t, move_new_reco move_set array_refs array_out_refs p1,
			  move_new_reco move_set array_refs array_out_refs p2)
  | Find(l0,p,def_node_opt) ->
      Find(List.map (fun (bl,def_list,otheruses_list, t,p1) ->
	(bl, def_list, otheruses_list, t, move_new_reco move_set array_refs array_out_refs p1)) l0,
	   move_new_reco move_set array_refs array_out_refs p, def_node_opt)
  | Output(t1,t2,p) ->
      Output(t1,t2,move_new_rec move_set array_refs array_out_refs p)
  | Let(pat,t,p1,p2) ->
      Let(pat,t,move_new_reco move_set array_refs array_out_refs p1,
	  move_new_reco move_set array_refs array_out_refs p2)
  | EventP(t,p) ->
      EventP(t, move_new_reco move_set array_refs array_out_refs p)

let move_new move_set p =
  let array_refs = ref [] in
  let array_out_refs = ref [] in
  array_ref_process [] array_refs array_out_refs p;
  move_new_rec move_set (!array_refs) (!array_out_refs) p
