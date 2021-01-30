open Types


(* Check that array references are suitably defined *)

(* - First pass: build tree of definition dependances. See terms.ml *)

(* - Second pass: check array references 
     The verification routine takes as argument the references that 
     are surely defined at the current point. *)

let rec check_def_term defined_refs t =
  match t.t_desc with
    Var(b,l) ->
      if not (List.exists (Terms.equal_binderref (b,l)) defined_refs) then
	begin
	  let t_string =
	    Display.string_out (fun () -> 
	      Display.display_term t)
	  in
	  Parsing_helper.input_error ("Variable reference "^t_string^" not defined") t.t_loc
	end;
      List.iter (check_def_term defined_refs) l
  | ReplIndex b -> ()
  | FunApp(f,l) ->
      List.iter (check_def_term defined_refs) l
  | TestE(t1,t2,t3) ->
      check_def_term defined_refs t1;
      check_def_term defined_refs t2;
      check_def_term defined_refs t3
  | LetE(pat, t1, t2, topt) ->
      check_def_term defined_refs t1;
      let accu = ref defined_refs in
      check_def_pat accu defined_refs pat;
      check_def_term (!accu) t2;
      begin
	match topt with
	  None -> ()
	| Some t3 -> check_def_term defined_refs t3
      end
  | FindE(l0,t3,_) ->
      List.iter (fun (bl,def_list,t1,t2) ->
	let (defined_refs_t1, defined_refs_t2) = Terms.defined_refs_find bl def_list defined_refs in
	check_def_term defined_refs_t1 t1;
	check_def_term defined_refs_t2 t2) l0;
      check_def_term defined_refs t3
  | ResE(b,t) ->
      check_def_term ((Terms.binderref_from_binder b)::defined_refs) t
  | EventAbortE(f) -> ()
  | EventE(t,p) ->
      check_def_term defined_refs t;
      check_def_term defined_refs p
  | GetE(tbl,patl,topt,p1,p2,_) ->
      let accu = ref defined_refs in
      check_def_pat_list accu defined_refs patl;
      (match topt with 
        | Some t -> check_def_term (!accu) t
        | None -> ());
      check_def_term (!accu) p1;
      check_def_term defined_refs p2
  | InsertE(tbl,tl,p) ->
      check_def_term_list defined_refs tl;
      check_def_term defined_refs p

and check_def_pat accu defined_refs = function
    PatVar b -> accu := (Terms.binderref_from_binder b) :: (!accu)
  | PatTuple (f,l) ->
      List.iter (check_def_pat accu defined_refs) l
  | PatEqual t -> check_def_term defined_refs t

and check_def_pat_list accu defined_refs = function
  | pat::l -> 
      check_def_pat accu defined_refs pat;
      check_def_pat_list accu defined_refs l
  | [] -> ()

and check_def_term_list defined_refs = function
  | t::l ->
      check_def_term defined_refs t;
      check_def_term_list defined_refs l
  | [] ->
      ()

let rec check_def_process defined_refs p =
  match p.i_desc with
    Nil -> ()
  | Par(p1,p2) -> 
      check_def_process defined_refs p1;
      check_def_process defined_refs p2
  | Repl(b,p) ->
      check_def_process defined_refs p
  | Input((c,tl),pat,p) ->
      List.iter (check_def_term defined_refs) tl;
      let accu = ref defined_refs in
      check_def_pat accu defined_refs pat;
      check_def_oprocess (!accu) p

and check_def_oprocess defined_refs p = 
  match p.p_desc with
    Yield | EventAbort _ -> ()
  | Restr(b,p) ->
      check_def_oprocess ((Terms.binderref_from_binder b)::defined_refs) p
  | Test(t,p1,p2) ->
      check_def_term defined_refs t;
      check_def_oprocess defined_refs p1;
      check_def_oprocess defined_refs p2
  | Find(l0,p2,_) ->
      List.iter (fun (bl,def_list,t,p1) ->
	let (defined_refs_t, defined_refs_p1) = Terms.defined_refs_find bl def_list defined_refs in
	check_def_term defined_refs_t t;
	check_def_oprocess defined_refs_p1 p1) l0;
      check_def_oprocess defined_refs p2
  | Output((c,tl),t2,p) ->
      List.iter (check_def_term defined_refs) tl;
      check_def_term defined_refs t2;
      check_def_process defined_refs p
  | Let(pat,t,p1,p2) ->
      check_def_term defined_refs t;
      let accu = ref defined_refs in
      check_def_pat accu defined_refs pat;
      check_def_oprocess (!accu) p1;
      check_def_oprocess defined_refs p2
  | EventP(t,p) ->
      check_def_term defined_refs t;
      check_def_oprocess defined_refs p
  | Get(tbl,patl,topt,p1,p2,_) ->
      let accu = ref defined_refs in
      check_def_pat_list accu defined_refs patl;
      (match topt with 
        | Some t -> check_def_term (!accu) t
        | None -> ());
      check_def_oprocess (!accu) p1;
      check_def_oprocess defined_refs p2
  | Insert(tbl,tl,p) ->
      check_def_term_list defined_refs tl;
      check_def_oprocess defined_refs p


(* - Main checking function for processes *)

let check_def_process_main p =
  Def.build_def_process None p;
  check_def_process [] p;
  Def.empty_def_process p

(* - Main checking function for equivalence statements *)
  

let array_index_args args =
  List.filter (fun b -> match b.btype.tcat with
    Interv _ -> true
  | BitString -> false) args

(* Check that, when there is a common index, all following indices 
   are common too. Note that, since each replication has a different
   bound, typing guarantees that, if there is a common index, then
   this common index is at the same position. *)
let check_common_index (b,l) (b',l') =
  let lenl = List.length l in
  let lenl' = List.length l' in
  let minl = min lenl lenl' in
  let sufl = Terms.skip (lenl-minl) l in
  let sufl' = Terms.skip (lenl'-minl) l' in
  let rec check_common l1 l2 = 
    match l1,l2 with
      [],[] -> ()
    | a1::r1,a2::r2 -> 
	if Terms.equal_terms a1 a2 then 
	  begin
	    Parsing_helper.input_error "This array index is used in another array reference and this is not supported yet" a1.t_loc
	    (* TO DO The line above could be replaced by the next code, which
	       is more permissive. However, cryptotransf.ml does not support yet
	       array references that share arguments.
	       See TO DO in cryptotransf.ml, function check_lhs_array_ref.
	    if not (List.for_all2 Terms.equal_terms r1 r2) then
	      Parsing_helper.input_error "This array index is used elsewhere and the following indices are not the same in all usages" a1.t_loc
		*)
	  end
	else
	  check_common r1 r2
    | _ -> Parsing_helper.internal_error "check_common_index: I should have extracted suffixes of the same length" 
  in
  check_common sufl sufl'

let rec get_arg_array_ref index_args accu t = 
  match t.t_desc with
    Var(b,l) ->
      if List.exists 
	  (function { t_desc = Var(b',l') } when List.memq b' index_args -> true
	    | _ -> false) l then
	(* This is an array reference with an argument as index.
           Check that it is correct *)
	if List.exists (Terms.equal_binderref (b,l)) (!accu) then
	  (* Already found before and was ok, so it's ok *)
	  ()
	else
	  let rec check_ok l args_at_creation =
	    match l, args_at_creation with
	      [],[] -> ()
	    | (l1::lr, c1::cr) ->
		begin
		  match l1.t_desc with
		    ReplIndex ri when ri == c1 ->
		      Parsing_helper.input_error "Incorrect array reference: contains an argument of the function, but also implicitly refers to some current replication indices, and this is not supported yet" t.t_loc
		      (* TO DO The line above could be replaced by the next code, which
			 is more permissive. However, cryptotransf.ml does not support yet
			 array references with a part that consists of replication indices
			 and another part consisting of arguments of the function.
			 See TO DO in cryptotransf.ml, function check_lhs_array_ref.
		      if not (List.for_all2 Terms.equal_terms l args_at_creation) then
			Parsing_helper.input_error "Incorrect array reference" t.t_loc
			  *)
		  | Var(b',l') ->
			if not (List.memq b' index_args) then
			  Parsing_helper.input_error "Incorrect array reference: argument of the function expected as index" t.t_loc;
			if not (Terms.is_args_at_creation b' l') then
			  Parsing_helper.input_error "Incorrect array reference: argument index should have no indices" l1.t_loc;
			if not (Terms.is_restr b) then
			  Parsing_helper.input_error "Only restrictions are allowed to take arguments as indices" t.t_loc;
			check_ok lr cr
		  | _ ->  Parsing_helper.input_error "Variable expected as index in array reference" t.t_loc
		end
	    | _ -> Parsing_helper.input_error "Bad number of indices in array reference" t.t_loc
	  in
	  check_ok l b.args_at_creation;
	  List.iter (check_common_index (b,l)) (!accu);
	  accu := (b,l) :: (!accu)
      else
	List.iter (get_arg_array_ref index_args accu) l
  | ReplIndex _ -> ()
  | FunApp(f,l) -> 
      List.iter (get_arg_array_ref index_args accu) l
  | TestE(t1,t2,t3) ->
      get_arg_array_ref index_args accu t1;
      get_arg_array_ref index_args accu t2;
      get_arg_array_ref index_args accu t3
  | LetE(pat, t1, t2, topt) ->
      get_arg_array_ref index_args accu t1;
      get_arg_array_ref_pat index_args accu pat;
      get_arg_array_ref index_args accu t2;
      begin
	match topt with
	  None -> ()
	| Some t3 -> get_arg_array_ref index_args accu t3
      end
  | FindE(l0,t3,_) ->
      List.iter (fun (bl,def_list,t1,t2) ->
	List.iter (fun (_,l) -> List.iter (get_arg_array_ref index_args accu) l) def_list;
	get_arg_array_ref index_args accu t1;
	get_arg_array_ref index_args accu t2) l0;
      get_arg_array_ref index_args accu t3
  | ResE(b,t) ->
      get_arg_array_ref index_args accu t
  | EventAbortE(f) -> ()
  | EventE _ ->
      Parsing_helper.input_error "event is not allowed in equivalences" t.t_loc
  | GetE (tbl, patl, topt, p1, p2,_) ->
      List.iter (get_arg_array_ref_pat index_args accu) patl;
      begin
	match topt with
	  None -> ()
	| Some t -> get_arg_array_ref index_args accu t
      end;
      get_arg_array_ref index_args accu p1;
      get_arg_array_ref index_args accu p2
  | InsertE(tbl, tl, p) ->
      List.iter (get_arg_array_ref index_args accu) tl;
      get_arg_array_ref index_args accu p

and get_arg_array_ref_pat index_args accu = function
    PatVar b -> ()
  | PatTuple (f,l) ->
      List.iter (get_arg_array_ref_pat index_args accu) l
  | PatEqual t -> get_arg_array_ref index_args accu t
    

let rec check_def_fungroup def_refs = function
    ReplRestr(repl, restr, funlist) ->
      List.iter (check_def_fungroup ((List.map (fun (b,_) -> Terms.binderref_from_binder b) restr) @ def_refs)) funlist
  | Fun(ch, args, res, priority) ->
      let index_args = array_index_args args in
      let array_ref_args = ref [] in
      get_arg_array_ref index_args array_ref_args res;
      check_def_term ((List.map Terms.binderref_from_binder args) @ (!array_ref_args) @ def_refs) res

let check_def_member l =
  List.iter (fun (fg, mode) -> check_def_fungroup [] fg) l


(* Build types and functions for encoding indices *)

let encode_idx_types_funs = ref []

let rec build_encode_idx_types_funs_fg cur_array = function
  | ReplRestr(repl_opt, restr, funlist) ->
      begin
	match repl_opt with
	| None -> List.iter (build_encode_idx_types_funs_fg cur_array) funlist
	| Some repl ->
	    let cur_array' = repl::cur_array in
	    let repl_type = repl.ri_type in
	    let repl_param = Terms.param_from_type repl_type in
	    let encoded_type =
	      { tname = Terms.fresh_id ("encoded_"^repl_param.pname^"_t");
		tcat = BitString;
		toptions = 0;
		tsize = None;
		tpcoll = None;
		timplsize = None;
		tpredicate = None;
		timplname = None;
		tserial = None;
		trandom = None }
	    in
	    let encode_fun =
	      { f_name = Terms.fresh_id ("encode_"^repl_param.pname);
		f_type = List.map (fun ri -> ri.ri_type) cur_array, encoded_type;
		f_cat = Tuple;
		f_options = Settings.fopt_COMPOS;
		f_statements = [];
		f_collisions = [];
		f_eq_theories = NoEq;
		f_impl = No_impl;
		f_impl_inv = None }
	    in
	    encode_idx_types_funs := (repl_type, (encoded_type, encode_fun)) :: (!encode_idx_types_funs);
	    List.iter (build_encode_idx_types_funs_fg cur_array') funlist
      end
  | Fun _ -> ()

let build_encode_idx_types_funs l =
  encode_idx_types_funs := [];
  List.iter (fun (fg, mode) -> build_encode_idx_types_funs_fg [] fg) l
    

(* Check and simplify the right member of equivalences 
   NOTE: It is important that is called after check_def_eqstatement 
   on this equivalence, so that the definition nodes of variables
   have been computed. *)

let rec close_node_rec accu n l =
  List.iter (fun b' ->
    let l' = Terms.skip ((List.length l) - (List.length b'.args_at_creation)) l in
    accu := ((b',l'))::(!accu)
			  ) n.binders;
  match n.above_node with
  | None -> ()
  | Some n' -> close_node_rec accu n' l

let close_node n l =
  let accu = ref [] in
  close_node_rec accu n l;
  !accu

let rec close_node_list nlist l =
  match nlist with
  | [] -> Parsing_helper.internal_error "close_def: binder has no definition"
  | [n] -> close_node n l
  | n::rest ->
      Terms.inter_binderref (close_node n l) (close_node_list rest l)
       
let close_def (b,l) =
  if b.def == [] then
    Parsing_helper.internal_error ("close_def: binder "^(Display.binder_to_string b)^" has no definition");
  close_node_list b.def l

(*
let same_binders l1 l2 =
  List.for_all2 (fun b t ->
    match t.t_desc with
      Var(b'',l') when b'' == b -> true
    | _ -> false) l1 l2
*)


(* The rest of the code does not allow making array accesses on indices of find
   in the RHS of an equivalence. To allow it for the user, we replace 
     find u <= N suchthat ... then M, with an array access to u.
   with
     find u' <= N suchthat ... then let u = u' in M{u'/u} *)
    
let remove_array_access_find_idx ext has_more_indices lindex t2 =
  (* Raises [Not_found] when no index of find has an array access.
     In this case, the find is unchanged. *)
  let rec check_lindex = function
    | [] -> raise Not_found
    | [(b,ri)] ->
	if Array_ref.has_array_ref b then
	  if has_more_indices then
	    (* Do not create an index variable that cannot later be encoded.
               Only full sequence of indices of a variable can be encoded. *)
	    Parsing_helper.input_error ((Display.binder_to_string b)^" has an array access. It should correspond to the whole sequence of indices of a variable. Please store a tuple containing this index as well as associated current replication indices in a variable in the then branch, and make array accesses to this variable") ext
	  else
	    let b' = Terms.new_binder b in
	    [(b', ri)], (b,b')
	else
	  raise Not_found
    | ((b,ri) as b_ri) :: rest ->
	if Array_ref.has_array_ref b then
	  (* Do not create an index variable that cannot later be encoded.
             Only full sequence of indices of a variable can be encoded. *)
	  Parsing_helper.input_error ((Display.binder_to_string b)^" has an array access. Only the last index of a find is allowed to have an array access. For other cases, please store a tuple containing the indices of find "^(if has_more_indices then "as well as associated current replication indices " else "")^"in a variable in the then branch, and make array accesses to this variable") ext;
	let (rest', subst) = check_lindex rest in
	(b_ri :: rest', subst)
  in
  try 
    let (lindex', (b,b')) = check_lindex lindex in
    let b'_term = Terms.term_from_binder b' in
    let t2_subst = Terms.copy_term (OneSubst(b, b'_term, ref false)) t2 in
    let t2' = Terms.build_term t2 (LetE(PatVar b, b'_term, t2_subst, None)) in
    (lindex', t2')
  with Not_found ->
    (lindex, t2)

      
let rec remove_common_prefix l1 l2 = 
  match (l1,l2) with
  | ri::r1, {t_desc = ReplIndex ri'}::r2 when ri == ri' -> 
      remove_common_prefix r1 r2
  | _ ->
      (l1,l2)

let remove_common_suffix l1 l2 = 
  let l1rev = List.rev l1 in
  let l2rev = List.rev l2 in
  let (l1rev',l2rev') = remove_common_prefix l1rev l2rev in
  (List.rev l1rev', List.rev l2rev')

(* [replace_suffix old_suffix new_suffix l] checks that
   [l] ends with [old_suffix] and replaces the suffix [old_suffix] with
   [new_suffix] in [l] *)
let replace_suffix old_suffix new_suffix l =
  let lprefix = List.length l - List.length old_suffix in
  let (prefix, suffix) = Terms.split lprefix l in
  if not (List.for_all2 Terms.equal_terms suffix old_suffix) then
    Parsing_helper.internal_error "replace_suffix: old suffix not found";
  prefix @ new_suffix

let rec check_rm_term cur_array t =
  match t.t_desc with
    Var(b,l) ->
      Terms.build_term t (Var(b, List.map (check_rm_term cur_array) l))
  | ReplIndex b ->
      Terms.build_term t (ReplIndex b)
  | FunApp(f,l) ->
      Terms.build_term t (FunApp(f, List.map (check_rm_term cur_array) l))
  | LetE(pat,t1,t2,topt) ->
      let topt' =
	match topt with
	| None -> None
	| Some t3 -> Some (check_rm_term cur_array t3)
      in
      Terms.build_term t
	(LetE(check_rm_pat cur_array pat,
	      check_rm_term cur_array t1,
	      check_rm_term cur_array t2, topt'))
  | ResE(b,t') ->
      Terms.build_term t (ResE(b, check_rm_term cur_array t'))
  | TestE(t1,t2,t3) ->
      Terms.build_term t
	(TestE(check_rm_term cur_array t1,
	       check_rm_term cur_array t2,
	       check_rm_term cur_array t3))
  | FindE(l0, t3, find_info) ->
      let t3' = check_rm_term cur_array t3 in
      let l0' = 
	List.map (function
	  | ([], [], t1, t2) ->
	      let t1' = check_rm_term cur_array t1 in
	      let t2' = check_rm_term cur_array t2 in
	      ([], [], t1', t2')
	      
	  | (lindex, def_list, t1, t2) ->
	    (* Variables in def_list should have a particular form of indexes: 
	         a suffix of lindex + the same suffix of cur_array
	       At least one of these variables should use the full lindex.
	       Furthermore, a single reference in def_list should imply that all other
	       references are defined. This implies that the same find cannot reference
	       variables defined in different functions under the same replication
	       (which simplifies the code of cryptotransf.ml).

	       We allow in fact 
	        suffix of lindex + other variables (named [other_seq_middle]) + the same suffix of cur_array
	       and transform it into the previous form by adding one index in lindex for
	       each element of other variables, and checking that these indices are equal to
	       the other variables in the condition of find.
	       *)
	  let max_sequence = ref None in
	  List.iter (fun ((_,l) as def) ->
	    let def_closure = close_def def in
	    if List.for_all (fun def' -> List.exists (Terms.equal_binderref def') def_closure) def_list then
	      max_sequence := Some l
		   ) def_list;
	  
	  let max_seq =
	    match !max_sequence with
	    | None ->
		Parsing_helper.input_error "In equivalences, in find, one \"defined\" variable reference should imply all others" t.t_loc;
	    | Some max_seq -> max_seq
	  in
	  let l_index = List.length lindex in
	  let l_max_seq_suffix = List.length max_seq - l_index in
	  List.iter (fun (b',l) ->
	    if List.length l < l_max_seq_suffix then
	      Parsing_helper.input_error "Variables in right member of equivalences should have as indexes the indexes defined by find, plus possibly index variables" t.t_loc
		) def_list;
	  if List.length max_seq < l_index then
	    Parsing_helper.input_error "Variables in right member of equivalences should have as indexes the indexes defined by find, plus possibly index variables" t.t_loc;
	  let (lindex_maxseq, max_seq_suffix) = Terms.split l_index max_seq in
	  if not (List.for_all2 (fun (_,ri) t ->
	    match t.t_desc with
	    | ReplIndex ri' -> ri == ri'
	    | _ -> false) lindex lindex_maxseq) then
	    Parsing_helper.input_error "Variables in right member of equivalences should have as indexes the indexes defined by find, plus possibly index variables" t.t_loc;
	  let suffix = Terms.skip (List.length cur_array - l_max_seq_suffix) cur_array in
	  let (_, other_seq_middle) = remove_common_suffix suffix max_seq_suffix in
	  let cur_array_suffix_terms =
	    List.map Terms.term_from_repl_index (Terms.skip (List.length other_seq_middle) suffix)
	  in
	  let (lindex, def_list, t1, t2) =
	    match other_seq_middle with
	    | [] -> (lindex, def_list, t1, t2)
	    | _ ->
		(* When the variables in [def_list] use indices not defined by [find] and not in [curarray],
                   we reorganize the [find], by replacing these indices with indices defined by the [find]
                   and verifying equality between the new and old indices. For instance:
                     find u = j <= N suchthat defined(x[j,k]) && M(x[j,k]) then M'(x[u,k]) else ...
                   becomes
                     find u = j <= N, u' = j' <= N' suchthat defined(x[j,j']) && j' = k && M(x[j,j']) then M'(x[u,u']) else ...
                   The index k is replaced with the new index j' defined by [find], and we verify that j' = k 
                   in the condition of [find] so that the new code is equivalent to the old one. *)

		(* We implicitly check that [other_seq_middle] is already defined without the need
		   to put it in the defined condition, by verifying that the equality test
                   [lindex_addition = other_seq_middle] is ok (hence included in the [allowed_index_seq] *)
		let lindex_addition =
		  List.map (fun t ->
		    match t.t_desc with
		    | Var(b, _) ->
			let b' = Terms.new_binder b in
			let ri' = Terms.create_repl_index b.sname b.btype in
			(b', ri')
		    | _ ->
			Parsing_helper.input_error "Variables in right member of equivalences should have as indexes the indexes defined by find, plus possibly index variables" t.t_loc
			  ) other_seq_middle
		in
		let lindex' = lindex @ lindex_addition in
	        (* Replace the sequence of indices [max_seq_suffix] with [new_seq_suffix = (List.map snd lindex_addition) @ removed common suffix]
                   in [def_list], yielding [def_list']. *)
		let new_seq_suffix =
		  (List.map (fun (_, ri) -> Terms.term_from_repl_index ri) lindex_addition) @
		  cur_array_suffix_terms
		in
		let def_list' = List.map (fun (b, l) -> (b, replace_suffix max_seq_suffix new_seq_suffix l)) def_list in
                (* Replace the array refs [def_list] with [def_list'] in [t1] *)
		let lsubst = List.map2 (fun br br' -> (br, Terms.term_from_binderref br')) def_list def_list' in
		let t1' = Terms.copy_term (SubstArgs lsubst) t1 in
		(* Add test [(max_seq_suffix) = ((List.map snd lindex_addition) @ removed common suffix)] in [t1] *)
		let test =
		  match max_seq_suffix, new_seq_suffix with
		  | [old_t], [new_t] -> Terms.make_equal new_t old_t 
		  | _ ->
		      let type_l = List.map (fun t -> t.t_type) max_seq_suffix in
		      let tuple_fun = Settings.get_tuple_fun type_l in
		      Terms.make_equal (Terms.app tuple_fun new_seq_suffix) (Terms.app tuple_fun max_seq_suffix) 
		in
		let t1'' = Terms.make_and test t1' in
                (* Replace the array refs [def_list{var/ri}] with [def_list'{var/ri}] in [t2] *)
		let subst_idx bl def_list =
		  let vars = List.map fst bl in
		  let repl_indices = List.map snd bl in
		  Terms.subst_def_list repl_indices (List.map Terms.term_from_binder vars) def_list 
		in
		let def_list_then = subst_idx lindex def_list in
		let def_list_then' = subst_idx lindex' def_list' in
		let lsubst' = List.map2 (fun br br' -> (br, Terms.term_from_binderref br')) def_list_then def_list_then' in
		let t2' = Terms.copy_term (SubstArgs lsubst') t2 in
		(lindex', def_list', t1'', t2')
	  in
	      (* if not (List.for_all2 (==) suffix max_seq_suffix) then
		 Parsing_helper.input_error "Variables in right member of equivalences should have as indexes the indexes defined by find" t.t_loc; *)
          let (lindex, t2) = remove_array_access_find_idx t.t_loc (cur_array_suffix_terms != []) lindex t2 in
	  let t1' = check_rm_term cur_array t1 in
	  let t2' = check_rm_term cur_array t2 in
	  (lindex, def_list, t1', t2')
	    ) l0
      in
      Terms.build_term t (FindE(l0', t3', find_info))
  | EventAbortE(f) -> Terms.build_term t (EventAbortE f)
  | EventE _ | GetE _ | InsertE _ ->
      Parsing_helper.input_error "insert, get, and event are not allowed in equivalences" t.t_loc

and check_rm_pat cur_array = function
    PatVar b -> PatVar b
  | PatTuple (f,l) -> PatTuple (f,List.map (check_rm_pat cur_array) l)
  | PatEqual t -> PatEqual (check_rm_term cur_array t)

let rec check_rm_fungroup cur_array = function
    ReplRestr(repl_opt, restr, funlist) ->
      let cur_array' = Terms.add_cur_array repl_opt cur_array in
      ReplRestr(repl_opt, restr, List.map (check_rm_fungroup cur_array') funlist)
  | Fun(ch, args, res, priority) ->
      let index_args = array_index_args args in
      let array_ref_args = ref [] in
      get_arg_array_ref index_args array_ref_args res;
      let allowed_index_seq_args = List.map (fun (b,l) -> l) (!array_ref_args) in
      let res = check_rm_term cur_array res in
      let rec make_lets body = function
	  [] -> ([], body)
	| (b::l) -> 
	    let (b_inputs', body') = make_lets body l in
	    if (b.btype.tcat <> BitString) && (Array_ref.has_array_ref b) then
	      if not (List.exists (Terms.equal_term_lists [Terms.term_from_binder b]) allowed_index_seq_args) then
		Parsing_helper.input_error ((Display.binder_to_string b)^" has an array access. It should correspond to the full sequence of indices of a variable. For other cases, please store the full sequence of indices in a tuple, and make array accesses to this tuple.") body.t_loc
	      else
		let b' = Terms.new_binder b in
		let b'_term = Terms.term_from_binder b' in
		let body'_subst = Terms.copy_term (OneSubst(b, b'_term, ref false)) body' in
		(b'::b_inputs', 
		 Terms.build_term_type body'.t_type
		   (LetE(PatVar b, b'_term, body'_subst, None)))
	    else
	      (b::b_inputs', body')
      in
      let (args', res') = make_lets res args in
      Fun(ch, args', res', priority)

(* [add_suffixes accu common_suffix l] adds to [accu]
   all suffixes of [l @ common_suffix] strictly containing [common_suffix] *)
let rec add_suffixes accu common_suffix = function
  | [] -> accu
  | (_::l) as l0 ->
      add_suffixes ((l0 @ common_suffix)::accu) common_suffix l
	     
let merge_types t1 t2 ext =
  if t1 == Settings.t_any then
    t2
  else if t2 == Settings.t_any then
    t1
  else 
    begin
      if t1 != t2 then
	Parsing_helper.input_error "All branches of if/let/find/get should yield the same type, even after encoding indices" ext;
      t1
    end

(* [renamed_vars] is a list of pairs of variables (b,b') such that
   b is a variable in the RHS of the equivalence, and b' is the variable
   used instead of b after encoding indices. *)
let renamed_vars = ref []

exception Not_idx

(* [get_assoc_var b] returns that variable that should be used instead of [b]
   after encoding indices. When [b] does not contain an index, it returns [b]
   itself. 
   This function does not check that indices are correctly used. The 
   full check is done in [encode_idx_term]. *)
let rec get_assoc_var b =
  try
    List.assq b (!renamed_vars)
  with Not_found ->
    if List.for_all (fun n ->
      match n.definition with
      | DTerm { t_desc = LetE(PatVar _,_,_,_) } ->
	  true
      | _ -> false
	    ) b.def then
      match b.def with
      | [] -> b
      | n::_ ->
	  match n.definition with
	  | DTerm { t_desc = LetE(PatVar _,t,_,_) } ->
	      begin
		try 
		  let encoded_ty =
		    if t.t_type.tcat != BitString then
		      let (encoded_ty,_) = List.assq t.t_type (!encode_idx_types_funs) in
		      encoded_ty
		    else if t.t_type == Settings.t_bitstring then
		      (* May be indices contained in a tuple *)
		      get_idx_type t
		    else
		      raise Not_idx
		  in
		  let b' = Terms.create_binder ("encoded_"^(Display.binder_to_string b)) encoded_ty b.args_at_creation in
		  renamed_vars := (b,b') :: (!renamed_vars);
		  b'
		with Not_idx ->
		  b
	      end
	  | _ -> assert false
    else
      b

and get_idx_type t =
  (* Get the encoded index type when [t] is a tuple containing indices.
     Raises [Not_idx] otherwise. *)
  match t.t_desc with
  | Var(b,l) ->
      let b' = get_assoc_var b in
      if b' == b then
	raise Not_idx
      else
        b'.btype	
  | ReplIndex _ -> assert false
  | FunApp(f,l) ->
      begin
	match l with
	| t1::_ -> 
	    if t1.t_type.tcat != BitString then
	      begin
		if f.f_cat != Tuple || f.f_name <> "" then
		  Parsing_helper.input_error "In the right-hand of equiv, only standard tuples can take indices as arguments" t.t_loc;
		let (encoded_ty,_) = List.assq t1.t_type (!encode_idx_types_funs) in
		encoded_ty
	      end
	    else
	      raise Not_idx
	| _ -> raise Not_idx
      end
  | LetE(pat,t1,t2,topt) ->
      begin
	match topt with
	| Some t3 when t3.t_type != Settings.t_any ->
            get_idx_type t3
	| _ -> get_idx_type t2
      end
  | ResE(b,t') ->
      get_idx_type t' 
  | TestE(t1,t2,t3) ->
      if t2.t_type != Settings.t_any then
	get_idx_type t2
      else
	get_idx_type t3
  | FindE(l0, t3, find_info) ->
      if t3.t_type != Settings.t_any then
	get_idx_type t3
      else
	let rec find_idx_type = function
	  | [] -> raise Not_idx
	  | (_,_,_,t2)::rest ->
	      if t2.t_type != Settings.t_any then
		get_idx_type t2
	      else
		find_idx_type rest
	in
	find_idx_type l0
  | EventAbortE(f) ->
      raise Not_idx
  | EventE _ | GetE _ | InsertE _ ->
      Parsing_helper.input_error "insert, get, and event are not allowed in equivalences" t.t_loc

(* [encode_idx ext allowed_index_seq idx_l] transforms 
   the list of indices [idx_l = [i1;...;in]] into
   [encode_N(i1,...,in)] which is the encoding the
   [idx_l], provided the sequence [i1,...,in] is in
   the allowed index sequences [allowed_index_seq]. *)
let encode_idx ext allowed_index_seq idx_l =
  let first_idx = List.hd idx_l in
  try 
    let seq =
      List.find (fun seq -> Terms.equal_terms first_idx (List.hd seq)) allowed_index_seq
    in
    if not (Terms.equal_term_lists seq idx_l) then
      raise Not_found;
    let (_, encode_fun) = List.assq first_idx.t_type (!encode_idx_types_funs) in
    Terms.app encode_fun seq
  with Not_found ->
    let idxl_to_string idxl =
      match idxl with
      | [idx] -> Display.string_out (fun () -> Display.display_term idx)
      | _ -> "(" ^ (Display.string_out (fun () -> Display.display_list Display.display_term idxl)) ^ ")"
    in
    let allowed_idx = String.concat "\n  " (List.map idxl_to_string allowed_index_seq) in
    Parsing_helper.input_error ("These indices "^(idxl_to_string idx_l)^" are not allowed. The allowed indices are:\n - the current replication indices, and any suffix thereof;\n - the indices of a find concatenated with the associated current replication indices to build a full sequence of indices, and any suffix thereof;\n - indices received as argument by the oracle, when there is a variable that has these indices.\nHence the indices allowed here are\n  "^allowed_idx) ext
    
let rec encode_idx_term cur_array allowed_index_seq t =
  match t.t_desc with
    Var(b,l) ->
      (* if b defined by "let b = EIT in", then replace b with associated variable b' *)
      let b' = get_assoc_var b in
      if b' == b && t.t_type.tcat != BitString then
	(* case b = find index or received index -> encode it *)
	encode_idx t.t_loc allowed_index_seq [t]
      else
	Terms.new_term b'.btype t.t_loc (Var(get_assoc_var b, l))
  | ReplIndex b ->
      encode_idx t.t_loc allowed_index_seq [t]
  | FunApp({ f_cat = Equal}, [t1; t2]) ->
      (* Allow comparison of indices, by encoding them *)
      let t1' = encode_idx_term cur_array allowed_index_seq t1 in
      let t2' = encode_idx_term cur_array allowed_index_seq t2 in
      if (t1'.t_type != t2'.t_type) && (t1'.t_type != Settings.t_any) && (t2'.t_type != Settings.t_any) then
	Parsing_helper.input_error "= should have two arguments of the same type, even after encoding of indices" t.t_loc;
      Terms.make_equal_ext t.t_loc t1' t2'
  | FunApp({ f_cat = Diff}, [t1; t2]) ->
      (* Allow comparison of indices, by encoding them *)
      let t1' = encode_idx_term cur_array allowed_index_seq t1 in
      let t2' = encode_idx_term cur_array allowed_index_seq t2 in
      if (t1'.t_type != t2'.t_type) && (t1'.t_type != Settings.t_any) && (t2'.t_type != Settings.t_any) then
	Parsing_helper.input_error "<> should have two arguments of the same type, even after encoding of indices" t.t_loc;
      Terms.make_diff_ext t.t_loc t1' t2'
  | FunApp(f,l) ->
      if List.exists (fun t -> t.t_type.tcat != BitString) l then
	begin
        (* case (i1,...,in) -> encode it *)
	  if f.f_cat != Tuple || f.f_name <> "" then
	    Parsing_helper.input_error "In the right-hand of equiv, only standard tuples can take indices as arguments" t.t_loc;
	  encode_idx t.t_loc allowed_index_seq l
	end
      else
	Terms.build_term t (FunApp(f, List.map (encode_idx_term_keep_type cur_array allowed_index_seq) l))
  | LetE(pat,t1,t2,topt) ->
      let t1' = encode_idx_term cur_array allowed_index_seq t1 in
      let t2' = encode_idx_term cur_array allowed_index_seq t2 in
      let topt', new_type =
	match topt with
	| None -> None, t2'.t_type
	| Some t3 ->
	    let t3' = encode_idx_term cur_array allowed_index_seq t3 in
	    Some t3', merge_types t2'.t_type t3'.t_type t.t_loc
      in
      if t1'.t_type != t1.t_type then
	(* [t1] is an index that got encoded into [t1'] *)
	begin
	  match pat with
	  | PatVar b ->
	      let b' = get_assoc_var b in
	      if b'.btype != t1'.t_type then
		Parsing_helper.input_error ("Variable "^(Display.binder_to_string b)^" assigned indices of different types, or not always assigned indices") t.t_loc;
	      Terms.new_term new_type t.t_loc
		(LetE(PatVar b', t1', t2', topt'))
	  | _ ->
	      Parsing_helper.input_error "an index to be encoded is matched with a non-variable pattern" t.t_loc
	end
      else
	Terms.new_term new_type t.t_loc
	  (LetE(encode_idx_pat cur_array allowed_index_seq t.t_loc pat,
		t1', t2', topt'))
  | ResE(b,t') ->
      let t'' = encode_idx_term cur_array allowed_index_seq t' in
      Terms.new_term t''.t_type t.t_loc (ResE(b, t''))
  | TestE(t1,t2,t3) ->
      let t2' = encode_idx_term cur_array allowed_index_seq t2 in
      let t3' = encode_idx_term cur_array allowed_index_seq t3 in
      let new_type = merge_types t2'.t_type t3'.t_type t.t_loc in
      Terms.new_term new_type t.t_loc
	(TestE(encode_idx_term_keep_type cur_array allowed_index_seq t1,
	       t2', t3'))
  | FindE(l0, t3, find_info) ->
      let t3' = encode_idx_term cur_array allowed_index_seq t3 in
      let t_common = ref t3'.t_type in
      let l0' = 
	List.map (function
	  | ([], [], t1, t2) ->
	      let t1' = encode_idx_term_keep_type cur_array allowed_index_seq t1 in
	      let t2' = encode_idx_term cur_array allowed_index_seq t2 in
	      t_common := merge_types (!t_common) t2'.t_type t.t_loc;	  
	      ([], [], t1', t2')
	      
	  | (lindex, def_list, t1, t2) ->
	    (* Variables in def_list should have a particular form of indexes: 
	         a suffix of lindex + the same suffix of a sequence in cur_array
	       At least one of these variables should use the full lindex.
	       Furthermore, a single reference in def_list should imply that all other
	       references are defined. This implies that the same find cannot reference
	       variables defined in different functions under the same replication
	       (which simplifies the code of cryptotransf.ml).

	       This form has already been checked in [check_rm_term].
	       Here, we just recover the considered suffix of cur_array,
	       because we need it to compute the allowed index sequences.
	       *)
	  let max_sequence = ref None in
	  List.iter (fun ((_,l) as def) ->
	    let def_closure = close_def def in
	    if List.for_all (fun def' -> List.exists (Terms.equal_binderref def') def_closure) def_list then
	      max_sequence := Some l
		   ) def_list;
	  
	  let max_seq =
	    match !max_sequence with
	    | None ->
		Parsing_helper.input_error "In equivalences, in find, one \"defined\" variable reference should imply all others" t.t_loc;
	    | Some max_seq -> max_seq
	  in
	  let l_index = List.length lindex in
	  let l_max_seq_suffix = List.length max_seq - l_index in
	  let suffix = Terms.skip (List.length cur_array - l_max_seq_suffix) cur_array in
	  let cur_array_suffix_terms = List.map Terms.term_from_repl_index suffix in
          let def_list' = List.map (fun(b,l) -> (get_assoc_var b,l)) def_list in
	  let allowed_index_seq_t1 =
	    add_suffixes allowed_index_seq cur_array_suffix_terms
	      (List.map (fun (_, ri) -> Terms.term_from_repl_index ri) lindex)
	  in
	  let t1' = encode_idx_term_keep_type cur_array allowed_index_seq_t1 t1 in
	  let allowed_index_seq_t2 =
	    add_suffixes allowed_index_seq cur_array_suffix_terms
	      (List.map (fun (b, _) -> Terms.term_from_binder b) lindex)
	  in
	  let t2' = encode_idx_term cur_array allowed_index_seq_t2 t2 in
	  t_common := merge_types (!t_common) t2'.t_type t.t_loc;	  
	  (lindex, def_list', t1', t2')
	    ) l0
      in
      Terms.new_term (!t_common) t.t_loc (FindE(l0', t3', find_info))
  | EventAbortE(f) ->
      Terms.build_term t (EventAbortE(f))
  | EventE _ | GetE _ | InsertE _ ->
      Parsing_helper.input_error "insert, get, and event are not allowed in equivalences" t.t_loc

and encode_idx_pat cur_array allowed_index_seq ext = function
    PatVar b ->
      if get_assoc_var b != b then
	Parsing_helper.input_error ("Variable "^(Display.binder_to_string b)^" sometimes contains an index to be encoded, sometimes not") ext;
      PatVar b
  | PatTuple (f,l) -> PatTuple (f,List.map (encode_idx_pat cur_array allowed_index_seq ext) l)
  | PatEqual t -> PatEqual (encode_idx_term_keep_type cur_array allowed_index_seq t)

and encode_idx_term_keep_type cur_array allowed_index_seq t =
  let t' = encode_idx_term cur_array allowed_index_seq t in
  if t'.t_type != t.t_type then
    Parsing_helper.input_error "index to be encoded is not allowed here" t.t_loc;
  t'

let rec encode_idx_fungroup cur_array = function
    ReplRestr(repl_opt, restr, funlist) ->
      let cur_array' = Terms.add_cur_array repl_opt cur_array in
      ReplRestr(repl_opt, restr, List.map (encode_idx_fungroup cur_array') funlist)
  | Fun(ch, args, res, priority) ->
      let index_args = array_index_args args in
      let array_ref_args = ref [] in
      get_arg_array_ref index_args array_ref_args res;
      let allowed_index_seq_args = List.map (fun (b,l) -> l) (!array_ref_args) in
      let allowed_index_seq = add_suffixes allowed_index_seq_args [] (List.map Terms.term_from_repl_index cur_array) in
      let res = encode_idx_term_keep_type cur_array allowed_index_seq res in
      let rec make_lets body = function
	  [] -> ([], body)
	| (b::l) -> 
	    let (b_inputs', body') = make_lets body l in
	    (* let already introduced for index arguments with array references in 
	       [check_rm_fungroup] *)
	    if b.btype.tcat == BitString then
	      let b' = Terms.new_binder b in
	      (b'::b_inputs', 
	       Terms.build_term_type body'.t_type
		 (LetE(PatVar b, Terms.term_from_binder b', body', None)))
	    else
	      (b::b_inputs', body')
      in
      let (args', res') = make_lets res args in
      Fun(ch, args', res', priority)

(* When there is a name just above a function in the left-hand side,
   the corresponding function in the right-hand side must not contain
   new names (in the term), for the crypto transformation to be correct
   as it is implemented. So we move the names in the sequence of names
   just above the function in the right-hand side. *)

let rec move_names_term add_names corresp_list t =
  match t.t_desc with
    Var(b,l) ->
      Terms.build_term t (Var(b, List.map (move_names_term add_names corresp_list) l))
  | ReplIndex b ->
      Terms.build_term t (ReplIndex b)
  | FunApp(f,l) ->
      Terms.build_term t (FunApp(f, List.map (move_names_term add_names corresp_list) l))
  | ResE(b,t1) ->
      let t' = move_names_term add_names corresp_list t1 in
      add_names := b::(!add_names);
      if b.root_def_std_ref || b.root_def_array_ref then
	let b' = Terms.new_binder b in
	corresp_list := (b,b')::(!corresp_list);
	Terms.build_term t (LetE(PatVar b', Stringmap.cst_for_type b.btype  , t', None))
      else
	t'
  | LetE(pat, t1, t2, topt) ->
      Terms.build_term t (LetE(move_names_pat add_names corresp_list pat,
		      move_names_term add_names corresp_list t1,
		      move_names_term add_names corresp_list t2,
		      match topt with
			None -> None
		      |	Some t3 -> Some (move_names_term add_names corresp_list t3)))
  | FindE(l0, t3, find_info) ->
      let move_br (b,l) = (b, List.map (move_names_term add_names corresp_list) l) in
      Terms.build_term t (FindE(List.map (fun (bl, def_list, t1, t2) ->
	(bl, 
	 List.map move_br def_list, 
	 move_names_term add_names corresp_list t1, 
	 move_names_term add_names corresp_list t2)) l0, 
		       move_names_term add_names corresp_list t3, find_info))
  | TestE(t1,t2,t3) ->
      Terms.build_term t (TestE(move_names_term add_names corresp_list t1,
		       move_names_term add_names corresp_list t2,
		       move_names_term add_names corresp_list t3))
  | EventAbortE(f) ->
      Terms.build_term t (EventAbortE(f))
  | EventE _ | GetE _ | InsertE _ ->
      Parsing_helper.input_error "insert, get, and event are not allowed in equivalences" t.t_loc

and move_names_pat add_names corresp_list = function
    PatVar b -> PatVar b
  | PatTuple(f,l) -> PatTuple(f, List.map (move_names_pat add_names corresp_list) l)
  | PatEqual t -> PatEqual (move_names_term add_names corresp_list t)

let rec move_names corresp_list lm_name_above lm_fungroup rm_fungroup =
  match (lm_fungroup, rm_fungroup) with
    (ReplRestr(_, restr, funlist), ReplRestr(repl', restr', funlist')) ->
      let (add_names, funlist'') = move_names_list corresp_list (restr != []) funlist funlist' in
      ([], ReplRestr(repl', (List.map (fun b -> (b, NoOpt)) add_names) @ restr', funlist''))
  | (Fun(_,_,_,_), Fun(ch',args', res', priority')) ->
      if lm_name_above then
	let add_names = ref [] in
	let res'' = move_names_term add_names corresp_list res' in
	(!add_names, Fun(ch', args', res'', priority'))
      else
	([], rm_fungroup)
  | _ -> Parsing_helper.internal_error "Structures of left- and right-hand sides of an equivalence must be the same"

and move_names_list corresp_list lm_name_above lm rm =
  match (lm,rm) with
    [],[] -> ([], [])
  | (lm1::lmr),(rm1::rmr) -> 
      let (add_names1, rm1') = move_names corresp_list lm_name_above lm1 rm1 in
      let (add_namesr, rmr') = move_names_list corresp_list lm_name_above lmr rmr in
      (add_names1 @ add_namesr, rm1'::rmr')
  | _ -> Parsing_helper.internal_error "Structures of left- and right-hand sides of an equivalence must be the same"

let rec update_def_list_term corresp_list t =
  Terms.build_term t 
     (match t.t_desc with
	Var(b,l) ->
	  Var(b, List.map (update_def_list_term corresp_list) l)
      | ReplIndex b -> ReplIndex b 
      | FunApp(f,l) ->
	  FunApp(f, List.map (update_def_list_term corresp_list) l)
      | ResE(b,t) ->
	  ResE(b, update_def_list_term corresp_list t)
      | LetE(pat, t1, t2, topt) ->
	  LetE(update_def_list_pat corresp_list pat,
	       update_def_list_term corresp_list t1,
	       update_def_list_term corresp_list t2,
	       match topt with
		 None -> None
	       | Some t3 -> Some (update_def_list_term corresp_list t3))
      | FindE(l0, t3, find_info) ->
	  FindE(List.map (fun (bl, def_list, t1, t2) ->
	    let def_list_subterms = ref [] in
	    List.iter (Terms.close_def_subterm def_list_subterms) def_list;
	    let add_def_list = ref def_list in
	    List.iter (fun (b,l) ->
	      try
		add_def_list := (List.assq b corresp_list, l) :: (!add_def_list)
	      with Not_found -> ()) (!def_list_subterms);
	    (bl, 
	     (!add_def_list), 
	     update_def_list_term corresp_list t1, 
	     update_def_list_term corresp_list t2)) l0, 
		update_def_list_term corresp_list t3, find_info)
      | TestE(t1,t2,t3) ->
	  TestE(update_def_list_term corresp_list t1,
		update_def_list_term corresp_list t2,
		update_def_list_term corresp_list t3)
      | EventAbortE(f) ->
	  EventAbortE(f)
      | EventE _ | GetE _ | InsertE _ ->
	  Parsing_helper.input_error "insert, get, and event are not allowed in equivalences" t.t_loc)

and update_def_list_pat corresp_list = function
    PatVar b -> PatVar b
  | PatTuple(f,l) -> PatTuple(f, List.map (update_def_list_pat corresp_list) l)
  | PatEqual t -> PatEqual (update_def_list_term corresp_list t)
    

let rec update_def_list corresp_list = function
    ReplRestr(repl, restr, fungroup) ->
      ReplRestr(repl, restr, List.map (update_def_list corresp_list) fungroup)
  | Fun(ch, args, res, priority) ->
      Fun(ch, args, update_def_list_term corresp_list res, priority)
	
let move_names_all lmg rmg =
  let corresp_list = ref [] in
  let rmg' = 
    List.map2 (fun (lm,_) (rm, mode) ->
      let (_, rm') = move_names corresp_list false lm rm in
      (rm', mode)) lmg rmg
  in
  List.map (fun (rm, mode) -> (update_def_list (!corresp_list) rm, mode)) rmg'


(* Define a mapping between restrictions in the right-hand side and 
   restrictions in the left-hand side, such that, if a name is used in
   a certain function in the right-hand side, then the corresponding
   name is also used in the corresponding function in the left-hand side. *)

(* uses b0 t is true when the term t uses the variable b0 *)

let rec uses b0 t = 
  match t.t_desc with
    Var (b,l) -> 
      ((b == b0) && (Terms.is_args_at_creation b l)) || 
      (List.exists (uses b0) l)
  | ReplIndex _ -> false
  | FunApp(f,l) -> List.exists (uses b0) l
  | TestE(t1,t2,t3) -> (uses b0 t1) || (uses b0 t2) || (uses b0 t3)
  | ResE(b,t) -> uses b0 t
  | FindE(l0,t3, _) -> 
      (List.exists (fun (bl,def_list,t1,t2) ->
	((uses b0 t1) || (uses b0 t2)) &&
	(* When [b0] occurs in [def_list], its definition
           will be dynamically checked, so [b0] does not
           need to be syntactically defined above the transformed
	   term in the game. Therefore, we do not consider that
	   as a usage of [b0]. *)
	(not (List.exists (fun (b,l) ->
	  (b == b0) && (Terms.is_args_at_creation b l)) def_list))
	  ) l0) || 
      (uses b0 t3)
  | LetE(pat, t1, t2, topt) ->
      (uses_pat b0 pat) ||
      (uses b0 t1) || (uses b0 t2) ||
      (match topt with
	None -> false
      |	Some t3 -> uses b0 t3)
  | EventAbortE(f) -> false
  | EventE _ | GetE _ | InsertE _ ->
      Parsing_helper.input_error "insert, get, and event are not allowed in equivalences" t.t_loc

and uses_pat b0 = function
    PatVar b -> false
  | PatTuple (f,l) -> List.exists (uses_pat b0) l
  | PatEqual t -> uses b0 t 


exception NotCorresp

let rec check_corresp_uses b b' accu funlist funlist' =
  match funlist, funlist' with
    (ReplRestr(_, _, funlist), ReplRestr(_, _, funlist')) ->
       List.fold_left2 (check_corresp_uses b b') accu funlist funlist'
  | (Fun (_,args,res,_), Fun (_,args',res',_)) -> 
      (* For references to b/b' without explicit indices *)
      let accu' = 
	if uses b' res' then 
	  if uses b res then accu else res::accu
	else accu
      in
      (* For references to b/b' with indices taken in arguments *)
      let index_args = array_index_args args in
      let array_ref_args = ref [] in
      get_arg_array_ref index_args array_ref_args res;
      let index_args' = array_index_args args' in
      let array_ref_args' = ref [] in
      get_arg_array_ref index_args' array_ref_args' res';
      let args_map = List.combine args' args in
      List.iter (fun (b'',l') -> 
	if b'' == b' then
	  (* b'[l'] used in res' *)
	  let l = List.map (function
	      { t_desc = Var(i,_) } -> 
		Terms.term_from_binder (List.assq i args_map)
	    | _ -> 
		Parsing_helper.internal_error "Variable expected as index") l'
	  in
	  (* Check if b[l] is used in res *)
	  if not (List.exists (Terms.equal_binderref (b,l)) (!array_ref_args)) then
	    (* I do not allow array accesses in the RHS that do not correspond to array accesses
	       in the LHS. If I wanted to allow that, I should complete the correspondence between
	       names also for array accesses, by extending complete_env in cryptotransf.ml *)
	    raise NotCorresp
	      ) (!array_ref_args');
      accu'

  | _ -> Parsing_helper.internal_error "Structures of left- and right-hand sides of an equivalence must be the same"

let find_assoc restr funlist b' bopt' funlist' =
  try
    if bopt' != Unchanged then raise Not_found;
    let (b,_) = List.find (fun (b,_) -> Terms.equiv_same_vars b b') restr in
    (* b' is marked "unchanged"; a restriction with the same name 
       exists in the left-hand side.
       Try to associate it with b'; check that all functions that
       use b' in the right-hand side also use b' in the left-hand side.
       If this is not the case, we add some elements in "def_check"
       (the second element of the pair, result of find_assoc,
       which will end up as third element of the name mapping) *)
    try
      let def_check = List.fold_left2 (check_corresp_uses b b') [] funlist funlist' in
      (b, def_check)
    with NotCorresp ->
      Parsing_helper.user_error (b.sname ^ " in the left-hand side does not correspond to " ^ b'.sname ^ " in the right-hand side, because there is an array access in the right-hand side that does not match the one in the left-hand side.\n")
  with Not_found -> 
    let rec find_min_def_check = function
	[] -> Parsing_helper.internal_error "should have at least one restriction in Check.find_assoc"
      |	[(b,_)] ->
	  begin
	    try 
	      (b, List.fold_left2 (check_corresp_uses b b') [] funlist funlist')
	    with NotCorresp ->
	      Parsing_helper.user_error (b'.sname ^ " in the right-hand side corresponds to no variable in the left-hand side, because there is an array access in the right-hand side that does not match one in the left-hand side.\n")
	  end
      |	((b,_)::l) ->
	  try
	    let defcheck_cur = List.fold_left2 (check_corresp_uses b b') [] funlist funlist' in
	    if defcheck_cur == [] then (b, defcheck_cur) else
	    let (btmp, defchecktmp) = find_min_def_check l in
	    if List.length defcheck_cur <= List.length defchecktmp then
	      (b, defcheck_cur)
	    else
	      (btmp, defchecktmp)
	  with NotCorresp -> 
	    find_min_def_check l
    in
    find_min_def_check restr
      

let rec build_restr_mapping_fungroup restr_mapping lm rm =
  match lm, rm with
    (ReplRestr(_, restr, funlist), ReplRestr(_, restr', funlist')) ->
      List.iter2 (build_restr_mapping_fungroup restr_mapping) funlist funlist';
      if restr = [] then
	()
      else
	List.iter (fun (b',bopt') ->
	  let (b, def_check) = find_assoc restr funlist b' bopt' funlist' in
	  (* print_string ("Mapping " ^ b'.sname ^ " to " ^ b.sname ^ "\n");
	  List.iter (fun (l,res) ->
	      print_string "check that ";
	      Display.display_var b l;
              print_string " is defined at occurrences of ";
              Display.display_term res;
              print_newline()) def_check; *)
	  restr_mapping := (b', b, def_check):: (!restr_mapping)) restr'
  | (Fun _, Fun _) -> ()
  | _ -> Parsing_helper.internal_error "Structures of left- and right-hand sides of an equivalence must be the same"

let build_restr_mapping restr_mapping lmg rmg =
  List.iter2 (fun (lm,_) (rm,_) -> 
    build_restr_mapping_fungroup restr_mapping lm rm) lmg rmg

(* Apply the lemma that infers !N G1 ~ !N G2 from G1 ~ G2 *)

let add_index_binder idx b =
  match b.link with
  | TLink { t_desc = Var(b',_) } -> b'
  | NoLink ->
      (* Reusing exactly the same name as in the original equivalence
	 Useful for detect correctly [unchanged] variables. *)
      let b1 = Terms.create_binder_internal b.sname b.vname b.btype (b.args_at_creation @ idx) in
      Terms.link b (TLink (Terms.term_from_binder b1));
      b1
  | _ -> Parsing_helper.internal_error "Variable should be mapped to a variable in add_index"
    
let rec add_index idx t =
  match t.t_desc with
  | Var(b,l) ->
      Terms.build_term t (Var(add_index_binder idx b,
			       (List.map (add_index idx) l) @
			       (List.map Terms.term_from_repl_index idx)))
  | ReplIndex b -> Terms.build_term t t.t_desc (* Must not be physically the same, for computation of facts *)
  | FunApp(f,l) -> Terms.build_term t (FunApp(f, List.map (add_index idx) l))
  | ResE(b,t1) ->
      Terms.build_term t (ResE(add_index_binder idx b, add_index idx t1))
  | EventAbortE _ -> Terms.build_term t t.t_desc (* Must not be physically the same, for computation of facts *)
  | EventE _ | GetE _ | InsertE _ ->
      Parsing_helper.internal_error "event/get/insert should not occur equivalences" 
  | TestE(t1,t2,t3) ->
      Terms.build_term t (TestE(add_index idx t1,
				 add_index idx t2,
				 add_index idx t3))
  | FindE(l0,t3,find_info) ->
      let l0' = 
	List.map (fun (bl, def_list, t1, t2) ->
	  let def_list' = List.map (add_index_br idx) def_list in
	  let t1' = add_index idx t1 in
	  let bl' = List.map (fun (b,b') ->
	    (add_index_binder idx b, b')) bl 
	  in
	  let t2' = add_index idx t2 in
	  (bl', def_list', t1', t2')
	  ) l0
      in
      Terms.build_term t (FindE(l0',
				 add_index idx t3,
				 find_info))
  | LetE(pat, t1, t2, topt) ->
      let t1' = add_index idx t1 in
      let pat' = add_index_pat idx pat in
      let t2' = add_index idx t2 in
      let topt' = 
	match topt with
	  None -> None
	| Some t3 -> Some (add_index idx t3)
      in
      Terms.build_term t (LetE(pat', t1', t2', topt'))

and add_index_br idx (b,l) =
  (add_index_binder idx b,
   List.map (add_index idx) l @ (List.map Terms.term_from_repl_index idx))

and add_index_pat idx = function
    PatVar b ->
      PatVar (add_index_binder idx b)
  | PatTuple(f,l) ->
      PatTuple(f, List.map (add_index_pat idx) l)
  | PatEqual t ->
      PatEqual (add_index idx t)
      
let add_index_restr_list idx =
  List.map (fun (b, opt) -> (add_index_binder idx b, opt))

let rec add_index_fungroup idx = function
  | ReplRestr(repl_opt, restr_list, fun_list) ->
      ReplRestr(repl_opt, add_index_restr_list idx restr_list,
		List.map (add_index_fungroup idx) fun_list)
  | Fun(c, inputs, t, opt) ->
      Fun(c, List.map (add_index_binder idx) inputs, add_index idx t, opt)

let rec add_index_proba idx = function
  | (AttTime | Time _ | Cst _ | Count _ | Zero | Card _ | TypeMaxlength _
  | EpsFind | EpsRand _ | PColl1Rand _ | PColl2Rand _) as x -> x
  | (OCount n) as p ->
      print_string ("Warning: reference of oracle count #" ^ n.cname ^ " becomes less precise when adding a replication at the root of the equivalence.\n");
      p
  | Proba(p,l) -> Proba(p, List.map (add_index_proba idx) l)
  | ActTime(f,l) -> ActTime(f, List.map (add_index_proba idx) l)
  | Maxlength(g,t) ->
      assert (g == Terms.lhs_game);
      Maxlength(g, add_index idx t)
  | Length(f,l) -> Length(f, List.map (add_index_proba idx) l)
  | Mul(x,y) -> Mul(add_index_proba idx x, add_index_proba idx y)
  | Add(x,y) -> Add(add_index_proba idx x, add_index_proba idx y)
  | Sub(x,y) -> Sub(add_index_proba idx x, add_index_proba idx y)
  | Div(x,y) -> Div(add_index_proba idx x, add_index_proba idx y)
  | Max(l) -> Max(List.map (add_index_proba idx) l)
  | Min(l) -> Min(List.map (add_index_proba idx) l)

let add_index_setf_proba idx =
  List.map (function
    | SetProba p1 -> SetProba(add_index_proba idx p1)
    | SetEvent _ | SetAssume -> Parsing_helper.internal_error "Event/assume should not occur in probability formula")
		
let add_index_top t (restr_list,fun_list,proba) =
  let idx = Terms.create_repl_index "i" t in
  let idxl = [idx] in
  let (restr_list', fun_list', proba') =
    Terms.auto_cleanup (fun () ->
      (add_index_restr_list idxl restr_list,
       List.map (add_index_fungroup idxl) fun_list,
       add_index_setf_proba idxl proba))
  in
  (Some idx, restr_list',fun_list', proba')

let instan_time add_time p =
  let rec instan_time = function
    AttTime -> Add(AttTime, add_time)
  | Time _ -> Parsing_helper.internal_error "unexpected time"
  | (Cst _ | Count _ | OCount _ | Zero | Card _ | TypeMaxlength _
     | EpsFind | EpsRand _ | PColl1Rand _ | PColl2Rand _ | Maxlength _) as x -> x
  | Proba(p,l) -> Proba(p, List.map instan_time l)
  | ActTime(f,l) -> ActTime(f, List.map instan_time l)
  | Length(f,l) -> Length(f, List.map instan_time l)
  | Mul(x,y) -> Mul(instan_time x, instan_time y)
  | Add(x,y) -> Add(instan_time x, instan_time y)
  | Sub(x,y) -> Sub(instan_time x, instan_time y)
  | Div(x,y) -> Div(instan_time x, instan_time y)
  | Max(l) -> Max(List.map instan_time l)
  | Min(l) -> Min(List.map instan_time l)
  in
  instan_time p

    
let add_repl equiv =
  match equiv.eq_fixed_equiv with
  | None -> equiv
  | Some(lm,rm,p,opt2) ->
      match lm,rm with
      | [ReplRestr(None,lrestr_list,lfun_list),lmode], [ReplRestr(None,rrestr_list,rfun_list),rmode] ->
	  let name, counter = Terms.new_var_name "N" in
	  let param = { pname = name ^ (if counter != 0 then "_" ^ (string_of_int counter) else "");
			psize = Settings.psize_DEFAULT }
	  in
	  let t = Terms.type_for_param param in
	    (* The probability [p] may refer to variables in the LHS of the equivalence
               (in arguments of maxlength). We add indices to these variables as well. *)
	  let (lrepl_opt, lrestr_list',lfun_list',p') = add_index_top t (lrestr_list,lfun_list,p) in
	  let (rrepl_opt, rrestr_list',rfun_list',_) = add_index_top t (rrestr_list,rfun_list, []) in
	  let lm' = [ReplRestr(lrepl_opt, lrestr_list',lfun_list'),lmode] in
	  let rm' = [ReplRestr(rrepl_opt, rrestr_list',rfun_list'),rmode] in
	  let lhs_for_time = ReplRestr(None, lrestr_list',lfun_list') in
	  let rhs_for_time = ReplRestr(None, rrestr_list',rfun_list') in
	  let time_add =
	      Computeruntime.compute_add_time(*_totcount*) lhs_for_time rhs_for_time param opt2
	  in
	  let p'' = List.map (function
	    | SetProba p1 -> SetProba (Polynom.p_mul(Count param, instan_time time_add p1))
	    | SetEvent _ | SetAssume -> Parsing_helper.internal_error "Event/assume should not occur in probability formula"
		  ) p'
	  in
	  let equiv' = { equiv with eq_fixed_equiv = Some(lm',rm',p'',opt2) } in
	    (* print_string "Obtained "; Display.display_equiv_gen equiv'; *)
	  equiv'
      | _ ->
	  let missing_repl = function
	    | ReplRestr(None,restr_list,fun_list),mode -> true
	    | _ -> false
	  in
	  if (List.exists missing_repl lm) || (List.exists missing_repl rm) then
	    Parsing_helper.internal_error "Bad missing replications; should have been detected in syntax.ml";
	  equiv

let check_equiv normalize equiv =
  let equiv =
    match equiv.eq_fixed_equiv with
    | None -> equiv
    | Some(lm,rm,p,opt2) ->
        (* 1. Check that all variables are correctly defined *)
	Def.build_def_member rm;
	check_def_member rm;
	Def.empty_def_member rm;

	(* 2. Convert insert/get into find in the RHS *)
	let rm' = Transf_tables.reduce_tables_eqside rm in

	(* 3. Optimize by removing useless assignments *)
	let rm'' = Transf_remove_assign.remove_assignments_eqside rm' in
	Settings.changed := false;
	{ equiv with
          eq_fixed_equiv = Some(lm, rm'', p, opt2) }	
  in

  (* 4. Add a replication in case there is no replication at the top.
     It is important to convert insert/get into find before adding a replication.
     Otherwise, we would need to add the replication index to the table(s). *)
  let equiv' = add_repl equiv in

  match equiv'.eq_fixed_equiv with
  | None -> equiv'
  | Some(lm,rm,p,opt2) ->
      (* we must call [check_def_member] before using [close_def] *)
      Def.build_def_member lm;
      check_def_member lm;
      Def.build_def_member rm;
      check_def_member rm;
      (* Require that each function has a different number of repetitions.
	 Then the typing guarantees that when several variables are referenced
	 with the same array indexes, then these variables come from the same function. *)
      Array_ref.array_ref_eqside rm;
      (* 5. Check the "find" constructs, and modify them if needed. 
         Avoid array accesses on variables defined by "find" and on
	 indices received as arguments. *) 
      let rm1 = List.map (fun (fg, mode) ->
	(check_rm_fungroup [] fg, mode)) rm
      in
      Def.empty_def_member rm;

      (* 6. Encode comparisons on indices *)
      Def.build_def_member rm1;
      Array_ref.array_ref_eqside rm1;
      renamed_vars := [];
      build_encode_idx_types_funs rm1;
      let rm2 = List.map (fun (fg, mode) ->
	(encode_idx_fungroup [] fg, mode)) rm1
      in

      (* 7. Move creations of fresh random variables in the RHS *)
      let rm3 = move_names_all lm rm2 in
      Array_ref.cleanup_array_ref();
      Def.empty_def_member rm1;
      
      let restr_mapping = ref [] in
      build_restr_mapping restr_mapping lm rm3;
      renamed_vars := [];
      let equiv'' =
	{ equiv' with
          eq_fixed_equiv = Some(lm, rm3, p, opt2);
          eq_name_mapping = Some(!restr_mapping) }
      in
      (* print_string "After encoding "; Display.display_equiv_gen equiv''; *)
      if normalize then
	equiv''
      else
	equiv
