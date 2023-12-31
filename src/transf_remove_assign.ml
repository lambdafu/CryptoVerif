open Types

(* Remove assignments 
Supports If/let/find/new/event in terms.
Be careful of variables defined at several places!  *)

type transf_args =
    { sarename_new : bool;
      remove_set : rem_set;
      queries : cur_queries_t;
      mutable replacement_def_list : (binder * binder) list;
       (* List of correspondences (b,b'), b = old binder, b' = new binder,
	  for defined conditions. When b is used only in "defined" conditions,
	  we try to find another binder b' defined in the same cases, so that
	  we can remove the definition of b completely. *)
      mutable done_transfos : detailed_instruct list;
      mutable done_sa_rename : (binder * binder) list}
    
let rec copiable t =
  match t.t_desc with
  | Var(_,l) | FunApp(_,l) ->
     List.for_all copiable l
  | ReplIndex _ -> true
  | TestE(t1,t2,t3) ->
     (copiable t1) && (copiable t2) && (copiable t3)
  | LetE _ | FindE _ | ResE _ | EventE _ | EventAbortE _ ->
     (* LetE and FindE are not copiable because that may 
      * break the invariant that each variable is
      * assigned at most once.
      * ResE is not copiable because it may lead to creating
      * several independent random values instead of one,
      * and may also break the invariant that each variable is
      * assigned at most once.
      * Events are not copiable because that may change the
      * moment at which the event is executed. 
      *)
     false
  | GetE _ | InsertE _ ->
     Parsing_helper.internal_error "Get/insert should not occur in terms"

(* [candidate_for_rem_assign refers in_find_cond transf_args b t p] returns [true]
 * when the assignment [let b = t in p] may be removed
 * [refers b p] returns whether [p] refers to [b] 
 * (Terms.refers_to_nodef for terms, Terms.refers_to_nodef_process for processes)
 *)

type rem_assign_level =
  | DontRemove
  | VariableUseless
  | Remove of bool (* the boolean is true when we want to apply advice *)
                                   
let candidate_for_rem_assign refers in_find_cond transf_args b t p =
  if (not (copiable t)) ||
       (* Cannot remove cyclic assignment *)
       (Terms.refers_to b t)
  then DontRemove
  else
    if not (refers b p || b.array_ref || Settings.occurs_in_queries b transf_args.queries) then
      VariableUseless
    else
      match transf_args.remove_set with
      | FindCond when in_find_cond -> Remove true
      | Binders l when List.memq b l -> Remove true
      | EqSide ->
	  begin
	    match t.t_desc with
	    | Var(b, l) when Terms.is_args_at_creation b l -> Remove false
	    | ReplIndex _ -> Remove false
            | _ -> DontRemove
	  end
      | _ -> 
         match t.t_desc with
	 | Var _ | ReplIndex _ when !Settings.expand_letxy -> Remove false
         | _ -> DontRemove

let make_assign_term pat t p =
  Terms.build_term_type p.t_type  (LetE(pat, t, p, None))  

let make_let_term rec_simplif pat t p1 topt =
  Terms.build_term_type p1.t_type
    (LetE(pat, t, rec_simplif p1,
          match topt with
          | None -> None
          | Some p2 -> Some (rec_simplif p2)))
                        
let make_test_term test p1 topt =
  Terms.build_term_type p1.t_type (TestE(test, p1, Terms.get_else topt))

let make_assign_proc pat t p =
  Terms.oproc_from_desc (Let(pat, t, p, Terms.oproc_from_desc Yield))  

let make_let_proc rec_simplif pat t p1 p2 =
  Terms.oproc_from_desc (Let(pat, t, rec_simplif p1, rec_simplif p2))

let make_test_proc test p1 p2 =
  Terms.oproc_from_desc (Test(test, p1, p2))  
                  
(* [find_replacement_for_def_term in_find_cond transf_args p b] finds a variable that
   can replace [b] in defined conditions (that is, a variable that is defined exactly when [b] is defined)
   in the process [p]. [b] is defined exactly when [p] is executed. *)
	    
let rec find_replacement_for_def_term in_find_cond transf_args p b =
  match p.t_desc with
  | ResE(b',p') ->
      if b' != b && b'.count_def == 1 then b' else find_replacement_for_def_term in_find_cond transf_args p' b
  | LetE(PatVar b', t, p', _) ->
      if b' != b && b'.count_def == 1 && (candidate_for_rem_assign Terms.refers_to_nodef in_find_cond transf_args b' t p' == DontRemove) then b' else 
      find_replacement_for_def_term in_find_cond transf_args p' b
  | EventE(_,p') -> find_replacement_for_def_term in_find_cond transf_args p' b
  | _ -> raise Not_found

(* [find_replacement_for_def_proc transf_args p b] finds a variable that
   can replace [b] in defined conditions (that is, a variable that is defined exactly when [b] is defined)
   in the process [p]. [b] is defined exactly when [p] is executed. *)
	    
let rec find_replacement_for_def_proc in_find_cond transf_args p b =
  match p.p_desc with
  | Restr(b',p') ->
      if b' != b && b'.count_def == 1 then b' else find_replacement_for_def_proc in_find_cond transf_args p' b
  | Let(PatVar b', t, p', _) ->
      if b' != b && b'.count_def == 1 && (candidate_for_rem_assign Terms.refers_to_process_nodef false transf_args b' t p' == DontRemove) then b' else 
      find_replacement_for_def_proc in_find_cond transf_args p' b
  | EventP(_,p') -> find_replacement_for_def_proc in_find_cond transf_args p' b
  | _ -> raise Not_found

let term_funs = (make_assign_term, make_let_term, make_test_term, Terms.get_else, find_replacement_for_def_term, Terms.copy_term, Terms.refers_to_nodef, Terms.put_lets_term)

let proc_funs = (make_assign_proc, make_let_proc, make_test_proc, (fun x -> x), find_replacement_for_def_proc, Terms.copy_oprocess, Terms.refers_to_process_nodef, Terms.put_lets)
                  
(* [find_replacement_for_def_ab final b above_vars] finds a variable that
   can replace [b] in defined conditions (that is, a variable that is defined exactly when [b] is defined)
   in the variables [above_vars] or by calling [final].
   [b] and [above_vars] are defined exactly at the same time.
   The variables in [above_vars] are not removed. *)

let rec find_replacement_for_def_ab final b = function
    [] -> final b
  | b'::l -> if b' != b && (b'.count_def == 1) then b' else find_replacement_for_def_ab final b l
	
(* Function for assignment expansion, shared between terms and processes *)

let expand_assign_one (make_assign, make_let, make_test, get_else, find_replacement_for_def, copy, refers, put_lets)
      in_find_cond transf_args above_vars rec_simplif_term rec_simplif_pat rec_simplif pat t p1 topt =
  match pat with
  | PatVar b ->
     begin
       match candidate_for_rem_assign refers in_find_cond transf_args b t p1 with
       | DontRemove ->
          make_assign pat (rec_simplif_term t) (rec_simplif (b::above_vars) p1)
       | VariableUseless ->
          begin
	    (* Value of the variable is useless *)
	    if not (b.root_def_std_ref || b.root_def_array_ref) then
	      (* Variable is useless *)
	      begin
		Settings.changed := true;
                transf_args.done_transfos <- (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: transf_args.done_transfos;
		rec_simplif above_vars p1
	      end
	    else
	      begin
	        (* We may keep calls to defined(b), so keep a definition of b
		     but its value does not matter *)
                try
                  (* Try to remove the definition of b completely, by replacing
                       defined(b[...]) with defined(b'[...]) *)
                  if b.count_def > 1 then raise Not_found;
                  let b' = find_replacement_for_def_ab (find_replacement_for_def in_find_cond transf_args p1) b above_vars in
                  Settings.changed := true;
                  transf_args.done_transfos <- (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: transf_args.done_transfos;
                  transf_args.replacement_def_list <- (b, b') :: transf_args.replacement_def_list;
                  rec_simplif above_vars p1
                with Not_found ->
		      let t' = Stringmap.cst_for_type t.t_type in
		      if not (Terms.equal_terms t t') then 
                        begin
                          transf_args.done_transfos <- (DRemoveAssign(b, DKeepDefPoint, DRemoveAll)) :: transf_args.done_transfos;
                          Settings.changed := true
                        end;
		      make_assign pat t' (rec_simplif (b::above_vars) p1)
	      end
	  end
       | Remove do_advise ->
	  match b.def with
	    [] -> Parsing_helper.internal_error "Should have at least one definition"
	  | [_] -> (* There is a single definition *)
	      begin
		(* All references to binder b will be removed *)
		Terms.link b (TLink t);
                (* copy_oprocess exactly replaces 
                   b[b.args_at_creation] with t, without changing any other variable. *)
                let copy_changed = ref false in
                let p1' = copy (Terms.OneSubst(b,t,copy_changed)) p1 in
                let subst_def = !copy_changed in (* Set to true if an occurrence of b has really been substituted *)
                Settings.changed := (!Settings.changed) || subst_def;
		if Settings.occurs_in_queries b transf_args.queries then
		  begin
		    (* if b occurs in queries then leave as it is *)
                    if subst_def then
                      transf_args.done_transfos <- (DRemoveAssign(b, DKeepDef, DRemoveAll)) :: transf_args.done_transfos;
		    make_assign pat t (rec_simplif (b::above_vars) p1')
		  end
		else if b.root_def_array_ref || b.array_ref then
		  (* We may keep calls to defined(b), so keep a definition of b
		     but its value does not matter *)
                  try
                    (* Try to remove the definition of b completely, by replacing
                       defined(b[...]) with defined(b'[...]) *)
                    let b' = find_replacement_for_def_ab (find_replacement_for_def in_find_cond transf_args p1') b above_vars in
                    Settings.changed := true;
                    transf_args.done_transfos <- (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: transf_args.done_transfos;
                    transf_args.replacement_def_list <- (b, b') :: transf_args.replacement_def_list;
                    rec_simplif above_vars p1'
                  with Not_found ->
		    let t' = Stringmap.cst_for_type t.t_type in
		    if not (Terms.equal_terms t t') then 
                      begin
                        transf_args.done_transfos <- (DRemoveAssign(b, DKeepDefPoint, DRemoveAll)) :: transf_args.done_transfos;
                        Settings.changed := true
                      end;
		    make_assign pat t' (rec_simplif (b::above_vars) p1')
		else
		  begin
                    (* b will completely disappear *)
                    Settings.changed := true;
                    transf_args.done_transfos <- (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: transf_args.done_transfos;
		    rec_simplif above_vars p1'
		  end
	      end
	  | _ -> (* There are several definitions.
		    I can remove in-scope requests, but out-of-scope array accesses will remain *)
              begin
                (* copy_oprocess exactly replaces 
                   b[b.args_at_creation] with t, without changing any other variable.
                   (Changing other variables led to a bug, because it replaced
                   v[v.args_at_creation] with its value in a "defined" condition,
                   even when v is defined less often than its value.) *)
                let copy_changed = ref false in
                let p1' = copy (Terms.OneSubst(b,t,copy_changed)) p1 in
                let subst_def = !copy_changed in (* Set to true if an occurrence of b has really been substituted *)
                Settings.changed := (!Settings.changed) || subst_def;
                if b.array_ref then
		  begin
                    let p1'' = rec_simplif (b::above_vars) p1' in
		    if do_advise && List.for_all (fun n ->
		      (* Check that all definitions of b are "let b = t in ..." *)
		      match n.definition with
		      |	DProcess { p_desc = Let(PatVar b', t', _, _) } 
		      | DTerm { t_desc = LetE(PatVar b', t', _, _) } ->
			  b == b' && Terms.equal_terms t t'
		      | _ -> false
		      ) b.def
		    then
		      begin
		        (* All definitions of b use the same term t.
			   All references to the value of binder b will be removed *)
			Terms.link b (TLink t);
		        (* We may keep calls to defined(b), so keep a definition of b
			   but its value does not matter *)
			let t' = Stringmap.cst_for_type t.t_type in
			if not (Terms.equal_terms t t') then 
			  begin
			    transf_args.done_transfos <- (DRemoveAssign(b, DKeepDefPoint, DRemoveAll)) :: transf_args.done_transfos;
			    Settings.changed := true
			  end
			else if subst_def then
			  transf_args.done_transfos <- (DRemoveAssign(b, DKeepDefPoint, DRemoveAll)) :: transf_args.done_transfos;
			make_assign pat t' p1''
		      end
		    else
		      begin
                        (* suggest to use "sa_rename b" before removing assignments *)
			if do_advise then Settings.advise := Terms.add_eq (SArenaming b) (!Settings.advise);
                        (* Keep the definition so that out-of-scope array accesses are correct *)
			if subst_def then
			  transf_args.done_transfos <- (DRemoveAssign(b, DKeepDef, DRemoveNonArray)) :: transf_args.done_transfos;
			make_assign pat t p1''
		      end
		  end
		else if Settings.occurs_in_queries b transf_args.queries then
                  begin
                    let p1'' = rec_simplif (b::above_vars) p1' in
		    (* Cannot change definition if b occurs in queries *)
                    if subst_def then
                      transf_args.done_transfos <- (DRemoveAssign(b, DKeepDef, DRemoveAll)) :: transf_args.done_transfos;
 		    make_assign pat t p1''
                  end
                else if b.root_def_array_ref then
		  (* We may keep calls to defined(b), so keep a definition of b
		     but its value does not matter *)
		  let t' = Stringmap.cst_for_type t.t_type in
		  if not (Terms.equal_terms t t') then 
                    begin
                      transf_args.done_transfos <- (DRemoveAssign(b, DKeepDefPoint, DRemoveAll)) :: transf_args.done_transfos;
                      Settings.changed := true
                    end
                  else if subst_def then
                    transf_args.done_transfos <- (DRemoveAssign(b, DKeepDefPoint, DRemoveAll)) :: transf_args.done_transfos;
                  let p1'' = rec_simplif (b::above_vars) p1' in
		  make_assign pat t' p1''
		else
                  (* b will completely disappear *)
		  begin
                    transf_args.done_transfos <- (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: transf_args.done_transfos;
		    Settings.changed := true;
                    let p1'' = rec_simplif above_vars p1' in
		    p1''
		  end
              end
     end
  | _ -> 
     make_let (rec_simplif []) (rec_simplif_pat pat) (rec_simplif_term t) p1 topt

let expand_assign ((make_assign, make_let, make_test, get_else, find_replacement_for_def, copy, refers, put_lets) as funs)
      let_t in_find_cond transf_args above_vars rec_simplif_term rec_simplif_pat rec_simplif pat t p1 topt =
  try
    let (transfos, test, bind) = Terms.simplify_let_tuple (fun t -> t) pat t in
    if transfos != [] then
      begin
	Settings.changed := true;
	transf_args.done_transfos <- (DLetSimplifyPattern(let_t, transfos)) :: transf_args.done_transfos;
        (* Put the lets *)
	let plet = put_lets bind p1 topt in
        (* Put the test *)
	let pfinal =
          if Terms.is_true test then
            plet
	  else
	    make_test test plet topt
        in
	(* Resimplify the transformed process.
           Note that the simplified process may contain several copies of [p2].
	   [p2] is then simplified several times. [above_vars = []] for
	   all simplifications of [p2], since the else branch of let
	   and then is always simplified with [above_vars = []].
           The program still thinks that variables in [p2] are defined
           as if [p2] existed only once, so sometimes it may think
	   that they are defined once, when in fact they have several
	   definitions after remove_assign. The only effect of this is
	   that [replacement_def_list] may contain several entries for
	   variables defined in [p2]. *) 
        rec_simplif above_vars pfinal
      end
    else
      expand_assign_one funs in_find_cond transf_args above_vars rec_simplif_term rec_simplif_pat rec_simplif pat t p1 topt 
  with Terms.Impossible -> 
    Settings.changed := true;
    transf_args.done_transfos <- (DLetSimplifyPattern(let_t, [pat, DImpossibleTuple])) :: transf_args.done_transfos;
    rec_simplif above_vars (get_else topt)


let several_def b =
  match b.def with
    [] | [_] -> false
  | _::_::_ -> true

let rec remove_assignments_term in_find_cond transf_args above_vars t =
  match t.t_desc with
    Var(b,l) ->
      Terms.build_term t (Var(b, List.map (remove_assignments_term in_find_cond transf_args above_vars) l))
  | ReplIndex i -> Terms.build_term t (ReplIndex i)
  | FunApp(f,l) ->
      Terms.build_term t (FunApp(f, List.map (remove_assignments_term in_find_cond transf_args above_vars) l))
  | TestE(t1,t2,t3) ->
      Terms.build_term t (TestE(remove_assignments_term in_find_cond transf_args above_vars t1,
		                 remove_assignments_term in_find_cond transf_args [] t2,
		                 remove_assignments_term in_find_cond transf_args [] t3))
  | FindE(l0, t3, find_info) ->
      Terms.build_term t (FindE(List.map (fun (bl, def_list, t1, t2) ->
	                             (bl, def_list,
			              remove_assignments_term true transf_args [] t1,
			              remove_assignments_term in_find_cond transf_args [] t2)) l0,
		                 remove_assignments_term in_find_cond transf_args [] t3, find_info))
  | LetE(pat,t1,t2,topt) ->
      if transf_args.remove_set == NoRemAssign then
	make_let_term (remove_assignments_term in_find_cond transf_args [])
	  (remove_assignments_pat in_find_cond transf_args above_vars pat)
	  (remove_assignments_term in_find_cond transf_args above_vars t1)
	  t2 topt
      else
	expand_assign term_funs (DTerm t) in_find_cond transf_args above_vars
	  (remove_assignments_term in_find_cond transf_args above_vars)
	  (remove_assignments_pat in_find_cond transf_args above_vars)
	  (remove_assignments_term in_find_cond transf_args)
	  pat t1 t2 topt
  | ResE(b,t) ->
      if transf_args.sarename_new && (several_def b) && (not (Array_ref.has_array_ref_q b transf_args.queries)) then
	begin
	  let b' = Terms.new_binder b in
	  let t' = Terms.copy_term (Terms.Rename(List.map Terms.term_from_repl_index b.args_at_creation, b, b')) t in
	  Settings.changed := true;
	  transf_args.done_sa_rename <- (b,b') :: transf_args.done_sa_rename;
          (* Allow using b' for testing whether a variable is defined *) 
          b'.count_def <- 1;
          let above_vars' = b' :: above_vars in
	  Terms.build_term t' (ResE(b', remove_assignments_term in_find_cond transf_args above_vars' t'))
	end
      else
	Terms.build_term t (ResE(b, remove_assignments_term in_find_cond transf_args (b::above_vars) t))
  | EventAbortE f ->
     t
  | EventE(t1,p) ->
     Terms.build_term t (EventE(remove_assignments_term in_find_cond transf_args above_vars t1,
		                 remove_assignments_term in_find_cond transf_args above_vars p))
  | GetE _ | InsertE _ ->      
      Parsing_helper.internal_error "Get/Insert should not appear in Transf_remove_assign.remove_assignments_term"

and remove_assignments_pat in_find_cond transf_args above_vars = function
    (PatVar _) as pat -> pat
  | PatEqual t -> PatEqual (remove_assignments_term in_find_cond transf_args above_vars t)
  | PatTuple(f,l) -> PatTuple(f, List.map (remove_assignments_pat in_find_cond transf_args above_vars) l)
    
let rec remove_assignments_rec transf_args p = 
  Terms.iproc_from_desc (
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) -> 
      Par(remove_assignments_rec transf_args p1,
	  remove_assignments_rec transf_args p2)
  | Repl(b,p) ->
      Repl(b,remove_assignments_rec transf_args p)
  | Input((c,tl),pat,p) ->
     Input((c, List.map (remove_assignments_term false transf_args []) tl),
           remove_assignments_pat false transf_args [] pat, 
	   remove_assignments_reco transf_args [] p))

and remove_assignments_reco transf_args above_vars p =
  match p.p_desc with
    Yield -> Terms.oproc_from_desc Yield
  | EventAbort f -> Terms.oproc_from_desc (EventAbort f)
  | Restr(b,p) ->
      if transf_args.sarename_new && (several_def b) && (not (Array_ref.has_array_ref_q b transf_args.queries)) then
	begin
	  let b' = Terms.new_binder b in
	  let p' = Terms.copy_oprocess (Terms.Rename(List.map Terms.term_from_repl_index b.args_at_creation, b, b')) p in
	  Settings.changed := true;
	  transf_args.done_sa_rename <- (b,b') :: transf_args.done_sa_rename;
          (* Allow using b' for testing whether a variable is defined *) 
          b'.count_def <- 1;
          let above_vars' = b' :: above_vars in
	  Terms.oproc_from_desc (Restr(b',remove_assignments_reco transf_args above_vars' p'))
	end
      else
	Terms.oproc_from_desc (Restr(b,remove_assignments_reco transf_args (b::above_vars) p))
  | Test(t,p1,p2) ->
      Terms.oproc_from_desc (Test(remove_assignments_term false transf_args above_vars t, 
	   remove_assignments_reco transf_args [] p1,
	   remove_assignments_reco transf_args [] p2))
  | Find(l0,p2,find_info) ->
      Terms.oproc_from_desc 
	(Find(List.map (fun (bl,def_list,t,p1) ->
	     (bl, def_list, 
	      remove_assignments_term true transf_args [] t,
	      remove_assignments_reco transf_args [] p1)) l0,
	   remove_assignments_reco transf_args [] p2, find_info))
  | Output((c,tl),t2,p) ->
      Terms.oproc_from_desc 
	(Output((c, List.map (remove_assignments_term false transf_args above_vars) tl), 
		remove_assignments_term false transf_args above_vars t2,
		remove_assignments_rec transf_args p))
  | Let(pat, t, p1, p2) ->
     let rec_simplif_term = remove_assignments_term false transf_args above_vars in
     let rec_simplif_pat = remove_assignments_pat false transf_args above_vars in
     let rec_simplif = remove_assignments_reco transf_args in
     if transf_args.remove_set == NoRemAssign then
       make_let_proc (rec_simplif []) (rec_simplif_pat pat) (rec_simplif_term t) p1 p2
     else
       expand_assign proc_funs (DProcess p) false transf_args above_vars rec_simplif_term rec_simplif_pat rec_simplif pat t p1 p2
  | EventP(t,p) ->
      Terms.oproc_from_desc 
	(EventP(remove_assignments_term false transf_args above_vars t,
		remove_assignments_reco transf_args above_vars p))
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

let rec do_sa_rename = function
    [] -> []
  | ((b,b')::l) ->
      let lb = List.map snd (List.filter (fun (b1,b1') -> b1 == b) l) in
      let lr = do_sa_rename (List.filter (fun (b1,b1') -> b1 != b) l) in
      (* In case b has been entirely removed from the game in
         an iteration of remove_assignments_repeat that is not
	 the last one, b has no definition at this point, 
	 so it is considered as a restriction by Terms.is_restr.
	 This is fine: in this case, we say that b has been removed indeed. *)
      if Terms.is_restr b then
	(DSArenaming(b, b'::lb))::lr
      else
	(DSArenaming(b, b::b'::lb))::lr

(* - Main function for assignment removal *)

let remove_assignments sarename_new remove_set g =
  let p = Terms.get_process g in
  Def.build_def_process (Some g) None p;
  if !Terms.current_bound_vars != [] then
    Parsing_helper.internal_error "bound vars should be cleaned up (transf1)";
  Array_ref.array_ref_process p;
  let transf_args =
    { sarename_new = sarename_new;
      remove_set = remove_set;
      queries = g.current_queries;
      done_sa_rename = [];
      done_transfos = [];
      replacement_def_list = [] }
  in
  (* - First pass: put links; split assignments of tuples if possible *)
  let p' = remove_assignments_rec transf_args p in
  (* - Second pass: copy the process following the links or replacing just one variable.
       Be careful for array references: update the indexes properly  *)
  let p'' = Terms.copy_process (Terms.Links_Vars_Args(transf_args.replacement_def_list)) p' in
  Terms.cleanup();
  Array_ref.cleanup_array_ref();
  Def.empty_def_process p;
  let g' = Terms.build_transformed_game p'' g in
  let (g'', proba, renames) =
    if transf_args.remove_set == NoRemAssign then
      (g', [], [])
    else
      Transf_auto_sa_rename.auto_sa_rename g'
  in      
  (g'', proba, renames @ (do_sa_rename transf_args.done_sa_rename) @ transf_args.done_transfos)

let rec remove_assignments_repeat n sarename_new remove_set g =
  let tmp_changed = !Settings.changed in
  Settings.changed := false;
  let (g', proba, transfos) = remove_assignments sarename_new remove_set g in
  if n != 1 && !Settings.changed then
    let (g'', proba', transfos') = remove_assignments_repeat (n-1) sarename_new remove_set g' in
    (g'', proba' @ proba, transfos' @ transfos)
  else
    begin
      Settings.changed := tmp_changed;
      (g', proba, transfos)
    end

let remove_assignments sarename_new remove_set g =
  if (remove_set == Minimal) || (remove_set == FindCond) then
    remove_assignments_repeat (!Settings.max_iter_removeuselessassign) sarename_new remove_set g
  else
    remove_assignments sarename_new remove_set g

(* - Main function for assignment removal for sides of equiv *)

let rec remove_assignments_fungroup transf_args = function
  | ReplRestr(repl_opt, restr, funlist) ->
      ReplRestr(repl_opt, restr, List.map (remove_assignments_fungroup transf_args) funlist)
  | Fun(ch, args, res, priority) ->
      Fun(ch, args, remove_assignments_term false transf_args [] res, priority)
      
let remove_assignments_rec_eqside transf_args rm =
  List.map (fun (fg, mode) ->
    (remove_assignments_fungroup transf_args fg, mode)
      ) rm
      
let remove_assignments_eqside rm =
  let transf_args =
    { sarename_new = false;
      remove_set = EqSide;
      queries = [];
      done_sa_rename = [];
      done_transfos = [];
      replacement_def_list = [] }
  in
  Def.build_def_member rm;
  if !Terms.current_bound_vars != [] then
    Parsing_helper.internal_error "bound vars should be cleaned up (transf1)";
  Array_ref.array_ref_eqside rm;
  (* - First pass: put links; split assignments of tuples if possible *)
  let rm' = remove_assignments_rec_eqside transf_args rm in
  (* - Second pass: copy the process following the links or replacing just one variable.
       Be careful for array references: update the indexes properly  *)
  let rm'' = Terms.copy_eqside (Terms.Links_Vars_Args(transf_args.replacement_def_list)) rm' in
  Terms.cleanup();
  Array_ref.cleanup_array_ref();
  Def.empty_def_member rm;
  Transf_auto_sa_rename.auto_sa_rename_eqside rm''

let rec remove_assignments_repeat_eqside n rm =
  let tmp_changed = !Settings.changed in
  Settings.changed := false;
  let rm' = remove_assignments_eqside rm in
  if n != 1 && !Settings.changed then
    remove_assignments_repeat_eqside (n-1) rm'
  else
    begin
      Settings.changed := tmp_changed;
      rm'
    end

let remove_assignments_eqside rm =
  remove_assignments_repeat_eqside (!Settings.max_iter_removeuselessassign) rm


