open Types

(* Remove assignments 

This transformation assumes that LetE/FindE/TestE/ResE occur only in 
conditions of find, which is guaranteed after expansion.
(In fact, it supports them as well in channel names, conditions of tests, events,
outputs, although that's not necessary.)
It also assumes (and checks) that variables defined in conditions of find
have no array references and do not occur in queries.

Note that it is important that there are no LetE or FindE in let
expressions or in patterns! Otherwise, we should verify for each
expression that we copy that it does not contain LetE or FindE: if we
copy a LetE or FindE, we may break the invariant that each variable is
assigned at most once.

Be careful of variables defined at several places!  *)

let expanded = ref true
       
let replacement_def_list = ref []
(* List of correspondences (b,b'), b = old binder, b' = new binder,
   for defined conditions. When b is used only in "defined" conditions,
   we try to find another binder b' defined in the same cases, so that
   we can remove the definition of b completely. *)

let done_transfos = ref []

let done_sa_rename = ref []

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

(* [candidate_for_rem_assign refers in_find_cond remove_set b t p] returns [true]
 * when the assignment [let b = t in p] may be removed
 * [refers b p] returns whether [p] refers to [b] 
 * (Terms.refers_to_nodef for terms, Terms.refers_to_nodef_process for processes)
 *)

type rem_assign_level =
  | DontRemove
  | VariableUseless
  | Remove of bool (* the boolean is true when we want to apply advice *)
                                   
let candidate_for_rem_assign refers in_find_cond remove_set b t p =
  if (not (copiable t)) ||
       (* Cannot remove cyclic assignment *)
       (Terms.refers_to b t)
  then DontRemove
  else
    if not (refers b p || b.array_ref || Settings.occurs_in_queries b) then
      VariableUseless
    else
      match remove_set with
      | All ->  Remove true
      | FindCond when in_find_cond -> Remove true
      | OneBinder b0 when b == b0 -> Remove true
      | _ -> 
         match t.t_desc with
	 | Var _ | ReplIndex _ when !Settings.expand_letxy -> Remove false
         | _ -> DontRemove

                  (*
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

let term_funs = (make_assign_term, make_let_term, make_test_term, Terms.get_else, find_replacement_for_def_term, ...)
               
let make_assign_proc pat t p =
  Terms.oproc_from_desc (Let(pat, t, p, Terms.oproc_from_desc Yield))  

let make_let_proc rec_simplif pat t p1 p2 =
  Terms.oproc_from_desc (Let(pat, t, rec_simplif [] p1, rec_simplif [] p2))

let make_test_proc test p1 p2 =
  Terms.oproc_from_desc (Test(test, p1, p2))  
                   *)
                  
(* [find_replacement_for_def_term in_find_cond remove_set b p] finds a variable that
   can replace [b] in defined conditions (that is, a variable that is defined exactly when [b] is defined)
   in the process [p]. [b] is defined exactly when [p] is executed. *)
	    
let rec find_replacement_for_def_term in_find_cond remove_set b p =
  match p.t_desc with
  | ResE(b',p') ->
      if b' != b && b'.count_def == 1 then b' else find_replacement_for_def_term in_find_cond remove_set b p'
  | LetE(PatVar b', t, p', _) ->
      if b' != b && b'.count_def == 1 && (candidate_for_rem_assign Terms.refers_to_nodef in_find_cond remove_set b' t p' == DontRemove) then b' else 
      find_replacement_for_def_term in_find_cond remove_set b p'
  | EventE(_,p') -> find_replacement_for_def_term in_find_cond remove_set b p'
  | _ -> raise Not_found

(* [find_replacement_for_def_t remove_set p b above_vars] finds a variable that
   can replace [b] in defined conditions (that is, a variable that is defined exactly when [b] is defined)
   in the variables [above_vars] or in the process [p]. 
   [b] and [above_vars] are defined exactly when [p] is executed.
   The variables in [above_vars] are not removed. *)

let rec find_replacement_for_def_t in_find_cond remove_set b p = function
    [] -> find_replacement_for_def_term in_find_cond remove_set b p
  | b'::l -> if b' != b && (b'.count_def == 1)then b' else find_replacement_for_def_t in_find_cond remove_set b p l
	
(* Function for assignment expansion for terms *)

let expand_assign_one_term in_find_cond remove_set above_vars rec_simplif_term rec_simplif_pat rec_simplif pat t p1 topt =
  match pat with
  | PatVar b ->
     begin
       match candidate_for_rem_assign Terms.refers_to_nodef in_find_cond remove_set b t p1 with
       | DontRemove ->
          Terms.build_term_type p1.t_type  (LetE(pat, rec_simplif_term t, rec_simplif (b::above_vars) p1, None))
       | VariableUseless ->
          begin
	    (* Value of the variable is useless *)
	    if not (b.root_def_std_ref || b.root_def_array_ref) then
	      (* Variable is useless *)
	      begin
		Settings.changed := true;
                done_transfos := (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: (!done_transfos);
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
                  let b' = find_replacement_for_def_t in_find_cond remove_set b p1 above_vars in
                  Settings.changed := true;
                  done_transfos := (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: (!done_transfos);
                  replacement_def_list := (b, b') :: (!replacement_def_list);
                  rec_simplif above_vars p1
                with Not_found ->
		      let t' = Terms.cst_for_type t.t_type in
		      if not (Terms.equal_terms t t') then 
                        begin
                          done_transfos := (DRemoveAssign(b, DKeepDefPoint, DRemoveAll)) :: (!done_transfos);
                          Settings.changed := true
                        end;
		      Terms.build_term_type p1.t_type  (LetE(pat, t', rec_simplif (b::above_vars) p1, None))
	      end
	  end
       | Remove do_advise ->
	  match b.def with
	    [] -> Parsing_helper.internal_error "Should have at least one definition"
	  | [d] -> (* There is a single definition *)
	      begin
		(* All references to binder b will be removed *)
		Terms.link b (TLink t);
                (* copy_oprocess exactly replaces 
                   b[b.args_at_creation] with t, without changing any other variable. *)
                let copy_changed = ref false in
                let p1' = Terms.copy_term (Terms.OneSubst(b,t,copy_changed)) p1 in
                let subst_def = !copy_changed in (* Set to true if an occurrence of b has really been substituted *)
                Settings.changed := (!Settings.changed) || subst_def;
		if Settings.occurs_in_queries b then
		  begin
		    (* if b occurs in queries then leave as it is *)
                    if subst_def then
                      done_transfos := (DRemoveAssign(b, DKeepDef, DRemoveAll)) :: (!done_transfos);
		    Terms.build_term_type p1.t_type  (LetE(pat, t, rec_simplif (b::above_vars) p1', None))
		  end
		else if b.root_def_array_ref || b.array_ref then
		  (* We may keep calls to defined(b), so keep a definition of b
		     but its value does not matter *)
                  try
                    (* Try to remove the definition of b completely, by replacing
                       defined(b[...]) with defined(b'[...]) *)
                    let b' = find_replacement_for_def_t in_find_cond remove_set b p1' above_vars in
                    Settings.changed := true;
                    done_transfos := (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: (!done_transfos);
                    replacement_def_list := (b, b') :: (!replacement_def_list);
                    rec_simplif above_vars p1'
                  with Not_found ->
		    let t' = Terms.cst_for_type t.t_type in
		    if not (Terms.equal_terms t t') then 
                      begin
                        done_transfos := (DRemoveAssign(b, DKeepDefPoint, DRemoveAll)) :: (!done_transfos);
                        Settings.changed := true
                      end;
		    Terms.build_term_type p1.t_type  (LetE(pat,  t', rec_simplif (b::above_vars) p1', None))
		else
		  begin
                    (* b will completely disappear *)
                    Settings.changed := true;
                    done_transfos := (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: (!done_transfos);
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
                let p1' = Terms.copy_term (Terms.OneSubst(b,t,copy_changed)) p1 in
                let subst_def = !copy_changed in (* Set to true if an occurrence of b has really been substituted *)
                Settings.changed := (!Settings.changed) || subst_def;
                if b.array_ref then
		  begin
                    let p1'' = rec_simplif (b::above_vars) p1' in
                    (* suggest to use "sa_rename b" before removing assignments *)
		    if do_advise then Settings.advise := Terms.add_eq (SArenaming b) (!Settings.advise);
                    (* Keep the definition so that out-of-scope array accesses are correct *)
                    if subst_def then
                      done_transfos := (DRemoveAssign(b, DKeepDef, DRemoveNonArray)) :: (!done_transfos);
                    Terms.build_term_type p1.t_type  (LetE(pat, t, p1'', None))
		  end
		else if Settings.occurs_in_queries b then
                  begin
                    let p1'' = rec_simplif (b::above_vars) p1' in
		    (* Cannot change definition if b occurs in queries *)
                    if subst_def then
                      done_transfos := (DRemoveAssign(b, DKeepDef, DRemoveAll)) :: (!done_transfos);
 		    Terms.build_term_type p1.t_type  (LetE(pat, t, p1'', None))
                  end
                else if b.root_def_array_ref then
		  (* We may keep calls to defined(b), so keep a definition of b
		     but its value does not matter *)
		  let t' = Terms.cst_for_type t.t_type in
		  if not (Terms.equal_terms t t') then 
                    begin
                      done_transfos := (DRemoveAssign(b, DKeepDefPoint, DRemoveAll)) :: (!done_transfos);
                      Settings.changed := true
                    end
                  else if subst_def then
                    done_transfos := (DRemoveAssign(b, DKeepDefPoint, DRemoveAll)) :: (!done_transfos);
                  let p1'' = rec_simplif (b::above_vars) p1' in
		  Terms.build_term_type p1.t_type  (LetE(pat, t', p1'', None))
		else
                  (* b will completely disappear *)
		  begin
                    done_transfos := (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: (!done_transfos);
		    Settings.changed := true;
                    let p1'' = rec_simplif above_vars p1' in
		    p1''
		  end
              end
     end
  | _ -> 
     Terms.build_term_type p1.t_type  (LetE(rec_simplif_pat pat, rec_simplif_term t, rec_simplif [] p1,
                                 match topt with
                                 | None -> None
                                 | Some p2 -> Some (rec_simplif [] p2)))

let expand_assign_term let_t in_find_cond remove_set above_vars rec_simplif_term rec_simplif_pat rec_simplif pat t p1 topt =
  try
    let (transfos, test, bind) = Terms.simplify_let_tuple (fun t -> t) pat t in
    if transfos != [] then
      begin
	Settings.changed := true;
	done_transfos := (DLetSimplifyPattern(let_t, transfos)) :: (!done_transfos);
        (* Put the lets *)
	let plet = Terms.put_lets_term bind p1 topt in
        (* Put the test *)
	let pfinal =
          if Terms.is_true test then
            plet
	  else
	    Terms.build_term_type p1.t_type (TestE(test, plet, Terms.get_else topt))
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
      expand_assign_one_term in_find_cond remove_set above_vars rec_simplif_term rec_simplif_pat rec_simplif pat t p1 topt 
  with Terms.Impossible -> 
    Settings.changed := true;
    done_transfos := (DLetSimplifyPattern(let_t, [pat, DImpossibleTuple])) :: (!done_transfos);
    rec_simplif above_vars (Terms.get_else topt)


(* Function for assignment expansion for processes *)

(* [find_replacement_for_def_proc remove_set b p] finds a variable that
   can replace [b] in defined conditions (that is, a variable that is defined exactly when [b] is defined)
   in the process [p]. [b] is defined exactly when [p] is executed. *)
	    
let rec find_replacement_for_def_proc remove_set b p =
  match p.p_desc with
  | Restr(b',p') ->
      if b' != b && b'.count_def == 1 then b' else find_replacement_for_def_proc remove_set b p'
  | Let(PatVar b', t, p', _) ->
      if b' != b && b'.count_def == 1 && (candidate_for_rem_assign Terms.refers_to_process_nodef false remove_set b' t p' == DontRemove) then b' else 
      find_replacement_for_def_proc remove_set b p'
  | EventP(_,p') -> find_replacement_for_def_proc remove_set b p'
  | _ -> raise Not_found

(* [find_replacement_for_def_p remove_set p b above_vars] finds a variable that
   can replace [b] in defined conditions (that is, a variable that is defined exactly when [b] is defined)
   in the variables [above_vars] or in the process [p]. 
   [b] and [above_vars] are defined exactly when [p] is executed.
   The variables in [above_vars] are not removed. *)

let rec find_replacement_for_def_p remove_set b p = function
    [] -> find_replacement_for_def_proc remove_set b p
  | b'::l -> if b' != b && (b'.count_def == 1) then b' else find_replacement_for_def_p remove_set b p l
	


let expand_assign_one remove_set above_vars rec_simplif_term rec_simplif_pat rec_simplif pat t p1 p2 =
  match pat with
  | PatVar b ->
     begin
       match candidate_for_rem_assign Terms.refers_to_process_nodef false remove_set b t p1 with
       | DontRemove ->
          Terms.oproc_from_desc (Let(pat, rec_simplif_term t, rec_simplif (b::above_vars) p1, Terms.oproc_from_desc Yield))
       | VariableUseless ->
          begin
	    (* Value of the variable is useless *)
	    if not (b.root_def_std_ref || b.root_def_array_ref) then
	      (* Variable is useless *)
	      begin
		Settings.changed := true;
                done_transfos := (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: (!done_transfos);
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
                  let b' = find_replacement_for_def_p remove_set b p1 above_vars in
                  Settings.changed := true;
                  done_transfos := (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: (!done_transfos);
                  replacement_def_list := (b, b') :: (!replacement_def_list);
                  rec_simplif above_vars p1
                with Not_found ->
		      let t' = Terms.cst_for_type t.t_type in
		      if not (Terms.equal_terms t t') then 
                        begin
                          done_transfos := (DRemoveAssign(b, DKeepDefPoint, DRemoveAll)) :: (!done_transfos);
                          Settings.changed := true
                        end;
		      Terms.oproc_from_desc (Let(pat, t', rec_simplif (b::above_vars) p1, Terms.oproc_from_desc Yield))
	      end
	  end
       | Remove do_advise ->
	  match b.def with
	    [] -> Parsing_helper.internal_error "Should have at least one definition"
	  | [d] -> (* There is a single definition *)
	      begin
		(* All references to binder b will be removed *)
		Terms.link b (TLink t);
                (* copy_oprocess exactly replaces 
                   b[b.args_at_creation] with t, without changing any other variable. *)
                let copy_changed = ref false in
                let p1' = Terms.copy_oprocess (Terms.OneSubst(b,t,copy_changed)) p1 in
                let subst_def = !copy_changed in (* Set to true if an occurrence of b has really been substituted *)
                Settings.changed := (!Settings.changed) || subst_def;
		if Settings.occurs_in_queries b then
		  begin
		    (* if b occurs in queries then leave as it is *)
                    if subst_def then
                      done_transfos := (DRemoveAssign(b, DKeepDef, DRemoveAll)) :: (!done_transfos);
		    Terms.oproc_from_desc (Let(pat, t, rec_simplif (b::above_vars) p1', Terms.oproc_from_desc Yield))
		  end
		else if b.root_def_array_ref || b.array_ref then
		  (* We may keep calls to defined(b), so keep a definition of b
		     but its value does not matter *)
                  try
                    (* Try to remove the definition of b completely, by replacing
                       defined(b[...]) with defined(b'[...]) *)
                    let b' = find_replacement_for_def_p remove_set b p1' above_vars in
                    Settings.changed := true;
                    done_transfos := (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: (!done_transfos);
                    replacement_def_list := (b, b') :: (!replacement_def_list);
                    rec_simplif above_vars p1'
                  with Not_found ->
		    let t' = Terms.cst_for_type t.t_type in
		    if not (Terms.equal_terms t t') then 
                      begin
                        done_transfos := (DRemoveAssign(b, DKeepDefPoint, DRemoveAll)) :: (!done_transfos);
                        Settings.changed := true
                      end;
		    Terms.oproc_from_desc (Let(pat,  t', rec_simplif (b::above_vars) p1', Terms.oproc_from_desc Yield))
		else
		  begin
                    (* b will completely disappear *)
                    Settings.changed := true;
                    done_transfos := (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: (!done_transfos);
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
                let p1' = Terms.copy_oprocess (Terms.OneSubst(b,t,copy_changed)) p1 in
                let subst_def = !copy_changed in (* Set to true if an occurrence of b has really been substituted *)
                Settings.changed := (!Settings.changed) || subst_def;
                if b.array_ref then
		  begin
                    let p1'' = rec_simplif (b::above_vars) p1' in
                    (* suggest to use "sa_rename b" before removing assignments *)
		    if do_advise then Settings.advise := Terms.add_eq (SArenaming b) (!Settings.advise);
                    (* Keep the definition so that out-of-scope array accesses are correct *)
                    if subst_def then
                      done_transfos := (DRemoveAssign(b, DKeepDef, DRemoveNonArray)) :: (!done_transfos);
                    Terms.oproc_from_desc (Let(pat, t, p1'', Terms.oproc_from_desc Yield))
		  end
		else if Settings.occurs_in_queries b then
                  begin
                    let p1'' = rec_simplif (b::above_vars) p1' in
		    (* Cannot change definition if b occurs in queries *)
                    if subst_def then
                      done_transfos := (DRemoveAssign(b, DKeepDef, DRemoveAll)) :: (!done_transfos);
 		    Terms.oproc_from_desc (Let(pat, t, p1'', Terms.oproc_from_desc Yield))
                  end
                else if b.root_def_array_ref then
		  (* We may keep calls to defined(b), so keep a definition of b
		     but its value does not matter *)
		  let t' = Terms.cst_for_type t.t_type in
		  if not (Terms.equal_terms t t') then 
                    begin
                      done_transfos := (DRemoveAssign(b, DKeepDefPoint, DRemoveAll)) :: (!done_transfos);
                      Settings.changed := true
                    end
                  else if subst_def then
                    done_transfos := (DRemoveAssign(b, DKeepDefPoint, DRemoveAll)) :: (!done_transfos);
                  let p1'' = rec_simplif (b::above_vars) p1' in
		  Terms.oproc_from_desc (Let(pat, t', p1'', Terms.oproc_from_desc Yield))
		else
                  (* b will completely disappear *)
		  begin
                    done_transfos := (DRemoveAssign(b, DRemoveDef, DRemoveAll)) :: (!done_transfos);
		    Settings.changed := true;
                    let p1'' = rec_simplif above_vars p1' in
		    p1''
		  end
              end
     end
  | _ -> 
      Terms.oproc_from_desc (Let(rec_simplif_pat pat, rec_simplif_term t, rec_simplif [] p1, rec_simplif [] p2))

	
let expand_assign let_p remove_set above_vars rec_simplif_term rec_simplif_pat rec_simplif pat t p1 p2 =
  try
    let (transfos, test, bind) = Terms.simplify_let_tuple (fun t -> t) pat t in
    if transfos != [] then
      begin
	Settings.changed := true;
	done_transfos := (DLetSimplifyPattern(let_p, transfos)) :: (!done_transfos);
        (* Put the lets *)
	let plet = Terms.put_lets bind p1 p2 in
        (* Put the test *)
	let pfinal =
          if Terms.is_true test then
            plet
	  else
	    Terms.oproc_from_desc (Test(test, plet, p2))
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
      expand_assign_one remove_set above_vars rec_simplif_term rec_simplif_pat rec_simplif pat t p1 p2
  with Terms.Impossible -> 
    Settings.changed := true;
    done_transfos := (DLetSimplifyPattern(let_p, [pat, DImpossibleTuple])) :: (!done_transfos);
    rec_simplif above_vars p2



let several_def b =
  match b.def with
    [] | [_] -> false
  | _::_::_ -> true

let rec remove_assignments_term in_find_cond remove_set above_vars t =
  match t.t_desc with
    Var(b,l) ->
      Terms.build_term2 t (Var(b, List.map (remove_assignments_term in_find_cond remove_set above_vars) l))
  | ReplIndex i -> Terms.build_term2 t (ReplIndex i)
  | FunApp(f,l) ->
      Terms.build_term2 t (FunApp(f, List.map (remove_assignments_term in_find_cond remove_set above_vars) l))
  | TestE(t1,t2,t3) ->
      Terms.build_term2 t (TestE(remove_assignments_term in_find_cond remove_set above_vars t1,
		                 remove_assignments_term in_find_cond remove_set [] t2,
		                 remove_assignments_term in_find_cond remove_set [] t3))
  | FindE(l0, t3, find_info) ->
      Terms.build_term2 t (FindE(List.map (fun (bl, def_list, t1, t2) ->
	                             (bl, def_list,
			              remove_assignments_term true remove_set [] t1,
			              remove_assignments_term in_find_cond remove_set [] t2)) l0,
		                 remove_assignments_term in_find_cond remove_set [] t3, find_info))
  | LetE(pat,t1,t2,topt) ->
     expand_assign_term (DTerm t) in_find_cond remove_set above_vars
       (remove_assignments_term in_find_cond remove_set above_vars)
       (remove_assignments_pat in_find_cond remove_set above_vars)
       (remove_assignments_term in_find_cond remove_set)
       pat t1 t2 topt
  | ResE(b,t) ->
      if (!Settings.auto_sa_rename) && (several_def b) && (not (Terms.has_array_ref_q b)) then
	begin
	  let b' = Terms.new_binder b in
	  let t' = Terms.copy_term (Terms.Rename(List.map Terms.term_from_repl_index b.args_at_creation, b, b')) t in
	  Settings.changed := true;
	  done_sa_rename := (b,b') :: (!done_sa_rename);
          (* Allow using b' for testing whether a variable is defined *) 
          b'.count_def <- 1;
          let above_vars' = b' :: above_vars in
	  Terms.build_term2 t' (ResE(b', remove_assignments_term in_find_cond remove_set above_vars' t'))
	end
      else
	Terms.build_term2 t (ResE(b, remove_assignments_term in_find_cond remove_set (b::above_vars) t))
  | EventAbortE f ->
     t
  | EventE(t1,p) ->
     Terms.build_term2 t (EventE(remove_assignments_term in_find_cond remove_set above_vars t1,
		                 remove_assignments_term in_find_cond remove_set above_vars p))
  | GetE _ | InsertE _ ->      
      Parsing_helper.internal_error "Get/Insert should not appear in Transf_remove_assign.remove_assignments_term"

and remove_assignments_pat in_find_cond remove_set above_vars = function
    (PatVar _) as pat -> pat
  | PatEqual t -> PatEqual (remove_assignments_term in_find_cond remove_set above_vars t)
  | PatTuple(f,l) -> PatTuple(f, List.map (remove_assignments_pat in_find_cond remove_set above_vars) l)
    
let rec remove_assignments_rec remove_set p = 
  Terms.iproc_from_desc (
  match p.i_desc with
    Nil -> Nil
  | Par(p1,p2) -> 
      Par(remove_assignments_rec remove_set p1,
	  remove_assignments_rec remove_set p2)
  | Repl(b,p) ->
      Repl(b,remove_assignments_rec remove_set p)
  | Input((c,tl),pat,p) ->
     Input((c, List.map (remove_assignments_term false remove_set []) tl),
           remove_assignments_pat false remove_set [] pat, 
	   remove_assignments_reco remove_set [] p))

and remove_assignments_reco remove_set above_vars p =
  match p.p_desc with
    Yield -> Terms.oproc_from_desc Yield
  | EventAbort f -> Terms.oproc_from_desc (EventAbort f)
  | Restr(b,p) ->
      if (!Settings.auto_sa_rename) && (several_def b) && (not (Terms.has_array_ref_q b)) then
	begin
	  let b' = Terms.new_binder b in
	  let p' = Terms.copy_oprocess (Terms.Rename(List.map Terms.term_from_repl_index b.args_at_creation, b, b')) p in
	  Settings.changed := true;
	  done_sa_rename := (b,b') :: (!done_sa_rename);
          (* Allow using b' for testing whether a variable is defined *) 
          b'.count_def <- 1;
          let above_vars' = b' :: above_vars in
	  Terms.oproc_from_desc (Restr(b',remove_assignments_reco remove_set above_vars' p'))
	end
      else
	Terms.oproc_from_desc (Restr(b,remove_assignments_reco remove_set (b::above_vars) p))
  | Test(t,p1,p2) ->
      Terms.oproc_from_desc (Test(remove_assignments_term false remove_set above_vars t, 
	   remove_assignments_reco remove_set [] p1,
	   remove_assignments_reco remove_set [] p2))
  | Find(l0,p2,find_info) ->
      Terms.oproc_from_desc 
	(Find(List.map (fun (bl,def_list,t,p1) ->
	     (bl, def_list, 
	      remove_assignments_term true remove_set [] t,
	      remove_assignments_reco remove_set [] p1)) l0,
	   remove_assignments_reco remove_set [] p2, find_info))
  | Output((c,tl),t2,p) ->
      Terms.oproc_from_desc 
	(Output((c, List.map (remove_assignments_term false remove_set above_vars) tl), 
		remove_assignments_term false remove_set above_vars t2,
		remove_assignments_rec remove_set p))
  | Let(pat, t, p1, p2) ->
     let rec_simplif_term = remove_assignments_term false remove_set above_vars in
     let rec_simplif_pat = remove_assignments_pat false remove_set above_vars in
      let rec_simplif = remove_assignments_reco remove_set in
      expand_assign (DProcess p) remove_set above_vars rec_simplif_term rec_simplif_pat rec_simplif pat t p1 p2
  | EventP(t,p) ->
      Terms.oproc_from_desc 
	(EventP(remove_assignments_term false remove_set above_vars t,
		remove_assignments_reco remove_set above_vars p))
  | Get _|Insert _ -> Parsing_helper.internal_error "Get/Insert should not appear here"

(* - Main function for assignment removal *)

let remove_assignments remove_set p =
  Terms.build_def_process None p;
  if !Terms.current_bound_vars != [] then
    Parsing_helper.internal_error "bound vars should be cleaned up (transf1)";
  Terms.array_ref_process p;
  replacement_def_list := [];
  (* - First pass: put links; split assignments of tuples if possible *)
  let p' = remove_assignments_rec remove_set p in
  (* - Second pass: copy the process following the links or replacing just one variable.
       Be careful for array references: update the indexes properly  *)
  let p'' = Terms.copy_process (Terms.Links_Vars_Args(!replacement_def_list)) p' in
  Terms.cleanup();
  Terms.cleanup_array_ref();
  Terms.empty_def_process p;
  replacement_def_list := [];
  p''

let rec remove_assignments_repeat n remove_set p =
  let tmp_changed = !Settings.changed in
  Settings.changed := false;
  let p' = remove_assignments remove_set p in
  if n != 1 && !Settings.changed then
    remove_assignments_repeat (n-1) remove_set p'
  else
    begin
      Settings.changed := tmp_changed;
      p'
    end

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

let remove_assignments remove_set g =
  let g_proc = Terms.get_process g in
  done_sa_rename := [];
  done_transfos := [];
  let r = 
    if (remove_set == Minimal) || (remove_set = FindCond) then
      remove_assignments_repeat (!Settings.max_iter_removeuselessassign) remove_set g_proc
    else
      remove_assignments remove_set g_proc
  in
  let sa_rename = !done_sa_rename in
  let transfos = !done_transfos in
  done_transfos := [];
  done_sa_rename := [];
  (Terms.build_transformed_game r g, [], (do_sa_rename sa_rename) @ transfos)

