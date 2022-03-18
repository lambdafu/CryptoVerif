open Types

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
      if Terms.is_args_at_creation b l &&
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
      array_ref_term (Terms.vars_from_pat in_scope pat) t2;
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
  | GetE(tbl,patl,topt,p1,p2,_) ->
      List.iter (array_ref_pattern in_scope) patl;
      let in_scope' = Terms.vars_from_pat_list in_scope patl in
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
    if Terms.is_args_at_creation b l &&
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
      array_ref_oprocess (Terms.vars_from_pat in_scope pat) p

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
      array_ref_oprocess (Terms.vars_from_pat in_scope pat) p1;
      array_ref_oprocess in_scope p2
  | EventP(t,p) ->
      array_ref_term in_scope t;      
      array_ref_oprocess in_scope p
  | Get(tbl,patl,topt,p1,p2,_) ->
      List.iter (array_ref_pattern in_scope) patl;
      let in_scope' = Terms.vars_from_pat_list in_scope patl in
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
      List.iter (array_ref_fungroup ((List.map (fun (b,ext,opt) -> b) restr) @ in_scope)) funlist
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

let has_array_ref_q b q =
  (has_array_ref b) || (Settings.occurs_in_queries b q)

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
      if not (Terms.is_args_at_creation b l &&
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
      exclude_array_ref_term (Terms.vars_from_pat in_scope pat) t2;
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
  | GetE(tbl,patl,topt,p1,p2,_) -> 
      List.iter (exclude_array_ref_pattern in_scope) patl;
      let in_scope' = Terms.vars_from_pat_list in_scope patl in
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
    if not (Terms.is_args_at_creation b l &&
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

