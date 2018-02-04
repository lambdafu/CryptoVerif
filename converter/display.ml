open Types
open Ptree
open Lexing
  
(* Allow changing the output destination *)
  
let output = ref (stdout : out_channel)
    
let print_string s =
  output_string (!output) s

let print_int i =
  print_string (string_of_int i)
    
let print_float f =
  print_string (string_of_float f)

let print_newline() =
  print_string "\n";
  flush (!output)

(* Allow making copies from an input file *)

let input = ref (stdin : in_channel)

let copy (loc_start, loc_end)  =
  seek_in (!input) loc_start.pos_cnum;
  let rec aux n =
    if n = 0 then () else
    begin
      output_char (!output) (input_char (!input));
      aux (n-1)
    end
  in
  aux (loc_end.pos_cnum - loc_start.pos_cnum)
    
let set_files oc ic =
  output := oc;
  input := ic
       
let display_arrays = ref false

let max_game_number = ref 1

let rec display_list_sep sep f = function
    [] -> ()
  | [a] -> f a
  | (a::l) -> f a; print_string sep;
      display_list_sep sep f l

let display_list f l = display_list_sep ", " f l
	
let rec remove_common_prefix l1 l2 = match (l1,l2) with
  ({t_desc = ReplIndex ri1}::l1',ri2::l2') when ri1 == ri2 -> 
    remove_common_prefix l1' l2'
| _ -> l1

let remove_common_suffix l1 l2 =
  List.rev (remove_common_prefix (List.rev l1) (List.rev l2))

(* Verifying that a variable name does not end with _nnn is necessary
to make sure that there cannot be confusions between b.sname = XXX_nnn,
b.vname = 0 and b.sname = XXX, b.vname = nnn. 
With this test, when the displayed name is XXX_nnn, then 
b.vname = nnn, b.sname = XXX (XXX must be non-empty).
Otherwise, b.vname = 0, b.sname = the displayed name. *)

let ends_with_underscore_number s =
  let l = String.length s in
  '0' <= s.[l-1] && s.[l-1] <= '9' &&
  (let rec underscore_number n = (n > 0) &&
    ((s.[n] = '_') || ('0' <= s.[n] && s.[n] <= '9' && underscore_number (n-1)))
  in
  underscore_number (l-2))

let display_table tbl = print_string (tbl.tblname)

let binder_to_string b =
  if (b.vname != 0) || (ends_with_underscore_number b.sname) then 
    b.sname ^ "_" ^ (string_of_int b.vname)
  else
    b.sname

let display_binder b =
  print_string (binder_to_string b)

let repl_index_to_string b =
  if (b.ri_vname != 0) || (ends_with_underscore_number b.ri_sname) then 
    b.ri_sname ^ "_" ^ (string_of_int b.ri_vname)
  else
    b.ri_sname

let display_repl_index b =
  print_string (repl_index_to_string b)

(* Define when to put parentheses around infix symbols *)

type infix_paren =
    NoInfix
  | AllInfix
  | AllInfixExcept of funsymb

(* Define when to put parentheses around process-like terms 
   (TestE, ResE, LetE, FindE, EventAbortE) *)

type process_paren =
    NoProcess
  | AllProcess
  | ProcessMayHaveElseBranch

(* [may_have_elset t] returns true when the term [t] could have an
   "else" branch but actually does not have one, so needs to be 
   put between parentheses when [t] is itself inside a term that 
   may have an else branch. *)

let rec may_have_elset t =
  match t.t_desc with
    ReplIndex _ | Var _ | FunApp _ -> false 
      (* An infix operator inside a process will be between parentheses; 
	  no need to add further parentheses *)
  | TestE _ | FindE _ | GetE _ -> false
      (* Terms TestE _ | FindE _ | GetE _ always have an else branch *)
  | LetE(_,_,t2,topt) ->
      ((!Settings.front_end) == Settings.Channels) &&
      (* In the oracles front-end, the let without else branch is 
	 always written x <- M; M' and so an else branch cannot be added *)
      (match topt with
	None -> true
      | Some t3 -> may_have_elset t3)
  | ResE(_,t') | InsertE(_,_,t') | EventE(_,t') -> may_have_elset t'
  | EventAbortE _ -> false

let rec display_var b tl =
  let tl = 
    if !display_arrays then tl else 
    remove_common_suffix tl b.args_at_creation 
  in
  display_binder b;
  if tl != [] then
    begin
      print_string "[";
      display_list (display_term_paren AllInfix AllProcess) tl;
      print_string "]"
    end
  
and display_binder_with_array b =
  display_binder b;
  if (!display_arrays) && (b.args_at_creation != []) then
    begin
      print_string "[";
      display_list display_repl_index b.args_at_creation;      
      print_string "]"
    end

and display_binder_with_type b =
  display_binder_with_array b;
  match b.btype.tcat with
    Interv n -> 
      print_string " <= ";
      print_string n.pname
  | _ -> 
      print_string ": ";
      print_string b.btype.tname

and display_repl_index_with_type b =
  display_repl_index b;
  print_string " <= ";
  print_string (Terms.param_from_type b.ri_type).pname

and display_findcond (def_list, t1) =
  let cond_printed = ref false in
  if def_list != [] then
    begin
      print_string "defined(";
      display_list (fun (b,tl) -> display_var b tl) def_list;
      print_string ")";
      cond_printed := true
    end;
  if !cond_printed then
    begin
      if not (Terms.is_true t1) then
	begin
	  print_string " && ";
	  display_term_paren (AllInfixExcept Settings.f_and) AllProcess t1
	end
    end
  else
    display_term_paren NoInfix AllProcess t1

and display_term t = 
  match t.t_desc with
    Var(b,tl) -> display_var b tl
  | ReplIndex b -> display_repl_index b
  | FunApp(f,l) ->
      begin
	match f.f_cat with
	  Std | Tuple | Event | LetFunTerm _ -> 
	    print_string f.f_name;
	    (* Event functions have replication indexes added at first argument
               Do not display it *)
	    let l = if f.f_cat == Event then List.tl l else l in
	    if (l != []) || (f.f_cat == Tuple) then
	      begin
		print_string "(";
		display_list (display_term_paren AllInfix AllProcess) l;
		print_string ")"
	      end
	| LetEqual | Equal | Diff | ForAllDiff ->
	    begin
	    match l with
	      [t1;t2] -> 
		display_term_paren AllInfix AllProcess t1;
		print_string (" " ^ f.f_name ^ " ");
		display_term_paren AllInfix AllProcess t2
	    | _ -> Parsing_helper.internal_error "Infix operators need two arguments (display)"
	    end
	| Or | And ->
	    match l with
	      [t1;t2] -> 
		display_term_paren (AllInfixExcept f) AllProcess t1;
		print_string (" " ^ f.f_name ^ " ");
		display_term_paren (AllInfixExcept f) AllProcess t2
	    | _ -> Parsing_helper.internal_error "Infix operators need two arguments (display)"
      end
  | TestE(t1,t2,t3) ->
      print_string "if ";
      display_term_paren NoInfix AllProcess t1;
      print_string " then ";
      display_term_paren AllInfix ProcessMayHaveElseBranch t2;
      print_string " else ";
      display_term_paren AllInfix NoProcess t3
  | FindE([([],def_list,t1,t2)],t3,find_info) ->
      print_string "if ";
      display_findcond (def_list,t1);
      print_string " then ";
      display_term_paren AllInfix ProcessMayHaveElseBranch t2;
      print_string " else ";
      display_term_paren AllInfix NoProcess t3
  | FindE(l0, t3, find_info) ->
      let first = ref true in
      print_string "find ";
      if find_info = Unique then print_string "[unique] ";
      List.iter (fun (bl, def_list, t1, t2) ->
	if !first then
	  first := false
	else
	  print_string " orfind ";
	display_list (fun (b,b') -> display_binder_with_array b; print_string " = "; display_repl_index_with_type b') bl;
	print_string " suchthat ";
	display_findcond (def_list, t1);
	print_string " then ";
	display_term_paren AllInfix ProcessMayHaveElseBranch t2) l0;
      print_string " else ";
      display_term_paren AllInfix NoProcess t3      
  | LetE(pat, t1, t2, topt) ->
      begin
	match pat with
	  PatVar b when ((!Settings.front_end) == Settings.Oracles) && (topt == None) ->
	    display_binder_with_type b;
	    print_string " <- ";
	    display_term_paren NoInfix AllProcess t1;
	    print_string "; ";	    
	| _ ->
	    print_string "let ";
	    display_pattern_paren pat;
	    print_string " = ";
	    display_term_paren NoInfix AllProcess t1;
	    print_string " in "
      end;
      begin
	display_term_paren AllInfix ProcessMayHaveElseBranch t2;
	match topt with
	  None -> ()
	| Some t3 ->
	    print_string " else ";
	    display_term_paren AllInfix NoProcess t3      
      end
  | ResE(b,t) ->
      if (!Settings.front_end) == Settings.Oracles then
	begin
	  display_binder_with_array b;
	  print_string " <-R ";
	  print_string b.btype.tname
	end
      else
	begin
	  print_string "new ";
	  display_binder_with_type b
	end;
      print_string "; ";
      display_term_paren AllInfix NoProcess t
  | EventAbortE(f) ->
      print_string "event_abort ";
      print_string f.f_name
  | EventE(t1, p) ->
      print_string "event ";
      display_term t1;
      print_string "; ";
      display_term_paren AllInfix NoProcess p
  | GetE(tbl, patl, topt, p1, p2) ->
      print_string "get ";
      display_table tbl;
      print_string "(";
      display_list display_pattern patl;
      print_string ")";
      (
        match topt with 
            None -> ();
          | Some t -> 
              print_string " suchthat ";
              display_term_paren NoInfix AllProcess t
      );
      print_string " in ";
      display_term_paren AllInfix ProcessMayHaveElseBranch p1;
      print_string " else ";
      display_term_paren AllInfix NoProcess p2
  | InsertE (tbl,tl,p) ->
      print_string "insert ";
      display_table tbl;
      print_string "(";
      display_list (display_term_paren NoInfix AllProcess) tl;
      print_string "); ";
      display_term_paren AllInfix NoProcess p
	
and display_term_paren infix_paren process_paren t =
  let put_paren =
    match t.t_desc with
      Var _ | ReplIndex _ 
    | FunApp({ f_cat = Std | Tuple | Event | LetFunTerm _ },_) -> false
    | FunApp({ f_cat = LetEqual | Equal | Diff | ForAllDiff | Or | And } as f,_) ->
	begin
	  match infix_paren with
	    NoInfix -> false
	  | AllInfix -> true
	  | AllInfixExcept f' -> f != f'
	end
    | TestE _ | ResE _ | FindE _ | LetE _ | EventAbortE _ | EventE _ | GetE _ | InsertE _ ->
	begin
	  match process_paren with
	    NoProcess -> false
	  | AllProcess -> true
	  | ProcessMayHaveElseBranch -> may_have_elset t
	end
  in
  if put_paren then 
    begin
      print_string "(";
      display_term t;
      print_string ")"
    end
  else
    display_term t

(* Patterns *)

and display_pattern = function
    PatVar b ->
      display_binder_with_type b
  | PatTuple (f,l) ->
      print_string f.f_name;
      print_string "(";
      display_list display_pattern l;
      print_string ")"
  | PatEqual t ->
      print_string "=";
      display_term_paren AllInfix AllProcess t

and display_pattern_paren pat =
  match pat with
    PatEqual _ ->
      print_string "(";
      display_pattern pat;
      print_string ")"
  | _ -> display_pattern pat
	
(* Display term with appropriate parentheses around *)

let display_term t = display_term_paren AllInfix AllProcess t

(* Statements *)

let display_pterm ((p : Ptree.term), ext) =
  copy ext

let display_statement (bl, t) =
  print_string "equation ";
  if bl <> [] then
    begin
      print_string "forall ";
      display_list (fun ((x,_),(t,_)) -> print_string (x^": "^t)) bl;
      print_string "; "
    end;
  display_pterm t;
  print_string "."

(* Equivalences *)

let display_ppattern ((pat : Ptree.pattern), ext) =
  copy ext

let display_pprobaf ((proba : Ptree.probabilityf), ext) =
  copy ext
    
let rec may_have_elsept (t,_) =
  match t with
    PIdent _ | PArray _ | PFunApp _
  | PEqual _ | PDiff _ | PAnd _ | POr _ | PInjEvent _ | PTuple _ -> false 
           (* An infix operator inside a process will be between parentheses; 
	      no need to add further parentheses *)
  | PTestE _ | PFindE _ | PGetE _ -> false
      (* Terms TestE _ | FindE _ | GetE _ always have an else branch *)
  | PLetE(_,_,t2,topt) ->
      ((!Settings.front_end) == Settings.Channels) &&
      (* In the oracles front-end, the let without else branch is 
	 always written x <- M; M' and so an else branch cannot be added *)
      (match topt with
	None -> true
      | Some t3 -> may_have_elsept t3)
  | PResE(_,_,t') | PInsertE(_,_,t') | PEventE(_,t') -> may_have_elsept t'
  | PEventAbortE _ -> false

let display_pterm_paren infix_paren process_paren ((t, ext) as text) =
  let put_paren =
    match t with
      PIdent _ | PArray _ | PFunApp _ | PInjEvent _ | PTuple _ -> false
    | PEqual _ | PDiff _ | PAnd _ | POr _ ->
	begin
	  match infix_paren, t with
	    NoInfix, _ -> false
	  | AllInfix, _ -> true
	  | AllInfixExcept f', PAnd _ -> f' != Settings.f_and
	  | AllInfixExcept f', POr _ -> f' != Settings.f_or
	  | AllInfixExcept f', _ -> true
	end
    | PTestE _ | PResE _ | PFindE _ | PLetE _ | PEventAbortE _ | PEventE _ | PGetE _ | PInsertE _ ->
	begin
	  match process_paren with
	    NoProcess -> false
	  | AllProcess -> true
	  | ProcessMayHaveElseBranch -> may_have_elsept text
	end
  in
  if put_paren then 
    begin
      print_string "(";
      display_pterm text;
      print_string ")"
    end
  else
    display_pterm text

let display_br ((i,ext),l) =
  print_string i;
  if l != [] then
    begin
      print_string "[";
      display_list (display_pterm_paren AllInfix AllProcess) l;
      print_string "]"
    end

let is_ptrue (t,_) =
  match t with
    PIdent("true",_) -> true
  | _ -> false
      
let display_pfindcond (def_list, t1) =
  if def_list != [] then
    begin
      print_string "defined(";
      display_list display_br def_list;
      print_string ")"
    end;
  if (def_list != []) && not (is_ptrue t1) then
    print_string " && ";
  if not (is_ptrue t1) then
    display_pterm_paren (AllInfixExcept Settings.f_and) AllProcess t1
  else if def_list == [] then
    print_string "true"

let display_options options =
  if options != [] then
    begin
      print_string " [";
      display_list (fun (i,ext) -> print_string i) options;
      print_string "]"
    end

let display_pbinder_with_type ((i,ext),ty) =
  print_string i;
  match ty with
    Tid (it,extt) -> print_string ": "; print_string it
  | TBound (it,extt) -> print_string " <= "; print_string it
      
let display_priority priority =
  if priority != 0 then
    begin
      print_string " [";
      print_int priority;
      print_string "]"
    end

let rec display_pprocasterm (t,ext) = 
  match t with
    PIdent _ | PArray _ | PFunApp _ | PTuple _
  | PEqual _ | PDiff _ | PAnd _ | POr _ ->
      print_string "return(";
      display_pterm (t,ext);
      print_string ")"
  | PInjEvent _ ->
      Parsing_helper.internal_error "PInjEvent allowed in queries only"
  | PTestE(t1,t2,t3) ->
      print_string "if ";
      display_pterm_paren NoInfix AllProcess t1;
      print_string " then ";
      display_pprocasterm_paren t2;
      print_string " else ";
      display_pprocasterm t3
  | PFindE([_, [], def_list, t1, t2], t3, options) ->
      print_string "if ";
      display_pfindcond (def_list,t1);
      print_string " then ";
      display_pprocasterm_paren t2;
      print_string " else ";
      display_pprocasterm t3
  | PFindE(l0,t3,options) ->
      print_string "find";
      display_options options;
      print_string " ";
      display_list_sep " orfind " (fun (_, bl, def_list, t1, t2) ->
	display_list (function (i1,_),(i2,_) ->
	  print_string i1; print_string " <= "; print_string i2) bl;
	print_string " suchthat ";
	display_pfindcond (def_list, t1);
	print_string " then ";
	display_pprocasterm_paren t2) l0;
      print_string " else ";
      display_pprocasterm t3      
  | PLetE(pat, t1, t2, topt) ->
      begin
	match fst pat with
	  PPatVar((i,ext),iopt) when ((!Settings.front_end) == Settings.Oracles) && (topt == None) ->
	    print_string i;
	    begin
	      match iopt with
		Some(it,_) -> print_string ": "; print_string it
	      | None -> ()
	    end;
	    print_string " <- ";
	    display_pterm_paren NoInfix AllProcess t1;
	    print_string "; ";	    
	| _ ->
	    print_string "let ";
	    display_ppattern pat;
	    print_string " = ";
	    display_pterm_paren NoInfix AllProcess t1;
	    print_string " in "
      end;
      begin
	display_pprocasterm_paren t2;
	match topt with
	  None -> ()
	| Some t3 ->
	    print_string " else ";
	    display_pprocasterm t3      
      end
  | PResE((i,ext),(it,extt),t) ->
      if (!Settings.front_end) == Settings.Oracles then
	begin
	  print_string i;
	  print_string " <-R ";
	  print_string it
	end
      else
	begin
	  print_string "new ";
	  print_string i;
	  print_string ": ";
	  print_string it
	end;
      print_string "; ";
      display_pprocasterm t
  | PEventAbortE(i,ext) ->
      print_string "event_abort ";
      print_string i
  | PEventE _ | PGetE _ | PInsertE _ ->
      Parsing_helper.internal_error "event/get/insert not allowed in definitions of crypto primitives"

and display_pprocasterm_paren text =
  if may_have_elsept text then 
    begin
      print_string "(";
      display_pprocasterm text;
      print_string ")"
    end
  else
    display_pprocasterm text
	
let rec display_pfungroup indent = function
    PReplRestr((replidxopt, repliopt, (repln,_)), restr, funlist) ->
      if (!Settings.front_end) == Settings.Oracles then
	begin
	  print_string "foreach ";
	  begin
	    match repliopt with
	      Some(i,_) -> print_string i
	    | None ->
		match !replidxopt with
		  Some b -> print_string (repl_index_to_string b)
		| None ->
		    Parsing_helper.internal_error "equivalence: replication shoud have been set"
	  end;
	  print_string " <= ";
	  print_string repln;
	  print_string " do ";
	  List.iter (fun ((i,_), (it,_), opt) -> 
	    print_string i;
	    print_string " <-R ";
	    print_string it;
	    display_options opt;
	    print_string "; ") restr
	end
      else
	begin
	  print_string "! ";
	  begin
	    match repliopt with
	      Some(i,_) -> print_string i; print_string " <= ";
	    | None -> ()
	  end;
	  print_string repln;
	  print_string " ";
	  List.iter (fun ((i,_), (it,_), opt) -> 
	    print_string "new ";
	    print_string i;
	    print_string ": ";
	    print_string it;
	    display_options opt;
	    print_string "; ") restr
	end;
      begin
	match funlist with 
	  [f] -> 
	    display_pfungroup indent f
	| _ -> 
	    print_string ("(\n" ^ indent);
	    display_list_sep (" |\n" ^ indent) (fun f ->
	      display_pfungroup (indent ^ "  ") f;
	      ) funlist;
	    print_string ")"
      end
  | PFun(chref, args, res, (priority, options)) ->
      (* @dummy_channel may appear at parsing, but we
	 already rename it in syntax.ml *)
      let (ch,_) = !chref in
      print_string ch;
      print_string "(";
      display_list display_pbinder_with_type args;
      print_string ")";
      display_priority priority;
      display_options options;
      print_string " := ";
      display_pprocasterm res


let display_peqmember (l,_) =
  display_list_sep "|\n" (fun (fg, mode,_) ->
    print_string "  ";
    display_pfungroup "    " fg;
    match mode with
      None -> ()
    | Some (i,_) -> print_string (" [" ^ i ^ "]")) l

let display_eqname = function
    NoName -> ()
  | CstName(s,_) -> print_string s; print_string " "
  | ParName((s,_),(p,_)) -> print_string (s ^ "(" ^ p ^ ")")

let rec get_ch_fungroup all_ch = function
    PReplRestr(_, restrlist, funlist) ->
      List.iter (get_ch_fungroup all_ch) funlist
  | PFun(chref, arglist, tres, _) ->
      let (ch, _) = !chref in
      all_ch := ch :: (!all_ch)

let rec fresh_oracle_name avoid_ch =
  let name = Terms.fresh_id "gen_Oracle" in
  if List.mem name avoid_ch then
    fresh_oracle_name avoid_ch
  else
    name

let rec lm_rename_fungroup all_ch = function
    PReplRestr(_, restrlist, funlist) ->
      List.iter (lm_rename_fungroup all_ch) funlist
  | PFun(chref, arglist, tres, _) ->
      let (s, ext) = !chref in
      let s =
	if s = "@dummy_channel" then
	  fresh_oracle_name all_ch
	else
	  s
      in
      chref := (s,ext)

let rec rm_rename_fungroup all_ch lm rm = 
  match (lm, rm) with
    PReplRestr(_, _, lfunlist), PReplRestr(_, _, rfunlist) ->
      List.iter2 (rm_rename_fungroup all_ch) lfunlist rfunlist
  | PFun(lchref, _, _, _), PFun(rchref, _, _, _) ->
      let (ch, ext) = !rchref in
      let ch =
	(* Note: this is slightly too permissive: 
           it allows a named oracle in the left-hand side to
	   correspond to an unnamed oracle in the right-hand side.
           This is not a serious problem. *)
	if ch = "@dummy_channel" then
	  fst (!lchref)
	else
	  ch
      in
      rchref := (ch, ext)
  | _, PReplRestr((_, _, (_,ext)), _,_) ->
      Parsing_helper.input_error "Left member is a function, right member is a replication" ext
  | _, PFun(ch, arglist, tres, _) ->
      Parsing_helper.input_error "Left member is a replication, right member is a function" (snd tres)

  
let display_equiv (n,((mem1,ext1) as m1),((mem2,ext2) as m2),proba,(prio,opt)) =
  (* Rename @dummy_channel in the equivalence *)
  let all_ch = ref [] in
  List.iter (fun (fg, _, _) -> get_ch_fungroup all_ch fg) mem1; (* Builds all_ch *)
  List.iter (fun (fg, _, _) -> lm_rename_fungroup (!all_ch) fg) mem1;
  List.iter2 (fun (lfg,_,_) (rfg, _,_) -> rm_rename_fungroup (!all_ch) lfg rfg) mem1 mem2;
  
  print_string "equiv";
  begin
    match n with
      NoName -> ()
    | _ ->  print_string "("; display_eqname n; print_string ")"
  end;
  print_string "\n";
  display_peqmember m1;
  print_newline();
  print_string "<=(";
  display_pprobaf proba;
  print_string ")=>";
  display_priority prio;
  display_options opt;
  print_string "\n";
  display_peqmember m2;
  print_string "."

let display_collision (newlist, foralllist, t1, proba, t2) =
  print_string "collision ";
  List.iter (fun ((i,ext),(it,ext2t)) ->
    if (!Settings.front_end) == Settings.Oracles then
      begin
	print_string i;
	print_string " <-R ";
	print_string it
      end
    else
      begin
	print_string "new ";
	print_string i;
	print_string ": ";
	print_string it
      end;
    print_string "; "
      ) newlist;
  if foralllist <> [] then
    begin
      print_string "forall ";
      display_list (fun ((i,ext),(it,ext2t)) ->
	print_string i;
	print_string ": ";
	print_string it) foralllist;
      print_string "; "
    end;
  print_string "return(";
  display_pterm t1;
  print_string ") <=(";
  display_pprobaf proba;
  print_string ")=> return(";
  display_pterm t2;
  print_string ")."
	
(* Processes *)

let display_channel c tl =
  print_string c.cname;
  if tl != [] then
    begin
      print_string "[";
      display_list display_term tl;
      print_string "]"
    end


let rec may_have_elseo p = 
  match p.p_desc with
    Yield | EventAbort _ -> false
  | Test(_,_,pelse) | Find(_,pelse,_) | Get(_,_,_,_,pelse) ->
      (pelse.p_desc = Yield) || (may_have_elseo pelse)
  | Let(pat,t,p1,p2) ->
      if ((!Settings.front_end) = Settings.Oracles) &&
	(p2.p_desc = Yield) &&
	(match pat with
	  PatVar _ -> true
	| _ -> false)
      then
	(* The "let" will be written x <- M; M' *)
	may_have_elseo p1
      else
	(p2.p_desc = Yield) || (may_have_elseo p2)
  | Restr(_,p) | EventP(_,p) | Insert (_,_,p) -> may_have_elseo p
  | Output(_,_,p) -> may_have_else p

and may_have_else p = 
  match p.i_desc with
    Nil | Par _ -> false (* Par always introduces parentheses; whatever
	there is inside will be surrounded by these parentheses so does not
	need further parentheses *)
  | Repl(_,p) -> may_have_else p
  | Input(_,_,p) -> may_have_elseo p

let rec display_process indent p = 
  match p.i_desc with
    Nil -> 
      print_string (indent ^ "0\n")
  | Par _ -> 
      let rec dec_par p0 = 
	match p0.i_desc with
	  Par(p,p') -> (dec_par p) @ (dec_par p')
	| p -> [p0]
      in
      let l = dec_par p in
      print_string (indent^"((\n");
      let rec display_par_list = function
	  [] -> Parsing_helper.internal_error "empty list of parallel processes"
	| [p] ->
	    display_process (indent^"  ") p;
	    print_string (indent^"))\n");
	| p::l ->
	    display_process (indent^"  ") p;
	    print_string (indent^") | (\n");
	    display_par_list l
      in
      display_par_list l
  | Repl(b,p) ->
      if (!Settings.front_end) == Settings.Oracles then
	begin
	  print_string (indent ^ "foreach ");
	  display_repl_index_with_type b;
	  print_string " do"
	end
      else
	begin
	  print_string (indent ^ "! ");
	  display_repl_index_with_type b
	end;
      print_newline();
      display_process indent p
  | Input((c,tl),pat,p) ->
      if (!Settings.front_end) == Settings.Oracles then
	begin
	  print_string (indent ^ c.cname);
	  if (!display_arrays) && (tl != []) then
	    begin
	      print_string "[";
	      display_list display_term tl;
	      print_string "]"
	    end;
	  display_pattern pat;
	  print_string " :=\n";
	  display_oprocess indent p
	end
      else
	begin
	  print_string (indent ^ "in(");
	  display_channel c tl;
	  print_string ", ";
	  display_pattern pat;
	  print_string ")";
	  display_optoprocess indent p
	end

and display_oprocess indent p =
  match p.p_desc with
    Yield -> 
      print_string (indent ^ "yield\n")
  | EventAbort f -> 
      print_string (indent ^ "event_abort " ^ f.f_name ^ "\n")
  | Restr(b,p) ->
      if (!Settings.front_end) == Settings.Oracles then
	begin
	  print_string indent;
	  display_binder_with_array b;
	  print_string " <-R ";
	  print_string b.btype.tname
	end
      else
	begin
	  print_string (indent ^ "new ");
	  display_binder_with_type b
	end;
      display_optoprocess indent p
  | Test(t,p1,p2) ->
      print_string (indent ^ "if ");
      display_term_paren NoInfix AllProcess t;
      print_string " then\n";
      if p2.p_desc = Yield then
	display_oprocess indent p1
      else
	begin
	  display_oprocess_paren indent p1;
	  print_string (indent ^ "else\n");
	  display_oprocess (indent ^ "  ") p2
	end
  | Find([([],def_list,t,p1)],p2, find_info) ->
      print_string (indent ^ "if ");
      display_findcond (def_list,t);
      print_string " then\n";
      if p2.p_desc = Yield then
	display_oprocess indent p1
      else
	begin
	  display_oprocess_paren indent p1;
	  print_string (indent ^ "else\n");
	  display_oprocess (indent ^ "  ") p2
	end
  | Find(l0,p2, find_info) ->
      let first = ref true in
      let single_branch = (p2.p_desc = Yield) && (List.length l0 = 1) in
      print_string (indent ^ "find ");
      if find_info = Unique then print_string "[unique] ";
      List.iter (fun (bl,def_list,t,p1) ->
	if !first then
	  first := false
	else
	  begin
	    print_string (indent ^ "orfind ")
	  end;
	display_list (fun (b, b') -> display_binder_with_array b; print_string " = "; display_repl_index_with_type b') bl;
	print_string " suchthat ";
	display_findcond (def_list,t);
	print_string " then\n";
	if single_branch then
	  display_oprocess indent p1
	else
	  display_oprocess_paren indent p1
	  ) l0;
      if l0 == [] then print_string "\n";
      if p2.p_desc != Yield then
	begin
	  print_string (indent ^ "else\n");
	  display_oprocess (indent ^ "  ") p2
	end
  | Output((c,tl),t2,p) ->
      if (!Settings.front_end) == Settings.Oracles then
	begin
	  print_string (indent ^ "return");
	  (* t2 is always a tuple, it will display the parentheses *)
	  display_term t2
	end
      else
	begin
	  print_string (indent ^ "out(");
	  display_channel c tl;
	  print_string ", ";
	  display_term t2;
	  print_string ")"
	end;
      display_optprocess indent p
  | Let(pat,t,p1,p2) ->
      begin
	match pat with
	  PatVar b when ((!Settings.front_end) == Settings.Oracles) && (p2.p_desc = Yield) ->
	    print_string indent;
	    display_binder_with_type b;
	    print_string " <- ";
	    display_term_paren NoInfix AllProcess t;
	    display_optoprocess indent p1
	| _ ->
	    print_string (indent ^ "let ");
	    display_pattern_paren pat;
	    print_string " = ";
	    display_term_paren NoInfix AllProcess t;
	    if (p1.p_desc = Yield) && (p2.p_desc = Yield) then
	      print_string "\n"
	    else
	      begin
		print_string " in\n";
		if p2.p_desc = Yield then
		  display_oprocess indent p1
		else
		  begin
		    display_oprocess_paren indent p1;
		    print_string (indent ^ "else\n");
		    display_oprocess (indent ^ "  ") p2
		  end
	      end
      end
  | EventP(t,p) ->
      print_string (indent ^ "event ");
      display_term t;
      display_optoprocess indent p
  | Get (tbl,patl,topt,p1,p2) ->
      print_string (indent ^ "get ");
      display_table tbl;
      print_string "(";
      display_list display_pattern patl;
      print_string ")";
      (
        match topt with 
            None -> ();
          | Some t -> 
              print_string " suchthat ";
              display_term_paren NoInfix AllProcess t
      );
      if (p1.p_desc = Yield) && (p2.p_desc = Yield) then
	print_string "\n"
      else
	begin
	  print_string " in\n";
	  if p2.p_desc = Yield then
	    display_oprocess indent p1
	  else
	    begin
	      display_oprocess_paren indent p1;
	      print_string (indent ^ "else\n");
	      display_oprocess (indent ^ "  ") p2
	    end
	end
  | Insert (tbl,tl,p) ->
      print_string (indent ^ "insert ");
      display_table tbl;
      print_string "(";
      display_list (display_term_paren NoInfix AllProcess) tl;
      print_string ")";
      display_optoprocess indent p


and display_optprocess indent p =
  if p.i_desc = Nil then 
    print_string "\n"
  else
    begin
      print_string ";\n";
      display_process indent p
    end
      
and display_optoprocess indent p =
  if p.p_desc = Yield then 
    print_string "\n"
  else
    begin
      print_string ";\n";
      display_oprocess indent p
    end

and display_oprocess_paren indent p =
  if may_have_elseo p then
    begin
      print_string (indent ^ "(\n");
      display_oprocess (indent ^ "  ") p;
      print_string (indent ^ ")\n")
    end
  else
    display_oprocess (indent ^ "  ") p


let display_process p =
  display_process "" p;
  print_newline()
	
    
let display_event (b,t) =
  if b then print_string "inj-";
  print_string "event(";
  display_term t;
  print_string ")"
 
let rec display_query1 = function
    [] -> Parsing_helper.internal_error "List should not be empty"
  | [x] -> display_event x
  | x::l ->
      display_event x;
      print_string " && ";
      display_query1 l

let rec display_query2 = function
    QEvent(b,t) ->
      display_event (b,t)
  | QTerm t ->
      display_term t
  | QOr(t1,t2) ->
      print_string "(";
      display_query2 t1;
      print_string " || ";
      display_query2 t2;
      print_string ")"
  | QAnd(t1,t2) ->
      print_string "(";
      display_query2 t1;
      print_string " && ";
      display_query2 t2;
      print_string ")"

let display_pub_vars pub_vars =
  if pub_vars <> [] then
    begin
      print_string " public_vars ";
      display_list display_binder pub_vars
    end

let display_query = function
    QSecret1 (b,l) -> 
      print_string "secret "; display_binder b; 
      display_pub_vars l;
      print_string " [onesession]"
  | QSecret (b,l) -> 
      print_string "secret "; display_binder b; 
      display_pub_vars l
  | AbsentQuery -> Parsing_helper.internal_error "AbsentQuery should have been handled"
  | QEventQ(t1,t2) -> 
      display_query1 t1; 
      print_string " ==> ";
      display_query2 t2;
      display_pub_vars (Settings.get_public_vars())
	

let rec display_query_list = function
    [] -> Parsing_helper.internal_error "There should be at least one query here"
  | a::b::l ->
      display_query a;
      print_string ";\n  ";
      display_query_list (b::l)
  | [a] ->
      display_query a
	
let rec collect_vars_t accu t =
  match t.t_desc with
    Var(b,_) ->
      if List.memq b accu then accu else b::accu
  | ReplIndex _ -> accu
  | FunApp(f,l) ->
      let l' = if f.f_cat = Event then List.tl l else l in
      List.fold_left collect_vars_t accu l'
  | _ ->
      Parsing_helper.internal_error "Correspondence queries should contain simple terms"

let rec collect_vars_t2 accu = function
    QEvent(_,t) | QTerm t -> collect_vars_t accu t
  | QOr(t1,t2) | QAnd(t1,t2) -> collect_vars_t2 (collect_vars_t2 accu t1) t2
	
let collect_vars_q accu = function
    QSecret1 _ | QSecret _ | AbsentQuery ->
      accu
  | QEventQ(t1,t2) ->
      let vars_t1 = List.fold_left (fun accu (_,t) -> collect_vars_t accu t) accu t1 in
      collect_vars_t2 vars_t1 t2

let display_queries ql =
  let ql' = List.map Syntax.check_query ql in 
  print_string "query ";
  let vars = List.fold_left collect_vars_q [] ql' in
  display_list display_binder_with_type vars;
  if vars != [] then print_string ";\n  ";
  display_query_list ql';
  print_string "."
	  
