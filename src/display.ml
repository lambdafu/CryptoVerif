open Types

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
    
let file_out filename f =
  let old_output = !output in
  let file = open_out filename in
  output := file;
  f();
  close_out file;
  output := old_output

       
let display_occurrences = ref false
let useful_occs = ref []

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
	  Std | Tuple | Event -> 
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
      print_string "find ";
      if find_info = Unique then print_string "[unique] ";
      display_list_sep " orfind " (fun (bl, def_list, t1, t2) ->
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
  let infix_paren' = 
    if (!display_occurrences) || (List.memq t.t_occ (!useful_occs)) then
      begin
	print_string "{";
	print_int t.t_occ;
	print_string "}";
	(* When we show the occurrence of an infix term, this
	   term must always be between parentheses (otherwise,
	   we cannot know whether the occurrence refers to the
	   whole infix term or to its first argument). *)
	AllInfix
      end
    else
      infix_paren
  in
  let put_paren =
    match t.t_desc with
      Var _ | ReplIndex _ 
    | FunApp({ f_cat = Std | Tuple | Event },_) -> false
    | FunApp({ f_cat = LetEqual | Equal | Diff | ForAllDiff | Or | And } as f,_) ->
	begin
	  match infix_paren' with
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

let display_statement (bl, t, side_cond) =
  print_string "equation ";
  if bl <> [] then
    begin
      print_string "forall ";
      display_list display_binder_with_type bl;
      print_string "; ";
    end;
  display_term t;
  if not (Terms.is_true side_cond) then
    begin
      print_string " if ";
      display_term side_cond
    end;
  print_newline()

(* Equivalences *)

let display_action = function
    AFunApp f -> 
      begin
	match f.f_cat with
	  Tuple -> 
	    print_string "(";
	    display_list (fun t -> print_string t.tname) (fst f.f_type);
	    print_string ")"
	| LetEqual | Equal | Diff | ForAllDiff  ->
	    print_string f.f_name;
	    print_string " ";
	    print_string (List.hd (fst f.f_type)).tname
	| _ -> print_string f.f_name
      end
  | APatFunApp f -> 
      begin
	match f.f_cat with
	  Tuple -> 
	    print_string "let (";
	    display_list (fun t -> print_string t.tname) (fst f.f_type);
	    print_string ")"	      
	| _ -> print_string ("let " ^ f.f_name)
      end
  | AReplIndex -> 
      if (!Settings.front_end) == Settings.Oracles then
	print_string "foreach"
      else
	print_string "!"
  | AArrayAccess n -> print_string ("[" ^ (string_of_int n) ^ "]")
  | ANew t -> 
      if (!Settings.front_end) == Settings.Oracles then
	print_string ("<-R " ^ t.tname)
      else
	print_string ("new " ^ t.tname)
  | ANewChannel -> 
      if (!Settings.front_end) == Settings.Oracles then
	print_string "newOracle"
      else
	print_string "newChannel"
  | AIf -> print_string "if"
  | AFind n -> print_string ("find " ^ (string_of_int n))
  | AOut (tl,t) -> 
      if (!Settings.front_end) == Settings.Oracles then
	Parsing_helper.internal_error "out action should not occur in oracles front-end";
      print_string "out ";
      if tl != [] then
	begin
	  print_string "[";
	  display_list (fun t -> print_string t.tname) tl;
	  print_string "] "
	end;
      print_string t.tname
  | AIn n -> 
      if (!Settings.front_end) == Settings.Oracles then
	Parsing_helper.internal_error "in action should not occur in oracles front-end";
      print_string ("in " ^ (string_of_int n))

let times_to_display = ref []

let rec display_proba level = function
    Proba(p,l) -> 
      print_string p.prname;
      if l != [] then
	begin
	  print_string "(";
	  display_list (display_proba 0) l;
	  print_string ")"
	end
  | Count p -> print_string p.pname
  | OCount c -> print_string "#"; print_string c.cname
  | Add(x,y) -> 
      if level > 1 then print_string "(";
      display_proba 1 x;
      print_string " + ";
      display_proba 1 y;
      if level > 1 then print_string ")"
  | Sub(x,y) -> 
      if level > 1 then print_string "(";
      display_proba 1 x;
      print_string " - ";
      display_proba 2 y;
      if level > 1 then print_string ")"
  | Max(l) -> 
      print_string "max(";
      display_list (display_proba 0) l;
      print_string ")"
  | Mul(x,y) ->
      if level > 3 then print_string "(";
      display_proba 3 x;
      print_string " * ";
      display_proba 3 y;
      if level > 3 then print_string ")"
  | Zero -> print_string "0"      
  | Cst n -> print_float n
  | Div(x,y) ->
      if level > 3 then print_string "(";
      display_proba 3 x;
      print_string " / ";
      display_proba 4 y;
      if level > 3 then print_string ")"
  | Card t ->
      print_string "|";
      print_string t.tname;
      print_string "|"
  | AttTime ->
	print_string "time"
  | Time(g,t)->
	begin
	  print_string "time(context for game ";
	  print_int g.game_number;
	  print_string ")";
	  try
	    ignore (List.assq g (!times_to_display))
	  with Not_found -> 
	    times_to_display := (g,t)::(!times_to_display)
	end
  | ActTime(act, pl) ->
      print_string "time(";
      display_action act;
      if pl != [] then
	begin
	  print_string ", ";
	  display_list (display_proba 0) pl
	end;
      print_string ")"
  | Maxlength(g,t) ->
      print_string "maxlength(";
      if g.game_number>=0 then
	begin
	  print_string "game ";
	  print_int g.game_number;
	  print_string ": "
	end;
      display_term t;
      print_string ")"
  | TypeMaxlength(ty) ->
      print_string "maxlength(";
      print_string ty.tname;
      print_string ")"
  | EpsFind ->
      print_string "eps_find"
  | EpsRand ty ->
      print_string ("eps_rand(" ^ ty.tname ^ ")")
  | PColl1Rand ty ->
      print_string ("Pcoll1rand(" ^ ty.tname ^ ")")
  | PColl2Rand ty ->
      print_string ("Pcoll2rand(" ^ ty.tname ^ ")")
  | Length(f,pl) ->
      print_string "length(";
      begin
	match f.f_cat with
	  Tuple -> 
	    print_string "(";
	    display_list (fun t -> print_string t.tname) (fst f.f_type);
	    print_string ")"	      
	| _ -> print_string f.f_name
      end;
      if pl != [] then
	begin
	  print_string ", ";
	  display_list (display_proba 0) pl
	end;
      print_string ")"

let display_pub_vars pub_vars =
  if pub_vars <> [] then
    begin
      print_string " with public variables ";
      display_list display_binder pub_vars
    end
	
let display_one_set = function
    SetProba p ->
      display_proba 0 p;
  | SetEvent(f, g, pub_vars, _) ->
      print_string "Pr[event ";
      print_string f.f_name;
      print_string " in game ";
      print_int g.game_number;
      display_pub_vars pub_vars;
      print_string "]"

let rec display_set = function
    [] -> print_string "0"
  | [a] -> display_one_set a
  | a::l -> 
      display_one_set a;
      print_string " + ";
      display_set l
  

(* Only for the oracles front-end *)

let rec display_procasterm t = 
  if (!display_occurrences) || (List.memq t.t_occ (!useful_occs)) then
    begin
      print_string "{";
      print_int t.t_occ;
      print_string "}"
    end;
  match t.t_desc with
    Var _ | FunApp _ ->
      print_string "return(";
      display_term t;
      print_string ")"
  | ReplIndex _ -> 
      Parsing_helper.internal_error "ReplIndex unexpected in display_procasterm"
  | TestE(t1,t2,t3) ->
      print_string "if ";
      display_term_paren NoInfix AllProcess t1;
      print_string " then ";
      display_procasterm_paren t2;
      print_string " else ";
      display_procasterm t3
  | FindE([([],def_list,t1,t2)],t3,find_info) ->
      print_string "if ";
      display_findcond (def_list,t1);
      print_string " then ";
      display_procasterm_paren t2;
      print_string " else ";
      display_procasterm t3
  | FindE(l0, t3, find_info) ->
      print_string "find ";
      if find_info = Unique then print_string "[unique] ";
      display_list_sep " orfind " (fun (bl, def_list, t1, t2) ->
	display_list (fun (b, b') -> display_binder_with_array b; print_string " = "; display_repl_index_with_type b') bl;
	print_string " suchthat ";
	display_findcond (def_list, t1);
	print_string " then ";
	display_procasterm_paren t2) l0;
      print_string " else ";
      display_procasterm t3      
  | LetE(pat, t1, t2, topt) ->
      begin
	match pat with
	  PatVar b when (!Settings.front_end) == Settings.Oracles ->
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
	display_procasterm_paren t2;
	match topt with
	  None -> ()
	| Some t3 ->
	    print_string " else ";
	    display_procasterm t3      
      end
  | ResE(b,t) ->
      if (!Settings.front_end) == Settings.Oracles then
	begin
	  display_binder_with_array b;
	  print_string " <-R ";
	  print_string b.btype.tname;
	end
      else
	begin
	  print_string "new ";
	  display_binder_with_type b
	end;
      print_string "; ";
      display_procasterm t
  | EventAbortE(f) ->
      print_string "event_abort ";
      print_string f.f_name
  | EventE _ | GetE _ | InsertE _ ->
      Parsing_helper.internal_error "event/get/insert not allowed in definitions of crypto primitives"

and display_procasterm_paren t =
  if may_have_elset t then 
    begin
      print_string "(";
      display_procasterm t;
      print_string ")"
    end
  else
    display_procasterm t


let rec display_fungroup indent = function
    ReplRestr(repl, restr, funlist) ->
      if (!Settings.front_end) == Settings.Oracles then
	begin
	  print_string "foreach ";
	  display_repl_index_with_type repl;
	  print_string " do ";
	  List.iter (fun (b,opt) -> 
	    display_binder_with_array b;
	    print_string " <-R ";
	    print_string b.btype.tname;
	    if opt == Unchanged then
	      print_string " [unchanged]";
	    print_string "; ") restr
	end
      else
	begin
	  print_string "! ";
	  display_repl_index_with_type repl;
	  print_string " ";
	  List.iter (fun (b,opt) -> 
	    print_string "new ";
	    display_binder_with_type b;
	    if opt == Unchanged then
	      print_string " [unchanged]";
	    print_string "; ") restr
	end;
      begin
	match funlist with 
	  [f] -> 
	    display_fungroup indent f
	| _ -> 
	    print_string ("(\n" ^ indent);
	    display_list_sep (" |\n" ^ indent) (fun f ->
	      display_fungroup (indent ^ "  ") f;
	      ) funlist;
	    print_string ")"
      end
  | Fun(ch, args, res, (priority, options)) ->
      print_string ch.cname;
      print_string "(";
      display_list display_binder_with_type args;
      print_string ")";
      if priority != 0 then
	begin
	  print_string " [";
	  print_int priority;
	  print_string "]"
	end;
      begin
	match options with
	  StdOpt -> ()
	| UsefulChange -> print_string " [useful_change]"
      end;
      print_string " := ";
      display_procasterm res


	
let display_eqmember l =
  display_list_sep "|\n" (fun (fg, mode) ->
    print_string "  ";
    display_fungroup "    " fg;
    if mode = AllEquiv then print_string " [all]") l

let display_eqname = function
    NoName -> ()
  | CstName(s,_) -> print_string s
  | ParName((s,_),(p,_)) -> print_string (s ^ "(" ^ p ^ ")")

let display_equiv ((n,m1,m2,set,opt,opt2),_) =
  print_string "equiv";
  begin
    match n with
      NoName -> ()
    | _ ->  print_string "("; display_eqname n; print_string ")"
  end;
  print_string "\n";
  display_eqmember m1;
  print_newline();
  print_string "<=(";
  display_set set;
  print_string ")=>";
  begin
    match opt,opt2 with
      StdEqopt, Decisional -> ()
    | PrioEqopt n, Decisional -> print_string (" [" ^ (string_of_int n) ^ "]")
    | ManualEqopt, Decisional -> print_string " [manual]"
    | StdEqopt, Computational -> print_string " [computational]"
    | PrioEqopt n, Computational -> print_string (" [" ^ (string_of_int n) ^ "] [computational]")
    | ManualEqopt, Computational -> print_string " [manual, computational]"
  end;
  print_string "\n";
  display_eqmember m2;
  print_newline()

let display_equiv_with_name (((n,_,_,_,_,_),_) as eq) =
  match n with
    NoName -> display_equiv eq
  | _ -> display_eqname n

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

let rec len_num n =
  if n > 9 then 1 + len_num (n / 10) else 1

let occ_space() =
  print_string (String.make (len_num (!Terms.max_occ) + 2) ' ')

let rec display_process indent p = 
  if (!display_occurrences) || (List.memq p.i_occ (!useful_occs)) then
    begin
      print_string (String.make ((len_num (!Terms.max_occ)) - (len_num p.i_occ)) ' ');
      print_string "{";
      print_int p.i_occ;
      print_string "}"
    end
  else
    occ_space();
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
	    occ_space();
	    print_string (indent^"))\n");
	| p::l ->
	    display_process (indent^"  ") p;
	    occ_space();
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
  if (!display_occurrences) || (List.memq p.p_occ (!useful_occs)) then
    begin
      print_string (String.make ((len_num (!Terms.max_occ)) - (len_num p.p_occ)) ' ');
      print_string "{";
      print_int p.p_occ;
      print_string "}"
    end
  else
    occ_space();
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
	  occ_space();
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
	  occ_space();
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
	    occ_space();
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
	  occ_space();
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
		    occ_space();
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
	      occ_space();
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
      occ_space();
      print_string (indent ^ "(\n");
      display_oprocess (indent ^ "  ") p;
      occ_space();
      print_string (indent ^ ")\n")
    end
  else
    display_oprocess (indent ^ "  ") p


let display_process p =
  display_process "" p;
  print_newline()
	
(* Instructions *)

let display_rem_set = function
    All -> print_string "all binders"
  | OneBinder b -> 
      print_string "binder ";
      display_binder b
  | Minimal -> 
      print_string "useless"
  | FindCond -> 
      print_string "findcond"

let display_move_set = function
    MAll -> print_string "all binders"
  | MNoArrayRef -> print_string "binders without array references"
  | MNew -> print_string "all new's"
  | MNewNoArrayRef -> print_string "new's without array references"
  | MLet -> print_string "all let's"
  | MOneBinder b -> 
      print_string "binder ";
      display_binder b

let display_bl_assoc bl_assoc =
  display_list display_binder bl_assoc

let display_user_info = function
    VarList(l,stop) ->
      display_list display_binder l;
      if stop then print_string "."
  | Detailed(vmopt,tmopt) ->
      begin
      match vmopt with
	None -> ()
      | Some(vm,vl,stop) ->
	  print_string "variables: ";
	  display_list (fun (b1,b2) -> display_binder b1; print_string " -> "; display_binder b2) vm;
	  if vm != [] && vl != [] then print_string ", ";
	  display_list display_binder vl;
	  if stop then print_string ".";
	  if tmopt != None then print_string ";"
      end;
      begin
      match tmopt with
	None -> ()
      | Some(tm,stop) ->
	  print_string "terms: ";
	  display_list (fun (occ,t) -> print_int occ; print_string " -> "; display_term t) tm;
	  if stop then print_string "."
      end
	      
    
let display_with_user_info user_info =
  match user_info with
    VarList([],_) | Detailed((None | Some([],[],_)), (None | Some([],_))) -> ()
  | _ ->
      print_string " with ";
      display_user_info user_info


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

let rec get_initial_game s =
  match s.prev_state with
    None -> s.game
  | Some(_,_,_,s') -> get_initial_game s'
      
let display_query3 = function
  | QSecret (b,pub_vars,onesession) ->
      if onesession then print_string "one-session ";
      print_string "secrecy of "; display_binder b;
      display_pub_vars pub_vars
  | AbsentQuery | QEquivalenceFinal _ ->
      Parsing_helper.internal_error "AbsentQuery and QEquivalenceFinal should have been handled"
  | QEquivalence(state,pub_vars) ->
      let g' = get_initial_game state in
      if g'.game_number = -1 then
	print_string "indistinguishability from other input game"
      else
	print_string ("indistinguishability from game " ^
		      (string_of_int g'.game_number));
      display_pub_vars pub_vars      
  | QEventQ(t1,t2, pub_vars) -> 
      display_query1 t1; 
      print_string " ==> ";
      display_query2 t2;
      display_pub_vars pub_vars
	
let get_game_id g =
  if g.game_number = -1 then 
    "[game not shown yet]" 
  else 
    string_of_int g.game_number

let display_query (q,g) = 
  match q with 
    AbsentQuery -> 
      print_string "indistinguishability from the final game"
  | QEquivalence (state, pub_vars) ->
      let g' = get_initial_game state in
      if g.game_number = -1 || g'.game_number = -1 then
	print_string "indistinguishability between two input games"
      else
	print_string ("indistinguishability between game " ^
		      (string_of_int g.game_number) ^
		      " and game " ^
		      (string_of_int g'.game_number));
      display_pub_vars pub_vars
  | QEquivalenceFinal(g', pub_vars) ->
      print_string ("indistinguishability from game " ^ (get_game_id g')); 
      display_pub_vars pub_vars
  | _ ->
      display_query3 q;
      if g.game_number <> 1 then
	print_string (" in game " ^ (get_game_id g))  

let display_instruct = function
    ExpandIfFindGetInsert -> print_string "expand get, insert, if, let, find"
  | Simplify [] -> print_string "simplify"
  | Simplify l -> 
      print_string "simplify with collision elimination at ";
      display_list print_string l
  | GlobalDepAnal (b,l) -> 
      print_string "global dependency analysis on ";
      display_binder b;
      if l != [] then
	begin
	  print_string " with collision elimination at ";
	  display_list print_string l
	end
  | MoveNewLet s -> print_string "move "; display_move_set s
  | RemoveAssign r -> print_string "remove assignments of "; display_rem_set r
  | SArenaming b -> 
      print_string "SA rename ";
      display_binder b
  | CryptoTransf(e, user_info) -> 
      print_string "equivalence ";
      display_equiv_with_name e;
      display_with_user_info user_info
  | InsertEvent(s,occ) ->
      print_string ("insert event " ^ s ^ " at occurrence " ^ (string_of_int occ))
  | InsertInstruct(s,ext_s,occ,ext_o) ->
      print_string ("insert instruction " ^ s ^ " at occurrence " ^ (string_of_int occ))
  | ReplaceTerm(s,ext_s,occ,ext_o) ->
      print_string ("replace term at occurrence " ^ (string_of_int occ) ^ " with " ^ s)
  | MergeArrays(bll, m) ->
      print_string "merge variables ";
      display_list (fun bl -> 
	print_string "("; 
	display_list (fun (b,_) -> display_binder b) bl;
	print_string ")") bll;
      begin
	match m with
	  MNoBranchVar -> print_string " (no branch variables)"
	| MCreateBranchVar -> ()
	| MCreateBranchVarAtProc _ -> print_string " (branch variables created at given processes)"
	| MCreateBranchVarAtTerm _ -> print_string " (branch variables created at given terms)"
      end
  | MergeBranches ->
      print_string "merge branches"
  | Proof ql -> 
      print_string "proof of ";
      display_list (fun (q, set) -> 
	display_query q; 
	if set != [] then
	  begin
	    print_string " up to probability ";
	    display_set set
	  end) ql
      

exception NotBoundEvent of funsymb * game

type query_specif =
    InitQuery of query
  | QEvent of funsymb

let equal_qs (qs1,g1) (qs2,g2) =
  (g1 == g2) && (match qs1,qs2 with
    InitQuery _, InitQuery _ -> true
  | QEvent f1, QEvent f2 -> f1 == f2
  | _ -> false)

(* A proof tree is a tree in which
   - nodes are games (field pt_game below) 
   - edges correspond to game transformations. These edges are labelled with
       * i: instruct, the instruction performed to obtain the son from the current game
       * p: setf list, the probability difference
       * pt_son: proof_tree, the obtained son
       * ql: (query_specif * game) list ref, the list of properties proved by going through the
         considered edge.
   We have a tree and not just a list of games, because events may be introduced by Shoup's lemma,
   and proved later to have negligible probability, so we may need to prove several properties
   at once. Moreover, these properties may be proved using different sequences of games, thus
   leading to a tree.
   The last edge (the one that proves a property) already deals with a single property.
   Other edges may be shared between the proofs of several properties. *)

type proof_tree =
    { pt_game : game;
      mutable pt_sons : (instruct * setf list * proof_tree * (query_specif * game) list ref) list }

(* For debugging *)

let rec display_proof_tree indent pt =
  print_string (indent ^ "Game " ^ (string_of_int pt.pt_game.game_number) ^"\n");
  let display_son indent_next (i, p, pt_son, ql) =
    begin
      match i with
	CryptoTransf(((_,_,_,_,_,Decisional),_),_) -> print_string (indent ^ "- Decisional step\n")
      |	_ -> print_string (indent ^ "- Computational step\n")
    end;
    print_string (indent ^ "- Probability: ");
    display_set p;
    print_newline();
    print_string (indent ^ "- Properties to prove: ");
    display_list (function
	(InitQuery _, _) -> print_string "Initial query"
      |	(QEvent f, g) -> print_string "Event "; print_string f.f_name; 
	  print_string " in game "; print_int g.game_number) (!ql);
    print_newline();    
    display_proof_tree indent_next pt_son
  in
  match pt.pt_sons with
    [] -> print_string (indent ^ "No son\n") 
  | [s] -> 
      print_string (indent ^ "Son:\n"); 
      display_son indent s
  | _ ->
      print_string (indent ^ "Sons:\n");
      List.iter (display_son (indent ^ "  ")) pt.pt_sons

(* Build the proof tree *)

let build_proof_tree ((q0,g0) as q) p s =
  let pt_init = { pt_game = g0;
		  pt_sons = [] }
  in
  let proof_tree_table = ref [(g0, pt_init)] in
  (* We need to ignore "Proof" steps because they do not change the game at all
     (the game is physically the same), which causes bugs if we don't ignore 
     this step *)
  let rec father_ignore_proof s =
    match s.prev_state with
      None -> None
    | Some(Proof _,p,_,s') ->
	if p != [] then Parsing_helper.internal_error "Proof steps should have 0 probability";
	father_ignore_proof s'
    | x -> x
  in
  (* Add a new query [q] in the list of proved properties, in a part of the proof tree that is
     already built *)
  let rec add_query q pt_cur s =
    if s.game == snd q then () else 
    match father_ignore_proof s with
      None -> ()
    | Some (i,p,_,s') ->
	try
	  let pt_father = List.assq s'.game (!proof_tree_table) in
	  let (_,_,_,queries) = List.find (fun (_,_,pt,_) -> pt == pt_cur) pt_father.pt_sons in
	  if not (List.exists (equal_qs q) (!queries)) then
	    queries := q :: (!queries);
	  add_query q pt_father s'
	with Not_found ->
	  Parsing_helper.internal_error "This game should always be found"
  in
  (* Build the proof tree for state [s], proving property [q]. [sons_to_add] is a list
     of sons (edges, in fact) to add to the proof corresponding to state [s]. 
     [sons_to_add] is either an empty list (when [s] is the last state, the one that proves [q]),
     or a list containing one element (the next step in the proof of [q]). *)
  let rec build_pt_rec sons_to_add q s =
    try
      let pt_cur = List.assq s.game (!proof_tree_table) in
      pt_cur.pt_sons <- sons_to_add @ pt_cur.pt_sons;
      (* print_string ("Found " ^ (string_of_int s.game.game_number) ^ "; adding sons ");
      display_list (fun (_,_,pt,_) -> print_int pt.pt_game.game_number) sons_to_add;
      print_newline(); *)
      add_query q pt_cur s
    with Not_found ->
      let pt_cur = { pt_game = s.game;
		     pt_sons = sons_to_add }
      in
      proof_tree_table := (s.game, pt_cur) :: (!proof_tree_table);
      (* print_string ("Added game " ^ (string_of_int s.game.game_number) ^ " with sons ");
      display_list (fun (_,_,pt,_) -> print_int pt.pt_game.game_number) sons_to_add;
      print_newline(); *)
      match father_ignore_proof s with
	None -> Parsing_helper.internal_error "Initial game should already have been entered in the proof tree"
      |	Some(i,p,_,s) ->
	  build_pt_rec [(i,p,pt_cur, ref [q])] q s;
	  List.iter (function 
	      SetProba _ -> ()
	    | SetEvent(f,g, pub_vars, popt') ->
		  (* Get the proof of the property "Event f is not executed in game g" *)
                match !popt' with
		  None -> raise (NotBoundEvent(f,g))
		| Some(p',s') ->
		    (* Build the query that test for event f in game g *)
		    let idx = Terms.build_term_type Settings.t_bitstring (FunApp(Settings.get_tuple_fun [], [])) in
		    let t = Terms.build_term_type Settings.t_bool (FunApp(f, [idx])) in
		    let q' = (QEventQ([false, t], QTerm (Terms.make_false()), pub_vars), g) in

		let sons_to_add =
		  let pt_final_event_f_in_g = { pt_game = { proc = Terms.iproc_from_desc Nil; 
							    game_number = -1;
							    current_queries = [] } (* dummy_game *);
						pt_sons = [] }
		  in
		  [(Proof [q',p'], p', pt_final_event_f_in_g, ref[QEvent f, g])]
		in
		build_pt_rec sons_to_add (QEvent f, g) s'
		  ) p
  in
  let sons_to_add =
    let pt_final_proof = { pt_game = { proc = Terms.iproc_from_desc Nil; 
				       game_number = -1;
				       current_queries = [] } (* dummy_game *);
			   pt_sons = [] }
    in
    [(Proof [q,p], p, pt_final_proof, ref [InitQuery q0, g0])]
  in
  build_pt_rec sons_to_add (InitQuery q0,g0) s;
  pt_init


let display_qevent = function
    QEvent f,_ -> print_string f.f_name
  | _ -> Parsing_helper.internal_error "QEvent expected"

let rec display_or_list = function
    [] -> ()
  | [a] -> display_qevent a
  | (a::l) -> display_qevent a; print_string " || ";
      display_or_list l

let display_adv ql game = 
  let (ql_no_initq, ql_initq) = List.partition (function InitQuery _,_ -> false | _ -> true) ql in
  match ql_initq with
    [InitQuery q0,g0] ->
      print_string "Adv[Game ";
      print_int game.game_number;
      print_string ": ";
      display_query (q0,g0);
      if ql_no_initq != [] then
	begin
	  print_string ", ";
	  display_or_list ql_no_initq
	end;
      print_string "]"
  | [] ->
      print_string "Pr[Game ";
      print_int game.game_number;
      print_string ": ";
      display_or_list ql_no_initq;
      print_string "]"
  | _ -> Parsing_helper.internal_error "Bad query list in display_adv"


let is_secrecy = function
     (InitQuery (QSecret _), _) -> true
  | _ -> false

let double_if_needed ql p =
  if List.exists is_secrecy ql then p @ p else p

let rec poly_from_set = function
    [] -> Polynom.zero
  | (SetProba r)::l -> Polynom.sum (Polynom.probaf_to_polynom r) (poly_from_set l)
  | _ -> Parsing_helper.internal_error "SetEvent should have been evaluated"

let proba_from_set s =
  Polynom.polynom_to_probaf (poly_from_set s)

let proba_from_set_may_double (q,g) s =
  match q with
    QSecret _ ->
      (* For secrecy, we need to double the probability *)
      let p = poly_from_set s in
      Polynom.polynom_to_probaf (Polynom.sum p p)
  | _ ->
      Polynom.polynom_to_probaf (poly_from_set s)

let rec evaluate_proba start_queries start_game above_proba ql pt =
  (* Sanity check: all elements of ql must occur in some edge in pt *)
  List.iter (fun qs -> 
    if not (List.exists (fun (_,_,_,ql_ref) -> 
      List.exists (equal_qs qs) (!ql_ref)
	) pt.pt_sons) then
      Parsing_helper.internal_error "Missing property in evaluate_proba"
	) ql;
  (* Sanity check: the ql_ref are disjoint *)
  let check_disjoint (_,_,_,ql_ref1) (_,_,_,ql_ref2) =
    if List.exists (fun qs1 -> List.exists (equal_qs qs1) (!ql_ref2)) (!ql_ref1) then
      Parsing_helper.internal_error "ql_ref not disjoint"
  in
  let rec check_disjoint_l pt1 = function
      [] -> ()
    | (pt2::r) -> check_disjoint pt1 pt2; check_disjoint_l pt1 r
  in
  let rec check_disjoint_ll = function
      [] -> ()
    | (pt1::ptl) -> check_disjoint_l pt1 ptl; check_disjoint_ll ptl
  in
  check_disjoint_ll pt.pt_sons;
  (* Take into account tree branching (several sons): split ql according to what
     each son proves *)
  match pt.pt_sons with
    [(i,p,pt_son,ql_ref)] when (match i with Proof _ -> false | _ -> true) &&
       (List.for_all (function SetProba _ -> true | SetEvent _ -> false) p) ->
	 evaluate_proba start_queries start_game ((double_if_needed ql p) @ above_proba) ql pt_son
  | _ -> 
      let ql_list = 
	List.map (fun (i,p,pt_son,ql_ref) ->
	  List.filter (fun qs -> List.exists (equal_qs qs) ql) (!ql_ref)) pt.pt_sons
      in
      display_adv start_queries start_game;
      print_string " <= ";
      display_proba 0 (proba_from_set above_proba);
      List.iter (fun ql_i ->
	print_string " + ";
	display_adv ql_i pt.pt_game) ql_list;
      print_newline();
      above_proba @ 
  (List.concat (List.map (fun (i,p,pt_son,ql_ref) ->
    let ql' = List.filter (fun qs -> List.exists (equal_qs qs) ql) (!ql_ref) in
    let rec compute_full_query_list = function
	[] -> ql'
      |	(SetProba _)::l -> compute_full_query_list l
      |	(SetEvent(f,g,pub_vars,_))::l -> (QEvent f, g) :: (compute_full_query_list l)
    in
    (* One transformation can consist of an arbitrary syntactic or cryptographic
       transformation, that follows a series of event insertions (Shoup lemma).
       In practice, the transformation is either:
       - an event insertion alone
       - or a cryptographic transformation with an event insertion (DDH).
         The event insertion is indeed done before DDH.
       - or a transformation without event insertion. *)
    let ql'' = compute_full_query_list p in
    let proba_p = List.filter (function SetProba _ -> true | SetEvent _ -> false) p in
    match i with
      Proof pl ->
	(* The desired property is proved *)
	begin
	  match pl,ql' with
	    [q,_],[q'] -> 
	      let p = double_if_needed ql' proba_p in
	      display_adv ql' pt.pt_game;
	      print_string " <= ";
	      display_proba 0 (proba_from_set p);
	      print_newline();
	      p
	  | _ -> Parsing_helper.internal_error "unexpected Proof element in proof tree"
	end
    | _ -> 
	(* We consider the whole set of queries ql' at once, 
	   and avoid counting several times the same events. *)
	let p = double_if_needed ql' proba_p in
	if ql'' == ql' then
	  (* No event introduced *)
	  evaluate_proba ql' pt.pt_game p ql'' pt_son
	else
	  begin
	    (* An event has been introduced, display its probability separately *)
	    display_adv ql' pt.pt_game;
	    print_string " <= ";
	    display_proba 0 (proba_from_set p);
	    print_string " + ";
	    display_adv ql'' pt_son.pt_game;
	    print_newline();
	    p @ (evaluate_proba ql'' pt_son.pt_game [] ql'' pt_son)
	  end
    ) pt.pt_sons))

let compute_proba_internal ((q0,g) as q) p s =
  let pt = build_proof_tree q p s in
  (* display_proof_tree "" pt; *)
  let start_queries = [InitQuery q0, g] in
  evaluate_proba start_queries g [] start_queries pt  

let compute_proba ((q0,g) as q) p s =
  match q0 with
  | QEquivalence(state,pub_vars) ->
     print_string ("Game "^(string_of_int s.game.game_number)^" is the same as game "^(string_of_int state.game.game_number));
     if p <> [] then
       begin
         print_string " up to probability ";
         display_proba 0 (proba_from_set p)
       end;
     print_string ".\n";
     let g' = get_initial_game state in
     (compute_proba_internal (QEquivalenceFinal(s.game, pub_vars),g) [] s) @ p @
     (compute_proba_internal (QEquivalenceFinal(state.game, pub_vars),g') [] state)
  | AbsentQuery ->
      compute_proba_internal (QEquivalenceFinal(s.game, []), g) p s
  | _ -> compute_proba_internal q p s
    
let display_pat_simp t =
  print_string (match t with 
    DEqTest -> " (equality test)"
  | DExpandTuple -> " (tuple expanded)"
  | DImpossibleTuple -> " (tuple matching always fails)")

let display_pat_simp_list l =
  display_list (fun (pat, t) ->
    print_string "pattern ";
    display_pattern pat;
    display_pat_simp t) l
  
    
let rec find_l def_list n = function
    [] -> print_string "[not found]"
  | (bl',def_list',t',p1')::l ->
      if def_list == def_list' then
	print_int n
      else
	find_l def_list (n+1) l

let get_find_branch p (bl,def_list,t,p1) =
  match p with
    DProcess {p_desc = Find(l,_,_)} -> find_l def_list 1 l
  | DTerm {t_desc = FindE(l,_,_)} -> find_l def_list 1 l
  | _ -> Parsing_helper.internal_error "Find expected in get_find_branch"

let get_nbr_find_branch p =
  match p with
    DProcess {p_desc = Find(l,_,_)} -> List.length l
  | DTerm {t_desc = FindE(l,_,_)} -> List.length l
  | _ -> Parsing_helper.internal_error "Find expected in get_find_branch"
  
	
let display_simplif_step = function
    SReplaceTerm(t,t') -> 
      print_string "    - Replaced ";
      display_term t;
      print_string " with ";
      display_term t';
      print_string " at ";
      print_int t.t_occ;
      print_newline()
  | STestTrue(p) ->
      print_string "    - Test at ";
      print_int (Terms.occ_from_pp p);
      print_string " always true\n"
  | STestFalse(p) ->
      print_string "    - Test at ";
      print_int (Terms.occ_from_pp p);
      print_string " always false\n"
  | STestMerge(p) ->
      print_string "    - Merge branches of test at ";
      print_int (Terms.occ_from_pp p);
      print_string "\n"
  | STestOr(p) ->
      print_string "    - Expand || in test at ";
      print_int (Terms.occ_from_pp p);
      print_string "\n"
  | STestEElim(t) ->
      print_string "    - Transformed test at ";
      print_int t.t_occ;
      print_string " into a logical formula\n"
  | SFindBranchRemoved(p,br) -> 
      print_string "    - Remove branch ";
      get_find_branch p br;
      print_string " in find at ";
      print_int (Terms.occ_from_pp p);
      print_newline()
  | SFindSingleBranch(p,br) ->
      print_string "    - A single branch always succeeds in find at ";
      print_int (Terms.occ_from_pp p);
      print_newline()
  | SFindRemoved(p) ->
      print_string "    - Find at ";
      print_int (Terms.occ_from_pp p);
      print_string " removed (else branch kept if any)\n"
  | SFindElseRemoved(p) ->
      print_string "    - Remove else branch of find at ";
      print_int (Terms.occ_from_pp p);
      print_newline()
  | SFindBranchMerge(p, brl) ->
      if get_nbr_find_branch p = List.length brl then
	print_string "    - Merge all branches of find at "
      else
	begin
	  print_string "    - Merge branches ";
	  display_list (get_find_branch p) brl;
	  print_string " with else branch of find at ";
	end;
      print_int (Terms.occ_from_pp p);
      print_newline()
  | SFindDeflist(p, def_list, def_list') ->
      if def_list == [] then
	print_string "    - Replaced an empty defined condition"
      else
	begin
	  print_string "    - Replaced defined condition ";
	  display_list (fun (b,l) -> display_var b l) def_list
	end;
      print_string " with ";
      if def_list' == [] then
	print_string "an empty condition"
      else 
	display_list (fun (b,l) -> display_var b l) def_list';
      print_string " in find at ";
      print_int (Terms.occ_from_pp p);
      print_newline()
  | SFindinFindCondition(p, t) ->
      print_string "    - Simplified find at ";
      print_int t.t_occ;
      print_string " in condition of find at ";
      print_int (Terms.occ_from_pp p);
      print_newline()
  | SFindinFindBranch(p,p') ->
      print_string "    - Simplified find at ";
      print_int (Terms.occ_from_pp p');
      print_string " in branch of find at ";
      print_int (Terms.occ_from_pp p);
      print_newline()
  | SFindtoTest(p) ->
      print_string "    - Transformed find at ";
      print_int (Terms.occ_from_pp p);
      print_string " into a test\n"
  | SFindIndexKnown(p, br, subst) ->
      print_string "    - In branch ";
      get_find_branch p br;
      print_string " of find at ";
      print_int (Terms.occ_from_pp p);
      print_string ", substituting ";
      display_list (fun (b,t) -> display_binder b; print_string " with ";
        display_term t) subst;
      print_newline() 
  | SLetElseRemoved(p) ->
      print_string "    - Remove else branch of let at ";
      print_int (Terms.occ_from_pp p);
      print_newline()
  | SLetRemoved(p) ->
      print_string "    - Remove let at ";
      print_int (Terms.occ_from_pp p);
      print_newline()
  | SLetSimplifyPattern(p, l) -> 
      print_string "    - Simplify ";
      display_pat_simp_list l;
      print_string " at ";
      print_int (Terms.occ_from_pp p);
      print_newline()

  | SResRemoved(p) ->
      print_string "    - Remove random number generation at ";
      print_int (Terms.occ_from_pp p);
      print_newline()
  | SResToAssign(p) ->
      print_string "    - Transform unused random number generation at ";
      print_int (Terms.occ_from_pp p);
      print_string " into constant assignment";
      print_newline()

let display_detailed_ins = function
    DExpandGetInsert(t) -> 
      print_string "  - Expand get/insert for table ";
      display_table t;
      print_newline()
  | DExpandIfFind ->
      print_string "  - Expand if/find/let\n"
  | DSimplify(l) ->
      print_string "  - Simplification pass\n";
      List.iter display_simplif_step (List.rev l)
  | DGlobalDepAnal(b,coll_elim) ->
      print_string "  - Global dependency analysis on ";
      display_binder b;
      if coll_elim != [] then
	begin
	  print_string " with collision elimination at ";
	  display_list print_string coll_elim
	end;
      print_newline()
  | DLetSimplifyPattern(let_p, l) ->
      print_string "  - Simplify ";
      display_pat_simp_list l;
      print_string " at "; 
      print_int (Terms.occ_from_pp let_p);
      print_newline()
  | DRemoveAssign(b, def_ch, usage_ch) ->
      print_string "  - Remove assignments on ";
      display_binder b;
      print_string (
	match def_ch with
	  DRemoveDef -> " (definition removed, "
	| DKeepDefPoint -> " (definition point kept, "
	| DKeepDef -> " (definition kept, ");
      print_string (
        match usage_ch with
	  DRemoveAll -> "all usages removed)\n"
	| DRemoveNonArray -> "array references kept)\n")
  | DSArenaming(b, bl) ->
      print_string "  - Rename variable ";
      display_binder b;
      print_string " into ";
      display_list display_binder bl;
      print_newline()
  | DMoveNew(b) ->
      print_string "  - Move random number generation ";
      display_binder b;
      print_newline()
  | DMoveLet(b) ->
      print_string "  - Move assignment to ";
      display_binder b;
      print_newline()      
  | DCryptoTransf(e, user_info) ->
      print_string "  - Equivalence ";
      display_equiv_with_name e;
      display_with_user_info user_info;
      print_newline()
  | DInsertEvent _  | DInsertInstruct _ 
  | DReplaceTerm _  | DMergeArrays _ ->
      (* Don't display anything since the detailed description is the
	 same as the high level one *)
      ()
  | DMergeBranches(p,l) ->
      begin
	match (p.p_desc, l) with
	  (Test _), _ ->
	    print_string "  - Merge branches of test at ";
	    print_int p.p_occ
	| (Let _), _ ->
	    print_string "  - Merge branches of let at ";
	    print_int p.p_occ
	| (Find(l0,_,_), l) when List.length l = List.length l0 + 1 ->
	    print_string "  - Merge all branches of find at ";
	    print_int p.p_occ	    
	| (Find _), p1::r ->
	    print_string "  - Merge branch(es) at ";
	    display_list (fun p2 -> print_int p2.p_occ) r;
	    print_string " with else branch of find at ";
	    print_int p.p_occ
	| _ -> Parsing_helper.internal_error "unexpected merge"
      end;
      print_newline()            
  | DMergeBranchesE(t,l) ->
      begin
	match (t.t_desc, l) with
	  (TestE _), _ ->
	    print_string "  - Merge branches of test at ";
	    print_int t.t_occ
	| (LetE _), _ ->
	    print_string "  - Merge branches of let at ";
	    print_int t.t_occ
	| (FindE(l0,_,_), l) when List.length l = List.length l0 + 1 ->
	    print_string "  - Merge all branches of find at ";
	    print_int t.t_occ	    
	| (FindE _), t1::r ->
	    print_string "  - Merge branch(es) at ";
	    display_list (fun t2 -> print_int t2.t_occ) r;
	    print_string " with else branch of find at ";
	    print_int t.t_occ
	| _ -> Parsing_helper.internal_error "unexpected merge"
      end;
      print_newline()      

let mark_useful_occ_p p = 
  useful_occs := p.p_occ :: (!useful_occs)
let mark_useful_occ_t t = 
  useful_occs := t.t_occ :: (!useful_occs)
let mark_useful_occ_pp p = 
  useful_occs := (Terms.occ_from_pp p) :: (!useful_occs)

let mark_occs_simplif_step f_t = function
    SReplaceTerm(t,_) | STestEElim(t) -> f_t t
  | STestTrue(p) | STestFalse(p) | STestMerge(p) | STestOr(p) 
  | SFindBranchRemoved(p,_) | SFindSingleBranch(p,_) 
  | SFindRemoved(p) | SFindElseRemoved(p) | SFindBranchMerge(p, _) 
  | SFindtoTest(p) | SFindIndexKnown(p, _,_) 
  | SFindDeflist(p, _,_)
  | SLetElseRemoved(p) | SLetRemoved(p) | SLetSimplifyPattern(p, _) 
  | SResRemoved(p) | SResToAssign(p) -> mark_useful_occ_pp p
  | SFindinFindCondition(p, t) -> mark_useful_occ_pp p; f_t t
  | SFindinFindBranch(p,p') -> mark_useful_occ_pp p; mark_useful_occ_pp p'

let mark_occs1 f_p f_t = function
    DExpandGetInsert(_) | DExpandIfFind | DGlobalDepAnal _ 
  | DRemoveAssign _ | DSArenaming _ | DMoveNew(_) | DMoveLet(_) 
  | DCryptoTransf _ | DMergeArrays _ -> ()
  | DInsertEvent (_,occ)  | DInsertInstruct (_,occ) | DReplaceTerm (_,_,occ) ->
      useful_occs := occ :: (!useful_occs)
  | DSimplify(l) ->
      List.iter (mark_occs_simplif_step f_t) l
  | DLetSimplifyPattern(let_p, _) -> mark_useful_occ_pp let_p
  | DMergeBranches(p,l) ->
      f_p p;
      begin
	match (p.p_desc, l) with
	  (Test _), _ | (Let _), _ -> ()
	| (Find(l0,_,_), l) when List.length l = List.length l0 + 1 -> ()
	| (Find _), p1::r ->
	    List.iter f_p r
	| _ -> Parsing_helper.internal_error "unexpected merge"
      end
  | DMergeBranchesE(t,l) ->
      f_t t;
      begin
	match (t.t_desc, l) with
	  (TestE _), _ | (LetE _), _ -> ()
	| (FindE(l0,_,_), l) when List.length l = List.length l0 + 1 -> ()
	| (FindE _), p1::r ->
	    List.iter f_t r
	| _ -> Parsing_helper.internal_error "unexpected merge"
      end

let mark_occs ins = 
  useful_occs := [];
  List.iter (mark_occs1 mark_useful_occ_p mark_useful_occ_t) ins

let already_displayed = ref []

let rec display_state ins_next s =
  if List.memq s (!already_displayed) then
    begin
      print_string "===================== New branch =====================\n";
      print_string "Game "; 
      print_int s.game.game_number;
      print_string " [Already displayed]\n";
    end
  else
    begin
      already_displayed := s :: (!already_displayed);
      match s.prev_state with
	None -> 
	  if s.game.game_number = -1 then
	    begin
	      incr max_game_number;
	      s.game.game_number <- !max_game_number
	    end;
	  print_string "Initial state\n";
	  print_string "Game "; 
	  print_int s.game.game_number;
	  print_string " is\n";
	  mark_occs ins_next;
	  display_process s.game.proc;
	  useful_occs := []
      | Some (Proof ql, p, _, s') ->
	  display_state ins_next s';
	  print_newline();
	  List.iter (fun ((q,g), p') -> 
	    if p' != [] then
	      begin
		print_string "Proved ";
		display_query (q, s'.game);
		print_string " up to probability ";
		display_proba 0 (proba_from_set_may_double (q, s'.game) p');
		print_newline()
	      end
	    else
	      begin
		print_string "Proved ";
		display_query (q, s'.game);
		print_newline()
	      end
		) ql;
	  if p != [] then
	    Parsing_helper.internal_error "Proof step should have empty set of excluded traces"
      | Some (i,p,ins,s') ->
	  display_state ins s';
	  print_newline();
      (* Record the game number *)
	  if s.game.game_number = -1 then
	    begin
	      incr max_game_number;
	      s.game.game_number <- !max_game_number
	    end;
	  print_string "Applying ";
	  display_instruct i;
	  if p != [] then
	    begin
	      print_string " [probability ";
	      display_set p;
	      print_string "]"
	    end;
	  print_newline();
	  List.iter display_detailed_ins (List.rev ins);
	  print_string "yields\n\n";
	  print_string "Game "; 
	  print_int s.game.game_number;
	  print_string " is\n";
	  mark_occs ins_next;
	  display_process s.game.proc;
	  useful_occs := []
    end


let get_initial_queries s =
  (get_initial_game s).current_queries

let rec get_all_states_from_sequence accu g s =
  if s.game == g then accu else
  match s.prev_state with
    None -> accu
  | Some(_, proba, _, s') ->
      get_all_states_from_sequence (get_all_states_from_proba accu proba) g s'

and get_all_states_from_proba accu = function
    [] -> accu
  | (SetProba _)::r -> get_all_states_from_proba accu r
  | (SetEvent(f,g,pub_vars,poptref)) :: r  ->
      let accu' = get_all_states_from_proba accu r in
      match !poptref with
	None -> accu'
      |	Some(p,s') -> get_all_states_from_sequence (s'::accu') g s'

let rec get_all_states_from_queries = function
    [] -> []
  | ((q,g), poptref,_)::r ->
      let accu = get_all_states_from_queries r in
      let accu' =
	match q with
	| QEquivalence(s',_) -> s' :: accu
	| _ -> accu
      in
      match !poptref with
	None -> accu'
      |	Some(p,s') -> get_all_states_from_sequence (s'::accu') g s'

let rec remove_dup seen_list r s =
  let seen_list' = List.filter (fun s' -> s' != s) seen_list in
  let r' = List.filter (fun s' -> s' != s) r in
  match s.prev_state with
    None -> (seen_list', r')
  | Some(_,_,_,s') ->
      remove_dup seen_list' r' s'

let rec remove_duplicate_states seen_list = function
    [] -> seen_list
  | (s::r) ->
      let (seen_list', r') = remove_dup seen_list r s in
      remove_duplicate_states (s::seen_list') r'

let display_conclusion s =
  let initial_queries = get_initial_queries s in
  (* List the unproved queries *)
  let rest = List.filter (function (q, poptref,_) -> (!poptref) == None) initial_queries in
  let rest' = List.filter (function (AbsentQuery, _),_,_ -> false | _ -> true) rest in
  if rest = [] then
    print_string "All queries proved.\n"
  else if rest' != [] then
    begin
      print_string "RESULT Could not prove ";
      display_list_sep "; " (fun (q, _,_) -> display_query q) rest;
      print_string ".\n"
    end

	
let display_state s =
  (* Display the proof tree *)
  times_to_display := [];
  already_displayed := [];
  let initial_queries = get_initial_queries s in
  let states_needed_in_queries = get_all_states_from_queries initial_queries in
  let states_to_display = remove_duplicate_states [] (s::states_needed_in_queries) in
  List.iter (fun s -> display_state [] s) states_to_display;  
  
  (* Display the probabilities of proved queries *)
  List.iter (fun (q,poptref,_) ->
    match !poptref with
      None -> ()
    | Some(p,s') -> 
        let p'' = compute_proba q p s' in
        print_string "RESULT Proved ";
        display_query q;
	if p'' != [] then
	  begin
            print_string " up to probability ";
            display_proba 0 (proba_from_set p'')
	  end;
	print_newline()
    ) initial_queries;

  (* Display the runtimes *)
  List.iter (fun (g,t) ->
    print_string "RESULT time(context for game ";
    print_int g.game_number;
    print_string ") = ";
    display_proba 0 t;
    print_newline()
    ) (List.rev (!times_to_display));
  times_to_display := [];

  (* List the unproved queries *)
  display_conclusion s

