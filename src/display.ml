open Types

(* Allow changing the output destination *)

type dest_t =
  | File of out_channel
  | Func of (string -> unit)
  
let dest = ref (File stdout)
    
let print_string s =
  match !dest with
  | File output -> output_string output s
  | Func f -> f s

let print_int i =
  print_string (string_of_int i)
    
let print_float f =
  print_string (Printf.sprintf "%g" f)

let print_newline() =
  print_string "\n";
  match !dest with
  | File output -> flush output
  | Func _ -> ()
    
let file_out filename ext f =
  let old_dest = !dest in
  let file =
    try
      open_out filename
    with Sys_error s ->
      raise (Parsing_helper.Error("Cannot open file " ^ filename ^ ": " ^ s, ext))
  in
  dest := File file;
  try 
    f();
    close_out file;
    dest := old_dest
  with x ->
    close_out file;
    dest := old_dest;
    raise x

let fun_out out_f f =
  let old_dest = !dest in
  dest := Func out_f;
  try 
    f();
    dest := old_dest
  with x ->
    dest := old_dest;
    raise x

let string_out f =
  let b = Buffer.create 80 in
  fun_out (Buffer.add_string b) f;
  Buffer.contents b
      
type display_occ_t = NoOcc | AllOccs | ProcessOccs      
let display_occurrences = ref NoOcc
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

let display_find_info = function
  | Nothing -> ()
  | Unique -> print_string "[unique] "
  | UniqueToProve e -> print_string ("[unique?"^e.f_name^"] ")

let display_type ty =
  match ty.tcat with
  | Interv n -> 
      print_string " <= ";
      print_string n.pname
  | _ -> 
      print_string ": ";
      print_string ty.tname

	
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
  display_type b.btype

and display_repl_index_with_type b =
  display_repl_index b;
  print_string " <= ";
  print_string (Terms.param_from_type b.ri_type).pname

and display_repl i =
  if (!Settings.front_end) == Settings.Oracles then
    begin
      print_string "foreach ";
      display_repl_index_with_type i;
      print_string " do"
    end
  else
    begin
      print_string "! ";
      display_repl_index_with_type i
    end

and display_restr b =
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
    end

and display_def_list def_list = 
  display_list (fun (b, l) -> display_var b l) def_list
   
and display_findcond (def_list, t1) =
  let cond_printed = ref false in
  if def_list != [] then
    begin
      print_string "defined(";
      display_def_list def_list;
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
	  Std | GuessCst | SepLetFun | Tuple | Event | NonUniqueEvent -> 
	    print_string f.f_name;
	    (* Event functions have replication indexes added at first argument
               Do not display it *)
	    let l = if f.f_cat == Event || f.f_cat == NonUniqueEvent then List.tl l else l in
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
      display_find_info find_info;
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
      display_restr b;
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
  | GetE(tbl, patl, topt, p1, p2, find_info) ->
      print_string "get ";
      display_find_info find_info;
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
    if (!display_occurrences == AllOccs) || (List.memq t.t_occ (!useful_occs)) then
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
    | FunApp({ f_cat = Std | GuessCst | SepLetFun | Tuple | Event | NonUniqueEvent },_) -> false
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

(* Display quantified variables *)

let rec display_binder_list_with_type = function
  | [] -> assert false
  | b::bl ->
      let (same_type, other_type) = List.partition (fun b' -> b'.btype == b.btype) bl in
      display_list display_binder (b::same_type);
      display_type b.btype;
      if other_type != [] then
	begin
	  print_string ", ";
	  display_binder_list_with_type other_type
	end
	       
let display_quantified q bl =
  if bl <> [] then
    begin
      print_string q;
      display_binder_list_with_type bl;
      print_string "; ";
    end

(* Statements *)

let display_statement (bl, t, side_cond) =
  print_string "equation ";
  display_quantified "forall " bl;
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
let _ = Terms.fresh_id "time" (* To make sure we do not use "time" itself as time 
				 identifier since it is reserved for the time of the adversary *)

let get_game_id g =
  if g.game_number = -1 then 
    "[not shown yet]" 
  else 
    string_of_int g.game_number

let display_time_id cat =
  match cat with
  | Game(g) ->
      print_string "time + time(game ";
      print_string (get_game_id g);
      print_string ")"
  | Context(g) -> 
      print_string "time + time(context for game ";
      print_string (get_game_id g);
      print_string ")"
  | Complex -> ()
	
let display_pub_vars pub_vars =
  if pub_vars <> [] then
    begin
      print_string " with public variables ";
      display_list display_binder pub_vars
    end
	
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
  | AbsentQuery ->
      print_string "indistinguishability from the final game"
  | QEquivalenceFinal(g', pub_vars) ->
      print_string ("indistinguishability from game " ^ (get_game_id g')); 
      display_pub_vars pub_vars
  | QEquivalence(state,pub_vars,_) ->
      let g' = get_initial_game state in
      if g'.game_number = -1 then
	print_string "indistinguishability from other input game"
      else
	print_string ("indistinguishability from game " ^
		      (string_of_int g'.game_number));
      display_pub_vars pub_vars      
  | QEventQ(t1,t2, pub_vars) ->
      let (forall, exists) = Terms.collect_vars_corresp t1 t2 in
      display_quantified "forall " forall;
      display_query1 t1; 
      print_string " ==> ";
      display_quantified "exists " exists;
      display_query2 t2;
      display_pub_vars pub_vars
	
let display_query (q,g) = 
  match q with 
    AbsentQuery -> 
      if g.game_number <> 1 then
	print_string ("indistinguishability between game "^(get_game_id g)^" and the final game")
      else
	print_string "indistinguishability between the input game and the final game"
  | QEquivalence (state, pub_vars, _) ->
      let g' = get_initial_game state in
      print_string ("indistinguishability between game " ^
		    (get_game_id g) ^
		    " and game " ^
		    (get_game_id g'));
      display_pub_vars pub_vars
  | QEquivalenceFinal(g', pub_vars) ->
      print_string ("indistinguishability between game " ^
		    (get_game_id g) ^
		    " and game " ^
		    (get_game_id g'));
      display_pub_vars pub_vars
  | _ ->
      display_query3 q;
      if g.game_number <> 1 then
	print_string (" in game " ^ (get_game_id g))  

      
	
let rec display_proba ?(separate_time = false) level = function
    Proba(p,l) -> 
      print_string p.prname;
      if l != [] then
	begin
	  print_string "(";
	  display_list (display_proba ~separate_time 0) l;
	  print_string ")"
	end
  | Count p -> print_string p.pname
  | OCount (c,n) ->
      print_string "#"; 
      if n > 0 then
	begin
	  print_string "(";
	  print_string c.cname;
	  print_string " foreach first ";
	  if n = 1 then
	    print_string "replication)"
	  else
	    print_string ((string_of_int n)^" replications)");
	end
      else
	print_string c.cname
  | Add(x,y) -> 
      if level > 1 then print_string "(";
      display_proba ~separate_time 1 x;
      print_string " + ";
      display_proba ~separate_time 1 y;
      if level > 1 then print_string ")"
  | Sub(x,y) -> 
      if level > 1 then print_string "(";
      display_proba ~separate_time 1 x;
      print_string " - ";
      display_proba ~separate_time 2 y;
      if level > 1 then print_string ")"
  | Max(l) -> 
      print_string "max(";
      display_list (display_proba ~separate_time 0) l;
      print_string ")"
  | Min(l) ->
      print_string "min(";
      display_list (display_proba ~separate_time 0) l;
      print_string ")"
  | Mul(x,y) ->
      if level > 3 then print_string "(";
      display_proba ~separate_time 3 x;
      print_string " * ";
      display_proba ~separate_time 3 y;
      if level > 3 then print_string ")"
  | Power(x,n) ->
      display_proba ~separate_time 5 x;
      print_string "^";
      print_int n
  | Zero -> print_string "0"      
  | Cst n -> print_float n
  | Div(x,y) ->
      if level > 3 then print_string "(";
      display_proba ~separate_time 3 x;
      print_string " / ";
      display_proba ~separate_time 4 y;
      if level > 3 then print_string ")"
  | Card t ->
      print_string "|";
      print_string t.tname;
      print_string "|"
  | AttTime ->
      print_string "time"
  | Time(cnt,cat,t)->
      if separate_time then
	begin
	  let tid = 
	    match !cnt with
	    | "" ->
		let tid = Terms.fresh_id "time" in
		cnt := tid;
		tid
	    | tid -> tid
	  in
	  if not (List.exists (fun (tid', cat', t') -> tid == tid')
		  (!times_to_display)) then
	    times_to_display := (tid, cat, t) :: (!times_to_display);
	  print_string tid
	end
      else
	begin
	  match cat with
	  | Complex -> display_proba ~separate_time level t
	  | _ -> 
	      if level > 1 then print_string "(";
	      display_time_id cat;
	      if level > 1 then print_string ")"
	end
  | ActTime(act, pl) ->
      print_string "time(";
      display_action act;
      if pl != [] then
	begin
	  print_string ", ";
	  display_list (display_proba ~separate_time 0) pl
	end;
      print_string ")"
  | Maxlength(g,t) ->
      print_string "maxlength(";
      if g == Terms.lhs_game then
	print_string "LHS: "
      else if g == Terms.rhs_game then
	print_string "RHS: "
      else if g == Terms.lhs_game_nodisplay then
	()
      else
	begin
	  print_string "game ";
	  print_string (get_game_id g);
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
	  display_list (display_proba ~separate_time 0) pl
	end;
      print_string ")"
  | OptimIf(cond,p1,p2) ->
      print_string "(optim-if ";
      display_optim_cond ~separate_time cond;
      print_string " then ";
      display_proba ~separate_time 0 p1;
      print_string " else ";
      display_proba ~separate_time 0 p2;
      print_string ")"
  | Advt(g, cur_q, ql) -> 
      let (ql_otherq, ql_eventq) = List.partition (fun (q,_) ->
	(Terms.get_event_query q == None)) ql
      in
      print_string (if cur_q || ql_otherq != [] then "Adv" else "Pr");
      print_string "[Game ";
      print_string (get_game_id g);
      print_string ": ";
      if cur_q then
	begin
	  assert(ql_otherq == []);
	  print_string "current_queries"
	end
      else
	begin
	  match ql_otherq with
	  | [q,_] -> display_query3 q
	  | [] -> ()
	  | _ -> assert false
	end;
      if (cur_q || ql_otherq != []) && ql_eventq != [] then print_string ", ";
      display_list_sep " || "
	(fun (q,_) ->
	  match Terms.get_event_query q with
	  | Some f -> print_string f.f_name
	  | None -> assert false) ql_eventq;
      print_string "]"
  | ProbaAssume ->
      print_string "Pr[COMMAND NOT CHECKED]"

and display_optim_cond ~separate_time = function
  | OCProbaFun(s,[p1; p2]) ->
      display_proba ~separate_time 0 p1;
      print_string (" "^s^" ");
      display_proba ~separate_time 0 p2
  | OCProbaFun(s,[p1]) ->
      print_string (s^"(");
      display_proba ~separate_time 0 p1;
      print_string ")"
  | OCBoolFun(s,[c1; c2]) ->
      display_optim_cond ~separate_time c1;
      print_string (" "^s^" ");
      display_optim_cond ~separate_time c2
  | _ -> Parsing_helper.internal_error "display_optim_cond: probability fcts should be unary or binary, boolean fcts should be binary"
    
let rec display_monomial = function
    (coef, []) -> print_float coef
  | (coef, (elem, n)::l) -> display_monomial (coef, l);
      print_string " * "; display_proba 3 elem; print_string " ^ "; print_int n

let rec display_polynom = function
    [] -> print_string "0"
  | [a] -> display_monomial a
  | (a::l) -> display_monomial a; print_string " + "; display_polynom l

let display_one_set ?separate_time = function
    SetProba p ->
      display_proba ?separate_time 0 p;
  | SetEvent(f, g, pub_vars, _) ->
      print_string "Pr[event ";
      print_string f.f_name;
      print_string " in game ";
      print_string (get_game_id g);
      display_pub_vars pub_vars;
      print_string "]"

let rec display_set ?separate_time = function
    [] -> print_string "0"
  | [a] -> display_one_set ?separate_time a
  | a::l -> 
      display_one_set ?separate_time a;
      print_string " + ";
      display_set ?separate_time l
  
let display_up_to_proba ?separate_time p =
  if p <> Zero then
    begin
      print_string " up to probability ";
      display_proba ?separate_time 0 p
    end
      
(* Only for the oracles front-end *)

let rec display_procasterm t = 
  if (!display_occurrences == AllOccs) || (List.memq t.t_occ (!useful_occs)) then
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
      display_find_info find_info;
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
      display_restr b;
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
    ReplRestr(repl_opt, restr, funlist) ->
      begin
	match repl_opt with
	| Some repl -> display_repl repl; print_string " "
	| None -> ()
      end;
      List.iter (fun (b,ext,opt) ->
	display_restr b;
	if opt == Unchanged then
	  print_string " [unchanged]";
	print_string "; ") restr;
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

let rec display_special_arg = function
  | SpecialArgId (s,_),_ -> print_string s
  | SpecialArgString (s,_),_ -> print_string "\""; print_string s; print_string "\""
  | SpecialArgTuple l,_ -> print_string "("; display_list display_special_arg l; print_string ")"
	
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

let display_special_equiv equiv = 
  match equiv.eq_special with
  | Some(special_name, args) ->
      print_string "equiv";
      begin
	match equiv.eq_name with
	  NoName -> ()
	| _ ->  print_string "("; display_eqname equiv.eq_name; print_string ")"
      end;
      print_string " special ";
      print_string (fst special_name);
      print_string "("; display_list display_special_arg args; print_string ")";
      print_newline()
  | None ->
      Parsing_helper.internal_error "either the fixed or special equiv should be present"
	
let display_equiv_gen equiv =
  match equiv.eq_fixed_equiv with
  | Some(lm,rm,p,opt2) ->
      display_equiv ((equiv.eq_name, lm, rm, p, equiv.eq_exec, opt2), None)
  | None ->
      display_special_equiv equiv

let display_pocc = function
  | Ptree.POccInt(n) -> print_int n
  | POccBefore(s,_) -> print_string "before "; print_string s
  | POccAfter(s,_) -> print_string "after "; print_string s
  | POccBeforeNth(n,(s,_)) -> print_string "before_nth "; print_int n; print_string " "; print_string s
  | POccAfterNth(n,(s,_)) -> print_string "after_nth "; print_int n; print_string " "; print_string s
  | POccAt(n,(s,_)) -> print_string "at "; print_int n; print_string " "; print_string s
  | POccAtNth(n,n',(s,_)) -> print_string "at_nth "; print_int n; print_string " "; print_int n'; print_string " "; print_string s

let display_parsed_user_info = function
  | Ptree.PRepeat(fast) ->
      if fast then print_string "**" else print_string "*"
  | Ptree.PVarList(l,stop) ->
      display_list (fun (s,_) -> print_string s) l;
      if stop then print_string "."
  | Ptree.PDetailed(l) ->
      display_list_sep "; " (function
	| Ptree.PVarMapping(vm,stop) -> 
	    print_string "variables: ";
	    display_list (fun ((b1,_),(b2,_)) -> print_string b1; print_string " -> "; print_string b2) vm;
	    if stop then print_string ".";
	| Ptree.PTermMapping(tm,stop) ->
	    print_string "terms: ";
	    display_list (fun (occ,(t,_)) -> display_pocc occ; print_string " -> "; print_string t) tm;
	    if stop then print_string "."
		) l
	      
let display_with_parsed_user_info user_info =
  match user_info with
  | Ptree.PRepeat _ | Ptree.PVarList([],_) | Ptree.PDetailed([]) -> ()
  | _ ->
      print_string " with ";
      display_parsed_user_info user_info

let display_call = function
  | Ptree.AutoCall -> print_string "automatic call"
  | Ptree.ManualCall(args, info) ->
      print_string "manual call ";
      if args != [] then
	begin
	  print_string "special(";
	  display_list display_special_arg args;
	  print_string ")";
	end;
      display_with_parsed_user_info info
	
(* Collision statements *)

let rec display_indep_cond level = function
  | IC_True -> print_string "true"
  | IC_And(c1,c2) ->
      if level != 0 then print_string "(";
      display_indep_cond 0 c1;
      print_string " && ";
      display_indep_cond 0 c2;
      if level != 0 then print_string ")"
  | IC_Or(c1,c2) ->
      if level != 1 then print_string "(";
      display_indep_cond 1 c1;
      print_string " || ";
      display_indep_cond 1 c2;
      if level != 1 then print_string ")"
  | IC_Indep(b1,b2) ->
      display_binder b1;
      print_string " independent-of ";
      display_binder b2
	
let display_collision c =
  print_string "collision ";
  List.iter (fun b -> display_restr b; print_string "; ") c.c_restr;
  if c.c_restr_may_be_equal then
    print_string " [random_choices_may_be_equal] ";
  display_quantified "forall " c.c_forall;
  print_string "return(";
  display_term c.c_redl;
  print_string ") <=(";
  display_proba 0 c.c_proba;
  print_string ")=> return(";
  display_term c.c_redr;
  print_string ")";
  let ic = (c.c_indep_cond != IC_True) in
  let sc = not (Terms.is_true c.c_side_cond) in
  if ic || sc then
    begin
      print_string " if ";
      if ic then display_indep_cond 0 c.c_indep_cond;
      if ic && sc then print_string " && ";
      if sc then display_term c.c_side_cond
    end

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
  | Test(_,_,pelse) | Find(_,pelse,_) | Get(_,_,_,_,pelse,_) ->
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
  if (!display_occurrences != NoOcc) || (List.memq p.i_occ (!useful_occs)) then
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
      print_string indent;
      display_repl b;
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
  if (!display_occurrences != NoOcc) || (List.memq p.p_occ (!useful_occs)) then
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
      print_string indent;
      display_restr b;
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
      display_find_info find_info;
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
  | Get (tbl,patl,topt,p1,p2, find_info) ->
      print_string (indent ^ "get ");
      display_find_info find_info;
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
	
(* Display facts; for debugging *)

let display_elsefind (bl, def_list, t) =
    print_string "for all ";
    display_list display_repl_index bl;
    print_string "; not(defined(";
    display_def_list def_list;
    print_string ") && ";
    display_term t;
    print_string ")";
    print_newline()

let display_facts (subst2, facts, elsefind) =
  print_string "Substitutions:\n";
  List.iter (fun t -> display_term t; print_newline()) subst2;
  print_string "Facts:\n";
  List.iter (fun t -> display_term t; print_newline()) facts;
  print_string "Elsefind:\n";
  List.iter display_elsefind elsefind

let display_def_list_lines def_list = 
  List.iter (fun (b, l) -> display_var b l; print_newline()) def_list

(* Display program points, for debugging *)
	
let display_ppl (ppl, args) =
  print_string "{";
  display_list (fun pp -> print_int (Terms.occ_from_pp pp)) ppl;
  print_string "}";
  if args != [] then
    begin
      print_string "[";
      display_list display_term args;
      print_string "]"
    end
	
let display_pps pps =
  List.iter (fun ppl -> display_ppl ppl; print_newline()) pps

(* Instructions *)

let display_rem_set = function
  | Binders l -> 
      print_string "binder ";
      display_list_sep " " display_binder l
  | Minimal -> 
      print_string "useless"
  | FindCond -> 
      print_string "findcond"
  | EqSide ->
      print_string "right-hand side of equiv"
  | NoRemAssign -> assert false
	
let display_move_set = function
    MAll -> print_string "all binders"
  | MNoArrayRef -> print_string "binders without array references"
  | MNew -> print_string "all new's"
  | MNewNoArrayRef -> print_string "new's without array references"
  | MLet -> print_string "all let's"
  | MBinders l -> 
      print_string "binder ";
      display_list_sep " " display_binder l

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


let display_coll_elim = function
    CollVars l -> print_string "variables: "; display_list print_string l
  | CollTypes l -> print_string "types: "; display_list print_string l 
  | CollTerms l -> print_string "terms: "; display_list print_int l
    
let display_instruct = function
    ExpandGetInsert_ProveUnique -> print_string "expand get, insert and prove unique annotations"
  | Expand -> print_string "expand"
  | Simplify(collector, l) ->
      print_string "simplify";
      if l != [] then
	begin
	  print_string " with collision elimination at ";
	  display_list_sep "; " display_coll_elim l
	end;
      if collector != None then
	print_string " eliminating code unreachable when queries fail"
  | SimplifyNonexpanded ->
      print_string "simplify (non-expanded game)"
  | GlobalDepAnal (b,l) -> 
      print_string "global dependency analysis on ";
      display_binder b;
      if l != [] then
	begin
	  print_string " with collision elimination at ";
	  display_list_sep "; " display_coll_elim l
	end
  | MoveNewLet s -> print_string "move "; display_move_set s
  | RemoveAssign (sarename_new, r) ->
      if sarename_new then
	print_string "SA rename new without array accesses";
      if sarename_new && (r != NoRemAssign) then
	print_string " and ";
      if r != NoRemAssign then
	begin
	  print_string "remove assignments of "; display_rem_set r
	end
  | UseVariable l -> print_string "use variable(s) "; display_list display_binder l
  | SArenaming b -> 
      print_string "SA rename ";
      display_binder b
  | CryptoTransf(e, user_info) -> 
      print_string "equivalence ";
      display_equiv_with_name e;
      display_with_user_info user_info
  | InsertEvent(s,_,occ,_) ->
      print_string ("insert event " ^ s ^ " at occurrence " ^ (string_of_int occ))
  | InsertInstruct(s,ext_s,occ,ext_o) ->
      print_string ("insert instruction " ^ s ^ " at occurrence " ^ (string_of_int occ))
  | ReplaceTerm(s,ext_s,occ,ext_o, check_opt) ->
      print_string ("replace term at occurrence " ^ (string_of_int occ) ^ " with " ^ s);
      begin
	match check_opt with
	| Check -> ()
	| Assume -> print_string " (WARNING: equality not checked)"
      end
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
      display_list (fun ((q,g), proba) -> 
	display_query3 q; 
	display_up_to_proba ~separate_time:true proba
	  ) ql
  | IFocus ql ->
      print_string "focus on queries";
      List.iter (fun q -> print_string "\n  - "; display_query3 q) ql
  | Guess arg ->
      begin
      print_string "guess ";
      match arg with
      | GuessVar((b,l),_) ->
	  print_string "the value of the variable ";
	  display_var b l
      | GuessRepl(repl_index,and_above,_) ->
	  print_string "the tested session for replication index ";
	  display_repl_index repl_index;
	  if and_above then print_string " and above"
      | GuessOcc(occ,and_above,_) ->
	  print_string "the tested session for the replication at ";
	  print_int occ;
	  if and_above then print_string " and above"
      end
  | GuessBranch(occ,_) ->
      print_string "guess branch at ";
      print_int occ

	
(* Display transformation steps *)
	
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
  

let print_occ occ =
  if occ == -1 then
    print_string "[occ not set]"
  else
    print_int occ
      
let display_simplif_step = function
    SReplaceTerm(t,t') -> 
      print_string "    - Replaced ";
      display_term t;
      print_string " with ";
      display_term t';
      print_string " at ";
      print_occ t.t_occ;
      print_newline()
  | STestTrue(p) ->
      print_string "    - Test at ";
      print_occ (Terms.occ_from_pp p);
      print_string " always true\n"
  | STestFalse(p) ->
      print_string "    - Test at ";
      print_occ (Terms.occ_from_pp p);
      print_string " always false\n"
  | STestMerge(p) ->
      print_string "    - Merge branches of test at ";
      print_occ (Terms.occ_from_pp p);
      print_string "\n"
  | STestOr(p) ->
      print_string "    - Expand || in test at ";
      print_occ (Terms.occ_from_pp p);
      print_string "\n"
  | STestEElim(t) ->
      print_string "    - Transformed test at ";
      print_occ t.t_occ;
      print_string " into a logical formula\n"
  | SFindBranchRemoved(p,br) -> 
      print_string "    - Remove branch ";
      get_find_branch p br;
      print_string " in find at ";
      print_occ (Terms.occ_from_pp p);
      print_newline()
  | SFindBranchNotTaken(p,br) -> 
      print_string "    - Branch ";
      get_find_branch p br;
      print_string " not taken in find at ";
      print_occ (Terms.occ_from_pp p);
      print_newline()
  | SFindSingleBranch(p,br) ->
      print_string "    - A single branch always succeeds in find at ";
      print_occ (Terms.occ_from_pp p);
      print_newline()
  | SFindRemoved(p) ->
      print_string "    - Find at ";
      print_occ (Terms.occ_from_pp p);
      print_string " removed (else branch kept if any)\n"
  | SFindElseRemoved(p) ->
      print_string "    - Remove else branch of find at ";
      print_occ (Terms.occ_from_pp p);
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
      print_occ (Terms.occ_from_pp p);
      print_newline()
  | SFindDeflist(p, def_list, def_list') ->
      if def_list == [] then
	print_string "    - Replaced an empty defined condition"
      else
	begin
	  print_string "    - Replaced defined condition ";
	  display_def_list def_list
	end;
      print_string " with ";
      if def_list' == [] then
	print_string "an empty condition"
      else 
	display_def_list def_list';
      print_string " in find at ";
      print_occ (Terms.occ_from_pp p);
      print_newline()
  | SFindinFindCondition(p, t) ->
      print_string "    - Simplified find at ";
      print_occ t.t_occ;
      print_string " in condition of find at ";
      print_occ (Terms.occ_from_pp p);
      print_newline()
  | SFindinFindBranch(p,p') ->
      print_string "    - Simplified find at ";
      print_occ (Terms.occ_from_pp p');
      print_string " in branch of find at ";
      print_occ (Terms.occ_from_pp p);
      print_newline()
  | SFindtoTest(p) ->
      print_string "    - Transformed find at ";
      print_occ (Terms.occ_from_pp p);
      print_string " into a test\n"
  | SFindIndexKnown(p, br, subst) ->
      print_string "    - In branch ";
      get_find_branch p br;
      print_string " of find at ";
      print_occ (Terms.occ_from_pp p);
      print_string ", substituting ";
      display_list (fun (b,t) -> display_binder b; print_string " with ";
        display_term t) subst;
      print_newline()
  | SFindInferUnique(p) ->
      print_string "    - Inferred that find at ";
      print_occ (Terms.occ_from_pp p);
      print_string " is [unique]";
      print_newline()     
                   
  | SLetElseRemoved(p) ->
      print_string "    - Remove else branch of let at ";
      print_occ (Terms.occ_from_pp p);
      print_newline()
  | SLetRemoved(p) ->
      print_string "    - Remove let at ";
      print_occ (Terms.occ_from_pp p);
      print_newline()
  | SLetSimplifyPattern(p, l) -> 
      print_string "    - Simplify ";
      display_pat_simp_list l;
      print_string " at ";
      print_occ (Terms.occ_from_pp p);
      print_newline()

  | SResRemoved(p) ->
      print_string "    - Remove random number generation at ";
      print_occ (Terms.occ_from_pp p);
      print_newline()
  | SResToAssign(p) ->
      print_string "    - Transform unused random number generation at ";
      print_occ (Terms.occ_from_pp p);
      print_string " into constant assignment";
      print_newline()

  | SEventRemoved(p) ->
      print_string "    - Removed event at ";
      print_occ (Terms.occ_from_pp p);
      print_string " (no longer used in queries)";
      print_newline()

  | SAdvLoses(p) ->
      print_string "    - Adversary always loses at ";
      print_occ (Terms.occ_from_pp p);
      print_newline()
	
let display_detailed_ins = function
    DExpandGetInsert(t) -> 
      print_string "  - Expand get/insert for table ";
      display_table t;
      print_newline()
  | DProveUnique(p) ->
      print_string "  - Proved that [unique] annotation at ";
      print_occ (Terms.occ_from_pp p);
      print_string " is correct\n";
  | DExpandIfFind(l) ->
      print_string "  - Expand if/find/let\n";
      List.iter display_simplif_step (List.rev l)
  | DSimplify(l) ->
      print_string "  - Simplification pass\n";
      List.iter display_simplif_step (List.rev l)
  | DGlobalDepAnal(b,coll_elim) ->
      print_string "  - Global dependency analysis on ";
      display_binder b;
      if coll_elim != [] then
	begin
	  print_string " with collision elimination at ";
	  display_list_sep "; " display_coll_elim coll_elim
	end;
      print_newline()
  | DLetSimplifyPattern(let_p, l) ->
      print_string "  - Simplify ";
      display_pat_simp_list l;
      print_string " at "; 
      print_occ (Terms.occ_from_pp let_p);
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
  | DUseVariable(b, rep_list) ->
      print_string "  - Use variable ";
      display_binder b;
      print_newline();
      List.iter (fun (t1,t2) ->
	print_string "    - ";
	display_term t1;
	print_string " replaced with ";
	display_term t2;
	print_string " at ";
	print_occ t1.t_occ;
	print_newline()
	  ) rep_list
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
  | DReplaceTerm _  | DMergeArrays _ | DGuess _ | DGuessBranch _ ->
      (* Don't display anything since the detailed description is the
	 same as the high level one *)
      ()
  | DMergeBranches(p,l) ->
      begin
	match (p.p_desc, l) with
	  (Test _), _ ->
	    print_string "  - Merge branches of test at ";
	    print_occ p.p_occ
	| (Let _), _ ->
	    print_string "  - Merge branches of let at ";
	    print_occ p.p_occ
	| (Find(l0,_,_), l) when List.length l = List.length l0 + 1 ->
	    print_string "  - Merge all branches of find at ";
	    print_occ p.p_occ	    
	| (Find _), p1::r ->
	    print_string "  - Merge branch(es) at ";
	    display_list (fun p2 -> print_occ p2.p_occ) r;
	    print_string " with else branch of find at ";
	    print_occ p.p_occ
	| _ -> Parsing_helper.internal_error "unexpected merge"
      end;
      print_newline()            
  | DMergeBranchesE(t,l) ->
      begin
	match (t.t_desc, l) with
	  (TestE _), _ ->
	    print_string "  - Merge branches of test at ";
	    print_occ t.t_occ
	| (LetE _), _ ->
	    print_string "  - Merge branches of let at ";
	    print_occ t.t_occ
	| (FindE(l0,_,_), l) when List.length l = List.length l0 + 1 ->
	    print_string "  - Merge all branches of find at ";
	    print_occ t.t_occ	    
	| (FindE _), t1::r ->
	    print_string "  - Merge branch(es) at ";
	    display_list (fun t2 -> print_occ t2.t_occ) r;
	    print_string " with else branch of find at ";
	    print_occ t.t_occ
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
  | SFindBranchRemoved(p,_) | SFindBranchNotTaken(p,_) | SFindSingleBranch(p,_) 
  | SFindRemoved(p) | SFindElseRemoved(p) | SFindBranchMerge(p, _) 
  | SFindtoTest(p) | SFindIndexKnown(p, _,_) 
  | SFindDeflist(p, _,_) | SFindInferUnique(p) 
  | SLetElseRemoved(p) | SLetRemoved(p) | SLetSimplifyPattern(p, _) 
  | SResRemoved(p) | SResToAssign(p) | SEventRemoved(p)
  | SAdvLoses(p) -> mark_useful_occ_pp p
  | SFindinFindCondition(p, t) -> mark_useful_occ_pp p; f_t t
  | SFindinFindBranch(p,p') -> mark_useful_occ_pp p; mark_useful_occ_pp p'

let mark_occs1 f_p f_t = function
    DExpandGetInsert _ | DGlobalDepAnal _ 
  | DRemoveAssign _ | DSArenaming _ | DMoveNew _ | DMoveLet _
  | DCryptoTransf _ | DMergeArrays _ -> ()
  | DInsertEvent (_,occ)  | DInsertInstruct (_,occ) | DReplaceTerm (_,_,occ) ->
      useful_occs := occ :: (!useful_occs)
  | DUseVariable(_,l) ->
      List.iter (fun (t1,t2) -> f_t t1) l
  | DExpandIfFind(l) | DSimplify(l) ->
      List.iter (mark_occs_simplif_step f_t) l
  | DProveUnique pp | DLetSimplifyPattern(pp, _) -> mark_useful_occ_pp pp
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
  | DGuess(arg) ->
      begin
	match arg with 
	| GuessOcc(occ,_,_) -> useful_occs := occ :: (!useful_occs)
	| GuessRepl _ | GuessVar _ -> ()
      end
  | DGuessBranch occ ->
      useful_occs := occ :: (!useful_occs)
			      
let mark_occs ins = 
  useful_occs := [];
  List.iter (mark_occs1 mark_useful_occ_p mark_useful_occ_t) ins

let already_displayed = ref []

let display_file s =
  let f = open_in s in
  let rec aux() =
    print_string (input_line f);
    print_newline();
    aux()
  in
  begin
    try 
      aux ()
    with End_of_file ->
      ()
  end;
  close_in f
                            
let display_game_process g =
  match g.proc with
  | RealProcess q -> display_process q
  | Forgotten sg -> display_file sg.text_display
     
                            
let rec display_state ins_next s =
  if List.memq s (!already_displayed) then
    begin
      print_string "===================== New branch =====================\n";
      print_string "Game "; 
      print_string (get_game_id s.game);
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
	  display_game_process s.game;
	  useful_occs := []
      | Some (Proof ql, p, _, s') ->
	  display_state ins_next s';
	  print_newline();
	  List.iter (fun ((q,g), p') -> 
	    print_string "Proved ";
	    display_query (q, s'.game);
	    display_up_to_proba ~separate_time:true p';
	    print_newline()
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
	      display_set ~separate_time:true p;
	      print_string "]"
	    end;
	  print_newline();
	  List.iter display_detailed_ins (List.rev ins);
	  print_string "yields\n\n";
	  print_string "Game "; 
	  print_int s.game.game_number;
	  print_string " is\n";
	  mark_occs ins_next;
	  display_game_process s.game;
	  useful_occs := []
    end


let display_conclusion sdi =
  let rest = sdi.unproved_queries in
  let rest' = List.filter (function (AbsentQuery, _) -> false | _ -> true) rest in
  if rest = [] then
    print_string "All queries proved.\n"
  else if rest' != [] then
    begin
      print_string "RESULT Could not prove ";
      display_list_sep "; " display_query rest;
      print_string ".\n"
    end

(* Display probability bounds *)
	
let display_proba_bound = function
  | BLeq(a,b) ->
      display_proba ~separate_time:true 0 a;
      print_string " <= ";
      display_proba ~separate_time:true 0 b;
      print_newline()
  | BSameGame(g1,g2,p) ->
      print_string ("Game "^(get_game_id g1)^" is the same as game "^(get_game_id g2));
      display_up_to_proba ~separate_time:true p;
      print_string ".\n"

let display_time_id_eq cat =
  match cat with
  | Game(g) | Context(g) when g.game_number <> -1 ->
      print_string " = ";
      display_time_id cat
  | _ -> ()
		
let display_state sdi =
  (* Display the proof tree *)
  times_to_display := [];
  already_displayed := [];
  List.iter (fun s -> display_state [] s) sdi.states_to_display;  
  
  (* Display the probabilities of proved queries *)
  List.iter (fun (q_g, bounds, assume, p) ->
    List.iter display_proba_bound bounds;
    if assume then
      print_string "RESULT Using unchecked commands, shown "
    else
      print_string "RESULT Proved ";
    display_query q_g;
    display_up_to_proba ~separate_time:true p;
    print_newline()
      ) sdi.proved_queries;

  (* Display the runtimes *)
  let rec display_times() = 
    let disp = List.rev (!times_to_display) in
    times_to_display := [];
    if disp != [] then
      begin
	List.iter (fun (tid,cat,t) ->
	  print_string "RESULT ";
	  print_string tid;
	  display_time_id_eq cat;
	  print_string " = ";
	  display_proba ~separate_time:true 0 t;
	  print_newline()
	    ) disp;
	(* Displaying the times in [disp] may add new times to be
           displayed. Display them. *)
	display_times()
      end
  in
  display_times();

  (* List the unproved queries *)
  display_conclusion sdi

