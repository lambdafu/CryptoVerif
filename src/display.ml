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

let query_from_q_g (q,_) =
  (q, ref ToProve(*not needed for display*))
    
let build_advt g ql = 
  Advt(g, false, List.map query_from_q_g ql)
      
	
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

let rec has_assume = function
  | ProbaAssume -> true
  | proba -> Terms.exists_sub_probaf has_assume proba
	
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
      
let display_up_to_proba_set ?separate_time s =
  display_up_to_proba ?separate_time (Polynom.proba_from_set s)

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
      display_list (fun ((q,g), set) -> 
	display_query3 q; 
	display_up_to_proba_set ~separate_time:true set
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
	
let rec map_remove_empty f = function
  | [] -> []
  | a::l ->
      let l' = map_remove_empty f l in
      let a' = f a in
      if snd a' == [] then l' else a' :: l'

let rec map_opt f = function
  | [] -> []
  | a::l ->
      let l' = map_opt f l in
      match f a with
      | Some a' -> a' :: l'
      | None -> l' 
	
let is_non_unique (q,_) =
  match Terms.get_event_query q with
  | Some f -> f.f_cat == NonUniqueEvent
  | _ -> false
	
let is_secrecy = function
  | (QSecret _), _ -> true
  | _ -> false

let has_secrecy ql = List.exists is_secrecy ql

let double_if_needed ql p =
  if has_secrecy ql then Mul(Cst 2.0, p) else p

type proba_bound =
  | BLeq of probaf * probaf
  | BSameGame of game * game * probaf
    
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

let equal_q_g (q,g) (q',g') =
  g == g' && Terms.equal_query q' q
	
let get_poptref g q =
  try 
    let (_,popt_ref) = List.find (fun (q_g',_) -> equal_q_g (q,g) q_g') g.current_queries in
    popt_ref
  with Not_found ->
    display_query3 q;
    print_string (" not found in game "^ (get_game_id g)^"\n");
    assert false
	
let rec is_full_poptref q poptref =
  match !poptref with
  | Inactive | ToProve -> false
  | Proved(ql,probaf, _) ->
      is_full_probaf q probaf

and is_full_probaf q probaf = not (is_not_full_probaf q probaf)

and is_not_full_probaf q = function
  | Advt(g,cur_q,ql) ->
      (List.exists (fun (q,popt_ref) -> not (is_full_poptref q popt_ref)) ql) ||
      (if cur_q then
	let popt_ref = get_poptref g q in
	not (is_full_poptref q popt_ref)
      else false)
  | probaf -> Terms.exists_sub_probaf (is_not_full_probaf q) probaf
      
and is_full_proba = function
  | SetProba _ (* Must not contain Advt *) -> true
  | SetEvent(f,g,pub_vars, poptref) ->
      let f_query = Terms.build_event_query f pub_vars in
      is_full_poptref f_query poptref

let get_proved poptref =
  match !poptref with
  | Inactive | ToProve -> Parsing_helper.internal_error "Probability not fully computed"
  | Proved(ql, proba_info, s) -> (ql, proba_info, s)

let contains_event_q f s =
  List.exists (Terms.is_event_query f) s.game.current_queries 

type maybe_other_side_ty =
  | ThisSide of query list * probaf * state
  | OtherSide of state
    
let get_proved_maybe_other_side other_side_info poptref =
  match !poptref with
  | Inactive | ToProve ->
      begin
	match other_side_info with
	| Some middle_s, Some s_other_side ->
	    (* We accept unproved queries event(..) => false when we prove
	       an equivalence between 2 games and we are not in the sequence
	       of games in which the query was proved *)
	    OtherSide(middle_s)
	| _ -> Parsing_helper.internal_error "Probability not fully computed"
      end
  | Proved(ql, proba, s) -> ThisSide(ql, proba, s)

let rec get_non_unique_q = function
  | [] -> []
  | q::l ->
      let l' = get_non_unique_q l in
      match Terms.get_nonunique_event_query q with
      | None -> l'
      | Some _ -> q::l'

(* A proof tree is a tree in which
   - nodes are games (field pt_game of pt_node below) 
   - edges correspond to game transformations. These edges are labelled with
       * pt_proba: pt_proba_info, the probability difference
       * pt_sons: pt_node list, the obtained sons (there can be several sons for a single edge in case of the guess_branch transformation)
       * pt_queries: (query_specif * game) list, the list of properties proved by going through the
         considered edge.
   We have a tree and not just a list of games, because events may be introduced by Shoup's lemma,
   and proved later to have negligible probability, so we may need to prove several properties
   at once. Moreover, these properties may be proved using different sequences of games, thus
   leading to a tree.
   The last edge (the one that proves a property) already deals with a single property.
   Other edges may be shared between the proofs of several properties. *)

type pt_proba_info =
  | Default of probaf * (funsymb * binder list(*public vars*)) list
      (* [Default(p,ql')] means [2 p + Adv_G0(Q0::ql')] for (one-session) secrecy
                                [p + Adv_G0(Q0::ql')] otherwise
	 [p] must not use Advt  
	 [pt_sons] must be [proof tree for G0] *)
  | Case of query list * probaf
      (* [Case(ql, p)] means that the proof applies only to queries in [ql],
	 use another edge for other queries.
	 [p] is a probability formula that can contain Adv_Gi(Q0::ql')
	 [pt_sons] must be the list of proof trees for Gi.
	 [pt_queries] must contain a sublist of queries in [ql].
	 There can be several edges connecting the same father to the same
	 sons for disjoint [ql]. *)
  | OtherSide of query
      (* [OtherSide q] means that [q] has been proved on the other side of
	 an equivalence query *)
	
type pt_node =
    { pt_game : game;
      mutable pt_edges : pt_edge list }

and pt_edge =
    { pt_proba: pt_proba_info;
      pt_sons: pt_node list;
      mutable pt_queries: (query * game) list }

let equal_pt_proba_case p1 p2 =
  match (p1,p2) with
  | Case(ql1,proba1), Case(ql2,proba2) ->
      (Terms.equal_lists_sets Terms.equal_query ql1 ql2) &&
      (Terms.equal_probaf proba1 proba2)
  | _ -> false
      
(* For debugging *)

let display_short_query q =
  match Terms.get_event_query q with
  | Some f -> print_string f.f_name
  | None -> display_query3 q

let display_q_g (q,g) =
  display_short_query q;
  print_string " in game "; print_string (get_game_id g)
	
let rec display_proof_tree indent pt =
  print_string (indent ^ "Game " ^ (get_game_id pt.pt_game) ^"\n");
  let display_edge indent_next edge =
    print_string (indent ^ "- Probability: ");
    begin
      match edge.pt_proba with
      | Default(p,ql') ->
	  display_proba 0 p;
	  if ql' != [] then
	    begin
	      print_string " Additional events: ";
	      display_list (fun (f,pub_vars) -> print_string f.f_name) ql'
	    end
      | Case(ql,p) ->
	  display_proba 0 p;
	  print_string " valid for queries ";
	  display_list display_short_query ql
      | OtherSide q ->
	  print_string "query "; display_short_query q; print_string " proved on the other side"
    end;
    print_newline();
    print_string (indent ^ "- Properties to prove: ");
    display_list display_q_g edge.pt_queries;
    print_newline();
    match edge.pt_sons with
    | [] -> print_string (indent ^ "No son\n")
    | [s] ->
	print_string (indent ^ "Son:\n");
	display_proof_tree indent_next s
    | _ ->
	print_string (indent ^ "Sons:\n");
	List.iter (display_proof_tree (indent ^ "  ")) edge.pt_sons
  in
  match pt.pt_edges with
    [] -> print_string (indent ^ "No outgoing edge\n") 
  | [e] -> 
      print_string (indent ^ "Outgoing edge:\n"); 
      display_edge indent e
  | _ ->
      print_string (indent ^ "Outgoing edges:\n");
      List.iter (display_edge (indent ^ "  ")) pt.pt_edges

(* Build the proof tree *)

(* [other_side_info] is used only for indistinguishability proofs between
   2 games G0 and G1. ProVerif generates two sequences of games
   G0 ---> G2 and G1 ---> G2' in which G2 and G2' are trivially 
   indistinguishable (just by eliminating collisions).
   Indistinguishability between G2 and G2' is proved when we are either 
   working on G2 or on G2'; let's say G2. Then the proof continues from
   G2, showing that the probability of events remaining in G2 is bounded.
   In this case, [other_side_info] is a pair 
   [(Some middle_state, other_side_state_option)]
   where [middle_state] is the final state of the sequence we are currently
   looking at and [other_side_state_option] is 
   [None] when we are looking at the sequence in which the proof succeeded
   (G0 ---> G2; all queries are necessarily proved in this sequence)
   [Some other_side_middle_state] when we are looking at the other sequence
   (G1 ---> G2'; some queries may not be explicitly proved in this sequence:
   - events that appear in the middle game and whose probability is bounded
   in the sequence in which the proof succeeded;
   - events that do not appear in the middle game, but whose absence was
   not necessarily proved; we know that they are absent because the proof
   succeeded in the other sequence and the middle games are the same.)
   In this case, [other_side_middle_state] is the final state of the sequence 
   G0 ---> G2 in which the proof succeeded.

   In other cases, [other_side_info = (None, None)].
   *)

let rec collect_advt accu = function
  | Advt(g,cur_q,ql) -> (g,cur_q,ql)::accu
  | AttTime | Cst _ | Count _ | Zero | Card _ | TypeMaxlength _
  | EpsFind | EpsRand _ | PColl1Rand _ | PColl2Rand _ | OCount _
  | Maxlength _ | ProbaAssume -> accu
  | Time(_,_,p) | Power(p,_) -> collect_advt accu p
  | Proba(_,l) | Max(l) | Min(l) | ActTime(_,l) | Length(_,l) ->
      List.fold_left collect_advt accu l
  | Add(p1,p2) | Mul(p1,p2) | Sub(p1,p2) | Div(p1,p2) ->
      collect_advt (collect_advt accu p1) p2
  | OptimIf(cond,x,y) -> collect_advt (collect_advt (collect_advt_optim_cond accu cond) x) y
	
and collect_advt_optim_cond accu = function
  | OCProbaFun(_,l) -> List.fold_left collect_advt accu l
  | OCBoolFun(_,l) -> List.fold_left collect_advt_optim_cond accu l
    

	
let rec build_proof_tree other_side_info g0 queries =
  let pt_init = { pt_game = g0;
		  pt_edges = [] }
  in
  let proof_tree_table = ref [(g0, pt_init)] in
  let get_node_for_game g =
    try
      let pt_cur = List.assq g (!proof_tree_table) in
      (* print_string ("Found " ^ (string_of_int g.game_number)); *)
      (pt_cur, true)
    with Not_found ->
      let pt_cur = { pt_game = g;
		     pt_edges = [] }
      in
      (* print_string ("Added game " ^ (string_of_int s.game.game_number)); *)
      proof_tree_table := (g, pt_cur) :: (!proof_tree_table);
      (pt_cur, false)
  in
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
  (* Add a new query [q] in the list of proved properties, in a part of the 
     proof tree that is already built *)
  let rec add_query ((q,g) as q_g) pt_cur s =
    if s.game == g then () else 
    match father_ignore_proof s with
      None -> ()
    | Some (i,p,_,s') ->
	let pt_father =
	  try
	    List.assq s'.game (!proof_tree_table)
	  with Not_found ->
	    print_string ("Game "^(get_game_id s'.game)^" not found\n");
	    Parsing_helper.internal_error "This game should always be found"
	in
	let e =
	  try 
	    List.find (fun e ->
	      (List.memq pt_cur e.pt_sons) &&
	      (match e.pt_proba with
	      | Default _ -> true
	      | Case(ql,_) -> List.exists (Terms.equal_query q) ql
	      | OtherSide q0  -> Terms.equal_query q q0)
		) pt_father.pt_edges
	  with Not_found ->
	    print_string "edge for query "; display_short_query q; print_string " not found\n";
	    Parsing_helper.internal_error "This edge should always be found"
	in
	if not (List.exists (fun (q',_) -> Terms.equal_query q q') e.pt_queries) then
	  e.pt_queries <- q_g :: e.pt_queries;
	add_query q_g pt_father s'
  in
  (* Build the proof tree for state [s], proving property [q]. [edge_to_add] is 
     an edge to add to the proof corresponding to state [s]. *)
  let rec build_pt_rec edge_to_add ((q,g) as q_g) s =
    let (pt_cur,known_game) = get_node_for_game s.game in
    (* print_string " adding sons ";
      display_list (fun s -> print_int s.pt_game.game_number) edge_to_add.pt_sons;
       print_newline(); *)
    begin
      try
	let edge_old =
	  List.find (fun edge_old ->
	    match edge_old.pt_proba with
	    | Case(ql_old, _) -> List.exists (Terms.equal_query q) ql_old
	    | _ -> false) pt_cur.pt_edges
	in
	(* There is already an edge for query [q] *)
	assert (equal_pt_proba_case edge_old.pt_proba edge_to_add.pt_proba);
	assert (Terms.equal_lists_sets_q edge_old.pt_sons edge_to_add.pt_sons);
	edge_old.pt_queries <- Terms.union equal_q_g edge_to_add.pt_queries edge_old.pt_queries
      with Not_found -> 
	pt_cur.pt_edges <- edge_to_add :: pt_cur.pt_edges
    end;
    if known_game then
      add_query q_g pt_cur s
    else
      match father_ignore_proof s with
	None -> Parsing_helper.internal_error "Initial game should already have been entered in the proof tree"
      |	Some(i,p,_,s) ->
	  let probaf = 
	    Polynom.p_sum (map_opt (function
	      | SetProba p -> Some p
	      | SetEvent _ -> None) p)
	  in
	  let add_events =
	    map_opt (function
	      | SetProba _ -> None
	      | SetEvent(f,g, pub_vars, popt') -> Some (f,pub_vars)) p
	  in
	  let edge =
	    { pt_proba = Default(probaf, add_events);
	      pt_sons = [pt_cur];
	      pt_queries = [q_g] }
	  in
	  build_pt_rec edge q_g s;
	  List.iter (function 
	      SetProba _ -> ()
	    | SetEvent(f,g, pub_vars, popt') ->
		(* Build the query that tests for event f in game g *)
                let f_query = Terms.build_event_query f pub_vars in
		handle_query ((f_query, g),popt')
		  ) p
  and handle_query ((query,g) as q_g,popt') =
    (* Get the proof of the property "query,g" *)
    match get_proved_maybe_other_side other_side_info popt' with
    | OtherSide s' -> 
	let edge =
	  { pt_proba = OtherSide query;
	    pt_sons = [];
	    pt_queries = [q_g] }
	in
	build_pt_rec edge q_g s'
    | ThisSide(ql,probaf,s') -> 
	let sons =
	  let collected_advt = collect_advt [] probaf in
	  List.map (fun (g_new, cur_q, ql) ->
	    let (pt_cur,_) = get_node_for_game g_new in
	    if cur_q then
	      begin
		let popt_new = get_poptref g_new query in
		handle_query ((query,g_new),popt_new)
	      end;
	    List.iter (fun (q,popt) ->
	      handle_query ((q,g_new),popt)
		) ql;
	    pt_cur
	      ) collected_advt
	in
	let edge =
	  { pt_proba = Case(ql, probaf);
	    pt_sons = sons;
	    pt_queries = [q_g] }
	in
	build_pt_rec edge q_g s'
  in
  List.iter handle_query queries;
  pt_init

let rec evaluate_proba other_side_info bounds start_adv start_game above_proba ql pt =
  (* Sanity check: all elements of ql must occur in some edge in pt *)
  List.iter (fun q_g -> 
    if not ((List.exists (fun e -> 
      List.exists (equal_q_g q_g) e.pt_queries
	) pt.pt_edges) )
    then
      begin
	print_string "Game "; print_string (get_game_id pt.pt_game);
	print_string ": missing ";
	display_q_g q_g;
	print_newline();
	Parsing_helper.internal_error "Missing property in evaluate_proba"
      end
	) ql;
  (* Sanity check: the ql_ref are disjoint *)
  let check_disjoint e1 e2 =
    if List.exists (fun qg1 -> List.exists (equal_q_g qg1) e2.pt_queries) e1.pt_queries then
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
  check_disjoint_ll pt.pt_edges;
  (* Take into account tree branching (several sons): split [ql] according to what
     each son proves *)
  match pt.pt_edges with
    [ { pt_proba = Default(p,[]); pt_sons = [pt_son] } ] ->
	 evaluate_proba other_side_info bounds start_adv start_game (Polynom.p_add(double_if_needed ql p, above_proba)) ql pt_son
  | _ ->
      let above_proba = Polynom.simplify_proba above_proba in
      (* When [pt] has several sons, split the queries in [ql] according to which 
         son proves them.
	 If we do not prove secrecy, Adv_Q(C,||_i D_i) <= sum_i Adv_Q(C,D_i)
	 If we prove secrecy, Adv_Q(C, ||_i D_i) <= sum_i Adv_Q(C,D_i) + sum_{i \neq i_0} \Adv_Q(C, D_{NUi}) 
	 where D_{i_0} is the element that contains the secrecy query and D{NUi} contains only the queries for non-unique events in D_i. *)
      let ql_list =
	(* Compute the list of D_i with the associated [edge_info] in the proof tree. *)
	map_remove_empty (fun edge ->
	  edge, List.filter (fun q_g -> List.exists (equal_q_g q_g) ql) edge.pt_queries) pt.pt_edges
      in
      let ql_list_with_nu =
	(* Add the list of D_{NUi} with the associated [edge] in the proof tree. *)
	if has_secrecy ql then
	  List.concat (List.map (fun (edge, ql') ->
	      if has_secrecy ql' then
	        (* We do not compute D_{NUi} for i=i_0 *)
		[ (1.0, edge, ql') ]
	      else if List.for_all is_non_unique ql' then
		[ (2.0, edge, ql') ]
	      else
		let nu_ql' = List.filter is_non_unique ql' in
		if nu_ql' = [] then
		  [ (1.0, edge, ql') ]
		else
		  [ (1.0, edge, nu_ql'); (1.0, edge, ql') ]
		    ) ql_list)
	else
	  (* When we do not prove secrecy, there is nothing to add *)
	  List.map (fun (edge, ql') -> (1.0, edge, ql')) ql_list
      in
      begin
	match other_side_info with
	| (Some middle_s, _) when middle_s.game == pt.pt_game ->
	    (* We omit the bound when it concerns only the middle game;
	       it would yield an inaccurate display with potentially missing
	       event probabilities in the sequence of games in which the 
	       property is not proved, and in the other sequence, events 
	       proved but presented only for that sequence while we need 
	       them for both sequences *)
	    if middle_s.game != start_game then
	      bounds := (BLeq(start_adv, Polynom.p_add (above_proba, build_advt pt.pt_game ql))) :: (!bounds) 
	| _ ->
	    bounds := (BLeq(start_adv, Polynom.p_sum (above_proba :: List.map (fun (factor, edge, ql) -> Polynom.p_mul (Cst factor, build_advt pt.pt_game ql)) ql_list_with_nu))) :: (!bounds) 
      end;
      Polynom.p_sum (above_proba :: (List.map (fun (factor, edge, ql') ->
	let start_adv = build_advt pt.pt_game ql' in
	let proba = 
	  (* We consider the whole set of queries ql' at once, 
	     and avoid counting several times the same events. *)
	  match edge.pt_proba with
	  | Default(p, ql) ->
	      begin
		match edge.pt_sons with
		| [pt_son] ->
		    let ql'' = (List.map (fun (f,pub_vars) -> (Terms.build_event_query f pub_vars, pt_son.pt_game)) ql) @ ql' in
		    let p = Polynom.simplify_proba (double_if_needed ql' p) in
		    if ql == [] then
	              (* No event introduced *)
		      evaluate_proba other_side_info bounds start_adv pt.pt_game p ql'' pt_son
		    else
		      begin
	                (* An event has been introduced, display its probability separately *)
			let adv' = build_advt pt_son.pt_game ql'' in
			bounds := (BLeq(start_adv, Polynom.p_add(p, adv'))) :: (!bounds); 
			Polynom.p_add (p, evaluate_proba other_side_info bounds adv' pt_son.pt_game Zero ql'' pt_son)
		      end
		| _ -> assert false
	      end
	  | Case(ql,p) ->
	      (* Sanity check: [ql'] included in [ql] *)
	      List.iter (fun (q',g) ->
		if not (List.exists (Terms.equal_query q') ql) then
		  Parsing_helper.internal_error "Query not in the right case in evaluate_proba"
		    ) ql';
	      (* Display bound *)
	      let rec map_proba_formula = function
		| Advt(g, cur_q, ql) ->
		    let updated_ql =
		      if cur_q then
			(List.map query_from_q_g ql') @ ql
		      else ql
		    in
		    Advt(g, false, updated_ql) 
		| proba -> Terms.map_sub_probaf map_proba_formula proba
	      in
	      let p_img = map_proba_formula p in
	      begin
		match other_side_info with
		| (Some middle_s, _)
		    when middle_s.game == pt.pt_game 
	            && List.exists (fun (q,_) -> Terms.get_event_query q == None) ql' ->
	            (* Do not display the proof of the initial equivalence query 
		       in the middle game (the middle game may contain events
		       and in this case, the probability of these events 
		       must be taken into account in the final result, which
		       would not be done here) *)
		      ()
		| _ -> 
		    bounds := (BLeq(start_adv, p_img)) :: (!bounds)	      
	      end;

	      (* Compute the actual proba *)
	      let rec evaluate_proba_formula = function
		| Advt(g, cur_q, ql) as adv ->
		    assert (cur_q == false);
		    let pt_son = List.find (fun pt -> pt.pt_game == g) edge.pt_sons in
		    let ql_g = List.map (fun (q,_) -> (q,g)) ql in
		    evaluate_proba other_side_info bounds adv g Zero ql_g pt_son
		| proba -> Terms.map_sub_probaf evaluate_proba_formula proba
	      in
	      evaluate_proba_formula p_img
	  | OtherSide q -> 
	      (* Sanity check: [ql'] included in [q] *)
	      List.iter (fun (q',_) ->
		if not (Terms.equal_query q' q) then
		  Parsing_helper.internal_error "Query not in the right case in evaluate_proba (other side)"
		    ) ql';
	      (* Compute the proba *)
	      Zero
	in
	Polynom.p_mul (Cst factor, proba)
	  ) ql_list_with_nu))

and compute_proba_internal other_side_info bounds g queries =
  let pt = build_proof_tree other_side_info g queries in
  (* display_proof_tree "" pt; *)
  let start_queries = List.map fst queries in
  evaluate_proba other_side_info bounds (build_advt g start_queries) g Zero start_queries pt 
    
let compute_proba (((q0,g),poptref) as full_q) =
  let g_non_unique_q = get_non_unique_q g.current_queries in
  let bounds = ref [] in
  let fullp = 
    match q0 with
    | QEquivalence(state,pub_vars,_) ->
	let (_,p,s) = get_proved poptref in
	bounds := (BSameGame(s.game, state.game, p)) :: (!bounds);
	let g' = get_initial_game state in
	let g'_non_unique_q = get_non_unique_q g'.current_queries in
	let q1 = QEquivalenceFinal(s.game, pub_vars) in
	let q2 = QEquivalenceFinal(state.game, pub_vars) in
	Polynom.p_add(compute_proba_internal (Some s, None) bounds g
			(((q1,g), ref (Proved([q1],Zero,s)))::g_non_unique_q),
		      Polynom.p_add (p, compute_proba_internal (Some state, Some s) bounds g'
				       (((q2,g'), ref(Proved([q2],Zero,state)))::g'_non_unique_q)))
    | AbsentQuery ->
	let (_,p,s) = get_proved poptref in
	let q0 = QEquivalenceFinal(s.game, []) in
	compute_proba_internal (None, None) bounds g (((q0,g),ref (Proved([q0],p,s)))::g_non_unique_q)
    | _ -> 
	compute_proba_internal (None, None) bounds g (full_q::g_non_unique_q) 
  in
  (List.rev (!bounds)), fullp

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
      print_occ (Incompatible.occ_from_pp p);
      print_string " always true\n"
  | STestFalse(p) ->
      print_string "    - Test at ";
      print_occ (Incompatible.occ_from_pp p);
      print_string " always false\n"
  | STestMerge(p) ->
      print_string "    - Merge branches of test at ";
      print_occ (Incompatible.occ_from_pp p);
      print_string "\n"
  | STestOr(p) ->
      print_string "    - Expand || in test at ";
      print_occ (Incompatible.occ_from_pp p);
      print_string "\n"
  | STestEElim(t) ->
      print_string "    - Transformed test at ";
      print_occ t.t_occ;
      print_string " into a logical formula\n"
  | SFindBranchRemoved(p,br) -> 
      print_string "    - Remove branch ";
      get_find_branch p br;
      print_string " in find at ";
      print_occ (Incompatible.occ_from_pp p);
      print_newline()
  | SFindBranchNotTaken(p,br) -> 
      print_string "    - Branch ";
      get_find_branch p br;
      print_string " not taken in find at ";
      print_occ (Incompatible.occ_from_pp p);
      print_newline()
  | SFindSingleBranch(p,br) ->
      print_string "    - A single branch always succeeds in find at ";
      print_occ (Incompatible.occ_from_pp p);
      print_newline()
  | SFindRemoved(p) ->
      print_string "    - Find at ";
      print_occ (Incompatible.occ_from_pp p);
      print_string " removed (else branch kept if any)\n"
  | SFindElseRemoved(p) ->
      print_string "    - Remove else branch of find at ";
      print_occ (Incompatible.occ_from_pp p);
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
      print_occ (Incompatible.occ_from_pp p);
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
      print_occ (Incompatible.occ_from_pp p);
      print_newline()
  | SFindinFindCondition(p, t) ->
      print_string "    - Simplified find at ";
      print_occ t.t_occ;
      print_string " in condition of find at ";
      print_occ (Incompatible.occ_from_pp p);
      print_newline()
  | SFindinFindBranch(p,p') ->
      print_string "    - Simplified find at ";
      print_occ (Incompatible.occ_from_pp p');
      print_string " in branch of find at ";
      print_occ (Incompatible.occ_from_pp p);
      print_newline()
  | SFindtoTest(p) ->
      print_string "    - Transformed find at ";
      print_occ (Incompatible.occ_from_pp p);
      print_string " into a test\n"
  | SFindIndexKnown(p, br, subst) ->
      print_string "    - In branch ";
      get_find_branch p br;
      print_string " of find at ";
      print_occ (Incompatible.occ_from_pp p);
      print_string ", substituting ";
      display_list (fun (b,t) -> display_binder b; print_string " with ";
        display_term t) subst;
      print_newline()
  | SFindInferUnique(p) ->
      print_string "    - Inferred that find at ";
      print_occ (Incompatible.occ_from_pp p);
      print_string " is [unique]";
      print_newline()     
                   
  | SLetElseRemoved(p) ->
      print_string "    - Remove else branch of let at ";
      print_occ (Incompatible.occ_from_pp p);
      print_newline()
  | SLetRemoved(p) ->
      print_string "    - Remove let at ";
      print_occ (Incompatible.occ_from_pp p);
      print_newline()
  | SLetSimplifyPattern(p, l) -> 
      print_string "    - Simplify ";
      display_pat_simp_list l;
      print_string " at ";
      print_occ (Incompatible.occ_from_pp p);
      print_newline()

  | SResRemoved(p) ->
      print_string "    - Remove random number generation at ";
      print_occ (Incompatible.occ_from_pp p);
      print_newline()
  | SResToAssign(p) ->
      print_string "    - Transform unused random number generation at ";
      print_occ (Incompatible.occ_from_pp p);
      print_string " into constant assignment";
      print_newline()

  | SEventRemoved(p) ->
      print_string "    - Removed event at ";
      print_occ (Incompatible.occ_from_pp p);
      print_string " (no longer used in queries)";
      print_newline()

  | SAdvLoses(p) ->
      print_string "    - Adversary always loses at ";
      print_occ (Incompatible.occ_from_pp p);
      print_newline()
	
let display_detailed_ins = function
    DExpandGetInsert(t) -> 
      print_string "  - Expand get/insert for table ";
      display_table t;
      print_newline()
  | DProveUnique(p) ->
      print_string "  - Proved that [unique] annotation at ";
      print_occ (Incompatible.occ_from_pp p);
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
      print_occ (Incompatible.occ_from_pp let_p);
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
  useful_occs := (Incompatible.occ_from_pp p) :: (!useful_occs)

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
	    display_up_to_proba_set ~separate_time:true p';
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


let get_initial_queries s =
  (get_initial_game s).current_queries

let rec reachable s s' =
  (s == s') ||
  (match s'.prev_state with
    None -> false
  | Some (_,_,_,s'') -> reachable s s'')
    
let rec get_all_states_from_sequence accu s =
  match s.prev_state with
    None -> accu
  | Some(_, proba, _, s') ->
      get_all_states_from_sequence (get_all_states_from_proba accu proba) s'

and add_sequence accu s' =
  if List.exists (reachable s') accu then accu else
  get_all_states_from_sequence (s' :: accu) s'
	
and get_all_states_from_proba accu = function
    [] -> accu
  | (SetProba _)::r -> get_all_states_from_proba accu r
  | (SetEvent(f,g,pub_vars,poptref)) :: r  ->
      let accu' = get_all_states_from_proba accu r in
      let f_query = Terms.build_event_query f pub_vars in
      add_sequence_poptref accu' f_query poptref

and add_sequence_poptref accu q poptref = 
  match !poptref with
  | ToProve | Inactive -> accu
  | Proved(ql,probaf,s') ->
      add_sequence_probaf (add_sequence accu s') q probaf

and add_sequence_probaf accu q probaf =
  let adv_list = collect_advt [] probaf in
  List.fold_left (fun accu (g,cur_q,ql) ->
    let accu' =
      List.fold_left (fun accu (q,poptref) ->
	add_sequence_poptref accu q poptref) accu ql
    in
    if cur_q then
      let popt_ref = get_poptref g q in
      add_sequence_poptref accu' q popt_ref
    else
      accu') accu adv_list
    
let rec get_all_states_from_queries = function
    [] -> []
  | ((q,g), poptref)::r ->
      let accu = get_all_states_from_queries r in
      let accu' =
	match q with
	| QEquivalence(s',_,_) ->
	    add_sequence accu s'
	| _ -> accu
      in
      add_sequence_poptref accu' q poptref

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
  let rest = List.filter (function (q, poptref) -> (!poptref) == ToProve || (!poptref) == Inactive) initial_queries in
  let rest' = List.filter (function (AbsentQuery, _),_ -> false | _ -> true) rest in
  if rest = [] then
    print_string "All queries proved.\n"
  else if rest' != [] then
    begin
      print_string "RESULT Could not prove ";
      display_list_sep "; " (fun (q, _) -> display_query q) rest;
      print_string ".\n"
    end

let display_time_id_eq cat =
  match cat with
  | Game(g) | Context(g) when g.game_number <> -1 ->
      print_string " = ";
      display_time_id cat
  | _ -> ()
		
let display_state s =
  (* Display the proof tree *)
  times_to_display := [];
  already_displayed := [];
  let initial_queries = get_initial_queries s in
  let states_needed_in_queries = get_all_states_from_queries initial_queries in
  let states_to_display = remove_duplicate_states [] (s::states_needed_in_queries) in
  List.iter (fun s -> display_state [] s) states_to_display;  
  
  (* Display the probabilities of proved queries *)
  let (non_unique_initial_queries, other_initial_queries) =
    List.partition Terms.is_nonunique_event_query initial_queries
  in
  if List.for_all (fun ((q,_),poptref) -> is_full_poptref q poptref) non_unique_initial_queries then
    List.iter (fun (((q,_) as q_g,poptref) as full_q) ->
      if is_full_poptref q poptref then
	begin
          let (bounds, p'') = compute_proba full_q in
	  List.iter display_proba_bound bounds;
	  if has_assume p'' then
	    begin
	      print_string "RESULT Using unchecked commands, shown ";
	      poptref := ToProve
	    end
	  else
            print_string "RESULT Proved ";
          display_query q_g;
	  display_up_to_proba ~separate_time:true (Polynom.simplify_proba p'');
	  print_newline()
	end
	  ) other_initial_queries;

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
  display_conclusion s

