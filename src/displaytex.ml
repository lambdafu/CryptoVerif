open Types

let nice_tex = ref true

let display_occurrences = ref false

let display_arrays = ref false

let times_to_display = ref []

let file = ref stdout

let print_string s =
  output_string (!file) s

let print_int i =
  print_string (string_of_int i)

let display_string s =
  for i = 0 to String.length s - 1 do
    match s.[i] with
      '\\' -> print_string "{\\textbackslash}"
    | '&' -> print_string "\\ensuremath{\\&}"
    | '{' -> print_string "\\ensuremath{\\{}"
    | '}' -> print_string "\\ensuremath{\\}}"
    | '_' -> print_string "{\\_}"
    | '^' -> print_string "{\\string^}"
    | '#' -> print_string "\\#"
    | '$' -> print_string "\\$"
    | '%' -> print_string "\\%"
    | '@' -> print_string "{\\string@}"
    | '~' -> print_string "{\\string~}"
    | '>' -> print_string "\\ensuremath{>}"
    | '<' -> print_string "\\ensuremath{<}"
    | c -> output_char (!file) c
  done  

let print_id prefix s suffix =
  print_string prefix;
  display_string s;
  print_string suffix

let rec display_list_sep sep f = function
    [] -> ()
  | [a] -> f a
  | (a::l) -> f a; print_string sep;
      display_list_sep sep f l

let display_list f l = display_list_sep ", " f l

let display_list_break f l = display_list_sep ", \\allowbreak " f l

let rec remove_common_prefix l1 l2 = match (l1,l2) with
  ({t_desc = ReplIndex ri1}::l1',ri2::l2') when ri1 == ri2 -> 
    remove_common_prefix l1' l2'
| _ -> l1

let remove_common_suffix l1 l2 =
  List.rev (remove_common_prefix (List.rev l1) (List.rev l2))

let display_table tbl = print_id "\\var{" tbl.tblname "}"

let display_type t =
  print_id "\\kwt{" t.tname "}"

let display_type_info ty =
  match ty.tcat with
  | Interv n -> 
      print_id " \\leq \\kwp{" n.pname "}"
  | _ -> 
      print_id ": \\kwt{" ty.tname "}"
    
let display_binder b =
  print_id "\\var{" b.sname "}";
  if (b.vname != 0) || (Display.ends_with_underscore_number b.sname) then 
    begin
      if !nice_tex then
	print_string ("_{" ^ (string_of_int b.vname) ^ "}")
      else
	print_string ("\\_" ^ (string_of_int b.vname))
    end

let display_repl_index b =
  print_id "\\var{" b.ri_sname "}";
  if (b.ri_vname != 0) || (Display.ends_with_underscore_number b.ri_sname) then 
    begin
      if !nice_tex then
	print_string ("_{" ^ (string_of_int b.ri_vname) ^ "}")
      else
	print_string ("\\_" ^ (string_of_int b.ri_vname))
    end

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

let display_find_info = function
  | Nothing -> ()
  | Unique -> print_string "[\\kwf{unique}]\\ "
  | UniqueToProve e -> print_id "[\\kwf{unique?" e.f_name "}]\\ " 
	
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
  display_type_info b.btype

and display_repl_index_with_type b =
  display_repl_index b;
  print_id " \\leq \\kwp{" (Terms.param_from_type b.ri_type).pname "}"

and display_repl i =
  if (!Settings.front_end) == Settings.Oracles then
    begin
      print_string "\\kw{foreach}\\ ";
      display_repl_index_with_type i;
      print_string "\\ \\kw{do}"
    end
  else if !nice_tex then
    begin
      print_string "!^{";
      display_repl_index_with_type i;
      print_string "}"
    end
  else
    begin
      print_string "!\\ ";
      display_repl_index_with_type i
    end
    
and display_restr b =
  if (!Settings.front_end) == Settings.Oracles then
    begin
      display_binder_with_array b;
      print_id " \\getR \\kwt{" b.btype.tname "}"
    end
  else
    begin
      print_string "\\kw{new}\\ ";
      display_binder_with_type b
    end
    
and display_def_list def_list = 
  display_list (fun (b, l) -> display_var b l) def_list
   
and display_findcond (def_list, t1) =
  let cond_printed = ref false in
  if def_list != [] then
    begin
      print_string "\\kw{defined}(";
      display_def_list def_list;
      print_string ")";
      cond_printed := true
    end;
  if !cond_printed then
    begin
      if not (Terms.is_true t1) then
	begin
	  print_string (if !nice_tex then "\\wedge " else "\\ \\&\\&\\ ");
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
	  Std | If | GuessCst | SepLetFun | Tuple | Event | NonUniqueEvent -> 
	    print_id "\\kwf{" f.f_name "}";
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
		print_string (" " ^ (match f.f_name with
		| "=" -> " = "
		| "<>" -> " \\neq "
		| "<A>" -> " \\mathbin{<A>} "
		| ">>=" -> " \\mathbin{>>=} "
		| _ -> f.f_name) ^ " ");
		display_term_paren AllInfix AllProcess t2
	    | _ -> Parsing_helper.internal_error "Infix operators need two arguments (display)"
	    end
	| Or | And ->
	    match l with
	      [t1;t2] -> 
		display_term_paren (AllInfixExcept f) AllProcess t1;
		print_string (" " ^ (match f.f_name with
		  "&&" -> if !nice_tex then "\\wedge " else "\\ \\&\\&\\ "
		| "||" -> if !nice_tex then "\\vee " else "\\ \\|\\|\\ "
		| _ -> f.f_name) ^ " ");
		display_term_paren (AllInfixExcept f) AllProcess t2
	    | _ -> Parsing_helper.internal_error "Infix operators need two arguments (display)"
 	    
      end
  | TestE(t1,t2,t3) ->
      print_string "\\kw{if}\\ ";
      display_term_paren NoInfix AllProcess t1;
      print_string "\\ \\kw{then}\\ ";
      display_term_paren AllInfix ProcessMayHaveElseBranch t2;
      print_string "\\ \\kw{else}\\ ";
      display_term_paren AllInfix NoProcess t3
  | FindE([([],def_list,t1,t2)],t3, find_info) ->
      print_string "\\kw{if}\\ ";
      display_findcond (def_list, t1);
      print_string "\\ \\kw{then}\\ ";
      display_term_paren AllInfix ProcessMayHaveElseBranch t2;
      print_string "\\ \\kw{else}\\ ";
      display_term_paren AllInfix NoProcess t3
  | FindE(l0, t3, find_info) ->
      let first = ref true in
      print_string "\\kw{find}\\ ";
      display_find_info find_info;
      List.iter (fun (bl, def_list, t1, t2) ->
	if !first then
	  first := false
	else if !nice_tex then
	  print_string "\\ \\oplus\\ "
	else
	  print_string "\\ \\kw{orfind}\\ ";
	display_list (fun (b,b') -> display_binder_with_array b; print_string " = "; display_repl_index_with_type b') bl;
	print_string "\\ \\kw{suchthat}\\ ";
	display_findcond (def_list, t1);
	print_string "\\ \\kw{then}\\ ";
	display_term_paren AllInfix ProcessMayHaveElseBranch  t2;
	(* print_string "$\\\\\n$"  Commented out because going to the next line inside a term 
	   causes a bug, for instance when the term is in \coutput. However, the drawback is that
	   we may get very long lines. If I go to the next line, I should align somehow... *)) l0;
      print_string "\\ \\kw{else}\\ ";
      display_term_paren AllInfix NoProcess t3      
  | LetE(pat, t1, t2, topt) ->
      begin
	match pat with
	  PatVar b when (!Settings.front_end) == Settings.Oracles ->
	    display_binder_with_type b;
	    print_string " \\store ";
	    display_term_paren NoInfix AllProcess t1;
	    print_string "; ";	    
	| _ ->
	    print_string "\\kw{let}\\ ";
	    display_pattern pat;
	    print_string " = ";
	    display_term_paren NoInfix AllProcess t1;
	    print_string "\\ \\kw{in}\\ "
      end;
      display_term_paren AllInfix ProcessMayHaveElseBranch t2;
      begin
	match topt with
	  None -> ()
	| Some t3 ->
	    print_string "\\ \\kw{else}\\ ";
	    display_term_paren AllInfix NoProcess t3      
      end
  | ResE(b,t) ->
      display_restr b;
      print_string ";\\ ";
      display_term_paren AllInfix NoProcess t
  | EventAbortE(f) ->
      print_string "\\kw{event\\string_abort}\\ ";
      print_id "\\kwf{" f.f_name "}"      
  | EventE(t, p) ->
      print_string "\\kw{event}\\ ";
      display_term t;
      print_string ";\\ ";
      display_term_paren AllInfix NoProcess t
  | GetE(tbl, patl, topt, p1, p2, find_info) ->
      print_string "\\kw{get}\\ ";
      display_find_info find_info;
      display_table tbl;
      print_string "(";
      display_list display_pattern patl;
      print_string ")";
      (
        match topt with 
            None -> ();
          | Some t -> 
              print_string "\\ \\kw{suchthat}\\ ";
              display_term_paren NoInfix AllProcess t
      );
      print_string "\\ \\kw{in}\\ ";
      display_term_paren AllInfix ProcessMayHaveElseBranch p1;
      print_string "\\ \\kw{else}\\ ";
      display_term_paren AllInfix NoProcess p2
  | InsertE (tbl,tl,p) ->
      print_string "\\kw{insert}\\ ";
      display_table tbl;
      print_string "(";
      display_list (display_term_paren NoInfix AllProcess) tl;
      print_string "); ";
      display_term_paren AllInfix NoProcess p

and display_term_paren infix_paren process_paren t =
  let infix_paren' = 
    if (!display_occurrences) || (List.memq t.t_occ (!Display.useful_occs)) then
      begin
	print_string "\\{";
	print_string (string_of_int t.t_occ);
	print_string "\\}";
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
    | FunApp({ f_cat = Std | If | GuessCst | SepLetFun | Tuple | Event | NonUniqueEvent },_) -> false
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
	  | ProcessMayHaveElseBranch -> Display.may_have_elset t
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
      print_id "\\kwf{" f.f_name "}";
      print_string "(";
      display_list display_pattern l;
      print_string ")"
  | PatEqual t ->
      print_string "=";
      display_term t

(* Display term with appropriate parentheses around *)

let display_term t = display_term_paren AllInfix AllProcess t

(* Display quantified variables *)

let rec display_binder_list_with_type = function
  | [] -> assert false
  | b::bl ->
      let (same_type, other_type) = List.partition (fun b' -> b'.btype == b.btype) bl in
      display_list display_binder (b::same_type);
      display_type_info b.btype;
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
  print_string "$\\kw{equation}\\ ";
  display_quantified "\\forall " bl;
  display_term t;
  if not (Terms.is_true side_cond) then
    begin
      print_string "\\ \\kw{if}\\ ";
      display_term side_cond
    end;
  print_string "$\\\\\n"

(* Equivalences *)

let display_action = function
    AFunApp f -> 
      begin
	match f.f_cat with
	  Tuple -> 
	    print_string "(";
	    display_list display_type (fst f.f_type);
	    print_string ")"	    
	| LetEqual | Equal | Diff | ForAllDiff ->
	    print_string (if f.f_cat = Diff then " \\neq " else ("\\kwf{" ^ f.f_name ^ "}"));
	    print_id " \\kwt{" (List.hd (fst f.f_type)).tname "}"
	| And -> print_string (if !nice_tex then "\\wedge " else "\\ \\&\\&\\ ")
	| Or -> print_string (if !nice_tex then "\\vee " else "\\ \\|\\|\\ ")
	| _ -> print_id "\\kwf{" f.f_name "}"
      end
  | APatFunApp f -> 
      begin
	match f.f_cat with
	  Tuple -> 
	    print_string "\\kw{let}\\ (";
	    display_list display_type (fst f.f_type);
	    print_string ")"
	| _ ->
	    print_id "\\kw{let}\\ \\kwf{" f.f_name "}"
      end
  | AReplIndex -> 
      if (!Settings.front_end) == Settings.Oracles then
	print_string "\\kw{foreach}"
      else
	print_string "!"
  | AArrayAccess n -> print_string ("[" ^ (string_of_int n) ^ "]")
  | ANew t -> 
      if (!Settings.front_end) == Settings.Oracles then
	print_string "\\getR "
      else
	print_string "\\kw{new}\\ ";
      display_type t
  | ANewChannel -> 
      if (!Settings.front_end) == Settings.Oracles then
	print_string "\\kw{newOracle}"
      else
	print_string "\\kw{newChannel}"
  | AIf -> print_string "\\kw{if}"
  | AFind n -> print_string ("\\kw{find}\\ " ^ (string_of_int n))
  | AOut (tl,t) -> 
      if (!Settings.front_end) == Settings.Oracles then
	Parsing_helper.internal_error "out action should not occur in oracles front-end";
      print_string "\\kw{out}\\ ";
      if tl != [] then
	begin
	  print_string "[";
	  display_list display_type tl;
	  print_string "]\\ "
	end;
      display_type t
  | AIn n -> 
      if (!Settings.front_end) == Settings.Oracles then
	Parsing_helper.internal_error "in action should not occur in oracles front-end";
      print_string ("\\kw{in}\\ " ^ (string_of_int n))

let display_time_id cat =
  match cat with
  | Game(g) ->
      print_string "\\kw{time} + \\kw{time}(\\mathit{game}\\ ";
      print_string (Display.get_game_id g);
      print_string ")"
  | Context(g) -> 
      print_string "\\kw{time} + \\kw{time}(\\mathit{context\\ for\\ game}\\ ";
      print_string (Display.get_game_id g);
      print_string ")"
  | _ -> ()

let display_pub_vars pub_vars =
  if pub_vars <> [] then
    begin
      print_string " with public variables $";
      display_list display_binder pub_vars;
      print_string "$"
    end

let display_pub_vars_math_mode pub_vars =
  if pub_vars <> [] then
    begin
      print_string "\\textrm{ with public variables }";
      display_list display_binder pub_vars
    end

let display_event (b,t) =
  print_string (if b then "\\kw{inj\\textrm{-}event}(" else "\\kw{event}(");
  display_term t;
  print_string ")"

	
let rec display_query1 = function
    [] -> Parsing_helper.internal_error "List should not be empty"
  | [x] -> display_event x
  | x::l ->
      display_event x;
      print_string (if !nice_tex then " \\wedge " else "\\ \\&\\&\\ ");
      display_query1 l

let rec display_query2 = function
    QEvent(b,t) ->
      display_event (b,t)
  | QTerm t ->
      display_term t
  | QOr(t1,t2) ->
      print_string "(";
      display_query2 t1;
      print_string (if !nice_tex then " \\vee " else "\\ \\|\\|\\ ");
      display_query2 t2;
      print_string ")"
  | QAnd(t1,t2) ->
      print_string "(";
      display_query2 t1;
      print_string (if !nice_tex then " \\wedge " else "\\ \\&\\&\\ ");
      display_query2 t2;
      print_string ")"

let display_query3 = function
  | QSecret (b,pub_vars,options) -> 
      begin
	match options with
	| RealOrRandom onesession ->
	    if onesession then print_string "one-session "
	| Reachability onesession ->
	    if onesession then print_string "one-session ";
	    print_string "reachability "
	| Bit ->
	    print_string "bit "
      end;
      print_string "secrecy of $"; 
      display_binder b; 
      print_string "$";
      display_pub_vars pub_vars
  | QEventQ(t1,t2,pub_vars) ->
      let (forall, exists) = Terms.collect_vars_corresp t1 t2 in
      print_string "$";
      display_quantified "\\forall " forall;
      display_query1 t1;
      print_string " \\Longrightarrow ";
      display_quantified "\\exists " exists;
      display_query2 t2;
      print_string "$";
      display_pub_vars pub_vars
  | AbsentQuery ->
      print_string "indistinguishability from the final game"
  | QEquivalenceFinal(g', pub_vars) ->
      print_string ("indistinguishability from game " ^ (Display.get_game_id g')); 
      display_pub_vars pub_vars
  | QEquivalence(state,pub_vars,_) ->
      let g' = Display.get_initial_game state in
      if g'.game_number = -1 then
	print_string "indistinguishability from other input game"
      else
	print_string ("indistinguishability from game " ^
		      (string_of_int g'.game_number));
      display_pub_vars pub_vars      

	
let display_query (q,g) = 
  match q with 
    AbsentQuery -> 
      if g.game_number <> 1 then
	print_string ("indistinguishability between game "^(Display.get_game_id g)^" and the final game")
      else
	print_string "indistinguishability between the input game and the final game"
  | QEquivalence (state, pub_vars,_) ->
      let g' = Display.get_initial_game state in
      print_string ("indistinguishability between game " ^
		    (Display.get_game_id g) ^
		    " and game " ^
		    (Display.get_game_id g'));
      display_pub_vars pub_vars
  | QEquivalenceFinal(g', pub_vars) ->
      print_string ("indistinguishability between game " ^
		    (Display.get_game_id g) ^
		    " and game " ^
		    (Display.get_game_id g')); 
      display_pub_vars pub_vars
  | _ ->
      display_query3 q;
      if g.game_number <> 1 then
	print_string (" in game " ^ (Display.get_game_id g))  

let rec display_proba ?(separate_time = false) level = function
    Proba (p,l) -> 
      print_id "\\var{" p.prname "}";
      if l != [] then
	begin
	  print_string "(";
	  display_list_break (display_proba ~separate_time 0) l;
	  print_string ")"
	end
  | Count p -> print_id "\\kwp{" p.pname "}"
  | OCount (c,n) ->
      print_string "\\#";
      if n > 0 then
	begin
	  print_id "(\\kwc{" c.cname "}";
	  print_string "\\ \\kw{foreach}\\ \\mathrm{first\\ ";
	  if n = 1 then
	    print_string "replication})"
	  else
	    print_string ((string_of_int n)^"\\ replications})");
	end
      else
	print_id "\\kwc{" c.cname "}"
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
      print_string "\\kw{max}(";
      display_list_break (display_proba ~separate_time 0) l;
      print_string ")"
  | Min(l) -> 
      print_string "\\kw{min}(";
      display_list_break (display_proba ~separate_time 0) l;
      print_string ")"
  | Mul(x,y) ->
      if level > 3 then print_string "(";
      display_proba ~separate_time 3 x;
      print_string " \\times ";
      display_proba ~separate_time 3 y;
      if level > 3 then print_string ")"
  | Power(x,n) ->
      display_proba ~separate_time 5 x;
      print_string "^{";
      print_int n;
      print_string "}"
  | Zero -> print_string "0"      
  | Cst n -> print_string (Printf.sprintf "%g" n)
  | Div(x,y) ->
      if level > 3 then print_string "(";
      display_proba ~separate_time 3 x;
      print_string " / ";
      display_proba ~separate_time 4 y;
      if level > 3 then print_string ")"
  | Card t ->
      print_id "|\\kwt{" t.tname "}|"
  | AttTime ->
      print_string "\\kw{time}"
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
	  print_id "\\var{" tid "}"
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
      print_string "\\kw{time}(";
      display_action act;
      if pl != [] then
	begin
	  print_string ", ";
	  display_list_break (display_proba ~separate_time 0) pl
	end;
      print_string ")"
  | Maxlength(g,t) ->
      print_string "\\kw{maxlength}(";
      if g == Terms.lhs_game then
	print_string "\\mathit{LHS}: "
      else if g == Terms.rhs_game then
	print_string "\\mathit{RHS}: "
      else if g == Terms.lhs_game_nodisplay then
	()
      else
	print_string ("\\mathit{game}\\ " ^ (Display.get_game_id g) ^ ": ");
      display_term t;
      print_string ")"
  | TypeMaxlength(ty) ->
      print_id "\\kw{maxlength}(\\kwt{" ty.tname "})"
  | EpsFind ->
      print_string "\\kw{eps\\_find}"
  | EpsRand ty ->
      print_id "\\kw{eps\\_rand}(\\kwt{" ty.tname "})"
  | PColl1Rand ty ->
      print_id "\\kw{Pcoll1rand}(\\kwt{" ty.tname "})"
  | PColl2Rand ty ->
      print_id "\\kw{Pcoll2rand}(\\kwt{" ty.tname "})"
  | Length(f,pl) ->
      print_string "\\kw{length}(";
      begin
	match f.f_cat with
	  Tuple -> 
	    print_string "(";
	    display_list display_type (fst f.f_type);
	    print_string ")"	      
	| _ -> print_id "\\kwf{" f.f_name "}"
      end;
      if pl != [] then
	begin
	  print_string ", \\allowbreak ";
	  display_list_break (display_proba ~separate_time 0) pl
	end;
      print_string ")"
  | OptimIf(cond,p1,p2) ->
      print_string "(\\kw{optim-if}\\ ";
      display_optim_cond ~separate_time cond;
      print_string "\\ \\kw{then}\\ ";
      display_proba ~separate_time 0 p1;
      print_string "\\ \\kw{else}\\ ";
      display_proba ~separate_time 0 p2;
      print_string ")"
  | Advt(g,cur_q,ql) ->
      let (ql_otherq, ql_eventq) = List.partition (fun (q,_) ->
	(Terms.get_event_query q == None)) ql
      in
      print_string (if cur_q || ql_otherq != [] then "\\mathsf{Adv}" else "\\Pr");
      print_string "[\\mathrm{Game}\\ ";
      print_string (Display.get_game_id g);
      print_string "$: ";
      if cur_q then
	begin
	  assert(ql_otherq == []);
	  print_string "current\\_queries"
	end
      else
	begin
	  match ql_otherq with
	  | [q,_] -> display_query3 q
	  | [] -> ()
	  | _ -> assert false
	end;
      print_string "$";
      if (cur_q || ql_otherq != []) && ql_eventq != [] then print_string ", ";
      display_list_sep " \\vee "
	(fun (q,_) ->
	  match Terms.get_event_query q with
	  | Some f -> print_id "\\kwf{" f.f_name "}"
	  | None -> assert false) ql_eventq;
      print_string "]"
  | ProbaAssume ->
      print_string "\\Pr[COMMAND NOT CHECKED]"

and display_optim_cond ~separate_time = function
  | OCProbaFun(s,[p1; p2]) ->
      display_proba ~separate_time 0 p1;
      print_string (match s with
      | "<=" -> "\\leq "
      | s -> s  (* "=", "<" *));
      display_proba ~separate_time 0 p2
  | OCProbaFun(s,[p1]) ->
      print_string ((match s with
      | "is-cst" -> "\\kwf{is\\textrm{-}cst}"
      | _ -> Parsing_helper.internal_error "display_optim_cond only allowed probability unary function is-cst"
	  )^"(");
      display_proba ~separate_time 0 p1;
      print_string ")"
  | OCBoolFun(s,[c1; c2]) ->
      display_optim_cond ~separate_time c1;
      print_string (match s with
      | "&&" -> if !nice_tex then "\\wedge " else "\\ \\&\\&\\ "
      | "||" -> if !nice_tex then "\\vee " else "\\ \\|\\|\\ "
      | _ -> Parsing_helper.internal_error "display_optim_cond: only allowed boolean functions && ||");
      display_optim_cond ~separate_time c2
  | _ -> Parsing_helper.internal_error "display_optim_cond: probability fcts should be unary or binary, boolean fcts should be binary"
    
let display_one_set ?separate_time = function
    SetProba r ->
      display_proba ?separate_time 0 r
  | SetEvent(f, g, pub_vars, _) ->
      print_id "\\Pr[\\kw{event}\\ \\kwf{" f.f_name "}\\textrm{ in game }";
      print_string (Display.get_game_id g);
      display_pub_vars_math_mode pub_vars;
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
      print_string " up to probability $";
      display_proba ?separate_time 0 p;
      print_string "$"
    end

(* Result of an oracle in an equivalence *)

let rec display_procasterm t = 
  if (!display_occurrences) || (List.memq t.t_occ (!Display.useful_occs)) then
    begin
      print_string "\\{";
      print_string (string_of_int t.t_occ);
      print_string "\\}"
    end;
  match t.t_desc with
    Var _ | FunApp _ ->
      print_string "\\kw{return}(";
      display_term t;
      print_string ")"
  | ReplIndex _ -> 
      Parsing_helper.internal_error "ReplIndex unexpected in display_procasterm"      
  | TestE(t1,t2,t3) ->
      print_string "\\kw{if}\\ ";
      display_term t1;
      print_string "\\ \\kw{then}\\ ";
      display_procasterm t2;
      print_string "\\ \\kw{else}\\ ";
      display_procasterm t3
  | FindE([([],def_list,t1,t2)],t3,find_info) ->
      print_string "\\kw{if}\\ ";
      display_findcond (def_list, t1);
      print_string "\\ \\kw{then}\\ ";
      display_procasterm t2;
      print_string "\\ \\kw{else}\\ ";
      display_procasterm t3
  | FindE(l0, t3, find_info) ->
      let first = ref true in
      print_string "\\kw{find}\\ ";
      display_find_info find_info;
      List.iter (fun (bl, def_list, t1, t2) ->
	if !first then
	  first := false
	else if !nice_tex then
	  print_string "\\ \\oplus\\ "
	else
	  print_string "\\ \\kw{orfind}\\ ";
	display_list (fun (b,b') -> display_binder_with_array b; print_string " = "; display_repl_index_with_type b') bl;
	print_string "\\ \\kw{suchthat}\\ ";
	display_findcond (def_list, t1);
	print_string "\\ \\kw{then}\\ ";
	display_procasterm t2;
	print_string "$\\\\\n$"  (* Should align somehow... *)) l0;
      print_string "\\ \\kw{else}\\ ";
      display_procasterm t3      
  | LetE(pat, t1, t2, topt) ->
      begin
	match pat with
	  PatVar b when (!Settings.front_end) == Settings.Oracles ->
	    display_binder_with_type b;
	    print_string " \\store ";
	    display_term t1;
	    print_string "; ";	    
	| _ ->
	    print_string "\\kw{let}\\ ";
	    display_pattern pat;
	    print_string " = ";
	    display_term t1;
	    print_string "\\ \\kw{in}\\ "
      end;
      display_procasterm t2;
      begin
	match topt with
	  None -> ()
	| Some t3 ->
	    print_string "\\ \\kw{else}\\ ";
	    display_procasterm t3      
      end
  | ResE(b,t) ->
      display_restr b;
      print_string ";\\ ";
      display_procasterm t
  | EventAbortE(f) -> 
      print_string "\\kw{event\\string_abort}\\ ";
      print_id "\\kwf{" f.f_name "}"      
  | EventE _ | GetE _ | InsertE _ ->
      Parsing_helper.internal_error "event/get/insert not allowed in definitions of crypto primitives"


let rec display_fungroup indent = function
    ReplRestr(repl_opt, restr, funlist) ->
      begin
	match repl_opt with
	| Some repl ->
	    display_repl repl; 
	    print_string "\\ "
	| None -> ()
      end;
      List.iter (fun (b,ext,opt) ->
	display_restr b;
	if opt = Unchanged then
	  print_string "\\ [unchanged]"; 
	print_string ";\\ ") restr;
      begin
	match funlist with 
	  [f] -> 
	    display_fungroup indent f
	| _ -> 
	    print_string ("($\\\\\n$" ^ indent);
	    let first = ref true in
	    List.iter (fun f ->
	      if !first then
		first := false
	      else
		print_string ("\\ |$\\\\\n$" ^ indent);
	      display_fungroup (indent ^ "\\quad ") f;
	      ) funlist;
	    print_string ")"
      end
  | Fun(ch, args, res, (priority, options)) ->
      print_id "\\kwc{" ch.cname "}(";
      display_list display_binder_with_type args;
      print_string ")";
      if priority != 0 then
	begin
	  print_string " [";
	  print_string (string_of_int priority);
	  print_string "]"
	end;
      begin
	match options with
	  StdOpt -> ()
	| UsefulChange -> print_string " [useful\\_change]"
      end;
      print_string " := ";
      display_procasterm res

let display_eqmember l =
  display_list (fun (fg, mode) ->
    print_string "\\quad";
    display_fungroup "\\qquad  " fg;
    if mode = AllEquiv then print_string " [all]") l

let display_eqname = function
    NoName -> ()
  | CstName(s,_) -> print_id "\\kwc{" s "}"
  | ParName((s,_),(p,_)) -> print_id "\\kwc{" s "}"; print_id "(\\kwf{" p "})"

let display_equiv ((n,m1,m2,set,opt,opt2),_) =
  print_string "$\\kw{equiv}";
  begin
    match n with
      NoName -> ()
    | _ ->  print_string "("; display_eqname n; print_string ")"
  end;
  print_string "$\\\\\n$";
  display_eqmember m1;
  print_string "$\\\\\n$";
  if !nice_tex then
    begin
      print_string "\\approx_{";
      display_set set;
      print_string "}"
    end
  else
    begin
      print_string "\\Leftarrow(";
      display_set set;
      print_string ")\\Rightarrow"
    end;
  begin
    match opt, opt2 with
      StdEqopt, Decisional -> ()
    | PrioEqopt n, Decisional -> print_string ("\\ [" ^ (string_of_int n) ^ "]")
    | ManualEqopt, Decisional -> print_string "\\ [manual]"
    | StdEqopt, Computational -> print_string "\\ [computational]"
    | PrioEqopt n, Computational -> print_string ("\\ [" ^ (string_of_int n) ^ "]\\ [computational]")
    | ManualEqopt, Computational -> print_string "\\ [manual, computational]"
  end;
  print_string "$\\\\\n$";
  display_eqmember m2;
  print_string "$\\\\\n"

let display_equiv_with_name (((n,_,_,_,_,_),_) as eq) =
  match n with
    NoName -> display_equiv eq
  | _ -> print_string "$"; display_eqname n; print_string "$"

(* Processes *)

let display_channel c tl =
  print_id "\\kwc{" c.cname "}";
  if tl != [] then
    begin
      print_string "[";
      display_list display_term tl;
      print_string "]"
    end
  
let rec split_par p = 
  match p.i_desc with
    Par(p1,p2) -> (split_par p1) @ (split_par p2)
  | _ -> [p]

let occ_space() =
  print_string "\\>$"

let rec display_process indent p = 
  if (!display_occurrences) || (List.memq p.i_occ (!Display.useful_occs)) then
    begin
      print_string "\\>\\{";
      print_string (string_of_int p.i_occ);
      print_string "\\}\\'$"
    end
  else
    occ_space();
  match p.i_desc with
    Nil -> 
      print_string (indent ^ "0$\\\\\n")
  | Par _ ->
      let pl = split_par p in
      print_string (indent ^ "($\\\\\n");
      let first = ref true in
      List.iter (fun pi ->
	if !first then first := false else 
	begin
	  occ_space();
	  print_string (indent ^ ") \\mid ($\\\\\n");
	end;
	display_process (indent ^ "\\quad ") pi) pl;
      occ_space();
      print_string (indent ^ ")$\\\\\n")	  
  | Repl(b,p) ->
      print_string indent;
      display_repl b;
      print_string "$\\\\\n";
      display_process indent p
  | Input((c,tl),pat,p) ->
      if (!Settings.front_end) == Settings.Oracles then
	begin
	  print_id (indent ^ "\\kwc{") c.cname "}";
	  if (!display_arrays) && (tl != []) then
	    begin
	      print_string "[";
	      display_list display_term tl;
	      print_string "]"
	    end;
	  display_pattern pat;
	  print_string " :=$\\\\\n";
	  display_oprocess indent p
	end
      else if !nice_tex then
	begin
	  print_string (indent ^ "\\cinput{");
	  display_channel c tl;
	  print_string "}{";
	  begin
	    match pat with
	      PatTuple(f,l) when f.f_cat == Tuple ->
		display_list display_pattern l
	    | _ -> display_pattern pat
	  end;
	  print_string "}";
	  display_optoprocess indent p
	end
      else
	begin
	  print_string (indent ^ "\\kw{in}(");
	  display_channel c tl;
	  print_string ", ";
	  display_pattern pat;
	  print_string ")";
	  display_optoprocess indent p
	end

and display_oprocess indent p = 
  if (!display_occurrences) || (List.memq p.p_occ (!Display.useful_occs)) then
    begin
      print_string "\\>\\{";
      print_string (string_of_int p.p_occ);
      print_string "\\}\\'$"
    end
  else
    occ_space();
  match p.p_desc with
    Yield -> 
      if (!Settings.front_end) == Settings.Oracles then
	print_string (indent ^ "\\kw{end}$\\\\\n")
      else if !nice_tex then
	print_string (indent ^ "\\overline{0}$\\\\\n")
      else
	print_string (indent ^ "\\kw{yield}$\\\\\n")
  | EventAbort f -> 
      print_string (indent ^ "\\kw{event\\string_abort}\\ ");
      print_id "\\kwf{" f.f_name "}";
      print_string "$\\\\\n"
  | Restr(b,p) ->
      print_string indent;
      display_restr b;
      display_optoprocess indent p
  | Test(t,p1,p2) ->
      print_string (indent ^ "\\kw{if}\\ ");
      display_term t;
      print_string "\\ \\kw{then}$\\\\\n";
      if p2.p_desc = Yield then
	display_oprocess indent p1
      else
	begin
	  display_oprocess_paren indent p1;
	  occ_space();
	  print_string (indent ^ "\\kw{else}$\\\\\n");
	  display_oprocess (indent ^ "\\quad ") p2
	end
  | Find([([],def_list,t,p1)],p2,find_info) ->
      print_string (indent ^ "\\kw{if}\\ ");
      display_findcond (def_list,t);
      print_string "\\ \\kw{then}$\\\\\n";
      if p2.p_desc = Yield then
	display_oprocess indent p1
      else
	begin
	  display_oprocess_paren indent p1;
	  occ_space();
	  print_string (indent ^ "\\kw{else}$\\\\\n");
	  display_oprocess (indent ^ "\\quad ") p2
	end
  | Find(l0,p2,find_info) ->
      let first = ref true in
      let single_branch = (p2.p_desc = Yield) && (List.length l0 = 1) in
      print_string (indent ^ "\\kw{find}\\ ");
      display_find_info find_info;
      List.iter (fun (bl,def_list,t,p1) ->
	if !first then
	  first := false
	else 
	  begin
	    occ_space();
	    if !nice_tex then
	      print_string (indent ^ "\\oplus\\ ")
	    else
	      print_string (indent ^ "\\kw{orfind}\\ ")
	  end;
	display_list (fun (b,b') -> display_binder_with_array b; print_string " = "; display_repl_index_with_type b') bl;
	print_string "\\ \\kw{suchthat}\\ ";
	display_findcond (def_list,t);
	print_string "\\ \\kw{then}$\\\\\n";
	if single_branch then
	  display_oprocess indent p1
	else
	  display_oprocess_paren indent p1
	  ) l0;
      if l0 == [] then print_string "$\\\\\n";
      if p2.p_desc != Yield then
	begin
	  occ_space();
	  print_string (indent ^ "\\kw{else}$\\\\\n");
	  display_oprocess (indent ^ "\\quad ") p2
	end
  | Output((c,tl),t2,p) ->
      if (!Settings.front_end) == Settings.Oracles then
	begin
	  print_string (indent ^ "\\kw{return}");
	  display_term t2
	end
      else if !nice_tex then
	begin
	  print_string (indent ^ "\\coutput{");
	  display_channel c tl;
	  print_string "}{";
	  begin
	    match t2.t_desc with
	      FunApp(f, l) when f.f_cat == Tuple ->
		display_list display_term l
	    | _ -> display_term t2
	  end;
	  print_string "}"
	end
      else
	begin
	  print_string (indent ^ "\\kw{out}(");
	  display_channel c tl;
	  print_string ", ";
	  display_term t2;
	  print_string ")"
	end;
      display_optprocess indent p
  | Let(pat,t,p1,p2) ->
      begin
	match pat with
	  PatVar b when (!Settings.front_end) == Settings.Oracles ->
	    print_string indent;
	    display_binder_with_type b;
	    print_string " \\store ";
	    display_term t;
	    display_optoprocess indent p1
	| _ ->
	    print_string (indent ^ "\\kw{let}\\ ");
	    display_pattern pat;
	    print_string " = ";
	    display_term t;
	    if (p1.p_desc = Yield) && (p2.p_desc = Yield) then
	      print_string "$\\\\\n"
	    else
	      begin
		print_string "\\ \\kw{in}$\\\\\n";
		if p2.p_desc = Yield then
		  display_oprocess indent p1
		else
		  begin
		    display_oprocess_paren indent p1;
		    occ_space();
		    print_string (indent ^ "\\kw{else}$\\\\\n");
		    display_oprocess (indent ^ "\\quad ") p2
		  end
	      end
      end
  | EventP(t,p) ->
      print_string (indent ^ "\\kw{event}\\ ");
      display_term t;
      display_optoprocess indent p
  | Get (tbl,patl,topt,p1,p2,find_info) ->
      print_string (indent ^ "\\kw{get}\\ ");
      display_find_info find_info;
      display_table tbl;
      print_string "(";
      display_list display_pattern patl;
      print_string ")";
      (
        match topt with 
            None -> ();
          | Some t -> 
              print_string "\\ \\kw{suchthat}\\ ";
              display_term t
      );
      if (p1.p_desc = Yield) && (p2.p_desc = Yield) then
	print_string "$\\\\\n"
      else
	begin
	  print_string "\\ \\kw{in}$\\\\\n";
	  if p2.p_desc = Yield then
	    display_oprocess indent p1
	  else
	    begin
	      display_oprocess_paren indent p1;
	      occ_space();
	      print_string (indent ^ "\\kw{else}$\\\\\n");
	      display_oprocess (indent ^ "\\quad  ") p2
	    end
	end
  | Insert (tbl,tl,p) ->
      print_string (indent ^ "\\kw{insert}\\ ");
      display_table tbl;
      print_string "(";
      display_list display_term tl;
      print_string ")";
      display_optoprocess indent p


and display_optprocess indent p =
  if p.i_desc = Nil then 
    print_string "$\\\\\n"
  else
    begin
      print_string ";$\\\\\n";
      display_process indent p
    end
      
and display_optoprocess indent p =
  if p.p_desc = Yield then 
    print_string "$\\\\\n"
  else
    begin
      print_string ";$\\\\\n";
      display_oprocess indent p
    end

and display_oprocess_paren indent p =
  if Display.may_have_elseo p then
    begin
      occ_space();
      print_string (indent ^ "($\\\\\n");
      display_oprocess (indent ^ "\\quad ") p;
      occ_space();
      print_string (indent ^ ")$\\\\\n")
    end
  else
    display_oprocess (indent ^ "\\quad ") p

let display_process p =
  display_process "" p;
  print_string "\\\\\n"
	
(* Instructions *)

let display_rem_set = function
  | Binders l -> 
      print_string "binder $";
      display_list_sep "\\ " display_binder l;
      print_string "$"
  | Minimal -> 
      print_string "useless"
  | FindCond -> 
      print_string "findcond"
  | EqSide ->
      print_string "right-hand side of equiv"
  | NoRemAssign -> assert false

let display_move_set = function
    MAll -> print_string "all\\ binders"
  | MNoArrayRef -> print_string "binders\\ without\\ array\\ references"
  | MNew -> print_string "all\\ new's"
  | MNewNoArrayRef -> print_string "new's\\ without\\ array\\ references"
  | MLet -> print_string "all\\ let's"
  | MBinders l -> 
      print_string "binder $";
      display_list_sep "\\ " display_binder l;
      print_string "$"
  | MUp(bl,occ,ext) ->
      print_string "up $";
      display_list_sep "\\ " display_binder bl;
      print_string "$ to occurrence ";
      print_string (string_of_int occ)

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
	  print_string "\\textrm{variables: }";
	  display_list (fun (b1,b2) -> display_binder b1; print_string " \\rightarrow "; display_binder b2) vm;
	  if vm != [] && vl != [] then print_string ", ";
	  display_list display_binder vl;
	  if stop then print_string ".";
	  if tmopt != None then print_string ";"
      end;
      begin
      match tmopt with
	None -> ()
      | Some(tm,stop) ->
	  print_string "\\textrm{terms: }";
	  display_list (fun (occ,t) -> print_int occ; print_string " \\rightarrow "; display_term t) tm;
	  if stop then print_string "."
      end
	      
    
let display_with_user_info user_info =
  match user_info with
    VarList([],_) | Detailed((None | Some([],[],_)), (None | Some([],_))) -> ()
  | _ ->
      print_string " with $";
      display_user_info user_info;
      print_string "$"

let display_coll_elim = function
    CollVars l ->
      print_string "variables: ";
      display_list_break (fun s -> print_id "$\\var{" s "}$") l
  | CollTypes l ->
      print_string "types: ";
      display_list_break (fun s -> print_id "$\\kwt{" s "}$") l
  | CollTerms l -> print_string "terms: "; display_list_break print_int l
    
let display_instruct = function
    ExpandGetInsert_ProveUnique -> print_string "expand get, insert and prove unique annotations"
  | Expand -> print_string "expand"
  | Simplify(collector, l) ->
      print_string "simplify";
      if l != [] then
	begin
	  print_string " with collision elimination at ";
	  display_list_sep "; \\allowbreak " display_coll_elim l
	end;
      if collector != None then
	print_string " eliminating code unreachable when queries fail"
  | SimplifyNonexpanded ->
      print_string "simplify (non-expanded game)"
  | GlobalDepAnal (b,l) ->
      print_string "global dependency analysis on $";
      display_binder b;
      print_string "$";
      if l != [] then
	begin
	  print_string " with collision elimination at ";
	  display_list_sep "; \\allowbreak " display_coll_elim l
	end
  | MoveNewLet s -> print_string "move\\ "; display_move_set s
  | RemoveAssign (sarename_new, r) ->
      if sarename_new then
	print_string "SA rename new without array accesses";
      if sarename_new && (r != NoRemAssign) then
	print_string " and ";
      if r != NoRemAssign then
	begin
	  print_string "remove assignments of "; display_rem_set r
	end
  | UseVariable l -> print_string "use variable(s) $"; display_list display_binder l; print_string "$"
  | SArenaming b -> 
      print_string "SA rename $";
      display_binder b;
      print_string "$"
  | CryptoTransf(e, user_info) -> 
      print_string "equivalence ";
      display_equiv_with_name e;
      display_with_user_info user_info
  | InsertEvent(s,_,occ,_) ->
      print_id "insert event $\\kwf{" s "}$";
      print_string (" at occurrence " ^ (string_of_int occ))
  | InsertInstruct(s,ext_s,occ,ext_o) ->
      print_string "insert instruction ";
      display_string s; 
      print_string (" at occurrence " ^ (string_of_int occ))
  | ReplaceTerm(s,ext_s,occ,ext_o,check_opt) ->
      print_string ("replace term at occurrence " ^ (string_of_int occ) ^ " with ");
      display_string s;
      begin
	match check_opt with
	| Check -> ()
	| Assume -> print_string " (WARNING: equality not checked)"
      end
  | MergeArrays(bll, m) ->
      print_string "merge variables $";
      display_list (fun bl -> 
	print_string "("; 
	display_list (fun (b,_) -> display_binder b) bl;
	print_string ")") bll;
      print_string "$";
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
	display_up_to_proba ~separate_time:true proba) ql
  | IFocus(ql) ->
      print_string "focus on queries";
      List.iter (fun q -> print_string "\\\\\n\\qquad -- "; display_query3 q) ql
  | Guess arg ->
      begin
      print_string "guess ";
      match arg with
      | GuessVar((b,l),no_test,_) ->
	  print_string "the value of the variable ";
	  display_var b l;
	  if no_test then
	    print_string " no\\_test"
      | GuessRepl(repl_index,and_above,_) ->
	  print_string "the tested session for replication index ";
	  display_repl_index repl_index;
	  if and_above then print_string " and above"
      | GuessOcc(occ,and_above,_) ->
	  print_string "the tested session for the replication at ";
	  print_int occ;
	  if and_above then print_string " and above"
      end
  | GuessBranch(occ,no_test,_) ->
      print_string "guess branch at ";
      print_int occ;
      if no_test then
	print_string " no\\_test"
  | MoveIf arg ->
      begin
	match arg with
	| MovePos l ->
	    let (locc,lfun) = List.partition (function MoveOcc _ -> true | MoveFun _ -> false) l in
	    print_string "move if_fun function ";
	    if locc != [] then
	      begin
		print_string "to occurrence(s) ";
		display_list (function MoveOcc(n,_) -> print_int n | MoveFun _ -> assert false) l
	      end;
	    if locc != [] && lfun != [] then
	      print_string " and ";
	    if lfun != [] then
	      begin
		print_string "to above function(s) ";
		display_list (function MoveFun(f,_) -> print_id "$\\kwf{" f.f_name "}$" | MoveOcc _ -> assert false) l
	      end
	| MoveLevel n -> print_string ("move if_fun function "^(string_of_int n)^" level(s) up")
	| MoveToTerm lopt ->
	    match lopt with
	    | None -> print_string "transform if_fun function to if term everywhere"
	    | Some l ->
		print_string "transform if_fun function to if term at occurrence(s) ";
		display_list (fun (n,_) -> print_int n) l
      end
	  
(* Display transformation steps *)
	
let display_pat_simp t =
  print_string (match t with 
    DEqTest -> " (equality test)"
  | DExpandTuple -> " (tuple expanded)"
  | DImpossibleTuple -> " (tuple matching always fails)")

let display_pat_simp_list l =
  display_list (fun (pat, t) ->
    print_string "pattern $";
    display_pattern pat;
    print_string "$";
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
      print_string "\\qquad -- Replaced $";
      display_term t;
      print_string "$ with $";
      display_term t';
      print_string "$ at ";
      print_occ t.t_occ;
      print_string "\\\\\n"
  | STestTrue(p) ->
      print_string "\\qquad -- Test at ";
      print_occ (Terms.occ_from_pp p);
      print_string " always true\\\\\n"
  | STestFalse(p) ->
      print_string "\\qquad -- Test at ";
      print_occ (Terms.occ_from_pp p);
      print_string " always false\\\\\n"
  | STestMerge(p) ->
      print_string "\\qquad -- Merge branches of test at ";
      print_occ (Terms.occ_from_pp p);
      print_string "\\\\\n"
  | STestOr(p) ->
      print_string ("\\qquad -- Expand $" ^ (if !nice_tex then "\\vee " else "\\|\\|") ^ "$ in test at ");
      print_occ (Terms.occ_from_pp p);
      print_string "\\\\\n"
  | STestEElim(t) ->
      print_string "\\qquad -- Transformed test at ";
      print_occ t.t_occ;
      print_string " into a logical formula\\\\\n"
  | SFindBranchRemoved(p,br) -> 
      print_string "\\qquad -- Remove branch ";
      get_find_branch p br;
      print_string " in find at ";
      print_occ (Terms.occ_from_pp p);
      print_string "\\\\\n"
  | SFindBranchNotTaken(p,br) -> 
      print_string "\\qquad -- Branch ";
      get_find_branch p br;
      print_string " not taken in find at ";
      print_occ (Terms.occ_from_pp p);
      print_string "\\\\\n"
  | SFindSingleBranch(p,br) ->
      print_string "\\qquad -- A single branch always succeeds in find at ";
      print_occ (Terms.occ_from_pp p);
      print_string "\\\\\n"
  | SFindRemoved(p) ->
      print_string "\\qquad -- Find at ";
      print_occ (Terms.occ_from_pp p);
      print_string " removed (else branch kept if any)\\\\\n"
  | SFindElseRemoved(p) ->
      print_string "\\qquad -- Remove else branch of find at ";
      print_occ (Terms.occ_from_pp p);
      print_string "\\\\\n"
  | SFindBranchMerge(p, brl) ->
      if get_nbr_find_branch p = List.length brl then
	print_string "\\qquad -- Merge all branches of find at "
      else
	begin
	  print_string "\\qquad -- Merge branches ";
	  display_list (get_find_branch p) brl;
	  print_string " with else branch of find at ";
	end;
      print_occ (Terms.occ_from_pp p);
      print_string "\\\\\n"
  | SFindDeflist(p, def_list, def_list') ->
      if def_list == [] then
	print_string "\\qquad -- Replaced an empty defined condition"
      else
	begin
	  print_string "\\qquad -- Replaced defined condition $";
	  display_def_list def_list;
	  print_string "$"
	end;
      print_string " with ";
      if def_list' == [] then
	print_string "an empty condition"
      else 
	begin
	  print_string "$";
	  display_def_list def_list';
	  print_string "$"
	end;
      print_string " in find at ";
      print_occ (Terms.occ_from_pp p);
      print_string "\\\\\n"
  | SFindinFindCondition(p, t) ->
      print_string "\\qquad -- Simplified find at ";
      print_occ t.t_occ;
      print_string " in condition of find at ";
      print_occ (Terms.occ_from_pp p);
      print_string "\\\\\n"
  | SFindinFindBranch(p,p') ->
      print_string "\\qquad -- Simplified find at ";
      print_occ (Terms.occ_from_pp p');
      print_string " in branch of find at ";
      print_occ (Terms.occ_from_pp p);
      print_string "\\\\\n"
  | SFindtoTest(p) ->
      print_string "\\qquad -- Transformed find at ";
      print_occ (Terms.occ_from_pp p);
      print_string " into a test\\\\\n"
  | SFindIndexKnown(p, br, subst) ->
      print_string "\\qquad -- In branch ";
      get_find_branch p br;
      print_string " of find at ";
      print_occ (Terms.occ_from_pp p);
      print_string ", substituting ";
      display_list (fun (b,t) -> 
	print_string "$"; display_binder b; print_string "$ with $";
        display_term t; print_string "$") subst;
      print_string "\\\\\n" 
  | SFindInferUnique(p) ->
      print_string "\\qquad -- Inferred that find at ";
      print_occ (Terms.occ_from_pp p);
      print_string " is [unique]\\\\\n" 
                   
  | SLetElseRemoved(p) ->
      print_string "\\qquad -- Remove else branch of let at ";
      print_occ (Terms.occ_from_pp p);
      print_string "\\\\\n"
  | SLetRemoved(p) ->
      print_string "\\qquad -- Remove let at ";
      print_occ (Terms.occ_from_pp p);
      print_string "\\\\\n"
  | SLetSimplifyPattern(p, l) -> 
      print_string "\\qquad -- Simplify ";
      display_pat_simp_list l;
      print_string " at ";
      print_occ (Terms.occ_from_pp p);
      print_string "\\\\\n"

  | SResRemoved(p) ->
      print_string "\\qquad -- Remove random number generation at ";
      print_occ (Terms.occ_from_pp p);
      print_string "\\\\\n"
  | SResToAssign(p) ->
      print_string "\\qquad -- Transform unused random number generation at ";
      print_occ (Terms.occ_from_pp p);
      print_string " into constant assignment";
      print_string "\\\\\n"

  | SEventRemoved(p) ->
      print_string "\\qquad -- Removed event at ";
      print_occ (Terms.occ_from_pp p);
      print_string " (no longer used in queries)";
      print_string "\\\\\n"
	
  | SAdvLoses(p) ->
      print_string "\\qquad -- Adversary always loses at ";
      print_occ (Terms.occ_from_pp p);
      print_string "\\\\\n"

let display_detailed_ins = function
    DExpandGetInsert(t) -> 
      print_string "\\quad -- Expand get/insert for table $";
      display_table t;
      print_string "$\\\\\n"
  | DProveUnique p ->
      print_string "\\quad -- Proved that [unique] annotation at ";
      print_occ (Terms.occ_from_pp p);
      print_string " is correct\\\\\n";
  | DExpandIfFind(l) ->
      print_string "\\quad -- Expand if/find/let\\\\\n";
      List.iter display_simplif_step (List.rev l)
  | DSimplify(l) ->
      print_string "\\quad -- Simplification pass\\\\\n";
      List.iter display_simplif_step (List.rev l)
  | DGlobalDepAnal(b,coll_elim) ->
      print_string "\\quad -- Global dependency analysis on $";
      display_binder b;
      print_string "$";
      if coll_elim != [] then
	begin
	  print_string " with collision elimination at ";
	  display_list_sep "; \\allowbreak" display_coll_elim coll_elim
	end;
      print_string "\\\\\n"
  | DLetSimplifyPattern(let_p, l) ->
      print_string "\\quad -- Simplify ";
      display_pat_simp_list l;
      print_string " at ";
      print_occ (Terms.occ_from_pp let_p);
      print_string "\\\\\n"
  | DRemoveAssign(b, def_ch, usage_ch) ->
      print_string "\\quad -- Remove assignments on $";
      display_binder b;
      print_string (
	match def_ch with
	  DRemoveDef -> "$ (definition removed, "
	| DKeepDefPoint -> "$ (definition point kept, "
	| DKeepDef -> "$ (definition kept, ");
      print_string (
        match usage_ch with
	  DRemoveAll -> "all usages removed)\\\\\n"
	| DRemoveNonArray -> "array references kept)\\\\\n")
  | DUseVariable(b, rep_list) ->
      print_string "\\quad  -- Use variable $";
      display_binder b;
      print_string "$\\\\\n";
       List.iter (fun (t1,t2) ->
	print_string "\\qquad    -- $";
	display_term t1;
	print_string "$ replaced with $";
	display_term t2;
	print_string "$ at ";
	print_occ t1.t_occ;
	print_newline()
	  ) rep_list
  | DSArenaming(b, bl) ->
      print_string "\\quad -- Rename variable $";
      display_binder b;
      print_string "$ into $";
      display_list display_binder bl;
      print_string "$\\\\\n"
  | DMoveNew(b) ->
      print_string "\\quad -- Move random number generation $";
      display_binder b;
      print_string "$\\\\\n"
  | DMoveLet(b) ->
      print_string "\\quad -- Move assignment to $";
      display_binder b;
      print_string "$\\\\\n"      
  | DMoveNewUp(bl,occ,new_b) ->
      print_string "\\quad -- Move random number generation(s) $";
      display_list display_binder bl;
      print_string "$ upwards to occurrence ";
      print_occ occ;
      print_string " as $";
      display_binder new_b;
      print_string "$\\\\\n"      
  | DMoveLetUp(bl,occ,new_b) ->
      print_string "  - Move assignment(s) $";
      display_list display_binder bl;
      print_string "$ upwards to occurrence ";
      print_occ occ;
      print_string " as $";
      display_binder new_b;
      print_string "$\\\\\n"      
  | DCryptoTransf(e, user_info) ->
      print_string "\\quad -- Equivalence ";
      display_equiv_with_name e;
      display_with_user_info user_info;
      print_string "\\\\\n"
  | DInsertEvent _  | DInsertInstruct _ 
  | DReplaceTerm _  | DMergeArrays _ | DGuess _ | DGuessBranch _ ->
      (* Don't display anything since the detailed description is the
	 same as the high level one *)
      ()
  | DMergeBranches(p,l) ->
      begin
	match (p.p_desc, l) with
	  (Test _), _ ->
	    print_string "\\quad -- Merge branches of test at ";
	    print_occ p.p_occ
	| (Let _), _ ->
	    print_string "\\quad -- Merge branches of let at ";
	    print_occ p.p_occ
	| (Find(l0,_,_), l) when List.length l = List.length l0 + 1 ->
	    print_string "\\quad -- Merge all branches of find at ";
	    print_occ p.p_occ	    
	| (Find _), p1::r ->
	    print_string "\\quad -- Merge branch(es) at ";
	    display_list (fun p2 -> print_occ p2.p_occ) r;
	    print_string " with else branch of find at ";
	    print_occ p.p_occ
	| _ -> Parsing_helper.internal_error "unexpected merge"
      end;
      print_string "\\\\\n"            
  | DMergeBranchesE(t,l) ->
      begin
	match (t.t_desc, l) with
	  (TestE _), _ ->
	    print_string "\\quad -- Merge branches of test at ";
	    print_occ t.t_occ
	| (LetE _), _ ->
	    print_string "\\quad -- Merge branches of let at ";
	    print_occ t.t_occ
	| (FindE(l0,_,_), l) when List.length l = List.length l0 + 1 ->
	    print_string "\\quad -- Merge all branches of find at ";
	    print_occ t.t_occ	    
	| (FindE _), t1::r ->
	    print_string "\\quad -- Merge branch(es) at ";
	    display_list (fun t2 -> print_occ t2.t_occ) r;
	    print_string " with else branch of find at ";
	    print_occ t.t_occ
	| _ -> Parsing_helper.internal_error "unexpected merge"
      end;
      print_string "\\\\\n"
  | DMoveIf l ->
      List.iter (fun (orig_occ,final_occ) ->
	print_string "\\quad -- Move if_fun function from ";
	print_occ orig_occ;
	print_string " to ";
	print_occ final_occ;
	print_string "\\\\\n"
	  ) l
  | DMoveIfToTerm l ->
      print_string "\\quad -- Transformed if_fun function into if term at ";
      display_list print_occ l;
      print_string "\\\\\n"

let already_displayed = ref []

let display_file s =
  let f = open_in s in
  let rec aux() =
    print_string (input_line f);
    print_string "\n";
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
  | Forgotten sg ->
     match sg.tex_display with
     | Some s -> display_file s
     | None -> Parsing_helper.internal_error "cannot display game in latex"
           
let rec display_state ins_next s =
  if List.memq s (!already_displayed) then
    begin
      print_string "===================== New branch =====================\n";
      print_string "Game "; 
      print_string (Display.get_game_id s.game);
      print_string " [Already displayed]\n";
    end
  else
    begin
      already_displayed := s :: (!already_displayed);
      match s.prev_state with
	None -> 
	  if s.game.game_number = -1 then
	    begin
	      incr Display.max_game_number;
	      s.game.game_number <- !Display.max_game_number
	    end;
	  print_string "Initial state\\\\\n";
	  print_string ("Game " ^ (Display.get_game_id s.game) ^ " is\\\\\n");
	  Display.mark_occs ins_next;
	  display_game_process s.game;
	  Display.useful_occs := []
      | Some (Proof ql, p, _, s') ->
	  display_state ins_next s';
	  print_string "\\\\\n";
	  List.iter (fun ((q,g), p') -> 
	    print_string "Proved ";
	    display_query (q, s'.game);
	    display_up_to_proba ~separate_time:true p';
	    print_string "\\\\\n"
	      ) ql;
	  if p != [] then
	    Parsing_helper.internal_error "Proof step should have empty set of excluded traces"
      | Some (i,p,ins,s') ->
	  display_state ins s';
      (* Record the game number *)
	  if s.game.game_number = -1 then
	    begin
	      incr Display.max_game_number;
	      s.game.game_number <- !Display.max_game_number
	    end;
	  print_string "\\\\\nApplying ";
	  display_instruct i;
	  if p != [] then
	    begin
	      print_string " {}[probability $";
	      display_set ~separate_time:true p;
	      print_string "${}]{}"
	    end;
	  print_string "\\\\\n";
	  List.iter display_detailed_ins (List.rev ins);
	  print_string "yields\\\\\n\\\\\n";
	  print_string ("Game " ^ (Display.get_game_id s.game) ^ " is\\\\\n");
	  Display.mark_occs ins_next;
	  display_game_process s.game;
	  Display.useful_occs := []
    end

(* Display probability bounds *)

let display_proba_bound = function
  | BLeq(a,b) ->
      print_string "$";
      display_proba ~separate_time:true 0 a;
      print_string " \\leq ";
      display_proba ~separate_time:true 0 b;
      print_string "$\\\\\n"
  | BSameGame(g1,g2,p) -> 
      print_string ("Game "^(Display.get_game_id g1)^" is the same as game "^(Display.get_game_id g2));
      display_up_to_proba ~separate_time:true p;
      print_string ".\\\\\n"

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
  (* Set a tab stop after the occurrence display *)
  print_string "\\begin{tabbing}\n";
  print_string (String.make (Display.len_num (!Terms.max_occ) + 2) '0');
  print_string "\\=\\kill\n";
  List.iter (fun s -> display_state [] s) sdi.states_to_display;  
  print_string "\\end{tabbing}\n";

  (* Display the probabilities of proved queries *)
  List.iter (fun (q_g, bounds, assume, p) ->
    List.iter display_proba_bound bounds;	  
    if assume then
      print_string "RESULT Using unchecked commands, shown "
    else
      print_string "RESULT Proved ";
    display_query q_g;
    display_up_to_proba ~separate_time:true p;
    print_string "\\\\\n"
      ) sdi.proved_queries;

  (* Display the runtimes *)
  let rec display_times() = 
    let disp = List.rev (!times_to_display) in
    times_to_display := [];
    if disp != [] then
      begin
	List.iter (fun (tid,cat,t) ->
	  print_string "RESULT $";
	  print_id "\\var{" tid "}";
	  display_time_id_eq cat;
	  print_string " = ";
	  display_proba ~separate_time:true 0 t;
	  print_string "$\\\\\n"
	    ) disp;
	(* Displaying the times in [disp] may add new times to be
           displayed. Display them. *)
	display_times()
      end
  in
  display_times();

  (* List the unproved queries *)
  let rest = sdi.unproved_queries in
  let rest' = List.filter (function (AbsentQuery, _) -> false | _ -> true) rest in
  if rest = [] then
    print_string "All queries proved.\\\\\n"
  else if rest' != [] then
    begin
      print_string "RESULT Could not prove ";
      display_list display_query rest;
      print_string ".\\\\\n"
    end


let preamble = "
\\documentclass{article}
\\usepackage[hmargin=1in,vmargin=1in]{geometry}
\\newcommand{\\kw}[1]{\\mathbf{#1}}
\\newcommand{\\kwf}[1]{\\mathsf{#1}}
\\newcommand{\\var}[1]{\\mathit{#1}}
\\newcommand{\\kwt}[1]{\\mathit{#1}}
\\newcommand{\\kwp}[1]{\\mathit{#1}}
\\newcommand{\\kwc}[1]{\\mathit{#1}}
\\begin{document}
"

let nice_tex_preamble = "
\\documentclass{article}
\\usepackage[hmargin=1in,vmargin=1in]{geometry}
\\newcommand{\\cinput}[2]{{#1}({#2})}
\\newcommand{\\coutput}[2]{\\overline{#1}\\langle{#2}\\rangle}
\\newcommand{\\kw}[1]{\\mathbf{#1}}
\\newcommand{\\kwf}[1]{\\mathsf{#1}}
\\newcommand{\\var}[1]{\\mathit{#1}}
\\newcommand{\\kwt}[1]{\\mathit{#1}}
\\newcommand{\\kwp}[1]{\\mathit{#1}}
\\newcommand{\\kwc}[1]{\\mathit{#1}}
\\begin{document}
"

let oracles_preamble = "
\\documentclass{article}
\\usepackage[hmargin=1in,vmargin=1in]{geometry}
\\newcommand{\\store}{\\leftarrow}
\\newcommand{\\getR}{\\stackrel{R}{\\store}}
\\newcommand{\\kw}[1]{\\mathbf{#1}}
\\newcommand{\\kwf}[1]{\\mathsf{#1}}
\\newcommand{\\var}[1]{\\mathit{#1}}
\\newcommand{\\kwt}[1]{\\mathit{#1}}
\\newcommand{\\kwp}[1]{\\mathit{#1}}
\\newcommand{\\kwc}[1]{\\mathit{#1}}
\\begin{document}
"

let postamble = "
\\end{document}
"

let start() = 
  begin
    try
      file := open_out (!Settings.tex_output)
    with Sys_error s ->
      Parsing_helper.user_error ("File error: " ^ s ^ "\n")
  end;
  if (!Settings.front_end) == Settings.Oracles then
    print_string oracles_preamble
  else if !nice_tex then
    print_string nice_tex_preamble
  else
    print_string preamble

let stop() =
  print_string postamble;
  close_out (!file)

let file_out filename ext f =
  let old_file = !file in
  let out_file =
    try
      open_out filename
    with Sys_error s ->
      raise (Parsing_helper.Error("Cannot open file " ^ filename ^ ": " ^ s, ext))
  in
  file := out_file;
  try 
    f();
    close_out out_file;
    file := old_file
  with x ->
    close_out out_file;
    file := old_file;
    raise x
