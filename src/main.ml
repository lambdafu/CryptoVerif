open Types

let front_end_set = ref false

(* Prepare the equation statements given by the user *)

let rec get_vars accu t =
  match t.t_desc with
    Var(b,[]) -> 
      if not (List.memq b (!accu)) then 
	accu := b :: (!accu)
  | FunApp(_,l) ->
      List.iter (get_vars accu) l
  | _ -> Parsing_helper.internal_error "statement terms should contain only Var and FunApp\n"

let record_statement (vl, t1, t2, side_cond) =
  match t1.t_desc with
    FunApp(f, l) ->
      let statement =
	{ c_restr = []; c_forall = vl; c_redl = t1; c_proba = Zero; c_redr = t2;
	  c_indep_cond = IC_True; c_side_cond = side_cond; c_restr_may_be_equal = false }
      in
      f.f_statements <- statement :: f.f_statements
  | _ -> 
      print_string "Statement ";
      Display.display_term t1;
      print_string " = ";
      Display.display_term t2;
      print_string " ignored: the left-hand side should start with a function symbol.\n"

let display_statement t side_cond =
  Display.display_term t;
  if not (Terms.is_true side_cond) then
    begin
      print_string " if ";
      Display.display_term side_cond
    end
	
let simplify_statement (vl, t, side_cond) =
  let glob_reduced = ref false in
  let rec reduce_rec t =
    let reduced = ref false in
    let t' = Terms.apply_eq_reds Terms.simp_facts_id reduced t in
    if !reduced then 
      begin
	glob_reduced := true;
	reduce_rec t'
      end
    else t
  in
  let t' = reduce_rec t in
  let side_cond' = reduce_rec side_cond in
  if Terms.is_true t' then 
    begin
      print_string "Warning: statement ";
      display_statement t side_cond;
      print_string " removed using the equational theory.\n"
    end
  else if Terms.is_false t' then
    begin
      print_string "Error: statement ";
      display_statement t side_cond;
      Parsing_helper.user_error " contradictory.\n"
    end
  else if Terms.is_false side_cond' then
    begin
      print_string "Warning: statement ";
      display_statement t side_cond;
      print_string " removed using the equational theory: side condition always false.\n"
    end
  else
    begin
      if !glob_reduced then 
	begin
	  print_string "Statement ";
	  display_statement t side_cond;
	  print_string " simplified into ";
	  display_statement t' side_cond';
	  print_string " using the equational theory.\n"
	end;
      match t'.t_desc with
	FunApp(f, [t1;t2]) when f.f_cat == Equal ->
	  let vars = ref [] in
	  get_vars vars t2;
	  get_vars vars side_cond';
	  if not (List.for_all (fun b ->
	    Terms.refers_to b t1
	      ) (!vars)) then
	    begin
	      print_string "Error in simplified statement ";
	      display_statement t' side_cond';
	      Parsing_helper.user_error ": all variables of the right-hand side and of the side condition should occur in the left-hand side.\n"
	    end;	  
	  record_statement (vl, t1, t2, side_cond') 
      | _ ->
	  let vars = ref [] in
	  get_vars vars side_cond';
	  if not (List.for_all (fun b ->
	    Terms.refers_to b t'
	      ) (!vars)) then
	    begin
	      print_string "Error in simplified statement ";
	      display_statement t' side_cond';
	      Parsing_helper.user_error ": all variables of the side condition should occur in the term.\n"
	    end;	  
	  record_statement (vl, t', Terms.make_true(), side_cond');
          match t'.t_desc with
          | FunApp(f, [t1;t2]) when f.f_cat == Diff ->
	     record_statement (vl, Terms.make_equal t1 t2, Terms.make_false(), side_cond')
          | _ -> 
	     ()
    end
	  
let record_collision collision =
  match collision.c_redl.t_desc with
    FunApp(f, l) -> 
      f.f_collisions <- collision :: f.f_collisions
  | _ -> 
      print_string "Collision ";
      Display.display_term collision.c_redl;
      print_string " <=(...)=> ";
      Display.display_term collision.c_redr;
      print_string " ignored: the left-hand side should start with a function symbol.\n"

let first_file = ref true

let call_m4 input_file output_file =
  let output_file_descr = Unix.openfile output_file [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC ] 0o600 in
  let args = Array.make 3 "m4" in
  args.(1) <- "-DCryptoVerif";
  args.(2) <- input_file;
  let (_,status) = Unix.waitpid [] (Unix.create_process "m4" args Unix.stdin output_file_descr Unix.stderr) in
  Unix.close output_file_descr;
  match status with
  | Unix.WEXITED 0 -> ()
  | _ -> Parsing_helper.user_error ("Preprocessing of " ^ input_file ^ " by m4 failed.\n")
    
let anal_file s0 =
  if not (!first_file) then
    Parsing_helper.user_error "You can analyze a single CryptoVerif file for each run of CryptoVerif.\nPlease rerun CryptoVerif with your second file.\n";
  first_file := false;
  let s =
    (* Preprocess .pcv files with m4 *)
    if StringPlus.case_insensitive_ends_with s0 ".pcv" then
      let s' = Filename.temp_file "cv" ".cv" in
      call_m4 s0 s';
      s'
    else
      s0
  in
  if not (!front_end_set) then
    begin
      (* Use the oracle front-end by default when the file name ends
	 in .ocv *)
      if StringPlus.case_insensitive_ends_with s ".ocv" then Settings.front_end := Settings.Oracles
    end;
  try
    Sys.catch_break true;
    let (statements, collisions, equivs, queries, proof, impl, final_p) = Syntax.read_file s in
    List.iter simplify_statement statements;
    List.iter record_collision collisions;
    let (p, queries) = 
      match final_p with
      | SingleProcess p' -> (p', queries)
      | Equivalence(p1,p2,q1,q2,pub_vars) ->
	  let p2 = Terms.move_occ_process p2 in
          Check.check_def_process_main p2;
	  let final_game =
	    { proc = RealProcess p2;
	      expanded = false;
	      game_number = -1;
	      current_queries = [] }
	  in
          (*W]e put AbsentQuery to make sure that events are preserved in [initial_expand_simplify]*)
	  final_game.current_queries <-
	     ((AbsentQuery,final_game), ref ToProve)::(List.map (fun q -> ((q,final_game), ref ToProve)) q2);
	  let final_state =
	    { game = final_game;
	      prev_state = None;
	      tag = None }
	  in
          let final_state_after_minimal_transfos =
            Instruct.initial_expand_simplify_success final_state
          in
	  let rec remove_absent_query state =
            state.game.current_queries <-
               List.filter (function ((AbsentQuery,_),_) -> false | _ -> true)
		 state.game.current_queries;
            match state.prev_state with
              None -> ()
            | Some(_,_,_,s') -> remove_absent_query s'
	  in
	  remove_absent_query final_state_after_minimal_transfos;
	  (p1, (QEquivalence (final_state_after_minimal_transfos, pub_vars, true))::q1)
    in
    let p = Terms.move_occ_process p in
    Check.check_def_process_main p;
    let _ = 
      if !Settings.get_implementation then
        Implementation.do_implementation impl
      else
        begin
          let g = { proc = RealProcess p;
		    expanded = false;
		    game_number = 1;
		    current_queries = [] } in
	  let var_num_state = Terms.get_var_num_state() in
          let queries = List.map (fun q ->
	    Check_corresp.well_formed q;
	    ((q,g), ref ToProve)) queries in
	  Terms.set_var_num_state var_num_state;
	  let queries =
            if List.for_all Terms.is_nonunique_event_query queries then 
	      ((AbsentQuery,g), ref ToProve)::queries
            else
	      queries
	  in
	  g.current_queries <- queries;
          Settings.equivs := equivs;
          
            (*
              List.iter Display.display_statement statements;
              print_newline();
              List.iter Display.display_equiv equivs;
              print_newline();
              Display.display_process p;
            *)
          Instruct.do_proof proof 
	    { game = g; 
	      prev_state = None;
	      tag = None } 
        end
    in
    (* Remove the preprocessed temporary file when everything went well *)
    if s0 <> s then
      Unix.unlink s
  with
  | End_of_file ->
      print_string "End of file.\n"
  | Sys.Break ->
      print_string "Stopped.\n"
  | Parsing_helper.Error(s, ext) ->
      Parsing_helper.input_error s ext
  | e ->
      Printexc.print_backtrace stdout;
      Parsing_helper.internal_error (Printexc.to_string e)

let _ =
  Arg.parse
    [ "-lib", Arg.String (fun s -> Settings.lib_name := s :: (!Settings.lib_name)),
      "<filename> \tchoose library file";
      "-tex", Arg.String (fun s -> Settings.tex_output := s),
      "<filename> \tchoose TeX output file";
      "-oproof", Arg.String (fun s -> Settings.proof_output := s),
      "<filename> \toutput the proof in this file";
      "-ocommands", Arg.String (fun s -> Settings.command_output := s),
      "<filename> \toutput the interactive commands in this file";
      "-oequiv", Arg.String (fun s -> Settings.equiv_output := s),
      "<filename> \tappend the generated special equivalences to this file";
      "-in", Arg.String (function 
	  "channels" -> Settings.front_end := Settings.Channels
	| "oracles" -> Settings.front_end := Settings.Oracles
	| _ -> Parsing_helper.user_error "Command-line option -in expects argument either \"channels\" or \"oracles\".\n"),
      "channels / -in oracles \tchoose the front-end";
      "-impl", Arg.Unit (fun () -> Settings.get_implementation := true),"\tget implementation of defined modules";
      "-o", Arg.String (fun s -> 
                          try 
                            if (Sys.is_directory s) then Settings.out_dir := s
                            else Parsing_helper.user_error "Command-line option -o expects a directory.\n"
                          with Sys_error _ ->
			    Parsing_helper.user_error "Command-line option -o expects a directory.\n"
                       ),
          "<directory> \tthe generated files will be placed in this directory, for -impl, out_game, out_state, and out_facts (Default: .)";
    ]
    anal_file ("Cryptoverif " ^ Version.version ^ ". Cryptographic protocol verifier, by Bruno Blanchet and David Cadé\nCopyright ENS-CNRS-Inria, distributed under the CeCILL-B license\nUsage:\n  cryptoverif [options] <file_to_analyze>\nwhere the options are listed below:")
