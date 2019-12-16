open Types

let front_end_set = ref false

let do_implementation impl =
  let impl = 
    Implementation.impl_check impl
  in
    List.iter (fun (x,opt,p)->
      print_string ("Generating implementation for module "^x^"...\n");
      let (impl,intf)=Implementation.impl_translate p opt in
      let f=open_out (Filename.concat (!Settings.out_dir) (x^".ml")) in
      output_string f impl;
      close_out f;
      let f'=open_out (Filename.concat (!Settings.out_dir) (x^".mli")) in
      output_string f' intf;
      close_out f';
      print_string ("Done.\n")
	) impl


(* Prepare the equation statements given by the user *)

let rec get_vars accu t =
  match t.t_desc with
    Var(b,[]) -> 
      if not (List.memq b (!accu)) then 
	accu := b :: (!accu)
  | FunApp(_,l) ->
      List.iter (get_vars accu) l
  | _ -> Parsing_helper.internal_error "statement terms should contain only Var and FunApp\n"

let record_statement ((_, _, t1, _,t2, _, _, _) as statement) =
  match t1.t_desc with
    FunApp(f, l) -> 
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
	  record_statement ([], vl, t1, Zero, t2, IC_True, side_cond', false)
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
	  record_statement ([], vl, t', Zero, Terms.make_true(), IC_True, side_cond', false);
          match t'.t_desc with
          | FunApp(f, [t1;t2]) when f.f_cat == Diff ->
	     record_statement ([], vl, Terms.make_equal t1 t2, Zero, Terms.make_false(), IC_True, side_cond', false)
          | _ -> 
	     ()
    end
	  
let record_collision ((_, _, t1, _,t2, _, _, _) as collision) =
  match t1.t_desc with
    FunApp(f, l) -> 
      f.f_collisions <- collision :: f.f_collisions
  | _ -> 
      print_string "Collision ";
      Display.display_term t1;
      print_string " <=(...)=> ";
      Display.display_term t2;
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
  | _ -> Parsing_helper.user_error ("Preprocessing of " ^ input_file ^ " by m4 failed.")
    
let anal_file s0 =
  if not (!first_file) then
    Parsing_helper.user_error "You can analyze a single CryptoVerif file for each run of CryptoVerif.\nPlease rerun CryptoVerif with your second file.";
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
    let (p, queries) = 
      match final_p with
      | SingleProcess p' -> (p', queries)
      | Equivalence(p1,p2,pub_vars) ->
         Check.check_def_process_main p2;
	 let final_game =
	   { proc = RealProcess (Terms.move_occ_process p2);
	     expanded = false;
	     game_number = -1;
	     current_queries = [] }
	 in
	 let final_state =
	   { game = final_game;
	     prev_state = None;
	     tag = None }
	 in
         let final_state_after_minimal_transfos =
           Instruct.initial_expand_simplify final_state
         in
	 (p1, [QEquivalence (final_state_after_minimal_transfos, pub_vars)])
    in
    Check.check_def_process_main p;
    let _ = 
      if (!Settings.get_implementation) then
        do_implementation impl
      else
        begin
          let g = { proc = RealProcess (Terms.move_occ_process p);
		    expanded = false;
		    game_number = 1;
		    current_queries = [] } in
            let queries =
              if queries == [] then 
	        [(AbsentQuery,g), ref ToProve]
              else
	        List.map (fun q -> ((q,g), ref ToProve)) queries in
	    g.current_queries <- queries;
            List.iter simplify_statement statements;
            List.iter record_collision collisions;
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
  | e ->
      Parsing_helper.internal_error (Printexc.to_string e)

let _ =
  Arg.parse
    [ "-lib", Arg.String (fun s -> Settings.lib_name := Some s),
      "<filename> \tchoose library file";
      "-tex", Arg.String (fun s -> Settings.tex_output := s),
      "<filename> \tchoose TeX output file";
      "-oproof", Arg.String (fun s -> Settings.proof_output := s),
      "<filename> \toutput the proof in this file";
      "-in", Arg.String (function 
	  "channels" -> Settings.front_end := Settings.Channels
	| "oracles" -> Settings.front_end := Settings.Oracles
	| _ -> Parsing_helper.user_error "Command-line option -in expects argument either \"channels\" or \"oracles\".\n"),
      "channels / -in oracles \tchoose the front-end";
      "-impl", Arg.Unit (fun () -> Settings.get_implementation := true),"\tget implementation of defined modules";
      "-o", Arg.String (fun s -> 
                          try 
                            if (Sys.is_directory s) then Settings.out_dir := s
                            else Parsing_helper.user_error "Command-line option -o expects a directory"
                          with
                              Sys_error _ -> Parsing_helper.user_error "Command-line option -o expects a directory"
                       ),
          "<directory> \tthe generated files will be placed in this directory, for -impl, out_game, out_state, and out_facts (Default: .)";
    ]
    anal_file ("Cryptoverif " ^ Version.version ^ ". Cryptographic protocol verifier, by Bruno Blanchet\nCopyright ENS-CNRS, distributed under the CeCILL-B license")
