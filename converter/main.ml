open Types

let front_end_set = ref false
let dir_sep = "/" (* Filename.dir_sep exists only in OCaml >= 3.11.2 and 
		     OCaml MinGW exists only in OCaml 3.11.0... *)

let ends_with s sub =
  let l_s = String.length s in
  let l_sub = String.length sub in
  (l_s >= l_sub) && (String.sub s (l_s - l_sub) l_sub = sub)




(* Prepare the equation statements given by the user *)

let rec get_vars accu t =
  match t.t_desc with
    Var(b,[]) -> 
      if not (List.memq b (!accu)) then 
	accu := b :: (!accu)
  | FunApp(_,l) ->
      List.iter (get_vars accu) l
  | _ -> Parsing_helper.internal_error "statement terms should contain only Var and FunApp\n"

let simplify_statement (vl, t) =
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
  if Terms.is_true t' then 
    begin
      print_string "Warning: statement ";
      Display.display_term t;
      print_string " removed using the equational theory.\n"
    end
  else if Terms.is_false t' then
    begin
      print_string "Error: statement ";
      Display.display_term t;
      Parsing_helper.user_error " contradictory.\n"
    end
  else
    let tnew = 
      if !glob_reduced then 
	begin
	  print_string "Statement ";
	  Display.display_term t;
	  print_string " simplified into ";
	  Display.display_term t';
	  print_string " using the equational theory.\n";
	  t'
	  end
      else 
	t
    in
    let record_statement ((_, _, t1, _,t2) as statement) =
      match t1.t_desc with
	FunApp(f, l) -> 
	  f.f_statements <- statement :: f.f_statements
      | _ -> 
	  print_string "Statement ";
	  Display.display_term t1;
	  print_string " = ";
	  Display.display_term t2;
	  print_string " ignored: the left-hand side should start with a function symbol.\n"
    in
    match tnew.t_desc with
      FunApp(f, [t1;t2]) when f.f_cat == Equal ->
	let vars = ref [] in
	get_vars vars t2;
	if not (List.for_all (fun b ->
	  Terms.refers_to b t1
	  ) (!vars)) then
	  begin
	    print_string "Error in simplified statement ";
	    Display.display_term t1;
	    print_string " = ";
	    Display.display_term t2;
	    Parsing_helper.user_error ": all variables of the right-hand side should occur in the left-hand side.\n"
	  end;	  
	record_statement ([], vl, t1, Zero, t2)
    | FunApp(f, [t1;t2]) when f.f_cat == Diff ->
	record_statement ([], vl, tnew, Zero, Terms.make_true());
	record_statement ([], vl, Terms.make_equal t1 t2, Zero, Terms.make_false())
    | _ -> 
	record_statement ([], vl, tnew, Zero, Terms.make_true())
	  
let record_collision ((_, _, t1, _,t2) as collision) =
  match t1.t_desc with
    FunApp(f, l) -> 
      f.f_collisions <- collision :: f.f_collisions
  | _ -> 
      print_string "Collision ";
      Display.display_term t1;
      print_string " <=(...)=> ";
      Display.display_term t2;
      print_string " ignored: the left-hand side should start with a function symbol.\n"

(* [copy ic oc len] copies [len] characters from input channel [ic] to 
   output channel [oc].
   When [len = -1] copies until the end of [ic]. *)
	
let rec copy ic oc len =
  if len = 0 then
    ()
  else if len = -1 then
    try
      let c = input_char ic in
      output_char oc c;
      copy ic oc (-1)
    with End_of_file -> ()
  else
    let c = input_char ic in
    output_char oc c;
    copy ic oc (len-1)

open Changes
open Lexing
  
let apply_change = function
    Replace s -> Display.print_string s
  | Remove -> ()
  | ChEquation s -> Display.display_statement s
  | ChEquiv e -> Display.display_equiv e
  | ChCollision c -> Display.display_collision c
  | ChQuery q -> Display.display_queries q
  | ChProcess p -> Display.display_process p
	
let convert_file f_in f_out =
  print_string ("Converting " ^ f_in ^ " into " ^ f_out ^"\n");
  try 
    let ic = open_in f_in in
    let oc = open_out f_out in
    let current_pos = ref 0 in
    Display.set_files oc ic;
    let changes = Changes.get_changes f_in in
    List.iter (fun ((loc_start, loc_end), ch) ->
      seek_in ic (!current_pos);
      copy ic oc (loc_start.pos_cnum - !current_pos);
      current_pos := loc_end.pos_cnum;
      apply_change ch
	) changes;
    seek_in ic (!current_pos);
    copy ic oc (-1);
    close_in ic;
    close_out oc
  with Sys_error s ->
    Parsing_helper.user_error ("File error: " ^ s ^ "\n")

let first_file = ref true

let anal_file s =
  if not (!first_file) then
    Parsing_helper.user_error "You can convert a single CryptoVerif file for each run of the converter.\nPlease rerun the converter with your second file.";
  first_file := false;
  if not (!front_end_set) then
    begin
      (* Use the oracle front-end by default when the file name ends
	 in .ocv *)
      let s_up = String.uppercase s in
      if ends_with s_up ".OCV" then Settings.front_end := Settings.Oracles
    end;
  try
    let (statements, collisions, equivs, move_new_eq, queries, proof, impl, p) = Syntax.read_file s in
    List.iter Check.check_def_eqstatement equivs;
    List.iter (fun (_,eq) -> Check.check_def_eqstatement eq) move_new_eq;
    Check.check_def_process_main p;
    let equivs = List.map Check.check_equiv equivs in
    let new_new_eq = List.map (fun (ty, eq) -> (ty, Check.check_equiv eq)) move_new_eq in
        begin
          let g = { proc = Terms.move_occ_process p; game_number = 1; current_queries = [] } in
            let queries =
              if queries == [] then 
	        [(AbsentQuery,g), ref None, None]
              else
	        List.map (fun q -> ((q,g), ref None, None)) queries in
	    g.current_queries <- queries;
            List.iter simplify_statement statements;
            List.iter record_collision collisions;
            Settings.equivs := equivs;
            Settings.move_new_eq := new_new_eq;
            Settings.collect_public_vars queries;
	    if !Settings.out_lib <> "" then
	      begin
		let lib_suffix = if (!Settings.front_end) == Settings.Channels then ".cvl" else ".ocvl" in
		let in_lib_name = (!Settings.lib_name) ^ lib_suffix in
		let out_lib_name = (!Settings.out_lib) ^ lib_suffix in
		convert_file in_lib_name out_lib_name
	      end;
	    if (!Settings.out_lib = "") && (!Settings.out_file = "") then
	      Parsing_helper.user_error "Error: Output file not set; you should use the command-line option -o.\n";
            (* create converted file *)
	    if !Settings.out_file <> "" then
	      convert_file s (!Settings.out_file)
        end
  with End_of_file ->
    print_string "End of file.\n"
    | e ->
        Parsing_helper.internal_error (Printexc.to_string e)

let _ =
  Arg.parse
    [ "-lib", Arg.String (fun s -> Settings.lib_name := s),
      "<filename> \tchoose library file";
      "-in", Arg.String (function 
	  "channels" -> Settings.front_end := Settings.Channels
	| "oracles" -> Settings.front_end := Settings.Oracles
	| _ -> Parsing_helper.user_error "Command-line option -in expects argument either \"channels\" or \"oracles\".\n"),
      "channels / -in oracles \tchoose the front-end";
      "-o", Arg.String (fun s -> Settings.out_file := s),
      "<filename>\tlocation of the converted file";
      "-olib", Arg.String (fun s -> Settings.out_lib := s),
      "<filename>\tlocation of the converted library"
    ]
    anal_file "Cryptoverif. Cryptographic protocol verifier, by Bruno Blanchet\nCopyright ENS-CNRS, distributed under the CeCILL-B license"
