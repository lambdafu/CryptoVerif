open Types

let front_end_set = ref false
let dir_sep = "/" (* Filename.dir_sep exists only in Ocaml >= 3.11.2 and 
		     OCaml MinGW exists only in OCaml 3.11.0... *)

let ends_with s sub =
  let l_s = String.length s in
  let l_sub = String.length sub in
  (l_s >= l_sub) && (String.sub s (l_s - l_sub) l_sub = sub)


let do_implementation impl =
  let impl = 
    Implementation.impl_check impl
  in
    List.iter
      (fun (x,opt,p)->
         print_string ("Generating implementation for module "^x^"...\n");
         let (impl,intf)=Implementation.impl_translate p opt in
         let f=open_out ((!Settings.out_dir)^dir_sep^x^".ml") in
           output_string f impl;
           close_out f;
           let f'=open_out ((!Settings.out_dir)^dir_sep^x^".mli") in
             output_string f' intf;
             close_out f';
             print_string ("Done.\n")
      ) impl


let anal_file s =
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
      if (!Settings.get_implementation) then
        do_implementation impl
      else
        begin
          let g = { proc = Terms.move_occ_process p; game_number = 1; current_queries = [] } in
            let queries =
              if queries == [] then 
	        [(AbsentQuery,g), ref None, None]
              else
	        List.map (fun q -> ((q,g), ref None, None)) queries in
	    g.current_queries <- queries;
            Settings.statements := statements;
            Settings.collisions := collisions;
            Settings.equivs := equivs;
            Settings.move_new_eq := new_new_eq;
            Settings.collect_public_vars queries;
            
            (*
              List.iter Display.display_statement statements;
              print_newline();
              List.iter Display.display_equiv equivs;
              print_newline();
              Display.display_process p;
            *)
            let _ = Instruct.execute_any_crypto proof 
	      { game = g; 
	        prev_state = None } in
              () 
        end
  with End_of_file ->
    print_string "End of file.\n"
    | e ->
        Parsing_helper.internal_error (Printexc.to_string e)

let _ =
  Arg.parse
    [ "-lib", Arg.String (fun s -> Settings.lib_name := s),
      "<filename> \tchoose library file";
      "-tex", Arg.String (fun s -> Settings.tex_output := s),
      "<filename> \tchoose TeX output file";
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
          "<directory> \tif \"-impl\" is given, the generated files will be placed in this directory (Default: .)";
    ]
    anal_file "Cryptoverif. Cryptographic protocol verifier, by Bruno Blanchet\nCopyright ENS-CNRS, distributed under the CeCILL-B license"
