let rec add_tags_lines filename tag in_file out_file =
  let line = input_line in_file in
  output_string out_file line;
  if StringPlus.contains line "EXPECTED" || StringPlus.contains line "EXPECTPV" then
  begin
    output_string out_file (" FILENAME: "^filename^" TAG: "^(string_of_int (!tag)));
    incr tag
  end;
  output_string out_file "\n";
  add_tags_lines filename tag in_file out_file

let add_tags_file filename =
  print_string ("Adding tags to "^filename);
  print_newline();
  let new_filename = filename ^".tmp" in
  let in_file = open_in filename in
  let out_file = open_out new_filename in
  let tag = ref 1 in
  try 
    add_tags_lines filename tag in_file out_file
  with End_of_file -> 
    close_in in_file;
    close_out out_file;
    Sys.rename new_filename filename

let rec add_tags_dir dirname =
    let file_array = Sys.readdir dirname in
    Array.sort compare file_array;
    Array.iter (fun filename ->
      let full_filename = Filename.concat dirname filename in
      if Sys.is_directory full_filename then
	add_tags_dir full_filename
      else if StringPlus.case_insensitive_contains filename ".m4." && 
	(List.exists (StringPlus.case_insensitive_ends_with filename)
	   [ ".cv"; ".ocv"; ".pcv"; ".pv"; ".pi"; ".horntype"; ".horn" ]) then
	add_tags_file full_filename
	  ) file_array

(* [usage()] displays an help message. Called when the arguments are 
   incorrect *)
	
let usage() =
  print_string "Incorrect arguments\nUsage: \naddexpectedtags <directories>\n";
  exit 0

(* Main function. Parses command-line arguments.
Usage:
 addexpectedtags <directories>
   *)

let _ =
  if Array.length Sys.argv < 2 then
    usage();
  for i = 1 to Array.length Sys.argv-1 do
    if Sys.is_directory Sys.argv.(i) then
      add_tags_dir Sys.argv.(i) 
  done
