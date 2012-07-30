let responder_port = 0x8081

let send ch s =
  output_binary_int ch (String.length s);
  output_string ch s;
  flush ch

let receive ch =
  let len = input_binary_int ch in
  let s = String.create len in
  really_input ch s 0 len;
  s

let _ =
  if Array.length Sys.argv < 2 then 
    begin
      print_string "Initiator expects the name of the responder to contact\n";
      exit 2
    end;
  let responder = Sys.argv.(1) in
  let responder_host = 
    try 
      Unix.gethostbyname responder
    with Not_found ->
      print_string ("Responder " ^ responder ^ " not found.\n");
      exit 2
  in
  let responder_addr = Unix.ADDR_INET(responder_host.Unix.h_addr_list.(0), responder_port) in
  let o1 = WLSK_Init.init() in
  print_string ("Contacting responder "^responder^"...\n"); 
  flush stdout;
  let (o2, idA) = o1 responder in
  let (in_resp, out_resp) = Unix.open_connection(responder_addr) in
  send out_resp idA;
  let n = receive in_resp in
  let (_,m31,m32) = o2 n in
  send out_resp (Crypto.concat_str_str m31 m32);
  Unix.shutdown_connection in_resp;
  close_in_noerr in_resp;
  close_out_noerr out_resp;
  print_string "Done.\n"
  
  
