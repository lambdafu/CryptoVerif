let responder_port = 0x8081
let cert_server_port = 0x8082

let send ch s =
  output_binary_int ch (String.length s);
  output_string ch s;
  flush ch

let receive ch =
  let len = input_binary_int ch in
  really_input_string ch len

let server_fun cert_server_addr init_in init_out =
  let m1 = receive init_in in
  let ob7 = ONS_B.init() in
  let (ob9, m41, m42) = ob7 m1 in
  print_string "Contacting certificate server...\n";
  flush stdout;
  let (in_cert, out_cert) = Unix.open_connection(cert_server_addr) in
  send out_cert (Crypto.concat_str_str m41 m42);
  let m5 = receive in_cert in
  Unix.shutdown_connection in_cert;
  close_in_noerr in_cert;
  close_out_noerr out_cert;
  print_string "Got reply.";
  flush stdout;
  let (m51,m52,m53) = Crypto.unconcat_str_str_str m5 in
  let m51key = Crypto.pkey_from m51 in
  let (ob11, m6) = ob9 (m51key, m52, m53) in
  let (initiator,_) = Crypto.unconcat_str_str m42 in
  print_string (" Certificate correct.\nReplying to initiator " ^ initiator ^"...\n"); 
  flush stdout;
  send init_out m6;
  let m7 = receive init_in in
  let _ = ob11 m7 in
  print_string "Initiator authenticated\n";
  flush stdout;
  Unix.shutdown_connection init_in;
  close_in_noerr init_in;
  close_out_noerr init_out;
  print_string "Done.\n"
  

let _ =
  if Array.length Sys.argv < 2 then 
    begin
      print_string "B expects the name of the certificate server to contact\n";
      exit 2
    end;
  let responder = Crypto.get_hostname() in
  let responder_host = 
    try 
      Unix.gethostbyname responder
    with Not_found ->
      print_string ("Responder " ^ responder ^ " not found.\n");
      exit 2
  in
  let responder_addr = Unix.ADDR_INET(responder_host.Unix.h_addr_list.(0), responder_port) in
  let cert_server = Sys.argv.(1) in
  let cert_server_host = 
    try 
      Unix.gethostbyname cert_server
    with Not_found ->
      print_string ("Certificate server " ^ cert_server ^ " not found.\n");
      exit 2
  in
  let cert_server_addr = Unix.ADDR_INET(cert_server_host.Unix.h_addr_list.(0), cert_server_port) in
  print_string "Launching responder\n";
  flush stdout;
  Unix.establish_server (server_fun cert_server_addr) responder_addr
  
