let cert_server_port = 0x8082

let send ch s =
  output_binary_int ch (String.length s);
  output_string ch s;
  flush ch

let receive ch =
  let len = input_binary_int ch in
  really_input_string ch len

let server_fun ch_in ch_out =
  let m1 = receive ch_in in
  let os13 = ONS_S.init() in
  let (m11,m12) = Crypto.unconcat_str_str m1 in
  let ((), m21, m22, m23) = os13 (m11,m12) in
  send ch_out (Crypto.concat_str_str_str (Crypto.pkey_to m21) m22 m23);
  Unix.shutdown_connection ch_in;
  close_in_noerr ch_in;
  close_out_noerr ch_out;
  let (host_name_req,_) = Crypto.unconcat_str_str m11 in
  let (host_name_cert,_) = Crypto.unconcat_str_str m12 in
  print_string ("Sent certificate for " ^ host_name_cert ^ " to " ^ host_name_req ^ "\n");
  flush stdout
  
let _ =
  let cert_server = Crypto.get_hostname() in
  let cert_server_host = 
    try 
      Unix.gethostbyname cert_server
    with Not_found ->
      print_string ("Certificate server " ^ cert_server ^ " not found.\n");
      exit 2
  in
  let cert_server_addr = Unix.ADDR_INET(cert_server_host.Unix.h_addr_list.(0), cert_server_port) in
  print_string "Launching certificate server\n";
  flush stdout;
  Unix.establish_server server_fun cert_server_addr
  
