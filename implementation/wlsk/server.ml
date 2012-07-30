let cert_server_port = 0x8082

let send ch s =
  output_binary_int ch (String.length s);
  output_string ch s;
  flush ch

let receive ch =
  let len = input_binary_int ch in
  let s = String.create len in
  really_input ch s 0 len;
  s

let server_fun ch_in ch_out =
  let m1 = receive ch_in in
  let os = WLSK_S.init() in
  let [m11;m12;m13;m14] = Base.decompos m1 in
  let ((), m21, m22) = os (m11,m12,m13,m14) in
  send ch_out (Crypto.concat_str_str m21 m22);
  Unix.shutdown_connection ch_in;
  close_in_noerr ch_in;
  close_out_noerr ch_out;
  print_string ("Server done with initiator " ^ m11 ^ " and responder " ^ m12 ^ "\n");
  flush stdout
  
let _ =
  let cert_server = Crypto.get_hostname() in
  let cert_server_host = 
    try 
      Unix.gethostbyname cert_server
    with Not_found ->
      print_string ("WLSK server " ^ cert_server ^ " not found.\n");
      exit 2
  in
  let cert_server_addr = Unix.ADDR_INET(cert_server_host.Unix.h_addr_list.(0), cert_server_port) in
  print_string "Launching WLSK server\n";
  flush stdout;
  Unix.establish_server server_fun cert_server_addr
  
