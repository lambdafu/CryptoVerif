print_string ("Generating key pair for " ^ (Crypto.get_hostname()) ^"...");
print_newline ();
let keygen = WLSK_keygen.init () in
let _ = keygen (Crypto.get_hostname()) in
print_string "Done.\n";
print_string "Key recorded in key table (do not rerun on the same machine without deleting the key table).\n"
