print_string ("Generating key pair for initiator " ^ (Crypto.get_hostname()) ^"...");
print_newline ();
let oagk = ONS_AGenKey.init () in
let (_,pkA) = oagk () in
print_string "Done.\n";
print_string "Key recorded in key table (do not rerun Akeygen on the same machine without deleting the key table).\n"
