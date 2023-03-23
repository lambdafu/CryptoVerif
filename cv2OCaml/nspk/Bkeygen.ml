print_string ("Generating key pair for responder "^(Crypto.get_hostname())^"...");
print_newline ();
let obgk = ONS_BGenKey.init () in
let (_,pkB) = obgk () in
print_string "Done.\n";
print_string "Key recorded in key table (do not rerun Bkeygen on the same machine without deleting the key table).\n"
