print_string "Generating key pair for the certificate server...";
print_newline ();
let ostart=ONS_Keygen.init () in
let (_,pkS) = ostart () in
print_string "Done.\n"
