

let _ = 
  if Array.length Sys.argv <> 2 then
    failwith ("Usage: "^(Sys.argv.(0))^" keyfile\nThe keyfile containing the sshd public key is /etc/ssh/ssh_host_rsa_key.pub on Debian based systems")
  else
    let ic = open_in_bin (Sys.argv.(1)) in
    let size = in_channel_length ic in
    let buf = String.create size in
      really_input ic buf 0 size;
      close_in ic;
      Base.insert_in_table "trusted_hosts" [buf]
