#!/bin/sh

CRYPTOKIT="-linkpkg -package cryptokit"
SSH=implementation/ssh-profile

cd ../.. 
echo Proving the protocol...
echo First, proving authentication
./cryptoverif $SSH/ssh.ocv > $SSH/ssh.out
egrep '(RESULT|All)' $SSH/ssh.out | grep -v "RESULT time"
echo "Second, proving secrecy of the exchanged keys: IVs, encryption keys, MAC keys"
for key in IVCC IVSC EKCC EKSC MKCC MKSC
do
    m4 -DONEKEY=$key $SSH/ssh-secrecy-key.m4.ocv > $SSH/ssh-secrecy-key-$key.ocv
    ./cryptoverif $SSH/ssh-secrecy-key-$key.ocv > $SSH/ssh-secrecy-key-$key.out
    egrep '(RESULT|All)' $SSH/ssh-secrecy-key-$key.out | grep -v "RESULT time"
done

echo Generating implementation...
./cryptoverif -impl -o $SSH $SSH/ssh.ocv
cd $SSH

# rm hk pkS skS trusted_hosts

ocamlfind ocamlopt $CRYPTOKIT -I .. -o server str.cmxa unix.cmxa nums.cmxa profileprim.c profile.mli profile.ml ../base.mli ../base.ml ../crypto.mli ../crypto.ml ssh_crypto.mli ssh_crypto.ml ssh_network.mli ssh_network.ml SSH_S.mli SSH_S.ml ssh_server.ml
ocamlfind ocamlopt $CRYPTOKIT -I .. -o client str.cmxa unix.cmxa nums.cmxa profileprim.c profile.mli profile.ml ../base.mli ../base.ml ../crypto.mli ../crypto.ml ssh_crypto.mli ssh_crypto.ml ssh_network.mli ssh_network.ml SSH_C.mli SSH_C.ml ssh_client.ml
ocamlfind ocamlopt $CRYPTOKIT -I .. -o keygen str.cmxa unix.cmxa nums.cmxa profileprim.c profile.mli profile.ml ../base.mli ../base.ml ../crypto.mli ../crypto.ml ssh_crypto.mli ssh_crypto.ml ssh_network.mli ssh_network.ml SSH_Keygen.mli SSH_Keygen.ml ssh_kgen.ml
ocamlfind ocamlopt $CRYPTOKIT -I .. -o add_key str.cmxa unix.cmxa nums.cmxa profileprim.c profile.mli profile.ml ../base.mli ../base.ml ../crypto.mli ../crypto.ml ssh_crypto.mli ssh_crypto.ml ssh_network.mli ssh_network.ml add_key.ml

