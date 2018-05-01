#!/bin/sh

CRYPTOKIT="-I ../cryptokit -I +cryptokit"

cd ../.. 
echo Proving the protocol...
echo First, proving authentication
./cryptoverif implementation/ssh/ssh.ocv > implementation/ssh/ssh.out
egrep '(RESULT|All)' implementation/ssh/ssh.out | grep -v "RESULT time"
echo "Second, proving secrecy of the exchanged keys: IVs, encryption keys, MAC keys"
for key in IVCC IVSC EKCC EKSC MKCC MKSC
do
    m4 -DONEKEY=$key implementation/ssh/ssh-secrecy-key.m4.ocv > implementation/ssh/ssh-secrecy-key-$key.ocv
    ./cryptoverif implementation/ssh/ssh-secrecy-key-$key.ocv > implementation/ssh/ssh-secrecy-key-$key.out
egrep '(RESULT|All)' implementation/ssh/ssh-secrecy-key-$key.out | grep -v "RESULT time"
done

echo Generating implementation...
./cryptoverif -impl -o implementation/ssh implementation/ssh/ssh.ocv
cd implementation/ssh

# rm hk pkS skS trusted_hosts

ocamlopt $CRYPTOKIT -I .. -o server str.cmxa unix.cmxa nums.cmxa cryptokit.cmxa ../base.mli ../base.ml ../crypto.mli ../crypto.ml ssh_crypto.mli ssh_crypto.ml ssh_network.mli ssh_network.ml SSH_S.mli SSH_S.ml ssh_server.ml
ocamlopt $CRYPTOKIT -I .. -o client str.cmxa unix.cmxa nums.cmxa cryptokit.cmxa ../base.mli ../base.ml ../crypto.mli ../crypto.ml ssh_crypto.mli ssh_crypto.ml ssh_network.mli ssh_network.ml SSH_C.mli SSH_C.ml ssh_client.ml
ocamlopt $CRYPTOKIT -I .. -o keygen str.cmxa unix.cmxa nums.cmxa cryptokit.cmxa ../base.mli ../base.ml ../crypto.mli ../crypto.ml ssh_crypto.mli ssh_crypto.ml ssh_network.mli ssh_network.ml SSH_Keygen.mli SSH_Keygen.ml ssh_kgen.ml
ocamlopt $CRYPTOKIT -I .. -o add_key str.cmxa unix.cmxa nums.cmxa cryptokit.cmxa ../base.mli ../base.ml ../crypto.mli ../crypto.ml ssh_crypto.mli ssh_crypto.ml ssh_network.mli ssh_network.ml add_key.ml

