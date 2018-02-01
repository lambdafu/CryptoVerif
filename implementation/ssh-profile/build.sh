#!/bin/sh

CRYPTOKIT="-I ../cryptokit -I +cryptokit"
SSH=implementation/ssh-profile

cd ../.. 
echo Proving the protocol...
echo First, proving authentication
./cryptoverif $SSH/ssh.ocv > $SSH/ssh.out
egrep '(RESULT|All)' $SSH/ssh.out | grep -v "RESULT time"
echo "Second, proving secrecy of the exchanged keys: IVs, encryption keys, MAC keys"
./cryptoverif $SSH/ssh-secrecy-key-civcs.ocv > $SSH/ssh-secrecy-key-civcs.out
egrep '(RESULT|All)' $SSH/ssh-secrecy-key-civcs.out | grep -v "RESULT time"
./cryptoverif $SSH/ssh-secrecy-key-civsc.ocv > $SSH/ssh-secrecy-key-civsc.out
egrep '(RESULT|All)' $SSH/ssh-secrecy-key-civsc.out | grep -v "RESULT time"
./cryptoverif $SSH/ssh-secrecy-key-cekcs.ocv > $SSH/ssh-secrecy-key-cekcs.out
egrep '(RESULT|All)' $SSH/ssh-secrecy-key-cekcs.out | grep -v "RESULT time"
./cryptoverif $SSH/ssh-secrecy-key-ceksc.ocv > $SSH/ssh-secrecy-key-ceksc.out
egrep '(RESULT|All)' $SSH/ssh-secrecy-key-ceksc.out | grep -v "RESULT time"
./cryptoverif $SSH/ssh-secrecy-key-cmkcs.ocv > $SSH/ssh-secrecy-key-cmkcs.out
egrep '(RESULT|All)' $SSH/ssh-secrecy-key-cmkcs.out | grep -v "RESULT time"
./cryptoverif $SSH/ssh-secrecy-key-cmksc.ocv > $SSH/ssh-secrecy-key-cmksc.out
egrep '(RESULT|All)' $SSH/ssh-secrecy-key-cmksc.out | grep -v "RESULT time"

echo Generating implementation...
./cryptoverif -impl -o $SSH $SSH/ssh.ocv
cd $SSH

# rm hk pkS skS trusted_hosts

ocamlopt $CRYPTOKIT -I .. -o server str.cmxa unix.cmxa nums.cmxa cryptokit.cmxa profileprim.c profile.mli profile.ml ../base.mli ../base.ml ../crypto.mli ../crypto.ml ssh_crypto.mli ssh_crypto.ml ssh_network.mli ssh_network.ml SSH_S.mli SSH_S.ml ssh_server.ml
ocamlopt $CRYPTOKIT -I .. -o client str.cmxa unix.cmxa nums.cmxa cryptokit.cmxa profileprim.c profile.mli profile.ml ../base.mli ../base.ml ../crypto.mli ../crypto.ml ssh_crypto.mli ssh_crypto.ml ssh_network.mli ssh_network.ml SSH_C.mli SSH_C.ml ssh_client.ml
ocamlopt $CRYPTOKIT -I .. -o keygen str.cmxa unix.cmxa nums.cmxa cryptokit.cmxa profileprim.c profile.mli profile.ml ../base.mli ../base.ml ../crypto.mli ../crypto.ml ssh_crypto.mli ssh_crypto.ml ssh_network.mli ssh_network.ml SSH_Keygen.mli SSH_Keygen.ml ssh_kgen.ml
ocamlopt $CRYPTOKIT -I .. -o add_key str.cmxa unix.cmxa nums.cmxa cryptokit.cmxa profileprim.c profile.mli profile.ml ../base.mli ../base.ml ../crypto.mli ../crypto.ml ssh_crypto.mli ssh_crypto.ml ssh_network.mli ssh_network.ml add_key.ml

