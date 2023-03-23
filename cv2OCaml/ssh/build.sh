#!/bin/sh
set -e

file_exists_or_abort()
{
    filename=$1
    if [ ! -f $filename ]
    then
	echo "File '$filename' not found. Did you execute this script in the directory in which it's stored?"
	exit 2
    fi
}

file_exists_or_abort ssh-secrecy-key.m4.ocv
file_exists_or_abort ssh.ocv

if [ -x ../../cryptoverif ]
then
    CV=../../cryptoverif
else
    CV=cryptoverif
fi

CRYPTOKIT="-linkpkg -package cryptokit"

echo Proving the protocol...
echo First, proving authentication
"$CV" ssh.ocv > ssh.out
grep -E '(RESULT|All)' ssh.out | grep -v "RESULT time"
echo "Second, proving secrecy of the exchanged keys: IVs, encryption keys, MAC keys"
for key in IVCC IVSC EKCC EKSC MKCC MKSC
do
    m4 -DONEKEY=$key ssh-secrecy-key.m4.ocv > ssh-secrecy-key-$key.ocv
    "$CV" ssh-secrecy-key-$key.ocv > ssh-secrecy-key-$key.out
    grep -E '(RESULT|All)' ssh-secrecy-key-$key.out | grep -v "RESULT time"
done
echo "Version that uses indifferentiability to prove the secrecy of all keys in one step, fast"
"$CV" ssh-secrecy-key-indiff.ocv > ssh-secrecy-key-indiff.out
grep -E '(RESULT|All)' ssh-secrecy-key-indiff.out | grep -v "RESULT time"


echo Generating implementation...
"$CV" -impl OCaml ssh.ocv

# rm hk pkS skS trusted_hosts

ocamlfind ocamlopt $CRYPTOKIT -I .. -o server str.cmxa ../base.mli ../base.ml ../crypto.mli ../crypto.ml ssh_crypto.mli ssh_crypto.ml ssh_network.mli ssh_network.ml SSH_S.mli SSH_S.ml ssh_server.ml
ocamlfind ocamlopt $CRYPTOKIT -I .. -o client str.cmxa ../base.mli ../base.ml ../crypto.mli ../crypto.ml ssh_crypto.mli ssh_crypto.ml ssh_network.mli ssh_network.ml SSH_C.mli SSH_C.ml ssh_client.ml
ocamlfind ocamlopt $CRYPTOKIT -I .. -o keygen str.cmxa ../base.mli ../base.ml ../crypto.mli ../crypto.ml ssh_crypto.mli ssh_crypto.ml ssh_network.mli ssh_network.ml SSH_Keygen.mli SSH_Keygen.ml ssh_kgen.ml
ocamlfind ocamlopt $CRYPTOKIT -I .. -o add_key str.cmxa ../base.mli ../base.ml ../crypto.mli ../crypto.ml ssh_crypto.mli ssh_crypto.ml ssh_network.mli ssh_network.ml add_key.ml

