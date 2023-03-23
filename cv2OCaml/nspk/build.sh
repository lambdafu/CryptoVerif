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

file_exists_or_abort nspk3tbl.ocv

if [ -x ../../cryptoverif ]
then
    CV=../../cryptoverif
else
    CV=cryptoverif
fi

CRYPTOKIT="-linkpkg -package cryptokit"

echo Proving the protocol...
"$CV" nspk3tbl.ocv > nspk3tbl.out
grep -E '(RESULT|All)' nspk3tbl.out | grep -v "RESULT time"
echo Generating implementation...
"$CV" -impl OCaml nspk3tbl.ocv 

set +e
rm idA idB idS pkA pkB pkS skA skB skS keytbl t tl
set -e

ocamlfind ocamlopt $CRYPTOKIT -I .. -o Skeygen ../base.mli ../base.ml ../crypto.mli ../crypto.ml ONS_Keygen.mli ONS_Keygen.ml Skeygen.ml
ocamlfind ocamlopt $CRYPTOKIT -I .. -o Akeygen ../base.mli ../base.ml ../crypto.mli ../crypto.ml ONS_AGenKey.mli ONS_AGenKey.ml Akeygen.ml
ocamlfind ocamlopt $CRYPTOKIT -I .. -o Bkeygen ../base.mli ../base.ml ../crypto.mli ../crypto.ml ONS_BGenKey.mli ONS_BGenKey.ml Bkeygen.ml
ocamlfind ocamlopt $CRYPTOKIT -I .. -o A ../base.mli ../base.ml ../crypto.mli ../crypto.ml ONS_A.mli ONS_A.ml A.ml
ocamlfind ocamlopt $CRYPTOKIT -I .. -o B ../base.mli ../base.ml ../crypto.mli ../crypto.ml ONS_B.mli ONS_B.ml B.ml
ocamlfind ocamlopt $CRYPTOKIT -I .. -o S ../base.mli ../base.ml ../crypto.mli ../crypto.ml ONS_S.mli ONS_S.ml S.ml

ocamlfind ocamlopt $CRYPTOKIT -I .. -o test ../base.mli ../base.ml ../crypto.mli ../crypto.ml ONS_Keygen.mli ONS_Keygen.ml ONS_B.mli ONS_B.ml ONS_AGenKey.mli ONS_AGenKey.ml ONS_BGenKey.mli ONS_BGenKey.ml ONS_A.mli ONS_A.ml ONS_S.mli ONS_S.ml test.ml
