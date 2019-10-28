#!/bin/sh

CRYPTOKIT="-linkpkg -package cryptokit"

cd ../.. 
echo Proving the protocol...
./cryptoverif implementation/nspk/nspk3tbl.ocv > implementation/nspk/nspk3tbl.out
egrep '(RESULT|All)' implementation/nspk/nspk3tbl.out | grep -v "RESULT time"
echo Generating implementation...
./cryptoverif -impl -o implementation/nspk implementation/nspk/nspk3tbl.ocv 
cd implementation/nspk

rm idA idB idS pkA pkB pkS skA skB skS keytbl t tl

ocamlfind ocamlopt $CRYPTOKIT -I .. -o Skeygen ../base.mli ../base.ml ../crypto.mli ../crypto.ml ONS_Keygen.mli ONS_Keygen.ml Skeygen.ml
ocamlfind ocamlopt $CRYPTOKIT -I .. -o Akeygen ../base.mli ../base.ml ../crypto.mli ../crypto.ml ONS_AGenKey.mli ONS_AGenKey.ml Akeygen.ml
ocamlfind ocamlopt $CRYPTOKIT -I .. -o Bkeygen ../base.mli ../base.ml ../crypto.mli ../crypto.ml ONS_BGenKey.mli ONS_BGenKey.ml Bkeygen.ml
ocamlfind ocamlopt $CRYPTOKIT -I .. -o A ../base.mli ../base.ml ../crypto.mli ../crypto.ml ONS_A.mli ONS_A.ml A.ml
ocamlfind ocamlopt $CRYPTOKIT -I .. -o B ../base.mli ../base.ml ../crypto.mli ../crypto.ml ONS_B.mli ONS_B.ml B.ml
ocamlfind ocamlopt $CRYPTOKIT -I .. -o S ../base.mli ../base.ml ../crypto.mli ../crypto.ml ONS_S.mli ONS_S.ml S.ml

ocamlfind ocamlopt $CRYPTOKIT -I .. -o test ../base.mli ../base.ml ../crypto.mli ../crypto.ml ONS_Keygen.mli ONS_Keygen.ml ONS_B.mli ONS_B.ml ONS_AGenKey.mli ONS_AGenKey.ml ONS_BGenKey.mli ONS_BGenKey.ml ONS_A.mli ONS_A.ml ONS_S.mli ONS_S.ml test.ml
