#!/bin/sh
set -e

../../../cryptoverif orderimpl.cv
../../../cryptoverif -impl -o . orderimpl.cv

CRYPTOKIT="-linkpkg -package cryptokit"

ocamlfind ocamlopt $CRYPTOKIT -I ../../../implementation/ -o main.exe ../../../implementation/base.mli ../../../implementation/base.ml ../../../implementation/crypto.mli ../../../implementation/crypto.ml WLSK_Init.mli WLSK_Init.ml main.ml

rm -f keytbl
./main.exe
# Should output A
