#!/bin/sh
set -e

CVD=../../..
$CVD/cryptoverif yieldcaught.cv
$CVD/cryptoverif -impl -o . yieldcaught.cv

CRYPTOKIT="-linkpkg -package cryptokit"

ocamlfind ocamlopt $CRYPTOKIT -I $CVD/implementation/ -o main.exe $CVD/implementation/base.mli $CVD/implementation/base.ml $CVD/implementation/crypto.mli $CVD/implementation/crypto.ml WLSK_Init.mli WLSK_Init.ml main.ml

rm -f keytbl
./main.exe
# Should output CORRECT: ...
