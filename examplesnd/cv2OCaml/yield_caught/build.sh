#!/bin/sh
set -e

CVD=../../..
$CVD/cryptoverif yieldcaught.cv
$CVD/cryptoverif -impl OCaml -o . yieldcaught.cv

CRYPTOKIT="-linkpkg -package cryptokit"

ocamlfind ocamlopt $CRYPTOKIT -I $CVD/cv2OCaml/ -o main.exe $CVD/cv2OCaml/base.mli $CVD/cv2OCaml/base.ml $CVD/cv2OCaml/crypto.mli $CVD/cv2OCaml/crypto.ml WLSK_Init.mli WLSK_Init.ml main.ml

rm -f keytbl
./main.exe
# Should output CORRECT: ...
