#!/bin/sh
set -e

../../../cryptoverif orderimpl.cv
../../../cryptoverif -impl OCaml -o . orderimpl.cv

CRYPTOKIT="-linkpkg -package cryptokit"

ocamlfind ocamlopt $CRYPTOKIT -I ../../../cv2OCaml/ -o main.exe ../../../cv2OCaml/base.mli ../../../cv2OCaml/base.ml ../../../cv2OCaml/crypto.mli ../../../cv2OCaml/crypto.ml WLSK_Init.mli WLSK_Init.ml main.ml

rm -f keytbl
./main.exe
# Should output A
