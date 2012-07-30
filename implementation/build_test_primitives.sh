#!/bin/sh

CRYPTOKIT="-I cryptokit -I +cryptokit"

ocamlopt $CRYPTOKIT -o test_primitives unix.cmxa nums.cmxa cryptokit.cmxa base.mli base.ml crypto.mli crypto.ml test_primitives.ml
ocamlopt $CRYPTOKIT -o test_insert unix.cmxa nums.cmxa cryptokit.cmxa base.mli base.ml crypto.mli crypto.ml test_insert.ml
ocamlopt $CRYPTOKIT -o test_get unix.cmxa nums.cmxa cryptokit.cmxa base.mli base.ml crypto.mli crypto.ml test_get.ml
