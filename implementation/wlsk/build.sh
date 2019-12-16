#!/bin/bash
set -e

function file_exists_or_abort()
{
    filename=$1
    if [ ! -f $filename ]
    then
	echo "File '$filename' not found. Did you execute this script in the directory in which it's stored?"
	exit 2
    fi
}

file_exists_or_abort woolamskcorr_tbl.cv

CRYPTOKIT="-linkpkg -package cryptokit"

echo Proving the protocol...
../../cryptoverif woolamskcorr_tbl.cv > woolamskcorr_tbl.out
grep -E '(RESULT|All)' woolamskcorr_tbl.out | grep -v "RESULT time"
echo Generating implementation...
../../cryptoverif -impl woolamskcorr_tbl.cv

set +e
rm keytbl wlsk_enc_key wlsk_mac_key wlsk_id
set -e

ocamlfind ocamlopt $CRYPTOKIT -I .. -o keygen ../base.mli ../base.ml ../crypto.mli ../crypto.ml WLSK_keygen.mli WLSK_keygen.ml keygen.ml
ocamlfind ocamlopt $CRYPTOKIT -I .. -o server ../base.mli ../base.ml ../crypto.mli ../crypto.ml WLSK_S.mli WLSK_S.ml server.ml
ocamlfind ocamlopt $CRYPTOKIT -I .. -o init ../base.mli ../base.ml ../crypto.mli ../crypto.ml WLSK_Init.mli WLSK_Init.ml init.ml
ocamlfind ocamlopt $CRYPTOKIT -I .. -o resp ../base.mli ../base.ml ../crypto.mli ../crypto.ml WLSK_Resp.mli WLSK_Resp.ml resp.ml

ocamlfind ocamlopt $CRYPTOKIT -I .. -o test_wlsk ../base.mli ../base.ml ../crypto.mli ../crypto.ml WLSK_Init.mli WLSK_Init.ml WLSK_Resp.mli WLSK_Resp.ml WLSK_S.mli WLSK_S.ml WLSK_keygen.mli WLSK_keygen.ml test_wlsk.ml
