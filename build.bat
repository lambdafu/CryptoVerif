cd src

ocamlyacc parser.mly
ocamllex lexer.mll
ocamlyacc oparser.mly
ocamllex olexer.mll
ocamlc -o ..\cryptoverif.exe str.cma parsing_helper.mli parsing_helper.ml occ_map.mli occ_map.ml types.ml ptree.mli parser.mli parser.ml lexer.ml oparser.mli oparser.ml olexer.ml settings.mli settings.ml terms.mli terms.ml stringmap.mli stringmap.ml syntax.mli syntax.ml polynom.mli polynom.ml display.mli display.ml displaytex.mli displaytex.ml check.mli check.ml computeruntime.mli computeruntime.ml proba.mli proba.ml facts.mli facts.ml simplify1.mli simplify1.ml transf_auto_sa_rename.mli transf_auto_sa_rename.ml transf_expand.mli transf_expand.ml transf_sarename.mli transf_sarename.ml transf_remove_assign.mli transf_remove_assign.ml transf_move.mli transf_move.ml transf_insert_event.mli transf_insert_event.ml transf_globaldepanal.mli transf_globaldepanal.ml transf_merge.mli transf_merge.ml transf_simplify.mli transf_simplify.ml transf_crypto.mli transf_crypto.ml transf_insert_replace.mli transf_insert_replace.ml transf_tables.mli transf_tables.ml check_distinct.mli check_distinct.ml check_corresp.mli check_corresp.ml success.mli success.ml invariants.mli invariants.ml instruct.mli instruct.ml implementation.mli implementation.ml main.ml

cd ..
