cd src

ocamlyacc parser.mly
ocamllex lexer.mll
ocamlc -o ..\cryptoverif.exe unix.cma str.cma parsing_helper.mli parsing_helper.ml occ_map.mli occ_map.ml types.ml ptree.mli settings.mli settings.ml parser.mli parser.ml lexer.ml stringPlus.mli stringPlus.ml terms.mli terms.ml display.mli display.ml  displaytex.mli displaytex.ml array_ref.mli array_ref.ml incompatible.mli incompatible.ml match_eq.mli match_eq.ml stringmap.mli stringmap.ml polynom.mli polynom.ml compute_state_display_info.mli compute_state_display_info.ml info_from_term.mli info_from_term.ml def.mli def.ml computeruntime.mli computeruntime.ml proba.mli proba.ml transf_auto_sa_rename.mli transf_auto_sa_rename.ml transf_tables.mli transf_tables.ml transf_remove_assign.mli transf_remove_assign.ml check.mli check.ml query_equiv.mli query_equiv.ml syntax.mli syntax.ml facts.mli facts.ml depanal.mli depanal.ml facts_of_elsefind.mli facts_of_elsefind.ml improved_def.mli improved_def.ml unique.mli unique.ml transf_simplify_nonexpanded.mli transf_simplify_nonexpanded.ml transf_expand.mli transf_expand.ml transf_sarename.mli transf_sarename.ml transf_use_variable.mli transf_use_variable.ml transf_move.mli transf_move.ml transf_insert_event.mli transf_insert_event.ml transf_globaldepanal.mli transf_globaldepanal.ml transf_merge.mli transf_merge.ml transf_simplify.mli transf_simplify.ml transf_crypto.mli transf_crypto.ml transf_insert_replace.mli transf_insert_replace.ml special_equiv.mli special_equiv.ml check_secrecy.mli check_secrecy.ml check_corresp.mli check_corresp.ml success.mli success.ml transf_guess.mli transf_guess.ml invariants.mli invariants.ml instruct.mli instruct.ml implementation.mli implementation.ml version.mli version.ml main.ml
ocamlc -o ..\cryptogen.exe cryptogen.ml

cd ..

cd cryptolib

..\cryptogen -args-from-to 1 10 all > gen.cvl
..\cryptogen -out oracles -args-from-to 1 10 all > gen.ocvl
..\cryptogen -out proverif -args-from-to 1 10 all > gen.pvl

copy commonlib.cvl + gen.cvl ..\default.cvl
copy commonlib.cvl + gen.ocvl ..\default.ocvl
copy crypto.pvl + gen.pvl ..\cryptoverif.pvl

cd ..
