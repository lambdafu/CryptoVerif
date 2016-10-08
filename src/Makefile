SOURCES=parsing_helper.mli parsing_helper.ml occ_map.mli occ_map.ml types.ml ptree.mli parser.mli parser.ml lexer.ml oparser.mli oparser.ml olexer.ml settings.mli settings.ml terms.mli terms.ml stringmap.mli stringmap.ml syntax.mli syntax.ml polynom.mli polynom.ml display.mli display.ml displaytex.mli displaytex.ml check.mli check.ml computeruntime.mli computeruntime.ml proba.mli proba.ml facts.mli facts.ml simplify1.mli simplify1.ml transf_auto_sa_rename.mli transf_auto_sa_rename.ml transf_expand.mli transf_expand.ml transf_sarename.mli transf_sarename.ml transf_remove_assign.mli transf_remove_assign.ml transf_move.mli transf_move.ml transf_insert_event.mli transf_insert_event.ml transf_globaldepanal.mli transf_globaldepanal.ml transf_merge.mli transf_merge.ml transf_simplify.mli transf_simplify.ml transf_crypto.mli transf_crypto.ml transf_insert_replace.mli transf_insert_replace.ml transf_tables.mli transf_tables.ml check_distinct.mli check_distinct.ml check_corresp.mli check_corresp.ml success.mli success.ml invariants.mli invariants.ml instruct.mli instruct.ml implementation.mli implementation.ml main.ml

OBJECTS = parsing_helper.cmo occ_map.cmo types.cmo parser.cmo lexer.cmo oparser.cmo olexer.cmo settings.cmo terms.cmo stringmap.cmo syntax.cmo polynom.cmo display.cmo displaytex.cmo check.cmo computeruntime.cmo proba.cmo facts.cmo simplify1.cmo transf_auto_sa_rename.cmo transf_expand.cmo transf_sarename.cmo transf_remove_assign.cmo transf_move.cmo transf_insert_event.cmo transf_globaldepanal.cmo transf_merge.cmo transf_simplify.cmo transf_crypto.cmo transf_insert_replace.cmo transf_tables.cmo check_distinct.cmo check_corresp.cmo success.cmo invariants.cmo instruct.cmo implementation.cmo main.cmo

OBJECTSOPT = parsing_helper.cmx occ_map.cmx types.cmx parser.cmx lexer.cmx oparser.cmx olexer.cmx settings.cmx terms.cmx stringmap.cmx syntax.cmx polynom.cmx display.cmx displaytex.cmx check.cmx computeruntime.cmx proba.cmx facts.cmx simplify1.cmx transf_auto_sa_rename.cmx transf_expand.cmx transf_sarename.cmx transf_remove_assign.cmx transf_move.cmx transf_insert_event.cmx transf_globaldepanal.cmx transf_merge.cmx transf_simplify.cmx transf_crypto.cmx transf_insert_replace.cmx transf_tables.cmx check_distinct.cmx check_corresp.cmx success.cmx invariants.cmx instruct.cmx implementation.cmx main.cmx

AUTOGEN = oparser.ml oparser.mli olexer.ml parser.ml parser.mli lexer.ml

all: cryptoverif
	cp cryptoverif ../cryptoverif

dbg: cryptoverif_dbg


%.ml: %.mll
	ocamllex $<

%.ml %.mli: %.mly
	ocamlyacc -v $<

cryptoverif:$(OBJECTSOPT)
	ocamlopt -o cryptoverif str.cmxa $(OBJECTSOPT)

cryptoverif_dbg:$(OBJECTS)
	ocamlc -o cryptoverif_dbg -g str.cma $(OBJECTS)

%.cmx:%.ml
	ocamlopt -c $<

%.cmo:%.ml
	ocamlc -annot -g -c $<

%.cmi:%.mli
	ocamlc -c $<

doc:
	ocamldoc -dot *ml *mli

clean:
	-rm cryptoverif *cmi *cmo *annot cryptoverif_dbg O* $(AUTOGEN) .depend

.PHONY:all dbg doc clean

.depend:$(AUTOGEN)
	ocamldep *mli *ml > .depend

include .depend
