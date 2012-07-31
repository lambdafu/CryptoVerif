SOURCES=parsing_helper.mli parsing_helper.ml types.ml ptree.mli parser.mli parser.ml lexer.ml oparser.mli oparser.ml olexer.ml binderset.mli binderset.ml settings.mli settings.ml terms.mli terms.ml stringmap.mli stringmap.ml syntax.mli syntax.ml polynom.mli polynom.ml display.mli display.ml displaytex.mli displaytex.ml computeruntime.mli computeruntime.ml proba.mli proba.ml transform.mli transform.ml check.mli check.ml facts.mli facts.ml simplify1.mli simplify1.ml globaldepanal.mli globaldepanal.ml mergebranches.mli mergebranches.ml simplify.mli simplify.ml cryptotransf.mli cryptotransf.ml insertinstruct.mli insertinstruct.ml success.mli success.ml invariants.mli invariants.ml reduce_tables.mli reduce_tables.ml instruct.mli instruct.ml implementation.mli implementation.ml main.ml

OBJECTS = parsing_helper.cmo types.cmo parser.cmo lexer.cmo oparser.cmo olexer.cmo binderset.cmo settings.cmo terms.cmo stringmap.cmo syntax.cmo polynom.cmo display.cmo displaytex.cmo computeruntime.cmo proba.cmo transform.cmo check.cmo facts.cmo simplify1.cmo globaldepanal.cmo mergebranches.cmo simplify.cmo cryptotransf.cmo insertinstruct.cmo success.cmo invariants.cmo reduce_tables.cmo instruct.cmo implementation.cmo main.cmo


OBJECTSOPT = parsing_helper.cmx types.cmx parser.cmx lexer.cmx oparser.cmx olexer.cmx binderset.cmx settings.cmx terms.cmx stringmap.cmx syntax.cmx polynom.cmx display.cmx displaytex.cmx computeruntime.cmx proba.cmx transform.cmx check.cmx facts.cmx simplify1.cmx globaldepanal.cmx mergebranches.cmx simplify.cmx cryptotransf.cmx insertinstruct.cmx success.cmx invariants.cmx reduce_tables.cmx instruct.cmx implementation.cmx main.cmx

AUTOGEN = oparser.ml oparser.mli olexer.ml parser.ml parser.mli lexer.ml

all: cryptoverif
	cp cryptoverif ../cryptoverif

dbg: cryptoverif_dbg


%.ml: %.mll
	ocamllex $<

%.ml %.mli: %.mly
	ocamlyacc $<

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
