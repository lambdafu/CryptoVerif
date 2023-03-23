CMX = $(addprefix src/,parsing_helper.cmx occ_map.cmx types.cmx settings.cmx parser.cmx lexer.cmx stringPlus.cmx terms.cmx array_ref.cmx incompatible.cmx info_from_term.cmx def.cmx match_eq.cmx stringmap.cmx polynom.cmx display.cmx  displaytex.cmx computeruntime.cmx proba.cmx transf_auto_sa_rename.cmx transf_tables.cmx transf_remove_assign.cmx check.cmx query_equiv.cmx syntax.cmx facts.cmx depanal.cmx facts_of_elsefind.cmx improved_def.cmx unique.cmx transf_simplify_nonexpanded.cmx transf_expand.cmx transf_sarename.cmx transf_use_variable.cmx transf_move.cmx transf_insert_event.cmx transf_globaldepanal.cmx transf_merge.cmx transf_simplify.cmx transf_crypto.cmx transf_insert_replace.cmx transf_guess.cmx special_equiv.cmx check_distinct.cmx check_corresp.cmx success.cmx invariants.cmx instruct.cmx implementationOCaml.cmx implementationFStar.cmx version.cmx main.cmx)
# The following is for .mli that do not have an .ml
CMI = $(addprefix src/,ptree.cmi)

CMXGEN = src/cryptogen.cmx

CMXANAL = $(addprefix src/,rusage.c stringPlus.cmx analyze.cmx)

CMXADDTAGS = $(addprefix src/,stringPlus.cmx addexpectedtags.cmx)

EXEC =
ifeq (Windows_NT,$(OS))
  EXEC = .exe
endif

ifeq ($(MAKECMDGOALS),clean)
  SKIPDEPEND=1
endif

GENERATED_ML_FILES = src/parser.ml src/parser.mli src/lexer.ml

.PHONY: all clean build

all:
	rm -f .depend && $(MAKE) .depend
	$(MAKE) build

.depend: | $(GENERATED_ML_FILES)
	ocamldep -all -I src -native src/*.mli src/*.ml > $@

ifndef SKIPDEPEND
include .depend
endif

OCAMLOPT = ocamlopt -I src -I +threads

BINARIES = cryptoverif$(EXEC) cryptogen$(EXEC) analyze$(EXEC) addexpectedtags$(EXEC)
LIBS = default.cvl default.ocvl cryptoverif.pvl

build: $(GENERATED_ML_FILES) $(BINARIES) $(LIBS)

# The following is a Group Target Rule
# https://www.gnu.org/software/make/manual/html_node/Multiple-Targets.html
src/parser.ml src/parser.mli &: src/parser.mly
	ocamlyacc -v $^

src/lexer.ml: src/lexer.mll
	ocamllex $^

cryptoverif$(EXEC): $(CMI) $(CMX)
	$(OCAMLOPT) -o $@ unix.cmxa str.cmxa $(CMX)

cryptogen$(EXEC): $(CMXGEN)
	$(OCAMLOPT) -o $@ $^

analyze$(EXEC): $(CMXANAL)
	$(OCAMLOPT) -o $@ unix.cmxa $^

addexpectedtags$(EXEC): $(CMXADDTAGS)
	$(OCAMLOPT) -o $@ $^

# If there is an %.mli, %.cmi shall be created from it.
src/%.cmi: src/%.mli
	$(OCAMLOPT) -c $< -o $@

# If there is no %.mli, this rule builds %.cmi from %.ml
src/%.cmx src/%.cmi &: src/%.ml
	$(OCAMLOPT) -c $< -o $@

cryptolib/gen.cvl: cryptogen$(EXEC)
	./cryptogen$(EXEC) -args-from-to 1 10 all > $@

cryptolib/gen.ocvl: cryptogen$(EXEC)
	./cryptogen$(EXEC) -out oracles -args-from-to 1 10 all > $@

cryptolib/gen.pvl: cryptogen$(EXEC)
	./cryptogen$(EXEC) -out proverif -args-from-to 1 10 all > $@

default.cvl: cryptolib/commonlib.cvl cryptolib/gen.cvl
	cat $^ > $@

default.ocvl: cryptolib/commonlib.cvl cryptolib/gen.ocvl
	cat $^ > $@

cryptoverif.pvl: cryptolib/crypto.pvl cryptolib/gen.pvl
	cat $^ > $@

clean:
	rm -f cryptoverif$(EXEC) cryptogen$(EXEC) analyze$(EXEC) addexpectedtags$(EXEC)
	rm -f src/parser.ml src/parser.mli src/lexer.ml
	rm -f cryptolib/gen.cvl cryptolib/gen.ocvl cryptolib/gen.pvl
	rm -f default.cvl default.ocvl cryptoverif.pvl
	rm -f src/*.cmi src/*.cmx src/*.o
	rm -f .depend
