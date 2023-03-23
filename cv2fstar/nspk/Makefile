all: test

# Boilerplate
# -----------

include Makefile.include

FST_FILES=$(wildcard src/*.fst) $(wildcard src/*.fsti)

ifndef NODEPEND
ifndef MAKE_RESTARTS
.depend: .FORCE
	@mkdir -p obj
	@$(FSTAR) --dep full $(FST_FILES) --extract 'OCaml:-* +NSL +Application' > $@

.PHONY: .FORCE
.FORCE:
endif
endif

include .depend

.PHONY: clean
clean:
	rm -rf obj dist .depend *.exe
	rm -rf tests/test.cmx tests/test.cmi tests/test.o

# Verification
# ------------

hints obj:
	mkdir $@

%.checked: | hints obj
	$(FSTAR) --hint_file hints/$(notdir $*).hints $(notdir $*) && touch -c $@

%.ml:
	$(FSTAR) --codegen OCaml \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<))

# OCaml
# -----

ifeq ($(OS),Windows_NT)
  export OCAMLPATH := $(FSTAR_HOME)/lib;$(OCAMLPATH)
else
  export OCAMLPATH := $(FSTAR_HOME)/lib:$(OCAMLPATH)
endif

OCAMLOPT = OCAMLPATH=$(OCAMLPATH) ocamlfind opt -package fstar.lib -package cryptokit -linkpkg -g -I $(HACL_HOME)/obj -I $(CV2FSTAR_HOME)/obj -I obj -w -8-20-26

TAC = $(shell which tac >/dev/null 2>&1 && echo "tac" || echo "tail -r")

ALL_CMX_FILES = $(patsubst %.ml,%.cmx,$(shell echo $(ALL_ML_FILES) | $(TAC)))

.PRECIOUS: obj/%.cmx
%.cmx: %.ml
	  $(OCAMLOPT) -c $< -o $@

libnspk.cmxa: $(ALL_CMX_FILES)
	OCAMLPATH=$(OCAMLPATH) ocamlfind opt -package fstar.lib -g -I $(HACL_HOME)/obj -I $(CV2FSTAR_HOME)/obj -I obj -a -o $@ $^

# Tests
# -----

.PHONY: test
test: test.exe
	./$<

test.exe: $(HACL_HOME)/obj/libhaclml.cmxa $(CV2FSTAR_HOME)/obj/Lib_RandomSequence.cmx $(CV2FSTAR_HOME)/libcv2fstar.cmxa libnspk.cmxa tests/test.cmx
	$(OCAMLOPT) -I obj -package fstar.lib -linkpkg $^ -o $@
