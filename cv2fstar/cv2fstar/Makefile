all: libcv2fstar.cmxa

# Boilerplate
# -----------

include Makefile.include

FST_FILES=$(wildcard src/*.fst) $(wildcard src/*.fsti)

ifndef NODEPEND
ifndef MAKE_RESTARTS
.depend: .FORCE
	@mkdir -p obj
	@$(FSTAR) --dep full $(FST_FILES) --extract 'OCaml:-* +Crypto +CVTypes +Helper +NatMap +RandomHelper +State' > $@

.PHONY: .FORCE
.FORCE:
endif
endif

include .depend

.PHONY: clean
clean:
	rm -rf obj dist .depend *.exe

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

OCAMLOPT = OCAMLPATH=$(OCAMLPATH) ocamlfind opt -package fstar.lib -package cryptokit -linkpkg -g -I $(HACL_HOME)/obj -I obj -w -8-20-26

TAC = $(shell which tac >/dev/null 2>&1 && echo "tac" || echo "tail -r")

ALL_CMX_FILES = $(patsubst %.ml,%.cmx,$(shell echo $(ALL_ML_FILES) | $(TAC)))

.PRECIOUS: obj/%.cmx
%.cmx: %.ml obj/Lib_RandomSequence.cmx
	  $(OCAMLOPT) -c $< -o $@

obj/Lib_RandomSequence.cmx: lib/Lib_RandomSequence.ml
	$(OCAMLOPT) -c $< -o $@

libcv2fstar.cmxa: $(ALL_CMX_FILES)
	OCAMLPATH=$(OCAMLPATH) ocamlfind opt -package fstar.lib -g -I $(HACL_HOME)/obj -I obj -a -o $@ $^

# Tests
# -----

# See nspk example.
