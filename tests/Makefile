OCAMLFIND ?= ocamlfind
OCAMLOPTC ?= "$(OCAMLFIND)" opt

all: coc

coc: core.ml core.mli top.ml newman.coc
	$(OCAMLOPTC) -c core.mli
	$(OCAMLOPTC) -c core.ml
	$(OCAMLOPTC) -c -pp "camlp4o" top.ml
	$(OCAMLOPTC) -o coc core.cmx top.cmx
	@echo '***** test: checking the proof of the Newman lemma *****'
	./coc < newman.coc
	@echo '******************** End of test ***********************'

clean:
	rm -f core.ml core.mli *.cmx *.cmi *.o

# Building core.ml : we do not want an Extract.vo to be produced
core.ml core.mli: Extract.v
	$(COQBIN)coqtop -R ../theories CoqInCoq -batch -load-vernac-source Extract.v

.PHONY: all clean
