SHELL=/bin/sh
OCAMLC=ocamlc -g
OCAMLOPT=ocamlopt -g
OCAMLLEX=ocamllex
OCAMLYACC=ocamlyacc
OCAMLDEP=ocamldep
RM=rm -f

all: parse

clean:
	$(RM) *~ *.cmx *.cmi *.cmo *.o
	$(RM) salparse2.ml salparse2.mli sallex.ml
	$(RM) parse

parse: sal_ast.cmx salparse2.cmx sallex.cmx sal2lisp.cmx lisp_ast.cmx parse.cmx
	$(OCAMLOPT) $^ -o $@

%.cmo: %.ml
	$(OCAMLC) -c $<

%.cmi: %.mli
	$(OCAMLC) -c $<

%.cmx: %.ml
	$(OCAMLOPT) -c $< -o $@ 

%.ml: %.mll
	$(OCAMLLEX) $< -o $@

%.ml: %.mly
	$(OCAMLYACC) $<

%.mli: %.mly
	$(OCAMLYACC) $<

include .depend

.depend: sallex.ml salparse2.ml salparse2.mli sal2lisp.ml lisp_ast.ml
	$(OCAMLDEP) -native *.ml *.mli > $@

