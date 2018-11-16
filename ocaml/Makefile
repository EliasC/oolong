.PHONY: all clean native count

OCB_FLAGS = -use-ocamlfind -use-menhir
OCB = ocamlbuild $(OCB_FLAGS)
WC = $(shell which cloc || echo wc)
SOURCES = parser.mly lexer.mll tables.ml ast.ml typechecker.ml interpreter.ml oolong.ml

oolong: native
	cp oolong.native oolong

native: sanity
	$(OCB) oolong.native

byte: sanity
	$(OCB) oolong.byte

sanity:
	@which menhir > /dev/null || (echo "Please run 'opam install menhir'" && false)

count:
	$(WC) $(SOURCES)

clean:
	$(OCB) -clean
	rm -f oolong