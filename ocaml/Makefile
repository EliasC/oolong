.PHONY: all clean native

OCB_FLAGS = -use-ocamlfind -use-menhir
OCB = ocamlbuild $(OCB_FLAGS)

oolong: native
	cp oolong.native oolong

native: sanity
	$(OCB) oolong.native

byte: sanity
	$(OCB) oolong.byte

sanity:
	@which menhir > /dev/null || (echo "Please run 'opam install menhir'" && false)

clean:
	$(OCB) -clean
	rm -f oolong