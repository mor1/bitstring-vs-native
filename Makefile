SHELL = /bin/sh
OCB = ocamlbuild

SOURCES = $(wildcard *.ml)
TARGETS = $(SOURCES:.ml=.native)

.PHONY: all clean
.DEFAULT: all

all: $(TARGETS)
clean:
	$(RM) *.native
	$(OCB) -clean

%.native: %.ml
	$(OCB) $@

dns_bs.native: dns_bs.ml
	$(OCB) -cflags -annot,-g,-I,+site-lib/bitstring\
		-ocamlopt 'ocamlopt -I +site-lib/bitstring'\
		-pp 'camlp4of -I /usr/local/lib/ocaml/site-lib/bitstring bitstring.cma bitstring_persistent.cma pa_bitstring.cmo' -Is site-lib/bitstring -libs unix,bitstring $@

