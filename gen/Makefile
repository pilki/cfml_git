OPTIONS=-I parsing -I typing -I utils -I tools
OCAMLBUILD=ocamlbuild $(OPTIONS)

all: 
	$(OCAMLBUILD) main.byte tools/myocamldep.byte

dep:
	$(OCAMLBUILD) tools/myocamldep.byte

main:
	$(OCAMLBUILD) main.byte 

clean:
	rm -Rf _build
	rm main.byte
