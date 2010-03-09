OPTIONS=-I lex -I parsing -I typing -I utils
OCAMLBUILD=ocamlbuild $(OPTIONS)

all: 
	$(OCAMLBUILD) main.byte tools/myocamldep.byte

clean:
	rm -Rf _build
	rm main.byte
