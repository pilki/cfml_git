OPTIONS=-I lex -I parsing -I typing -I utils

all:
	ocamlbuild $(OPTIONS) main.byte

opt:
	ocamlbuild main.opt

clean:
	rm -Rf _build
	rm main.byte
