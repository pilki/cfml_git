OPTIONS=-I parsing -I typing -I utils -I tools
OCAMLBUILD=ocamlbuild $(OPTIONS)

all: progs lib

progs: force
	$(OCAMLBUILD) main.byte makecmi.byte tools/myocamldep.byte 

lib: makecmi.byte
	./makecmi.byte -nostdlib -nopervasives stdlib/pervasives.mli
	./makecmi.byte -nostdlib -I stdlib stdlib/list.mli
	./makecmi.byte -nostdlib -I stdlib stdlib/array.mli

force:

clean:
	rm -Rf _build
	rm main.byte
