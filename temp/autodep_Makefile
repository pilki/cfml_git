# make sure that you first do
#   chmod +x ocamldep.wrapper 
#   chmod +x go.sh

# you might also need "chmod +x *.byte" when you recompile

SETTINGS=local_settings.sh
SETTINGS_TEMPLATE=template_settings.sh

# if you have a local installation of Coq, you should edit the file 
# local_settings.sh (once the Makefile has created it) with something like:
# COQBIN=/var/tmp/coq-8.3pl2/bin/


############################################################################
# Targets

.PHONY: all settings tools tlclib cflib camllib cf imper clean tests
.SUFFIXES: .camldep .ml .ml.d .v.d _ml.v _ml.vo _proof.v _proof.vo .v .vo .cmo .cmi
.SECONDARY: *.ml.d *.v.d *.cmi *.cmo *.vo imper/*.ml.d imper/*.v.d imper/*.cmi imper/*_ml.v imper/*_ml.vo 
.PRECIOUS: *.ml.d *.v.d *.cmi *.cmo *.vo 

all: settings tools tlclib cf cflib imper


############################################################################
# Creation of a default settings file if none exist

settings: $(SETTINGS)

$(SETTINGS):
	@if [ -f $(SETTINGS) ]; then \
		echo found; \
	else \
		cp $(SETTINGS_TEMPLATE) $(SETTINGS); \
	fi

#ifeq ($(findstring $(SETTINGS), $(wildcard *.sh)), $(SETTINGS))
#	echo > $(SETTINGS)
#	echo export COQBIN= >> $(SETTINGS)
#	echo export OCAMLBIN= >> $(SETTINGS)
#	echo export TLCLIB=./lib/v3/ >> $(SETTINGS)
#	echo export CORE=-j2 >> $(SETTINGS)
#endif

include $(SETTINGS)

ifeq ($(TLCLIB),)
export COQBIN=
export OCAMLBIN=
export TLCLIB=./lib/v3/
export CORES=-j2 
endif


############################################################################

# List of dependencies
TLCLIB_SRC=$(wildcard $(TLCLIB)*.v)
CAML_FILES_IN=$(addprefix $(1)/,*.ml *.mli *.mll *.mly)
MAP=$(foreach a,$(2),$(call $(1),$(a)))
GENERATOR_SUBDIRS=. lex parsing typing tools utils
GENERATOR_DIRS=$(addprefix gen/,$(GENERATOR_SUBDIRS))
GENERATOR_PATTERNS=$(call MAP, CAML_FILES_IN, $(GENERATOR_DIRS))
GENERATOR_SRC=$(wildcard $(GENERATOR_PATTERNS))
CAMLLIB_MLI=$(filter-out gen/stdlib/camlinternal% %genlex.mli %moreLabels.mli %oo.mli, $(wildcard gen/stdlib/*.mli))
# TODO: compute dependencies between the /gen/stdlib/*.mli files to avoid the above filter-out 
CAMLLIB_CMI=$(CAMLLIB_MLI:.mli=.cmi)

# OPTIONS
INCLUDES=-I . -I gen/stdlib -I $(TLCLIB) -I ./imper 
GENERATOR_OPTIONS=-rectypes $(INCLUDES)

# Tools that should be available on the machine
COQC=$(COQBIN)coqc -dont-load-proofs $(INCLUDES)
COQDEP=$(COQBIN)coqdep $(INCLUDES)
COQDOC=$(COQBIN)coqdoc
OCAMLBUILD=$(OCAMLBIN)ocamlbuild

# Tools that are built
GENERATOR=./main.byte
MYOCAMLCMI=./makecmi.byte 
MYOCAMLDEP=./myocamldep.byte 
MYTOOLS=$(GENERATOR) $(MYOCAMLCMI) $(MYOCAMLDEP)
#$(INCLUDES) #todo:rename



############################################################################
# List of library files and developments

CFLIB=\
	CFHeaps \
	CFSpec \
	CFPrint \
	CFTactics \
	CFPrim \
	CFLib 

IMPER=\
	imper/Compose \
	imper/Swap \
	imper/MutableList \
	imper/Counter \
	imper/Landin \
	imper/Dijkstra \
	imper/UnionFind \
	imper/SparseArray 

# those do not compile
MORE=\
	imper/Facto \
	imper/FunctionalList \
	imper/InOut \
	imper/StrongUpdate \
	imper/TreeCopy \
	imper/LambdaEval \
	imper/Loops \

SPECIAL_INTERFACES=\
	imper/NullPointers \
	imper/StrongPointers


############################################################################
# DETAILED TARGETS

# todo: first compute dependencies, then run .vo compilation
# todo: integrate shadow compilation of .vo files

tlclib: $(TLCLIB_SRC)
	make -C $(TLCLIB) lib

cflib: $(CFLIB:=.vo)

camllib: $(CAMLLIB_CMI)

imper: $(IMPER:=_proof.vo)

force:
	echo $(FORCED_VFILES)


############################################################################
# .vo files

%.vo: %.v %.v.d
	$(COQC) $< 


############################################################################
# _ml.v files

cf: $(IMPER:=_ml.v)

%_ml.v: %.ml %.ml.d %.cmi $(GENERATOR) $(GENERATOR_SRC) $(SPECIAL_INTERFACES:=.cmi) Makefile
	$(GENERATOR) $(GENERATOR_OPTIONS) $<


############################################################################
# .ml.d files

# using ocamldep to compute dependencies between ml files, 
# then enforcing corresponding dependencies between %_ml.vo files

# todo: add ocamldep wrapper here as well
%.ml.d: %.ml $(MYOCAMLDEP) Makefile
	$(MYOCAMLDEP) $(INCLUDES) $< > $@
	@cp -f $@ $@.tmp
	@sed -e 's/.*://' -e 's/\\$$//' < $@.tmp | fmt -1 | \
	  sed -e 's/^ *//' -e 's/$$/:/' >> $@  
	@sed -i 's/\.cmo/.cmi/g' $@
	@rm -f $@.tmp
#todo avoid circular dependencies

# avoid computing dependencies with make clean...
ifeq ($(findstring $(MAKECMDGOALS),clean clean_all),)
-include $(IMPER:.ml.d)
endif


############################################################################
# .cmi files

%.cmi: %.ml %.ml.d $(CAMLLIB_CMI) $(GENERATOR)
	$(GENERATOR) -rectypes -onlycmi $(INCLUDES) $<
#todo: could also use $(MYOCAMLCMI) $(INCLUDES) $< with a dependency on $(MYOCAMLCMI) 

# special treatment for compiling the .mli files from the standard library

imper/NullPointers.cmi: imper/NullPointers.mli $(CAMLLIB_CMI) $(MYOCAMLCMI)
	$(MYOCAMLCMI) -rectypes -I gen/stdlib $<
imper/StrongPointers.cmi: imper/StrongPointers.mli $(CAMLLIB_CMI) $(MYOCAMLCMI)
	$(MYOCAMLCMI) -rectypes -I gen/stdlib $<

# special treatment for compiling the .mli files from the standard library

gen/stdlib/pervasives.cmi: gen/stdlib/pervasives.mli $(MYOCAMLCMI)
	$(MYOCAMLCMI) -nostdlib -nopervasives $<
gen/stdlib/%.cmi: gen/stdlib/%.mli gen/stdlib/pervasives.cmi $(MYOCAMLCMI)
	$(MYOCAMLCMI) -nostdlib -I gen/stdlib $<


# todo: add support for mli files

############################################################################
# .v.d files

# using a trick to force dependencies to mention files that do not exist yet

FORCED_VFILES=$(IMPER:=_ml.v)

%.v.d: %.v
	@./ocamldep.wrapper $(FORCED_VFILES) - $(COQDEP) $< > $@

ifeq ($(findstring $(MAKECMDGOALS),clean clean_all),)
-include $(CFLIB:=.v.d) $(IMPER:=_proof.v.d) $(IMPER:=_ml.v.d)
endif

# For some reason the makefile is incapable of working out this dependency on the fly:
# even though it is contained in imper/Counter.ml.d, the file with this dependency
# is not included early enough
imper/Counter.cmi: imper/MutableList.cmi


############################################################################
# .byte files

tools: $(MYTOOLS)

# the makefile does not like the symbolic link generated by ocamlbuild so we copy file

%.byte: $(GENERATOR_SRC)
	$(OCAMLBUILD) -I gen $(addprefix -I ,$(GENERATOR_DIRS)) $@
	@mv $@ temp.byte 
	@cp -L temp.byte $@
	@rm temp.byte


############################################################################
# Cleanup

clean:  
	@rm -f *.d *.vo *.glob *.cmo *.cmi *_ml.v || echo ok
	@rm -f imper/*.d imper/*_ml.v imper/*.vo imper/*.glob imper/*.cmo imper/*.cmi || echo ok
	@rm -f .camldep || echo ok
	@echo "CLEANED UP"
# todo: factorize better the code above

clean_settings:
	@rm -f $(SETTINGS) || @echo ok

clean_tools:
	@rm -Rf _build || echo ok
	@rm -f *.byte || echo ok
	@rm -f gen/stdlib/*.cmi || echo ok

clean_all: clean clean_settings clean_tools


############################################################################
# Debugging commands

test:
	@echo $(OCAMLBUILD)
	@echo $(TLCLIB)
	@echo $(TLCLIB_SRC)
	@echo $(GENERATOR_DIRS)	
	@echo $(GENERATOR_PATTERNS)
	@echo $(GENERATOR_SRC)

changes: $(MYOCAMLDEP)
	$(MYOCAMLDEP) $(INCLUDES) imper/Counter.ml > changes

needed: $(GENERATOR_SRC)
	echo newer
	touch needed





