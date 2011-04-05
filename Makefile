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

.PHONY: all depend settings tools tlclib cflib camllib cf imper clean clean_files clean_tools clean_settings clean_deps tests
.SUFFIXES: .camldep .ml .ml.d .v.d _ml.v _ml.v.d _ml.vo _proof.v _proof.vo .v .vo .cmo .cmi .byte
.INTERMEDIATE: %.ml.d %.v.d %.cmi %.cmo %.vo %.ml.d %.v.d %_ml.v %_ml.v.d %_ml.vo %.byte 
.PRECIOUS: %.ml.d %_ml.v.d %.v.d %.cmi %.cmo %_ml.v %_ml.vo %.vo %.byte 

# Generate an error if there is no 'depend' file and the target is not 'depend'
NODEPEND=
ifeq ($(findstring depend, $(wildcard depend)),)
ifeq ($(findstring $(MAKECMDGOALS),depend),)
NODEPEND=nodepend
endif
endif

# Generate an error if there is no 'camllib/*.mli' file is there
NOCAMLLIB=
ifeq ($(findstring camllib/pervasives.mli, $(wildcard camllib)),)
ifeq ($(findstring $(MAKECMDGOALS),camllib),)
NOCAMLLIB=nodepend
endif
endif


all: $(NODEPEND) settings tools tlclib cf cflib imper

nodepend:
	@echo you need to first call make depend 
	@exit 1


############################################################################
# Local settings

# creation of the default local_settings.sh file

settings: $(SETTINGS)

$(SETTINGS):
	@if [ -f $(SETTINGS) ]; then \
		echo found; \
	else \
		cp $(SETTINGS_TEMPLATE) $(SETTINGS); \
	fi

# include local_settings.sh file if it exists,
# otherwise create it (only if target is 'all')

ifeq ($(findstring $(SETTINGS), $(wildcard *.sh)), $(SETTINGS))
MKSETTINGS=
include $(SETTINGS)
else
MKSETTINGS=$(SETTINGS)
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
GENERATOR_SUBDIRS=lex parsing typing tools utils
GENERATOR_DIRS=gen $(addprefix gen/,$(GENERATOR_SUBDIRS))
GENERATOR_PATTERNS=$(call MAP, CAML_FILES_IN, $(GENERATOR_DIRS))
GENERATOR_SRC=$(wildcard $(GENERATOR_PATTERNS))
# todo: compute dependencies between the /gen/stdlib/*.mli files to avoid the above filter-out 

# OPTIONS
INCLUDES=-I . -I camllib -I $(TLCLIB) -I ./imper 
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

# Cmi files
CAMLLIB_MLI_PATH=$(filter-out gen/stdlib/camlinternal% %genlex.mli %moreLabels.mli %oo.mli, $(wildcard gen/stdlib/*.mli))
CAMLLIB_MLI=$(patsubst gen/stdlib/%,%,$(CAMLLIB_MLI_PATH))
CAMLLIB_CMI=$(addprefix camllib/,$(CAMLLIB_MLI:.mli=.cmi))
SPECIAL_INTERFACES=\
	camllib/NullPointers \
	camllib/StrongPointers
SHARED_CMI=$(CAMLLIB_CMI) $(SPECIAL_INTERFACES:=.cmi)


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
	imper/Demo \
	imper/Compose \
	imper/Swap \
	imper/MutableList \
	imper/Counter \
	imper/Dijkstra \
	imper/UnionFind \
	imper/SparseArray 

#	imper/Landin \
# those do not compile
MORE=\
	imper/Facto \
	imper/FunctionalList \
	imper/InOut \
	imper/StrongUpdate \
	imper/TreeCopy \
	imper/LambdaEval \
	imper/Loops \

############################################################################
# DETAILED TARGETS

# todo: first compute dependencies, then run .vo compilation
# todo: integrate shadow compilation of .vo files

tlclib: $(TLCLIB_SRC)
	make -C $(TLCLIB) lib

cflib: $(CFLIB:=.vo)

camllib: $(SHARED_CMI)

imper: $(IMPER:=_proof.vo)

force:
	echo $(FORCED_VFILES)

depend: camllibsrc $(IMPER:=.ml.d) $(IMPER:=_ml.v) $(IMPER:=_ml.v.d) $(IMPER:=_proof.v.d) $(IMPER:=.cmi) $(CFLIB:=.v.d)
	@touch depend

# include these dependencies only if the target is not 'clean' nor 'depend'
ifeq ($(findstring $(MAKECMDGOALS),clean clean_files clean_tools clean_deps clean_settings depend),)
-include $(IMPER:=.ml.d) $(IMPER:=_ml.v.d) $(IMPER:=_proof.v.d) $(CFLIB:=.v.d) 
endif
#--todo: why make depends keeps rebuilding the _ml.v files ?

# include dependencies on ml files only if the target is 'depend' 
ifeq ($(findstring $(MAKECMDGOALS),depend),depend)
-include $(IMPER:=.ml.d)
endif


############################################################################
# .vo files

%.vo: %.v
	$(COQC) $< 
# %.v.d


############################################################################
# _ml.v files

cf: $(IMPER:=_ml.v)

%_ml.v: %.ml %.cmo $(GENERATOR) $(SHARED_CMI)
	$(GENERATOR) $(GENERATOR_OPTIONS) $<

# .cmo files are mentioned in the .ml.d files
%.cmo: %.cmi
#	@touch $@


############################################################################
# .ml.d files

ifeq ($(findstring $(MAKECMDGOALS),depend),depend)

imper/%.ml.d: imper/%.ml $(MYOCAMLDEP) 
	$(MYOCAMLDEP) $(INCLUDES) $< | sed 's/:/: stuff/' > $@

endif

# a dummy target that represents something to do
stuff: $(SETTINGS)


############################################################################
# .v.d files

# using a trick to force dependencies to mention files that do not exist yet

FORCED_VFILES=$(IMPER:=_ml.v)

ifeq ($(findstring $(MAKECMDGOALS),depend),depend)

%.v.d: %.v 
	@echo $(COQDEP) $< > $@
	@./ocamldep.wrapper $(FORCED_VFILES) - $(COQDEP) $< > $@

endif


############################################################################
# .cmi files

#--todo: should use myocamlcmi instead?
imper/%.cmi: imper/%.ml $(GENERATOR) $(SHARED_CMI)
	$(GENERATOR) -rectypes -onlycmi $(INCLUDES) $<
#%.ml.d 



############################################################################
# camllib files

camllibsrc: done
	touch camllibscr
	$(foreach file, $(CAMLLIB_MLI), cp gen/stdlib/$(file) camllib/; )
	touch $@

done: ./go.sh

# special treatment for compiling the .mli files from the standard library

camllib/pervasives.cmi: camllib/pervasives.mli $(MYOCAMLCMI)
	$(MYOCAMLCMI) -nostdlib -nopervasives $<
camllib/%.cmi: camllib/%.mli camllib/pervasives.cmi $(MYOCAMLCMI)
	$(MYOCAMLCMI) -nostdlib -I camllib $<


# special treatment for compiling the .mli files from the extended library

camllib/NullPointers.cmi: camllib/NullPointers.mli $(CAMLLIB_CMI) $(MYOCAMLCMI)
	$(MYOCAMLCMI) -rectypes -I camllib $<
camllib/StrongPointers.cmi: camllib/StrongPointers.mli $(CAMLLIB_CMI) $(MYOCAMLCMI)
	$(MYOCAMLCMI) -rectypes -I camllib $<



############################################################################
# .byte files

tools: $(MYTOOLS)

# the makefile does not like the symbolic link generated by ocamlbuild so we copy file

%.byte: $(GENERATOR_SRC)
	@rm -f $@
	@rm -f camllib/*.cmi camllib/*.ml.d || echo ok
	$(OCAMLBUILD) -I gen $(addprefix -I ,$(GENERATOR_DIRS)) $@
	@mv $@ temp.byte 
	@cp -L temp.byte $@
	@rm temp.byte


############################################################################
# Cleanup

clean_files:  
	@rm -f *.vo *.glob *.cmo *.cmi *_ml.v || echo ok
	@rm -f imper/*_ml.v imper/*.vo imper/*.glob imper/*.cmo imper/*.cmi || echo ok
	@rm -f camllibsrc camllib/*.cmi camllib/*.d || echo ok
   
clean_deps:
	@rm -f depend *.v.d *.ml.d imper/*.ml.d imper/*.v.d || echo ok

clean_settings:
	@rm -f $(SETTINGS) || @echo ok

clean_tools:
	@rm -Rf _build || echo ok
	@rm -f *.byte || echo ok

clean: clean_deps clean_files clean_settings clean_tools
	@echo "CLEANED UP"


############################################################################
# Debugging commands

test:
	@echo $(OCAMLBUILD)
	@echo $(TLCLIB)
	@echo $(TLCLIB_SRC)
	@echo $(GENERATOR_DIRS)	
	@echo $(GENERATOR_PATTERNS)
	@echo $(GENERATOR_SRC)
	@echo $(CAMLLIB_MLI_PATH)
	@echo $(SHARED_CMI)


############################################################################
# Other tricks



# -- todo: add support for user provided mli files

# @sed -i 's/\.cmo/.cmi/g' $@
#	@sed -e 's/.*://' -e 's/\\$$//' < $@.tmp | fmt -1 | \
#	  sed -e 's/^ *//' -e 's/$$/:/' >> $@  

# .SECONDARY: %.ml.d %.v.d %.cmi %.cmo %.vo %.ml.d %.v.d %.cmi %_ml.v %_ml.v.d %_ml.vo %.byte

#gen/stdlib/pervasives.cmi: gen/stdlib/pervasives.mli $(MYOCAMLCMI)
#	$(MYOCAMLCMI) -nostdlib -nopervasives $<
#gen/stdlib/%.cmi: gen/stdlib/%.mli gen/stdlib/pervasives.cmi $(MYOCAMLCMI)
#	$(MYOCAMLCMI) -nostdlib -I gen/stdlib $<



#$(MYOCAMLDEP) $(INCLUDES) $<  > $@
#'s/\($*\)\.o[ :]*/\1/g'

#'\''s/\($*\)\.o[ :]*/\1.o $@ : /g'\'' > $@
#
#	$(MYOCAMLDEP) $(INCLUDES) $< > $@
#	@cp -f $@ $@.tmp
#	@sed -e 's/.*://' -e 's/\\$$//' < $@.tmp | fmt -1 | \
#	  sed -e 's/^ *//' -e 's/$$/:/' >> $@  
#	@rm -f $@.tmp

