############################################################################
# ===========
# Basic usage
# ===========
#
# -> make init
#       to generate the local_settings.sh file
#       and copy the files from Caml standard library
#
# -> make depend 
#       to generate all the dependency files
#
# -> make
#	     to generate all files
#
# -> make imper/Demo_proof.vo
#       to compile one development
#
# -> make imper/Demo_ml.v
#       to test the generator on one development
#
# -> make clean 
#       to remove generated files
#
# -> make clean_all 
#       to also remove the local settings file 
#       and to reset the Caml library files
#
############################################################################
# =============================
# Organization and dependencies
# =============================
#
# /gen      contains the source code for the generator
# /imper    contains the developments 
# /*.v      contains the CFML library 
# /camllib  contains the mli file for the Caml standard library
#
# The dependencies used by the Makefile are the following:
# - the generator depends on all its source code
# - the *_ml.v files depend on the generator and on the camllib/*.cmi files
# - the *_ml.v files depend on *.ml files
# - the CFML library depends on its source scripts and on the TLC library
# - the *_ml.vo files depend on *_ml.vo and on the CFML library
# - the *_proof.vo files depend on the _proof.v files and on the *_ml.vo files 
#
# Note that if the file A.ml depends on B.ml, then the generation of A_ml.v
# requires the existence of B.cmi and the generation of A_ml.vo requires the
# existence of B_ml.vo.
#
############################################################################
# ==============
# Local settings
# ==============
#
# The file local_settings.sh is used to specify the following directories:
# - COQBIN: the location of the Coq binaries (Coq version v8.3pl2)
# - OCAMLBIN: the location of the OCaml binaries
# - TLCLIB: the location of the TLC Coq library
#
# The file "local_settings.sh" can be created by calling "make settings".
# The default parameters used are those contained in the file "template_settings.sh".
# If you call "make settings" again, the file "local_settings.sh" will not
# be overwritten. Moreover, "make clean" does not remove this file.
#
############################################################################


############################################################################
############################################################################
# Sanity checks: make sure that 'settings' and 'depend' have already been run 

# Settings files

LOCAL_SETTINGS=local_settings.sh
TEMPLATE_SETTINGS=template_settings.sh

# Commands

CLEANCMD=clean clean_all clean_init clean_tools clean_deps
DEPENDFIRST=
INITFIRST=

# Generate an error if 'local_settings.sh' does not exist 
# and target is not 'init' nor 'settings' or 'clean*'
# If 'local_settings.sh' exists, include its content

ifeq ($(findstring $(LOCAL_SETTINGS), $(wildcard *.sh)), $(LOCAL_SETTINGS))
include $(LOCAL_SETTINGS)
else
ifeq ($(findstring $(MAKECMDGOALS),init settings $(CLEANCMD)),)
INITFIRST=initfirst
endif
endif

# Generate an error if there is the 'camllib/*.mli' files do not seem 
# to be present and the target is not 'camllibsrc' or 'init' or 'clean*'

ifeq ($(findstring camllib/pervasives.mli, $(wildcard camllib/*.mli)),)
ifeq ($(findstring $(MAKECMDGOALS),init camllibsrc $(CLEANCMD)),)
INITFIRST=initfirst
endif
endif

# Generate an error if there is no 'depend' file and the target 
# is not 'depend' nor 'init' nor 'settings' nor 'camllibsrc' or 'clean*'
# (provided the error INITFIRST has not yet been triggered)

ifeq ($(INITFIRST),)
ifeq ($(findstring depend, $(wildcard depend)),)
ifeq ($(findstring $(MAKECMDGOALS),depend init settings camllibsrc $(CLEANCMD)),)
DEPENDFIRST=dependfirst
endif
endif
endif


############################################################################
############################################################################
# Filenames

# Developments

IMPER=\
	imper/Demo \
	imper/Compose \
	imper/Swap \
	imper/MutableList \
	imper/Counter \
	imper/Dijkstra \
	imper/UnionFind 

# Developments that do not compile currently

MORE=\
	imper/SparseArray \
	imper/Landin \
	imper/Facto \
	imper/FunctionalList \
	imper/InOut \
	imper/StrongUpdate \
	imper/TreeCopy \
	imper/LambdaEval \
	imper/Loops 

# Source scripts of the CFML library

CFLIB=\
	CFHeaps \
	CFSpec \
	CFPrint \
	CFTactics \
	CFPrim \
	CFLib 

# Generator tools

GENERATOR=./main.byte
MYOCAMLCMI=./makecmi.byte 
MYOCAMLDEP=./myocamldep.byte 

# External tools

COQC=$(COQBIN)coqc -dont-load-proofs 
COQDEP=$(COQBIN)coqdep 
COQDOC=$(COQBIN)coqdoc
OCAMLBUILD=$(OCAMLBIN)ocamlbuild
OCAMLDEPWRAPPER=ocamldep.wrapper
GOSCRIPT=go.sh

# Include path (add "-I $(TLCLIB)" only if $(TLCLIB) is not empty)

ifeq ($(TLCLIB),)
TLCLIB_INCLUDE=
else
TLCLIB_INCLUDE=-I $(TLCLIB) 
endif

INCLUDES=-I . -I camllib -I ./imper $(TLCLIB_INCLUDE)


############################################################################
############################################################################
# Static and dynamic dependencies

# Dependencies on the TLC library

TLCLIB_SRC=$(wildcard $(TLCLIB)*.v)

# Dependencies on the source code of the generator

CAML_FILES_IN=$(addprefix $(1)/,*.ml *.mli *.mll *.mly)
MAP=$(foreach a,$(2),$(call $(1),$(a)))
GENERATOR_SUBDIRS=lex parsing typing tools utils
GENERATOR_DIRS=gen $(addprefix gen/,$(GENERATOR_SUBDIRS))
GENERATOR_PATTERNS=$(call MAP, CAML_FILES_IN, $(GENERATOR_DIRS))
GENERATOR_SRC=$(wildcard $(GENERATOR_PATTERNS))

# Dependencies on the executables of the generator

MYTOOLS=$(GENERATOR) $(MYOCAMLCMI) $(MYOCAMLDEP)

# Dependencies on the source code of the (extended) standard Caml library

CAMLLIB_MLI_PATH=$(filter-out gen/stdlib/camlinternal% %genlex.mli %moreLabels.mli %oo.mli, $(wildcard gen/stdlib/*.mli))
CAMLLIB_MLI=$(patsubst gen/stdlib/%,%,$(CAMLLIB_MLI_PATH))
CAMLLIB_CMI=$(addprefix camllib/,$(CAMLLIB_MLI:.mli=.cmi))
SPECIAL_INTERFACES=\
	camllib/NullPointers \
	camllib/StrongPointers
SHARED_CMI=$(CAMLLIB_CMI) $(SPECIAL_INTERFACES:=.cmi)

# List of all dynamic dependency files

DEPENDENCIES=$(IMPER:=.ml.d) $(IMPER:=_ml.v.d) $(IMPER:=_proof.v.d) $(CFLIB:=.v.d)


############################################################################
############################################################################
# Targets and intermediate targets

# Declare the complete list of special targets

.PHONY: all dependfirst initfirst depend settings tools cflib camllib camllibsrc cf imper clean clean_files clean_tools clean_deps clean_init clean_all test 

# Declare the file extensions and declare intermediate files as precious

.SUFFIXES: .cmi .cmo .byte .ml .ml.d .v .v.d .vo _ml.v _ml.v.d _ml.vo _proof.v _proof.vo  
.INTERMEDIATE: %.cmi %.cmo %.byte %.ml.d %.v.d %.vo %_ml.v %_ml.v.d %_ml.vo %_proof.vo
.PRECIOUS: %.cmi %.cmo %.byte %.ml.d %.v.d %.vo %_ml.v %_ml.v.d %_ml.vo %_proof.vo


############################################################################
############################################################################
# Execution of "make all"

all: $(INITFIRST) $(DEPENDFIRST) tools tlclib cf cflib imper

initfirst:
	@echo you need to first call make init
	@exit 1

dependfirst:
	@echo you need to first call make depend 
	@exit 1


############################################################################
############################################################################
# Initialization: creation of local settings and copy of Caml standard library

init: settings camllibsrc
	@chmod +x $(OCAMLDEPWRAPPER)
	@chmod +x $(GOSCRIPT)
	@echo initialization successful

settings: 
	@if [ -f $(LOCAL_SETTINGS) ]; then \
		echo $(LOCAL_SETTINGS) already exists; \
	else \
		echo creating a default $(LOCAL_SETTINGS) file; \
		cp $(TEMPLATE_SETTINGS) $(LOCAL_SETTINGS); \
	fi

camllibsrc: 
	@$(foreach file, $(CAMLLIB_MLI), cp gen/stdlib/$(file) camllib/; )
	@echo camllib source files successfully copied 


############################################################################
############################################################################
# DETAILED TARGETS


# Compilation of the TLC library

tlclib: $(TLCLIB_SRC)
	make -C $(TLCLIB) lib
	touch $@

# Compilation of the characteristic formula generator

tools: $(MYTOOLS)

# Compilation of the standard Caml library

camllib: $(SHARED_CMI)

# Generation of all the characteristic formulae files

cf: $(IMPER:=_ml.v)

# Compilation of the CFML library

cflib: $(CFLIB:=.vo)

# Compilation of all the proofs

imper: $(IMPER:=_proof.vo)

# Generation of all the dependency files (includes the generation of _ml.v files)

depend: $(DEPENDENCIES)
	@touch depend
	@echo dependency computation successful


############################################################################
############################################################################
# Computation of dependencies

# The rules for generating %.d files are only included when the goal is 'depend'

ifeq ($(findstring $(MAKECMDGOALS),depend),depend)


# To generate the *.ml.d files, we add $(LOCAL_SETTINGS) as dummy target 
# to avoid having a *.cmo file that depends on no other file
# (TODO: should use a better 'sed' command to instead add the ml file as dependency,
# but the difficulty is to escape the slashes that appear in the filename $<)

imper/%.ml.d: imper/%.ml $(MYOCAMLDEP) 
	@echo $(MYOCAMLDEP) $(INCLUDES) $<
	@$(MYOCAMLDEP) $(INCLUDES) $< | sed 's/:/: $(LOCAL_SETTINGS)/' > $@

# To generate *.v.d, we use the ocaml-wrapper trick to 
# force dependencies to mention files that do not exist yet

FORCED_VFILES=$(IMPER:=_ml.v)

%.v.d: %.v 
	@echo $(COQDEP) $(INCLUDES) $< > $@
	@./$(OCAMLDEPWRAPPER) $(FORCED_VFILES) - $(COQDEP) $(INCLUDES) $< > $@


endif



############################################################################
############################################################################
# Include of dependency files

# Ocamldep generates dependencies between .cmo files, so we need the following:

%.cmo: %.cmi
	@touch $@

# We include all dependencies, unless the target is 'init*' or 'depend' or 'clean*'

ifeq ($(findstring $(MAKECMDGOALS),depend init settings camllibsrc $(CLEANCMD)),)
-include $(DEPENDENCIES)
endif

# When target is 'depend', we include only the .ml.d dependencies 
 
ifeq ($(findstring $(MAKECMDGOALS),depend),depend)
-include $(IMPER:=.ml.d)
endif



############################################################################
############################################################################
# Compilation 


# Construction of the generator programs
# (the Makefile does not handle well the the fact that ocamlbuild 
#  generaters symbolic links, so we need to move the binary file)

%.byte: $(GENERATOR_SRC)
	@rm -f $@
	$(OCAMLBUILD) -I gen $(addprefix -I ,$(GENERATOR_DIRS)) $@
	@mv $@ temp.byte 
	@cp -L temp.byte $@
	@rm temp.byte


# Compilation of a Coq file

%.vo: %.v
	$(COQC) $(INCLUDES) $< 


# Generation of a characteristic formula file;
# it requires the %.cmo, hence the %.cmi as well as the 
# *.cmi files corresponding to the *.ml imported files

%_ml.v: %.ml %.cmo $(GENERATOR) $(SHARED_CMI)  
	$(GENERATOR) -rectypes $(INCLUDES) $<


# Generation of a %.cmi file (could also use MYOCAMLCMI)

imper/%.cmi: imper/%.ml $(GENERATOR) $(SHARED_CMI)
	$(GENERATOR) -onlycmi -rectypes $(INCLUDES) $<


# Compilation of the .mli files from the Caml standard library

camllib/pervasives.cmi: camllib/pervasives.mli $(MYOCAMLCMI)
	$(MYOCAMLCMI) -nostdlib -nopervasives $<
camllib/%.cmi: camllib/%.mli camllib/pervasives.cmi $(MYOCAMLCMI)
	$(MYOCAMLCMI) -nostdlib -I camllib $<


# Compiling of the .mli files extending the Caml standard library

camllib/NullPointers.cmi: camllib/NullPointers.mli $(CAMLLIB_CMI) $(MYOCAMLCMI)
	$(MYOCAMLCMI) -rectypes -I camllib $<
camllib/StrongPointers.cmi: camllib/StrongPointers.mli $(CAMLLIB_CMI) $(MYOCAMLCMI)
	$(MYOCAMLCMI) -rectypes -I camllib $<


############################################################################
############################################################################
# Cleaning

clean_files:  
	@rm -f *.vo *.glob *.cmo *.cmi *_ml.v || echo ok
	@rm -f imper/*_ml.v imper/*.vo imper/*.glob imper/*.cmo imper/*.cmi || echo ok
	@rm -f camllib/*.cmi camllib/*.d || echo ok
   
clean_deps:
	@rm -f depend *.v.d *.ml.d imper/*.ml.d imper/*.v.d || echo ok

clean_tools:
	@rm -Rf _build || echo ok
	@rm -f *.byte || echo ok

clean: clean_deps clean_files clean_tools
	@echo "CLEANED UP"

clean_init:
	@rm -f $(LOCAL_SETTINGS) || @echo ok
	@$(foreach file, $(CAMLLIB_MLI), rm camllib/$(file); )

clean_all: clean clean_init


############################################################################
############################################################################
# Debugging 

test:
	@echo $(TLCLIB_INCLUDE)
	@echo $(OCAMLBUILD)
	@echo $(TLCLIB)
	@echo $(TLCLIB_SRC)
	@echo $(GENERATOR_DIRS)	
	@echo $(GENERATOR_PATTERNS)
	@echo $(GENERATOR_SRC)
	@echo $(CAMLLIB_MLI_PATH)
	@echo $(SHARED_CMI)


############################################################################
############################################################################
# TODO 

# compute dependencies between the /gen/stdlib/*.mli files 
# to avoid the filter-out 

# use myocamlcmi instead to generate imper/%.cmi files

# integrate shadow compilation of .vo files

# integrate parallel make

# have go.sh include local_settings.sh

# use immediate errors instead of INITFIRST= and DEPENDFIRST=

# have MYTOOLS be compiled in a single execution of ocamlbuild

# why demo_ml.v is always rebuilt?

# why imper/*.cmi files are deleted?

# target 'tlclib': if I do not 'touch' a file with this name but place 'tlclib' in the phony then strangely the goal is never up to date