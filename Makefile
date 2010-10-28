#COQBIN=/home/charguer/coq/trunk/bin/
INCLUDES=-I . -I ./demo -I ./okasaki -I ./lib -I ./imper
# -I ocamllib 
COQC=$(COQBIN)coqc -dont-load-proofs $(INCLUDES)
COQDEP=$(COQBIN)coqdep $(INCLUDES)
COQDOC=$(COQBIN)coqdoc
OCAMLC=ocamlc $(INCLUDES)
OCAMLDEP=ocamldep $(INCLUDES)
MYOCAMLDEP=gen/myocamldep.byte 
GENERATOR=gen/main.byte

TOOLS=\
	Shared.v \
	FuncDefs.v \
	FuncPrint.v \
	FuncPrim.v \
	FuncTactics.v

OKACOD=\
	okasaki/Okasaki_ml.v \
	okasaki/QueueSig_ml.v \
	okasaki/DequeSig_ml.v \
	okasaki/OrderedSig_ml.v \
	okasaki/FsetSig_ml.v \
	okasaki/HeapSig_ml.v \
	okasaki/SortableSig_ml.v \
	okasaki/RandomAccessListSig_ml.v \
	okasaki/CatenableListSig_ml.v \
	okasaki/BatchedQueue_ml.v \
	okasaki/BankersQueue_ml.v \
	okasaki/PhysicistsQueue_ml.v \
	okasaki/RealTimeQueue_ml.v \
	okasaki/ImplicitQueue_ml.v \
	okasaki/BootstrappedQueue_ml.v \
	okasaki/HoodMelvilleQueue_ml.v \
	okasaki/BankersDeque_ml.v \
	okasaki/RedBlackSet_ml.v \
	okasaki/LeftistHeap_ml.v \
	okasaki/PairingHeap_ml.v \
	okasaki/LazyPairingHeap_ml.v \
	okasaki/BinomialHeap_ml.v \
	okasaki/SplayHeap_ml.v \
	okasaki/RedBlackSet_ml.v \
	okasaki/UnbalancedSet_ml.v \
	okasaki/BottomUpMergeSort_ml.v \
	okasaki/BinaryRandomAccessList_ml.v \
	okasaki/AltBinaryRandomAccessList_ml.v \
	okasaki/QueueBisSig_ml.v \
	okasaki/CatenableListImpl_ml.v \
	okasaki/Okasaki_ml.v 

OKAS=\
	okasaki/QueueSig_proof.v \
	okasaki/DequeSig_proof.v \
	okasaki/OrderedSig_proof.v \
	okasaki/FsetSig_proof.v \
	okasaki/HeapSig_proof.v \
	okasaki/SortableSig_proof.v \
	okasaki/RandomAccessListSig_proof.v \
	okasaki/QueueBisSig_proof.v \
	okasaki/CatenableListSig_proof.v 

OKAQ=\
	okasaki/BatchedQueue_proof.v \
	okasaki/BankersQueue_proof.v \
	okasaki/PhysicistsQueue_proof.v \
	okasaki/RealTimeQueue_proof.v \
	okasaki/ImplicitQueue_proof.v \
	okasaki/BootstrappedQueue_proof.v \
	okasaki/HoodMelvilleQueue_proof.v \
	okasaki/BankersDeque_proof.v 

OKAH=\
	okasaki/LeftistHeap_proof.v \
	okasaki/PairingHeap_proof.v \
	okasaki/LazyPairingHeap_proof.v \
	okasaki/SplayHeap_proof.v \
	okasaki/BinomialHeap_proof.v 

OKAO=\
	okasaki/UnbalancedSet_proof.v \
	okasaki/RedBlackSet_proof.v \
	okasaki/BottomUpMergeSort_proof.v \
	okasaki/CatenableListImpl_proof.v \
	okasaki/BinaryRandomAccessList_proof.v \
	okasaki/AltBinaryRandomAccessList_proof.v 

OKA=$(OKAS) $(OKAQ) $(OKAH) $(OKAO)

#	imper/MyLib.cmi \

#imper/MyLib_ml.vo/:imper/MyLib_ml.v
#	$(COQC) imper/MyLib_ml.v

#	imper/LambdaByte_ml.v \
#	imper/LambdaByte_proof.v \

VAC=\
	vacid/sparse_array_ml.v \
	vacid/sparse_array_proof.v 

NEW=\
	imper/MutableList_ml.v \
	imper/Facto_ml.v \
	imper/Counter_ml.v \
	imper/Facto_proof.v \
	imper/MutableList_proof.v \
	imper/Counter_proof.v \

IMP=\
	CFHeaps.v \
	CFSpec.v \
	CFPrint.v \
	CFTactics.v \
	CFPrim.v \
	CFLib.v 

IMPER=\
	imper/Landin_ml.v \
	imper/Landin_proof.v \
	imper/TreeCopy_ml.v \
	imper/Loops_ml.v \
	imper/StrongUpdate_ml.v \
	imper/InOut_ml.v \
	imper/Facto_proof.v \
	imper/TreeCopy_proof.v \
	imper/Loops_proof.v \
	imper/StrongUpdate_proof.v \
	imper/InOut_proof.v \
	imper/Dijkstra_ml.v \
	imper/Dijkstra_proof.v  \
	imper/CPS_ml.v \
	imper/CPS_proof.v \
	demo/test_ml.v \
	demo/test_proof.v \
	imper/ListIterators_ml.v \
	imper/ListIterators_proof.v \
	imper/LambdaEval_ml.v \
	imper/LambdaEval_proof.v \
	imper/Compose_ml.v \
	imper/Compose_proof.v \
	imper/Swap_ml.v \
	imper/Swap_proof.v \
	imper/TreeCopy_ml.v \
	imper/TreeCopy_proof.v 

#	okasaki/Okasaki_ml.v

# 	
#	okasaki/BinaryRandomAccessList_ml.v \

#okasaki/PhysicistsQueue_ml.v 


# 	okasaki/Stream_ml.v \
#	okasaki/StreamSig_ml.v \
#	okasaki/StreamSig_proof.v 
#	okasaki/list_skew_binary_ml.v \
#	okasaki/list_skew_binary_proof.v 

DEMO=\
	demo/half_ml.v \
	demo/half_proof.v \
	demo/demo_ml.v \
	demo/demo_proof.v \
#	demo/test_ml.v \
#	demo/test_proof.v 

#	okasaki/queue_realtime_ml.v \
#	okasaki/queue_batch_ml.v \
#	demo/map_ml.v \
#	demo/map_proof.v 
# 	okasaki/queue.v \
#	okasaki/queue_realtime_proof.v \
#	okasaki/queue_hood_melville_proof.v \
#	okasaki/queue_batch_proof.v 

TEST=\
	demo/test_ml.v \
	demo/test_proof.v 


BUILTIN=\
	imper/NullPointers.cmi \
	imper/StrongPointers.cmi


ALL=$(IMP) $(TEST) $(VAC)
OLD=$(TOOLS) $(DEMO) $(OKA) $(OKACOD)
# $(COD) $(DEV) $(TUTO) $(FORM) $(DEV) $(OKA) $(DEV:.v=.vo)

.PHONY: all def clean cleanall dep tools tools demo oka vac new cod dvpt test gen lib none
.SUFFIXES: .camldep .ml _ml.v _ml.vo _proof.v _proof.vo .v .vo 
.SECONDARY: *.cmi okasaki/*.cmi demo/*.cmi imper/*.cmi vacid/*.cmi
.SECONDARY: *_ml.v okasaki/*_ml.v demo/*_ml.v imper/*_ml.v vacid/*_ml.v
.SECONDARY: *_ml.vo okasaki/*_ml.vo demo/*_ml.vo imper/*_ml.vo vacid/*_ml.vo
.SECONDARY: *.d okasaki/*.d demo/*.d imper/*.d vacid/*.d

def: all
all: gen full .camldep 
full: $(ALL:.v=.vo) 
tools: $(TOOLS:.v=.vo) 
demo: $(DEMO:.v=.vo)
vac: $(VAC:.v=.vo)
imp: $(IMP:.v=.vo)
imper: $(IMPER:.v=.vo)
builtin: $(BUILTIN)

oka: $(OKA:.v=.vo) $(OKACOD:.v=.vo)
okac: $(OKACOD:.v=.vo)
okaq: $(OKAQ:.v=.vo)
okao: $(OKAO:.v=.vo)
okah: $(OKAH:.v=.vo)
okas: $(OKAS:.v=.vo)

new: $(NEW:.v=.vo) 
cod: $(OKACOD:.v=.vo) 
dvpt: $(DEV:.v=.vo) 
test: $(TEST:.v=.vo) 
gen: 
	make -C gen
dep: .camldep $(ALL:.v=.d) 
none:

editq:
	coqide -I lib $(OKAQ) &
edito:
	coqide -I lib $(OKAO) &
edith:
	coqide -I lib $(OKAH) &
edits:
	coqide -I lib $(OKAS) &
editi:
	coqide -I lib $(IMP) &


stats:
	@php -f stats.php $(OKAQ) $(OKAH) $(OKAO) > stats.txt
	@echo "STAT COMPUTED"
#$(OKAS)

statstime:
	@php -f stats.php time $(OKAQ) $(OKAH) $(OKAO) > stats.txt
	@echo "STAT COMPUTED"

CAMLFILES=$(wildcard okasaki/*.ml)
statsml:
	@php -f stats.php $(CAMLFILES:.ml=_proof.v)

libcompile:
	make lib -C lib

#cp lib/*.vo .

lib: libcompile
# force

force: ;

#LibCore.vo: lib/LibCore.v
#	make lib -C lib
#	cp lib/*.vo .
#does not depend on all

#during dvpt only: force
$(GENERATOR): 
	make -C gen

$(MYOCAMLDEP): 
	make -C gen 


imper/StrongPointers.cmi: imper/StrongPointers.mli
	$(OCAMLC) $<
imper/NullPointers.cmi: imper/NullPointers.mli
	$(OCAMLC) $<
#TODO	$(GENERATOR) -rectypes -onlycmi imper/MyLib.mli


%_ml.v: %.ml %.cmi $(GENERATOR) $(BUILTIN)
	@echo "GENERATING $@"
	@$(GENERATOR) -rectypes $(INCLUDES) $<
# -debug

%.cmi: %.ml $(BUILTIN)
	@echo "MAKING CMI: $@"
	@$(GENERATOR) -rectypes -onlycmi $(INCLUDES) $<

%_ml.vo: %_ml.v %_ml.d CFPrim.vo
	@echo "COQC $<"
	@$(COQC) $< 

%_proof.vo: %_proof.v %_ml.vo %_proof.d CFLib.vo
	@echo "COQC $<"
	@$(COQC) $<

%.vo: %.v %.d 
	@echo "COQC $<"
	@$(COQC) $< 

%.d: %.v
	@echo "COQDEP $<"
	@$(COQDEP) $< > $@

# how to hide unfound files?

#%_ml.d: %_ml.v
#	@$(COQDEP) $< > $@
 
.camldep: demo/*.ml okasaki/*.ml $(MYOCAMLDEP) 
	@echo "OCAMLDEP"
	$(MYOCAMLDEP) $(INCLUDES) demo/*.ml okasaki/*.ml vacid/*.ml > .camldeptemp
	sed 's/.cmo/.cmi/g' .camldeptemp > .camldep
	rm .camldeptemp

.libdep: lib/*.v
	$(COQDEP) $(wildcard lib/*.v) > .libdep

	
include .camldep
#include .libdep

ifeq ($(findstring $(MAKECMDGOALS),stats imp clean gen dep .camldep),)
include .camldep
include .libdep
endif

COLD=clean cleanall dep new test gen stats .camldep 
ifeq ($(findstring $(MAKECMDGOALS),$(COLD)),)
include $(ALL:.v=.d)
endif

ifneq ($(findstring $(MAKECMDGOALS),new),)
include $(ALL:.v=.d)  $(NEW:.v=.d)
#include
#include $(TOOLS:.v=.d)
endif

ifneq ($(findstring $(MAKECMDGOALS),test),)
include $(TEST:.v=.d) 
endif

include $(TOOLS:.v=.d)

cleancod:
	rm *_ml.v *_ml.vo
	rm demo/*_ml.v demo/*_ml.vo
	rm okasaki/*_ml.v okasaki/*_ml.vo

clean:
	@rm -f *.d *.vo *.glob *.cmo *.cmi *_ml.v || echo clean_local
	@rm -f demo/*.d demo/*_ml.v demo/*.vo demo/*.glob demo/*.cmo demo/*.cmi || echo clean_demo
	@rm -f okasaki/*.d okasaki/*_ml.v okasaki/*.vo okasaki/*.glob okasaki/*.cmo okasaki/*.cmi || echo clean_okasaki
	@rm -f imper/*.d imper/*_ml.v imper/*.vo imper/*.glob imper/*.cmo imper/*.cmi || echo clean_imper
	@rm -f .camldep || echo ok
	@echo "CLEANED UP"
# todo: add vacid

cleanall: clean
	@rm -Rf gen/_build gen/main.byte || echo clean_gen
	@echo "CLEANED UP ALL"


#todo: faire passer les dossiers de camldep via une liste



