#COQBIN=/home/charguer/coq/trunk/bin/
INCLUDES=-I . -I ./demo -I ./okasaki -I ./lib
# -I ocamllib 
COQC=$(COQBIN)coqc -dont-load-proofs $(INCLUDES)
COQDEP=$(COQBIN)coqdep $(INCLUDES)
COQDOC=$(COQBIN)coqdoc
OCAMLC=ocamlc $(INCLUDES)
OCAMLDEP=ocamldep $(INCLUDES)

GENERATOR=gen/main.byte 

TOOLS=\
	Shared.v \
	FuncDefs.v \
	FuncPrint.v \
	FuncPrim.v \
	FuncTactics.v

OKA=\
	okasaki/Okasaki_ml.v \
	okasaki/QueueSig_ml.v \
	okasaki/DequeSig_ml.v \
	okasaki/OrderedSig_ml.v \
	okasaki/FsetSig_ml.v \
	okasaki/HeapSig_ml.v \
	okasaki/SortableSig_ml.v \
	okasaki/BatchedQueue_ml.v \
	okasaki/BankersQueue_ml.v \
	okasaki/PhysicistsQueue_ml.v \
	okasaki/RealTimeQueue_ml.v \
	okasaki/RedBlackSet_ml.v \
	okasaki/LeftistHeap_ml.v \
	okasaki/PairingHeap_ml.v \
	okasaki/BinomialHeap_ml.v \
	okasaki/SplayHeap_ml.v \
	okasaki/RedBlackSet_ml.v \
	okasaki/UnbalancedSet_ml.v \
	okasaki/BottomUpMergeSort_ml.v \
	okasaki/QueueSig_proof.v \
	okasaki/DequeSig_proof.v \
	okasaki/OrderedSig_proof.v \
	okasaki/FsetSig_proof.v \
	okasaki/HeapSig_proof.v \
	okasaki/SortableSig_proof.v \
	okasaki/BatchedQueue_proof.v \
	okasaki/BankersQueue_proof.v \
	okasaki/PhysicistsQueue_proof.v \
	okasaki/RealTimeQueue_proof.v \
	okasaki/LeftistHeap_proof.v \
	okasaki/PairingHeap_proof.v \
	okasaki/BinomialHeap_proof.v \
	okasaki/SplayHeap_proof.v \
	okasaki/RedBlackSet_proof.v \
	okasaki/UnbalancedSet_proof.v \
	okasaki/BottomUpMergeSort_proof.v 

NEW=\
	okasaki/OrderedSig_proof.v \
	okasaki/HeapSig_proof.v \
	okasaki/LazyPairingHeap_ml.v 

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
	demo/test_ml.v \
	demo/test_proof.v 

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

ALL=$(TOOLS) $(DEMO) $(OKA) 
# $(COD) $(DEV) $(TUTO) $(FORM) $(DEV) $(OKA) $(DEV:.v=.vo)

.PHONY: all def clean cleanall dep tools tools demo oka new cod dvpt test gen lib none
.SUFFIXES: .ml _ml.v _ml.vo _proof.v _proof.vo .v .vo 
.SECONDARY: *.cmi okasaki/*.cmi demo/*.cmi
.SECONDARY: *_ml.v okasaki/*_ml.v demo/*_ml.v
.SECONDARY: *.d okasaki/*.d demo/*.d *_ml.d okasaki/*_ml.d demo/*_ml.d

def: all
all: full .camldep
full: $(ALL:.v=.vo) 
tools: $(TOOLS:.v=.vo) 
demo: $(DEMO:.v=.vo)
oka: $(OKA:.v=.vo)
new: $(NEW:.v=.vo) 
cod: $(COD:.v=.vo) 
dvpt: $(DEV:.v=.vo) 
test: $(TEST:.v=.vo)
gen: $(GENERATOR)
dep: .camldep $(ALL:.v=.d)
none:

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

$(GENERATOR): force
	make -C gen

%_ml.v: %.ml %.cmi $(GENERATOR) 
	@echo "GENERATING $<"
	@$(GENERATOR) -debug $(INCLUDES) $<

%.cmi: %.ml 
	@echo "OCAMLC $<"
	@$(OCAMLC) -c $< 

%_ml.vo: %_ml.v %_ml.d FuncPrim.vo #LibCore.vo 
	@echo "COQC $<"
	@$(COQC) $< 

%_proof.vo: %_proof.v %_ml.vo %_proof.d FuncTactics.vo #LibCore.vo 
	@echo "COQC $<"
	@$(COQC) $<

%.vo: %.v %.d #LibCore.vo
	@echo "COQC $<"
	@$(COQC) $< 

%.d: %.v
	@echo "COQDEP $<"
	@$(COQDEP) $< > $@

# how to hide unfound files?

#%_ml.d: %_ml.v
#	@$(COQDEP) $< > $@
 
.camldep: demo/*.ml okasaki/*.ml
	@echo "OCAMLDEP"
	$(OCAMLDEP) demo/*.ml okasaki/*.ml > .camldeptemp
	sed 's/.cmo/.cmi/g' .camldeptemp > .camldep
	rm .camldeptemp

.libdep: lib/*.v
	$(COQDEP) $(wildcard lib/*.v) > .libdep

include .camldep
include .libdep

COLD=clean cleanall dep new test
ifeq ($(findstring $(MAKECMDGOALS),$(COLD)),)
include $(ALL:.v=.d)
endif

ifneq ($(findstring $(MAKECMDGOALS),new),)
include $(NEW:.v=.d) 
include $(TOOLS:.v=.d)
endif

ifneq ($(findstring $(MAKECMDGOALS),test),)
include $(TEST:.v=.d) 
include $(TOOLS:.v=.d)
endif


cleancod:
	rm *_ml.v *_ml.vo
	rm demo/*_ml.v demo/*_ml.vo
	rm okasaki/*_ml.v okasaki/*_ml.vo

clean:
	@rm -f *.d *.vo *.glob *.cmo *.cmi *_ml.v || echo clean_local
	@rm -f demo/*.d demo/*_ml.v demo/*.vo demo/*.glob demo/*.cmo demo/*.cmi || echo clean_demo
	@rm -f okasaki/*.d okasaki/*_ml.v okasaki/*.vo okasaki/*.glob okasaki/*.cmo okasaki/*.cmi || echo clean_okasaki
	@rm -f .camldep || echo ok
	@echo "CLEANED UP"

cleanall: clean
	@rm -Rf gen/_build gen/main.byte || echo clean_gen
	@echo "CLEANED UP ALL"


#todo: faire passer les dossiers de camldep via une liste



