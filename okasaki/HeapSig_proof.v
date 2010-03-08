Set Implicit Arguments.
Require Import FuncTactics HeapSig_ml OrderedSig_ml OrderedSig_proof.

Module Type HeapSigSpec.

Declare Module H : MLHeap.
Declare Module OS : OrderedSigSpec with Module O := H.MLElement.
Import H MLElement OS. 

Global Instance heap_rep : Rep heap (multiset T).

(* todo: where to define these in order to avoid copy-paste ? *)

Definition min_of (E:multiset T) (X:T) := 
  X \in E /\ forall_ Y \in E, X <= Y.

Definition removed_min (E E':multiset T) :=
  exists X, min_of E X /\ E = \{X} \u E'.

Parameter empty_spec : rep empty \{}.
Parameter is_empty_spec : RepTotal is_empty (E;heap) >> 
  bool_of (E = \{}).

Parameter insert_spec : RepTotal insert (X;t) (E;heap) >>
  \{X} \u E ; heap.
Parameter merge_spec : RepTotal merge (E1;heap) (E2;heap) >>
  E1 \u E2 ; heap.

Parameter find_min_spec : RepSpec find_min (E;heap) |R>>
  E <> \{} -> R (min_of E ;; t).
Parameter delete_min_spec : RepSpec delete_min (E;heap) |R>>
  E <> \{} -> R (removed_min E ;; heap).

End HeapSigSpec.

