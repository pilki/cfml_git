Set Implicit Arguments.
Require Import FuncTactics HeapSig_ml OrderedSig_ml OrderedSig_proof.

(** Definition of the minimum of a multiset *)

Definition min_of `{Le A} (E:multiset A) (X:A) := 
  X \in E /\ forall_ Y \in E, X <= Y.

(** Definition of the removal of the minimum from a multiset *)

Definition removed_min  `{Le A} (E E':multiset A) :=
  exists X, min_of E X /\ E = \{X} \u E'.

Hint Unfold removed_min.


(* Signature for heaps *)

Module Type HeapSigSpec.

Declare Module H : MLHeap.
Declare Module OS : OrderedSigSpec with Module O := H.MLElement.
Import H MLElement OS. 

Global Instance heap_rep : Rep heap (multiset T).
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

