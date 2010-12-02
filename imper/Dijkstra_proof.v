Set Implicit Arguments.
Require Import CFLib Dijkstra_ml.
Open Scope comp_scope.


(*************************************************************)

Module Type OrderedSigSpec.

Declare Module O : MLOrdered.
Import O.
Parameter T : Type.
Parameter S : htype T t.

Global Instance le_inst : Le T.
Global Instance le_order : Le_total_order.

Parameter le_spec : Spec le (x:t) (y:t) |R>> forall Y X, 
  keep R (x ~> S X \* y ~> S Y) (\= isTrue (LibOrder.le X Y)).

Hint Extern 1 (RegisterSpec le) => Provide le_spec.

End OrderedSigSpec.


(*************************************************************)

(** Definition of the minimum of a multiset *)

Definition is_min_of `{Le A} (E:multiset A) (X:A) := 
  X \in E /\ forall_ Y \in E, X <= Y.

(*************************************************************)

Module Type HeapSigSpec.

Declare Module H : MLHeap.
Declare Module OS : OrderedSigSpec with Module O := H.MLElement.
Import H MLElement OS. 

Parameter Heap : htype (multiset T) heap.

Parameter create_spec :
  Spec create () |R>> 
    R [] (~> Heap S \{}).

Parameter is_empty_spec : 
  Spec is_empty (h:heap) |R>> forall E,
    keep R (h ~> Heap S E) (\= isTrue (E = \{})).

Parameter push_spec : 
  Spec push (x:t) (h:heap) |R>> forall E X,
    R (h ~> Heap S E \* x ~> S X) (# h ~> Heap (\{X} \u E)).

Parameter pop_spec : 
  Spec pop (h:heap) |R>> forall E,
    R (h ~> Heap S E) (fun x => Hexists X F, 
      [is_min_of E X] \* [E = \{X} \u F] \* x ~> S X \* h ~> Heap F).

End HeapSigSpec.


(*************************************************************)

Module NextNodeSpec :> OrderedSigSpec with Module O := NextNode.
Module O := NextNode.
Import O.
Definition T : Type := int*int.
Definition S : htype T t := Id.

Global Instance le_inst : Le T.
  exists (fun p1 p2 => snd p1 <= snd p2).
Defined.
  
Global Instance le_order : Le_total_order.
Admitted.

Lemma le_spec : Spec le (x:t) (y:t) |R>> forall Y X, 
  keep R (x ~> S X \* y ~> S Y) (\= isTrue (LibOrder.le X Y)).
Proof.
Qed.

Hint Extern 1 (RegisterSpec le) => Provide le_spec.

End NextNodeSpec.

(*************************************************************)

Module DijkstraSpec.
Declare Module Heap : MLHeapSig with module MLElement = MLNextNode.
Import NextNodeSpec.

(*-----------------------------------------------------------*)







(*-----------------------------------------------------------*)

End DijkstraSpec. 
