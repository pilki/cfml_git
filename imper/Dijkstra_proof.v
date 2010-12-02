Set Implicit Arguments.
Require Import CFLib Dijkstra_ml.
Open Scope comp_scope.

(*************************************************************)


(*-----------------------------------------------------------*)

Definition Min A (f:A->int) (P:A->Prop) :=  
  epsilon (fun n => (exists x, P x /\ n = f x)
                 /\ (forall x, P x -> n <= f x)).

Definition MinBar A (f:A->int) (P:A->Prop) :=  
  If (exists x, P x) Then Finite(Min f P) Else Infinite.

Lemma MinBar_Infinite : forall A (f:A->int) P,
  (forall x, ~ P x) -> MinBar f P = Infinite.
Proof. Admitted.

Lemma MinBar_Finite : forall A x (f:A->int) P,
  P x -> (forall y, f x <= f y) ->
  MinBar f P = Finite (f x).
Proof. Admitted.

Lemma MinBar_Finite_inv : forall A n x (f:A->int) P,
  MinBar f P = Finite n -> P x -> n <= f x.
Proof. Admitted.

Lemma MinBar_Infinite_inv : forall A x (f:A->int) P,
  MinBar f P = Infinite -> ~ P x.
Proof. Admitted.

(*-----------------------------------------------------------*)

Parameter graph : Type -> Type.
Parameter nodes : forall A, graph A -> set int.
Parameter edges : forall A, graph A -> set (int*int*A).
  
Definition has_edge A (g:graph A) x y w :=
  (x,y,w) \in edges g.

Parameter edges_are_nodes : forall A (g : graph A) x y w,
  has_edge g x y w -> x \in nodes g /\ y \in nodes g.

Definition nonnegative_edges (g:graph int) :=
  forall x y w, has_edge g x y w -> w >= 0.

(*-----------------------------------------------------------*)

Definition path A := list (int*int*A).

Inductive is_path A (g:graph A) : int -> int -> Prop :=
  | is_path_nil : forall x, 
      is_path nil
  | is_path_cons : forall x y z w p,
      is_path g x y p ->
      has_edge g y z w ->
      is_path g x z ((y,z,w)::p).

Definition weight (p:path int) :=
  nosimpl (fold_left (fun e acc => let '(_,_,w) := e in w+acc) 0).

Definition dist (g:graph int) x y :=  
  MinBar weight (is_path g x y).


Lemma weight_nil : 
  weight (nil : path int) = 0.
Proof. auto. Qed.

Lemma weight_cons : forall (p:path int) x y w, 
  weight ((x,y,w)::p) = w + weight p.
Proof. unfold weight; rew_list~. Qed.

(*-----------------------------------------------------------*)

Parameter range : int -> int -> set int.

Definition GraphAdjList (G:graph int) (g:loc) :=
  Hexists N, g ~> Array Id N
         \* [nodes G = range 0 (size N)]
         \* [forall_ x \in (nodes G), forall y w, 
               Mem (y,w) (N\(x)) = has_edge G x y w].


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

Implicit Types T : array int.
Implicit Types B : array int.
Implicit Types H : set int.

Section Invariants.
Variables (G:graph int) (a:int).

(*-----------------------------------------------------------*)

Record inv T B H reach : Prop :=
  { source_ok     : B\(a) = 0;
    treated_ok    : forall v, T\(v) -> B\(v) = dist G a v;
    untreated_ok  : forall v, ~ T\(v) -> v <> a -> 
                      B\(v) = MinBar weight reach;
    heap_correct  : forall v d, ~ T\(v) -> v <> a -> (v,d) \in H -> 
                      exists p, reach v p /\ weight p = d;
    heap_complete : forall v p, reach v p -> 
                      exists d, (v,d) \in H /\ d <= weight p }.  

Definition enters T v p := 
  exists q y w, is_path G a y q 
             /\ has_edge G y v w
             /\ T\(y)
             /\ ~ T\(v).
  
Definition enters_via x L v p :=
  exists q w, p = (x,v,w)::q /\ is_path G a x q /\ Mem (v,w) L.

Definition new_enters x L T v p :=
  enters T v p \/ enters_via x L v p.

(*-----------------------------------------------------------*)

Lemma new_enters_grows : forall x L T v p y w,
  new_enters x L T v p -> new_enters x ((y,w)::L) T v p.
Proof.
Admitted.

Lemma new_enters_inv : forall x L T v p y w,
  new_enters x ((y,w)::L) T v p -> 
      new_enters x L T v p 
   \/ exists q, p = (x,y,w)::q /\ is_path G a x q.
Proof.
Admitted.

Lemma enters_step : forall T x v p, ~ T\(x) ->
  enters (T\(x:=true)) v p = (enters T v p \/ enters_via x (N\(x)) v p).
Proof.
Admitted.

Lemma enters_shorter : forall T y p, 
  ~ T\(v) -> is_path G a y p ->
  exists z q, enters T z q /\ weight q <= weight p.
Proof.
Admitted.

Lemma enters_best : forall T x p,
  ~ T\(x) -> enters T x p ->
  (forall y q, enters T y q -> weight p <= weight q) ->
  dist G a x = Fin (weight p).
Proof.
Admitted.


(*-----------------------------------------------------------*)

End Invariants.

Lemma dijkstra_spec :
  Spec dijkstra g a b |R>> forall G,
    nonnegative_weights G ->
    a \in nodes G ->
    b \in nodes G ->
    keep R (g ~> GraphAdjList G) (\= dist G a b).
Proof.
Qed.


(*-----------------------------------------------------------*)

End DijkstraSpec. 
