Set Implicit Arguments.
Require Import CFLib Dijkstra_ml.
Open Scope comp_scope.

(*
Module Type MLOrderedPairInt :=
  MLOrdered with Definition t := (int*int)%type.
Module MLNextNode' :  MLOrdered with Definition t := (int*int)%type.
*)

(*************************************************************)


(*-----------------------------------------------------------*)

Definition Min A (f:A->int) (P:A->Prop) :=  
  epsilon (fun n => (exists x, P x /\ n = f x)
                 /\ (forall x, P x -> n <= f x)).

Definition MinBar A (f:A->int) (P:A->Prop) :=  
  If (exists x, P x) then Finite(Min f P) else Infinite.

Lemma MinBar_Infinite : forall A (f:A->int) (P:A->Prop),
  (forall x, ~ P x) -> MinBar f P = Infinite.
Proof. Admitted.

Lemma MinBar_Finite : forall A x (f:A->int) (P:A->Prop),
  P x -> (forall y, f x <= f y) ->
  MinBar f P = Finite (f x).
Proof. Admitted.

Lemma MinBar_Finite_inv : forall A n x (f:A->int) (P:A->Prop),
  MinBar f P = Finite n -> P x -> n <= f x.
Proof. Admitted.

Lemma MinBar_Infinite_inv : forall A x (f:A->int) (P:A->Prop),
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

Inductive is_path A (g:graph A) : int -> int -> path A -> Prop :=
  | is_path_nil : forall x, 
      is_path g x x nil
  | is_path_cons : forall x y z w p,
      is_path g x y p ->
      has_edge g y z w ->
      is_path g x z ((y,z,w)::p).

Definition weight (p:path int) :=
  nosimpl (fold_right (fun e acc => let '(_,_,w) := e in w+acc) 0 p).

Definition dist (g:graph int) x y :=  
  MinBar weight (is_path g x y).


Lemma weight_nil : 
  weight (nil : path int) = 0.
Proof. auto. Qed.

Lemma weight_cons : forall (p:path int) x y w, 
  weight ((x,y,w)::p) = w + weight p.
Proof. intros. unfold weight. rew_list~. Qed.

(*-----------------------------------------------------------*)

Parameter range : int -> int -> set int.

Definition GraphAdjList (G:graph int) (g:loc) :=
  Hexists N, g ~> Array Id N
         \* [nodes G = range 0 (LibArray.length N)]
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
  keep R (x ~> S X \* y ~> S Y) (\= istrue (LibOrder.le X Y)).

Hint Extern 1 (RegisterSpec le) => Provide le_spec.

End OrderedSigSpec.


(*************************************************************)

(** Definition of the minimum of a multiset *)

Definition is_min_of `{Le A} (E:multiset A) (X:A) := 
  X \in E /\ forall_ Y \in E, X <= Y.

(*************************************************************)

Module Type HeapSigSpec.

Declare Module H : MLHeapSig.
Declare Module OS : OrderedSigSpec with Module O := H.MLElement.
Import H MLElement OS. 

Parameter Heap : htype T t -> htype (multiset T) heap.

Parameter create_spec :
  Spec create () |R>> 
    R [] (~> Heap S \{}).

Parameter is_empty_spec : 
  Spec is_empty (h:heap) |R>> forall E,
    keep R (h ~> Heap S E) (\= istrue (E = \{})).

Parameter push_spec : 
  Spec push (x:t) (h:heap) |R>> forall E X,
    R (h ~> Heap S E \* x ~> S X) (# h ~> Heap S (\{X} \u E)).

Parameter pop_spec : 
  Spec pop (h:heap) |R>> forall E,
    R (h ~> Heap S E) (fun x => Hexists X F, 
      [is_min_of E X] \* [E = \{X} \u F] \* x ~> S X \* h ~> Heap S F).

End HeapSigSpec.


(*************************************************************)

Module NextNodeSpec <: OrderedSigSpec with Module O := MLNextNode.
Module O := MLNextNode.
Import O.
Definition T : Type := (int*int)%type.
Definition S : htype T t := Id.

Global Instance le_inst : Le T.
Proof.
  constructor.
  exact (fun (p1 p2 : int*int) => snd p1 <= snd p2).
Defined.
  
Global Instance le_order : Le_total_order.
Admitted. (* todo :order prod *)

Lemma le_spec : Spec le (x:t) (y:t) |R>> forall Y X, 
  keep R (x ~> S X \* y ~> S Y) (\= istrue (LibOrder.le X Y)).
Proof.
Admitted.

Hint Extern 1 (RegisterSpec le) => Provide le_spec.

End NextNodeSpec.

(*************************************************************)

Global Instance len_inhab : Inhab len.
Proof. constructor. exact Infinite. Qed.


(*************************************************************)
Require Import LibArray LibMap.

Module DijkstraSpec.
Declare Module Heap : MLHeapSig with Module MLElement := MLNextNode.
Import NextNodeSpec.

Implicit Types T : array bool.
Implicit Types B : array len.
Implicit Types H : set (int*int).
Implicit Types p : path int.

Section Invariants.
Variables (G:graph int) (s:int).

(*-----------------------------------------------------------*)

Global Instance test : BagRead int Type (array bool).
Proof. constructor. exact (fun t i => read t i = true). Defined.
Global Instance test' : BagRead int Prop (array bool).
Proof. constructor. exact (fun t i => read t i = true). Defined.

Record inv T B H reach : Prop :=
  { source_ok     : B\(s) = Finite 0;
    treated_ok    : forall v, T\(v) -> B\(v) = dist G s v;
    untreated_ok  : forall v, ~ T\(v) -> v <> s -> 
                      B\(v) = MinBar weight (reach v);
    heap_correct  : forall v d, ~ T\(v) -> v <> s -> (v,d) \in H -> 
                      exists p, reach v p /\ weight p = d;
    heap_complete : forall v p, reach v p -> 
                      exists d, (v,d) \in H /\ d <= weight p }.  

Definition enters T v p := 
  exists q y w, is_path G s y q 
             /\ has_edge G y v w
             /\ T\(y)
             /\ ~ T\(v).
  
Definition enters_via x L v p :=
  exists q w, p = (x,v,w)::q /\ is_path G s x q /\ Mem (v,w) L.

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
   \/ exists q, p = (x,y,w)::q /\ is_path G s x q.
Proof.
Admitted.

Lemma enters_step : forall L T x v p, ~ T\(x) ->
  (forall y w, Mem (y,w) L <-> (x,y,w) \in edges G) ->
  enters (T\(x:=true)) v p = (enters T v p \/ enters_via x L v p).
Proof.
Admitted.

Lemma enters_shorter : forall T v y p, 
  ~ T\(v) -> is_path G s y p ->
  exists z q, enters T z q /\ weight q <= weight p.
Proof.
Admitted.

Lemma enters_best : forall T x p,
  ~ T\(x) -> enters T x p ->
  (forall y q, enters T y q -> weight p <= weight q) ->
  dist G s x = Finite (weight p).
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
