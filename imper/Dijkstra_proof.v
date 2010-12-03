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

Lemma Min_eq : forall A x (f:A->int) (P:A->Prop),
  P x -> (forall y, P y -> f x <= f y) -> Min f P = f x.
Proof.
  intros. unfold Min.
  spec_epsilon* as y [(?&?&?) Sy]. clearbody y. subst y.
  forwards*: Sy x. forwards*: H0 x0. apply* le_antisym.
Qed.

Lemma Min_exists_nonneg : forall A (f:A->int) (P:A->Prop),
  (exists x, P x) -> 
  (forall x, P x -> f x >= 0) ->
  exists n, (exists x, P x /\ n = f x)
          /\ (forall x, P x -> n <= f x).
Proof.
(*
  introv [a Pa] Pos. 
  match goal with |- ?G' => set (G := G') end.
  cuts: (forall m:nat, G \/ (forall x, P x -> f x <= m -> False)).
    destruct (H (abs (f a))) as [?|M].
      auto.
      false~ (M a). rewrite~ abs_pos. apply le_refl.
  induction m.
  destruct (classic (exists x, P x /\ f x = 0)) as [(y&Py&Hy)|M].
    left. exists* 0.
    right. intros x Px Non. rew_classic in M. specializes M x.
     rew_classic in M. destruct M as [?|H]. false. apply H. 
      apply~ le_antisym. rewrite le_is_flip_ge. unfold flip. auto.
  destruct IHm as [?|N]. eauto. right. intros x Px Le.
    destruct (classic (exists x, P x /\ f x = m)) as [(y&Py&Hy)|M].
*)
Admitted.

Lemma Min_inv : forall A x (f:A->int) (P:A->Prop),
  (forall x, P x -> f x >= 0) ->
  P x -> 
  Min f P <= f x.
Proof.
(*
  unfold Min. introv H Px. 
  spec_epsilon as z Hz. exists (f x). 
*)
Admitted.

Lemma MinBar_Infinite : forall A (f:A->int) (P:A->Prop),
  (forall x, ~ P x) -> MinBar f P = Infinite.
Proof.
  intros. unfold MinBar. case_if~. destruct e as [x ?]. false*.
Qed.

Lemma MinBar_Finite : forall A x (f:A->int) (P:A->Prop),
  P x -> (forall y, P y -> f x <= f y) ->
  MinBar f P = Finite (f x).
Proof. 
  intros. unfold MinBar. case_if. 
  fequal. apply~ Min_eq. 
  rew_classic in n. false*.
Qed.

Lemma MinBar_Finite_inv : forall A n x (f:A->int) (P:A->Prop),
  MinBar f P = Finite n -> (forall x, P x -> f x >= 0) -> P x -> n <= f x.
Proof.
  unfold MinBar. introv H Pos Px. case_if.
  destruct e as [y ?]. invert H as M. apply~ Min_inv.
  false.
Qed.

Lemma MinBar_Infinite_inv : forall A x (f:A->int) (P:A->Prop),
  MinBar f P = Infinite -> ~ P x.
Proof. 
  unfold MinBar. introv H Px. case_if.
  false.
  rew_classic in n. false*.
Qed.

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

Parameter le_spec : Spec le (x:t) (y:t) |R>> forall X Y,  
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

Hint Extern 1 (RegisterSpec create) => Provide create_spec.
Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.
Hint Extern 1 (RegisterSpec push) => Provide push_spec.
Hint Extern 1 (RegisterSpec pop) => Provide pop_spec.
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

Lemma le_spec : Spec le (x:t) (y:t) |R>> forall X Y, 
  keep R (x ~> S X \* y ~> S Y) (\= istrue (LibOrder.le X Y)).
Proof.
  xcf. unfold S. intros x y X Y. xextract. intros. subst. xgo~.
Qed.

Hint Extern 1 (RegisterSpec le) => Provide le_spec.

End NextNodeSpec.

(*************************************************************)

Global Instance len_inhab : Inhab len.
Proof. constructor. exact Infinite. Qed.


(*************************************************************)
Require Import LibArray LibMap.

Module DijkstraSpec.
Declare Module MLHeap : MLHeapSig with Module MLElement := MLNextNode.
Import NextNodeSpec.
Module Dijkstra := MLDijkstra MLHeap.
Import Dijkstra.


Implicit Types V : array bool.
Implicit Types B : array len.
Implicit Types H : multiset (int*int).
Implicit Types p : path int.

Section Invariants.
Variables (G:graph int) (s:int).

(*-----------------------------------------------------------*)

Record inv V B H reach : Prop :=
  { source_ok     : B\(s) = Finite 0;
    treated_ok    : forall v, V\(v) = true -> B\(v) = dist G s v;
    untreated_ok  : forall v, V\(v) = false -> v <> s -> 
                      B\(v) = MinBar weight (reach v);
    heap_correct  : forall v d, V\(v) = false -> v <> s -> (v,d) \in H -> 
                      exists p, reach v p /\ weight p = d;
    heap_complete : forall v p, reach v p -> 
                      exists d, (v,d) \in H /\ d <= weight p }.  

Definition from_out V v p :=
  is_path G s v p /\ V\(v) = false.

Definition enters V v p :=
  from_out V v p /\ (exists q y w, p = (y,v,w)::q /\ V\(y) = true).

Definition enters_via x L V v p :=
  from_out V v p /\ exists q w, p = (x,v,w)::q /\ Mem (v,w) L.

Definition new_enters x L V v p :=
  enters V v p \/ enters_via x L V v p.

(*-----------------------------------------------------------*)

Hint Constructors Mem.

Hint Extern 1 (index _ _) => skip.

Axiom bool_test' : forall b,
  b = true \/ b = false.

Hint Constructors is_path.

Tactic Notation "rew_array" "~" :=
  rew_array; auto_tilde.
Tactic Notation "rew_array" "~" "in" hyp(H) :=
  rew_array in H; auto_tilde.

(*-----------------------------------------------------------*)

Lemma new_enters_grows : forall x L V v p y w,
  new_enters x L V v p -> new_enters x ((y,w)::L) V v p.
Proof. introv [H|(q&w'&?&?&M)]. left~. right. split~. exists___*. Qed.

Lemma new_enters_inv : forall x L V v p y w,
  new_enters x ((y,w)::L) V v p -> 
      new_enters x L V v p 
   \/ (from_out V v p /\ exists q, p = (x,y,w)::q).
Proof.
  introv [H|(P&(q&w'&E&M))]. left. left~.
  inverts M. right*. left; right; split*.
Qed.

Lemma from_out_update : forall x V v p, v <> x ->
  from_out (V\(x:=true)) v p = from_out V v p.
Proof. intros. unfold from_out. rew_array~. Qed.

Lemma enters_step : forall L V x v p, V\(x) = false -> v <> x ->
  (forall y w, Mem (y,w) L = has_edge G x y w) ->
  enters (V\(x:=true)) v p = new_enters x L V v p.
Proof.
  introv Vx Nvx EQ. extens. iff H. hnf in H.
  destruct H as (F&(q&y&w&E&Vy)).
   rewrite~ from_out_update in F. tests (y = x).
    right. split~. exists q w. split~. rewrite EQ. 
     lets: (proj1 F). subst p. inverts* H.
    left. rew_array~ in Vy. splits*.
  destruct H as [(F&(q&y&w&E&Vy))|(P&(q&w&E&M))];
   (split; [ rewrite~ from_out_update | ]).
     exists q y w. split~. rew_array~. intro_subst; false.
     exists q x w. split~. rew_array~.
Qed.

Lemma enters_shorter : forall V v p, 
  V\(s) = true -> nonnegative_edges G ->
  is_path G s v p -> V\(v) = false -> 
  exists z q, enters V z q /\ weight q <= weight p.
Proof.
  introv Vs NG P. set_eq s': s in P. set_eq G': G in P. 
  induction P; intros; subst. false. destruct (bool_test' (V\(y))).
    exists z ((y,z,w)::p). split. 
      split. split~.
      exists p y w. split~. apply le_refl.
    forwards~ (z'&q&E&L): IHP. exists z' q. split~.
     rewrite weight_cons. forwards: NG H. math.    
Qed.

Lemma enters_best : forall V x p,
  V\(s) = true -> nonnegative_edges G ->
  V\(x) = false -> enters V x p ->
  (forall y q, enters V y q -> weight p <= weight q) ->
  dist G s x = Finite (weight p).
Proof.
  introv Vs NG Vx E BE.
  unfold dist.
  lets ((?&_)&_): E. applys~ (@MinBar_Finite (path int)) p.
  intros p' P'. forwards~ (y&q&E'&L): enters_shorter V P'.
   forwards: BE E'. math.
Qed.

(*-----------------------------------------------------------*)

End Invariants.

Import MLHeap.

Parameter Heap : htype (multiset (int*int)) heap.

Parameter create_spec :
  Spec create () |R>> 
    R [] (~> Heap \{}).

Parameter is_empty_spec : 
  Spec is_empty (h:heap) |R>> forall E,
    keep R (h ~> Heap E) (\= istrue (E = \{})).

Parameter push_spec : 
  Spec push (x:int*int) (h:heap) |R>> forall E X,
    R (h ~> Heap E \* x ~> S X) (# h ~> Heap (\{X} \u E)).

Parameter pop_spec : 
  Spec pop (h:heap) |R>> forall E,
    R (h ~> Heap E) (fun x => Hexists X F, 
      [is_min_of E X] \* [E = \{X} \u F] \* x ~> Id X \* h ~> Heap F).

Hint Extern 1 (RegisterSpec create) => Provide create_spec.
Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.
Hint Extern 1 (RegisterSpec push) => Provide push_spec.
Hint Extern 1 (RegisterSpec pop) => Provide pop_spec.


(*-----------------------------------------------------------*)

Hint Extern 1 (index _ _) => skip.

Ltac xwhile_inv_core W I :=
  first [ eapply (@while_loop_cf_to_inv _ I W); [ try prove_wf | | ]
        | eapply (@while_loop_cf_to_inv _ I _ W ) ].

Tactic Notation "xwhile_inv" constr(W) constr(I) :=
  xwhile_pre ltac:(fun _ => xwhile_inv_core W I).

Lemma shortest_path_spec :
  Spec shortest_path g a b |R>> forall G,
    nonnegative_edges G ->
    a \in nodes G ->
    b \in nodes G ->
    keep R (g ~> GraphAdjList G) (\= dist G a b).
Proof.
  xcf. introv Pos Ds De. unfold GraphAdjList at 1. hdata_simpl.
  xextract as N NG Adj. xapps. xapps. xapps. xapps. xapps~. xapps.
  xwhile_inv (fun H:multiset(int*int) => H) (fun H:multiset(int*int) => Hexists V B,
      g ~> Array Id N \* v ~> Array Id V \* b ~> Array Id B \* h ~> Heap H \* 
      [inv G s V B H (enters G s T)]).



(*-----------------------------------------------------------*)

End DijkstraSpec. 
