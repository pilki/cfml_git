Set Implicit Arguments.
Require Import FuncTactics LibCore.
Require Import OrderedSig_ml HeapSig_ml OrderedSig_proof HeapSig_proof.
Require Import LazyPairingHeap_ml.


Module LazyPairingHeapSpec (O:MLOrdered) (OS:OrderedSigSpec with Module O:=O)
  <: HeapSigSpec with Definition H.MLElement.t := O.t.

(** instantiations *)

Module Import H <: MLHeap := MLLazyPairingHeap O.
Module Import OS := OS.
Existing Instance le_inst.
Existing Instance le_order.

Definition min_of (E:multiset T) (X:T) := 
  X \in E /\ forall_ Y \in E, X <= Y.

Definition removed_min (E E':multiset T) :=
  exists X, min_of E X /\ E = \{X} \u E'.

(** invariant *)

Definition is_ge (X Y:T) := X <= Y.

Inductive inv : heap -> multiset T -> Prop :=
  | inv_empty : 
      inv Empty \{} 
  | inv_node : forall x X ho hs Eo Es E',
      rep x X ->
      inv ho Eo ->
      inv hs Es ->
      foreach (is_ge X) Eo ->
      foreach (is_ge X) Es ->
      E' = \{X} \u Eo \u Es ->   
      inv (Node x ho hs) E'.

Instance heap_rep : Rep heap (multiset T) := inv.

(** automation *)

Hint Extern 1 (_ < _) => simpl; math.
Hint Extern 1 (_ <= _) => simpl; math.

Hint Extern 1 (_ = _ :> multiset _) => permut_simpl : multiset.

Definition U := multiset T.

Ltac myauto cont :=
  match goal with 
  | |- _ = _ :> LibSet.set ?T => try solve [ change (multiset T) with U; cont tt ]
  | |- _ => cont tt
  end. (* todo: pour éviter un hint trop lent de hint-core avec eauto *)

Ltac auto_tilde ::= myauto ltac:(fun _ => eauto).
Ltac auto_star ::= try solve [ intuition (eauto with multiset) ].

(** useful facts *)

Hint Constructors inv Forall Forall2.
Hint Extern 1 (@rep heap _ _ _ _) => simpl.
Hint Extern 1 (@rep heaps _ _ _ _) => simpl.

Lemma foreach_ge_trans : forall (X Y : OS.T) (E : multiset OS.T),
  foreach (is_ge X) E -> Y <= X -> foreach (is_ge Y) E.
Proof. intros. apply~ foreach_weaken. intros_all. apply* le_trans. Qed.

Hint Resolve foreach_ge_trans.
Hint Unfold removed_min.

(** verification *)

Lemma empty_spec : rep empty \{}.
Proof. apply empty_cf. xret~. Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma is_empty_spec : RepTotal is_empty (E;heap) >> 
  bool_of (E = \{}).
Proof.
  xcf. intros e E RepE. inverts RepE; xgo. 
  auto. intros_all. fset_inv.
Qed. 

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Fixpoint size h :=
  match h with
  | Empty => 1%nat
  | Node a ho hs => (1 + size ho + size hs)%nat
  end.

Lemma spec_induction_mut_2_2_2 : 
  forall A11 A12 B1 A21 A22 B2 (lt:binary(A11*A12+A21*A22)),
  forall (Wf: wf lt) f1 f2 (K1:A11->A12->~~B1->Prop) (K2:A21->A22->~~B2->Prop),
  spec_2 (fun x1 x2 R => 
    spec_2 (fun y1 y2 R' => lt (inl (y1,y2)) (inl (x1,x2)) -> K1 y1 y2 R') f1 ->
    spec_2 (fun y1 y2 R' => lt (inr (y1,y2)) (inl (x1,x2)) -> K2 y1 y2 R') f2 ->
    K1 x1 x2 R) f1 ->
  spec_2 (fun x1 x2 R => 
    spec_2 (fun y1 y2 R' => lt (inl (y1,y2)) (inr (x1,x2)) -> K1 y1 y2 R') f1 ->
    spec_2 (fun y1 y2 R' => lt (inr (y1,y2)) (inr (x1,x2)) -> K2 y1 y2 R') f2 ->
    K2 x1 x2 R) f2 ->
  spec_2 K1 f1 /\ spec_2 K2 f2.
Admitted.

Definition link_spec := Spec link h1 h2 |R>>
  forall x ho hs X Eo Es E2,
  h1 = Node x ho hs ->
  rep x X ->
  inv ho Eo ->
  inv hs Es ->
  inv h2 E2 ->
  foreach (is_ge X) Eo ->
  foreach (is_ge X) Es ->
  foreach (is_ge X) E2 ->
  R (\{X} \u Eo \u Es \u E2 ; heap).

Definition sum_measure A1 A2 (mu1:A1->nat) (mu2:A2->nat) (p:A1+A2) : nat :=
  match p with 
  | inl x => mu1 x 
  | inr x => mu2 x 
  end.
  (*(sum_measure (fun h1 h2 => 2 * (size h1 + size h2)) (fun h size).*)

Definition size_pair (p:heap*heap) :=
  let (h1,h2) := p in (size h1 + size h2)%nat.


Lemma merge_spec : RepTotal merge (E1;heap) (E2;heap) >>
  E1 \u E2 ; heap.
Proof.
  applys (>>> proj1 __ link_spec).
  sets lt: (fun p1 p2 => match p1,p2 with
    | inl x, inr y => size_pair x < size_pair y
    | inr x, inl y => size_pair x <= size_pair y
    | _,_ => False end).
  eapply (spec_induction_mut_2_2_2 (lt:=lt)).
   skip.
  (* verif merge *)
  xcf. introv _ IH R1 R2. subst lt. simpl in IH. xmatch; xcleanpat.
  xgo. inverts R2. equates* 1.
  xgo. inverts R1. equates* 1.
  inverts R1. inverts R2. xapp~. xif.
    xapp~. ximpl. equates* 1.
    applys_to P_x0 nle_to_sle. xapp~. ximpl. equates* 1.
  (* verif link *)
  xcf. introv IH _ Sh1 Rx Ro Rs R2 Lo Ls L2. subst lt. simpl in IH.
  xmatch; inverts H.
  xgo. inverts Ro. constructors*. 
  xgo~. skip. constructors*. (*todo: measure the models*)
Qed.

Hint Extern 1 (RegisterSpec merge) => Provide merge_spec.

(* todo: simplify using rep_unique *)



(*-- old

Hint Extern 1 (RegisterSpec link) => Provide link_spec.

Lemma merge_spec : RepTotal merge (E1;heap) (E2;heap) >>
  E1 \u E2 ; heap.
Proof.
  xcf. introv R1 R2. xmatch; xcleanpat.
  xgo. inverts R2. equates* 1.
  xgo. inverts R1. equates* 1.
  inverts R1. inverts R2. xapp~. xif.
  xapp~. ximpl. equates* 1.
  applys_to P_x0 nle_to_sle. xapp~. ximpl. equates* 1.
Qed.

Hint Extern 1 (RegisterSpec merge) => Provide merge_spec.

Lemma link_spec : Spec link h1 h2 |R>>
  forall x ho hs X Eo Es E2,
  h1 = Node x ho hs ->
  rep x X ->
  inv ho Eo ->
  inv hs Es ->
  inv h2 E2 ->
  foreach (is_ge X) Eo ->
  foreach (is_ge X) Es ->
  foreach (is_ge X) E2 ->
  R (\{X} \u Eo \u Es \u E2 ; heap).
Proof.
  xcf. introv Sh1 Rx Ro Rs R2 Lo Ls L2.
  xmatch; inverts H.
  xgo. inverts Ro. constructors*.
  xgo~. constructors*.
Qed.

Hint Extern 1 (RegisterSpec link) => Provide link_spec.

*)

Lemma insert_spec : RepTotal insert (X;O.t) (E;heap) >>
  \{X} \u E ; heap.
Proof. xgo~. ximpl. equates* 1. Qed.

Hint Extern 1 (RegisterSpec insert) => Provide insert_spec.

Lemma min_of_prove : forall X Eo Es,
  foreach (is_ge X) Eo ->
  foreach (is_ge X) Es ->
  min_of ('{X} \u Eo \u Es) X.
Proof.
  introv Lo Ls. split~. introv M. multiset_in M.
  apply le_refl. apply~ Lo. apply~ Ls.
Qed.

Hint Resolve min_of_prove.

Lemma find_min_spec : RepSpec find_min (E;heap) |R>>
  E <> \{} -> R (min_of E ;; O.t).
Proof. xcf. intros e E RepE HasE. inverts RepE; xgo*. Qed.

Hint Extern 1 (RegisterSpec find_min) => Provide find_min_spec.

Lemma delete_min_spec : RepSpec delete_min (E;heap) |R>>
  E <> \{} -> R (removed_min E ;; heap).
Proof. 
  xcf. intros e E RepE HasE. inverts RepE; xgo~.
  unfolds. eauto 8.
Qed.

Hint Extern 1 (RegisterSpec delete_min) => Provide delete_min_spec.

End LazyPairingHeapSpec.

