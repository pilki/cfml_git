Set Implicit Arguments.
Require Import FuncTactics LibCore.
Require Import OrderedSig_ml HeapSig_ml OrderedSig_proof HeapSig_proof.
Require Import LazyPairingHeap_ml.


Instance union_inst : forall A, BagCard (multiset A).
Admitted.

Class Card_empty `{BagEmpty T, BagCard T} :=
  { card_empty : card \{} = 0%nat }.
Class Card_single `{BagSingle A T, BagCard T} :=
  { card_single : forall X, card \{X} = 1%nat }.
Class Card_union `{BagUnion T, BagCard T} :=
  { card_union : forall E F, card (E \u F) = (card E + card F)%nat }.

Instance card_empty_inst : forall A, Card_empty (T:=multiset A).
Admitted.
Instance card_single_inst : forall A, Card_single (T:=multiset A).
Admitted.
Instance card_union_inst : forall A, Card_union (T:=multiset A).
Admitted.


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

Definition rep_spec_2 (a1 a2 A1 A2 B : Type)
  (rep1:a1->A1->Prop) (rep2:a2->A2->Prop)
  (RK:a1->a2->A1->A2->~~B->Prop) f :=
  spec_2 (B:=B) (fun x1 x2 R => forall X1 X2, 
    rep1 x1 X1 -> rep2 x2 X2 -> RK x1 x2 X1 X2 R) f.

Definition rep_spec_2_hyp (a1 a2 A1 A2 B : Type)
  (rep1:a1->A1->Prop) (rep2:a2->A2->Prop) (P:A1->A2->Prop)
  (RK:a1->a2->A1->A2->~~B->Prop) f :=
  spec_2 (B:=B) (fun x1 x2 R => forall X1 X2, 
    rep1 x1 X1 -> rep2 x2 X2 -> P X1 X2 -> RK x1 x2 X1 X2 R) f.


(*
Lemma testing: 
  forall a A B (P:a->A->Prop) (K:a->A->~~B->Prop) (f:val),
  True ->
  spec_1 (fun x R => forall X, P x X -> K x X R) f.
Admitted.
*)

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

(*
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
*)

(*
Definition link_spec := Spec link h1 h2 |R>>
  forall E1 E2,
  inv h1 E1 ->
  inv h2 E2 ->
  forall x ho hs X Eo Es,
  h1 = Node x ho hs ->
  rep x X ->
  inv ho Eo ->
  inv hs Es ->
  foreach (is_ge X) Eo ->
  foreach (is_ge X) Es ->
  foreach (is_ge X) E2 ->
  R (\{X} \u Eo \u Es \u E2 ; heap).
*)
(*
Definition link_spec := RepSpec link (E1;heap) (E2;heap) |R>>
  forall x h1 ho hs X Eo Es,
  rep x X ->
  inv ho Eo ->
  inv hs Es ->
  h1 = Node x ho hs ->
  foreach (is_ge X) Eo ->
  foreach (is_ge X) Es ->
  foreach (is_ge X) E2 ->
  R (\{X} \u Eo \u Es \u E2 ; heap).
*)

(*
Definition is_rep_root X E :=
  match E with
  | Empty => False
  | Node x ho hs => rep x X 
  end.
*)

Definition link_spec := RepSpec link (E1;heap) (E2;heap) |R>>
  forall X, min_of E1 X -> foreach (is_ge X) E2 ->
  R (E1 \u E2 ; heap).


(*
Definition sum_measure A1 A2 (mu1:A1->nat) (mu2:A2->nat) (p:A1+A2) : nat :=
  match p with 
  | inl x => mu1 x 
  | inr x => mu2 x 
  end.
  (*(sum_measure (fun h1 h2 => 2 * (size h1 + size h2)) (fun h size).*)

Definition size_pair (p:heap*heap) :=
  let (h1,h2) := p in (size h1 + size h2)%nat.
*)
(*
  sets lt: (fun p1 p2 => match p1,p2 with
    | inl x, inr y => size_pair x < size_pair y
    | inr x, inl y => size_pair x <= size_pair y
    | _,_ => False end).
*)


Axiom rep_induction_mut_2_2_2 : 
  forall (a11 a12 A11 A12 B1 : Type)
  (rep11:a11->A11->Prop) (rep12:a12->A12->Prop)
  (mu1:A11->A12->nat) (RK1:a11->a12->A11->A12->~~B1->Prop) f1,
  forall (a21 a22 A21 A22 B2 : Type)
  (rep21:a21->A21->Prop) (rep22:a22->A22->Prop)
  (mu2:A21->A22->nat) (RK2:a21->a22->A21->A22->~~B2->Prop) f2,
  let IH := (fun n => 
      rep_spec_2_hyp (B:=B1) rep11 rep12 (fun X11 X12 => (mu1 X11 X12 < n)%nat) RK1 f1
   /\ rep_spec_2_hyp (B:=B2) rep21 rep22 (fun X21 X22 => (mu2 X21 X22 < n)%nat) RK2 f2) in
  rep_spec_2_hyp (B:=B1) rep11 rep12 (fun X11 X12 => IH (mu1 X11 X12)) RK1 f1 -> 
  rep_spec_2_hyp (B:=B2) rep21 rep22 (fun X21 X22 => IH (mu2 X21 X22)) RK2 f2 -> 
     rep_spec_2 (B:=B1) rep11 rep12 RK1 f1 
  /\ rep_spec_2 (B:=B2) rep21 rep22 RK2 f2.

(*
Lemma test : (BagEmpty (multiset T)).
typeclass. Qed.
Lemma test2 : (BagCard (multiset T)).
typeclass. Qed.
Lemma test23 : @card_empty (multiset T) _ _ _ = card_empty.
typeclass. Qed.
*)

Hint Rewrite (card_empty (T:=multiset T)) (card_single (T:=multiset T))
  (card_union (T:=multiset T)) : rew_card.
Ltac rew_card := autorewrite with rew_card.

Hint Extern 1 ((_ < _)%nat) => simpl; rew_card; math.

Lemma is_ge_refl : forall x, is_ge x x.
Proof. intros. apply le_refl. Qed.
Hint Resolve is_ge_refl.

Lemma min_of_prove : forall X Eo Es,
  foreach (is_ge X) Eo ->
  foreach (is_ge X) Es ->
  min_of ('{X} \u Eo \u Es) X.
Proof.
  introv Lo Ls. split~. introv M. multiset_in M.
  apply le_refl. apply~ Lo. apply~ Ls.
Qed.

Hint Resolve min_of_prove.


Lemma min_of_eq : forall X Y E1 E2,
  min_of (\{Y} \u E1 \u E2) X ->
  foreach (is_ge Y) E1 ->
  foreach (is_ge Y) E2 ->
  Y <= X.
Proof.
  introv [M1 M2] G1 G2. multiset_in M1.
  apply le_refl.
  apply~ G1.
  apply~ G2.
Qed.

(*
Lemma min_of_eq : forall X Y E1 E2,
  min_of (\{Y} \u E1 \u E2) X ->
  foreach (is_ge X) E1 ->
  foreach (is_ge X) E2 ->
  X <= Y.
Proof.
  introv [M1 M2] G1 G2. multiset_in M1.
  apply le_refl.
  apply~ M2.
  apply~ M2.
Qed.
*)

Lemma merge_spec : RepTotal merge (E1;heap) (E2;heap) >>
  E1 \u E2 ; heap.
Proof.
  applys (>>> proj1 __ link_spec).
  eapply rep_induction_mut_2_2_2 with 
   (mu1 := fun E1 E2 => (2 * (card E1 + card E2) + 1)%nat)
   (mu2 := fun E1 E2 => (2 * (card E1 + card E2))%nat);
   unfold rep_spec_2, rep_spec_2_hyp.
  (* verif merge *)
  xcf. introv R1 R2 [_ IH]. xmatch; xcleanpat.
  xgo. inverts R2. equates* 1.
  xgo. inverts R1. equates* 1.
  inverts R1. inverts R2. xapp~. xif.
    xapp~.
    applys_to P_x0 nle_to_sle. xapp~. ximpl. equates* 1.
  (* verif link *)
  xcf. intros h1 h2 E1 E2 R1 R2 [IH _] X MX GX. inverts R1. 
  xgo. applys_to MX proj1. eapply (in_empty X). eauto.
  xmatch.
  xgo. inverts H0. forwards~: (>>> min_of_eq MX). constructors*.
  xgo~. forwards~: (>>> min_of_eq MX). constructors*.
Qed.

Hint Extern 1 (RegisterSpec merge) => Provide merge_spec.

Lemma insert_spec : RepTotal insert (X;O.t) (E;heap) >>
  \{X} \u E ; heap.
Proof. xgo~. ximpl. equates* 1. Qed.

Hint Extern 1 (RegisterSpec insert) => Provide insert_spec.

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

