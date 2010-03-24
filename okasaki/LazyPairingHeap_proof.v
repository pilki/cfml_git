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

(** model *)

Instance heap_rep : Rep heap (multiset T).
Proof.
  apply (Build_Rep inv). 
  induction x; introv HX HY; inverts HX; inverts HY; prove_rep.
Defined.

(** automation *)

Hint Extern 1 (_ < _) => simpl; math.
Hint Extern 1 (_ <= _) => simpl; math.
Hint Extern 1 (_ = _ :> multiset _) => permut_simpl : multiset.

Definition U := multiset T.

Ltac myauto cont :=
  match goal with 
  | |- _ = _ :> multiset ?T => try solve [ change (multiset T) with U; cont tt ]
  | |- _ => cont tt
  end. 

Ltac auto_tilde ::= myauto ltac:(fun _ => eauto).
Ltac auto_star ::= try solve [ intuition (eauto with multiset) ].

Hint Rewrite (card_empty (T:=multiset T)) (card_single (T:=multiset T))
  (card_union (T:=multiset T)) : rew_card.

Ltac rew_card := autorewrite with rew_card.
Hint Extern 1 ((_ < _)%nat) => simpl; rew_card; math.

Ltac prove_card := simpl; rew_card; math. (* todo : work as hint *)

Hint Constructors inv Forall Forall2.

(** useful facts *)

Lemma is_ge_refl : forall x, is_ge x x.
Proof. intros. apply le_refl. Qed.

Lemma foreach_ge_trans : forall (X Y : OS.T) (E : multiset OS.T),
  foreach (is_ge X) E -> Y <= X -> foreach (is_ge Y) E.
Proof. intros. apply~ foreach_weaken. intros_all. apply* le_trans. Qed.

Hint Resolve is_ge_refl foreach_ge_trans.

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
  apply le_refl. apply~ G1. apply~ G2.
Qed.

(** verification *)

Lemma empty_spec : rep empty \{}.
Proof. 
  apply empty_cf. xret~. 
Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma is_empty_spec : RepTotal is_empty (E;heap) >> 
  bool_of (E = \{}).
Proof.
  xcf. intros e E RepE. inverts RepE; xgo. 
  auto. multiset_inv.
Qed. 

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Definition link_spec := RepSpec link (E1;heap) (E2;heap) |R>>
  forall X, foreach (is_ge X) E2 -> min_of E1 X -> 
  R (E1 \u E2 ; heap).

Lemma merge_spec : RepTotal merge (E1;heap) (E2;heap) >>
  E1 \u E2 ; heap.
Proof.
  applys (>>> proj1 __ link_spec).
  eapply conj_strengthen_2; try intros M.
  xintros. intros. gen_eq n:((2*(card E1 + card E2) + 1)%nat). 
   gen n x1 x2 E1 E2 H H0. apply M.
  unfolds. xintros. intros. gen_eq n:((2*(card E1 + card E2))%nat).
   gen n x1 x2 X E1 E2 H H0 H1 H2. apply M.
  forwards (H1&H2): (eq_gt_induction_2);
    try match goal with |- _ /\ _ =>
      splits; intros n; pattern (eq n); [ apply H1 | apply H2 ] end; auto~.
  introv IHmerge IHlink. simpl. split.
  (* verif merge *)
  clear IHmerge. introv R1 R2 N. subst n. xcf_app. xmatch; xcleanpat.
  xgo. inverts R2. equates* 1.
  xgo. inverts R1. equates* 1.
  inverts R1. inverts R2. xapp~. xif.
    xapp~. prove_card.
    applys_to P_x0 nle_to_sle. equates 1. fapplys IHlink; auto~.
     prove_card. extens. intros h. iff M. equates* 1. equates* 1.
  (* verif link *)
  clear IHlink. intros h1 h2 X E1 E2 R1 R2 GX MX N. subst n.
  xcf_app. inverts R1.
  xgo. applys_to MX proj1. eapply (in_empty X). eauto.
  xmatch.
  xgo. inverts H0. forwards~: (>>> min_of_eq MX). constructors*.
  xgo~.
    fapplys IHmerge; auto~. prove_card. 
    fapplys IHmerge; auto~. apply P_x1. prove_card. 
   forwards~: (>>> min_of_eq MX). constructors*.
Qed.

Hint Extern 1 (RegisterSpec merge) => Provide merge_spec.

Lemma insert_spec : RepTotal insert (X;O.t) (E;heap) >>
  \{X} \u E ; heap.
Proof. 
  xgo~. ximpl. equates* 1. 
Qed.

Hint Extern 1 (RegisterSpec insert) => Provide insert_spec.

Lemma find_min_spec : RepSpec find_min (E;heap) |R>>
  E <> \{} -> R (min_of E ;; O.t).
Proof. 
  xcf. intros e E RepE HasE. inverts RepE; xgo*.
Qed.

Hint Extern 1 (RegisterSpec find_min) => Provide find_min_spec.

Lemma delete_min_spec : RepSpec delete_min (E;heap) |R>>
  E <> \{} -> R (removed_min E ;; heap).
Proof. 
  xcf. intros e E RepE HasE. inverts RepE; xgo~. ximpl. xrep~. 
Qed.

Hint Extern 1 (RegisterSpec delete_min) => Provide delete_min_spec.

End LazyPairingHeapSpec.

