Set Implicit Arguments.
Require Import FuncTactics LibCore Shared.
Require Import OrderedSig_ml HeapSig_ml OrderedSig_proof HeapSig_proof.
Require Import SplayHeap_ml.

Module SplayHeapSpec (O:MLOrdered) (OS:OrderedSigSpec with Module O:=O)
  <: HeapSigSpec with Definition H.MLElement.t := O.t.

(** instantiations *)

Module Import H <: MLHeap := MLSplayHeap O.
Module Import OS := OS.
Existing Instance le_inst.
Existing Instance le_order.

(** invariant *)

Definition is_le (X Y:T) := Y <= X.
Definition is_ge (X Y:T) := X <= Y.

Inductive inv : heap -> multiset T -> Prop :=
  | inv_empty : 
      inv Empty \{} 
  | inv_node : forall a y b A Y B E,
      inv a A -> inv b B -> rep y Y ->
      foreach (is_le Y) A -> foreach (is_ge Y) B ->
      E = (\{Y} \u A \u B) ->
      inv (Node a y b) E.

(** model *)

Instance heap_rep : Rep heap (multiset T).
Proof.
  apply (Build_Rep inv).
  induction x; introv HX HY; inverts HX; inverts HY; prove_rep.
Defined.

(** automation *)

Hint Extern 1 (_ = _ :> multiset _) => check_noevar_goal; permut_simpl : multiset.

Definition U := multiset T.

Ltac myauto cont := 
  match goal with 
  | |- _ = _ :> multiset T => try solve [ change (multiset T) with U; cont tt ]
  | |- _ => cont tt
  end. 

Ltac auto_tilde ::= myauto ltac:(fun _ => eauto).
Ltac auto_star ::= try solve [ intuition (eauto with multiset) ].
Ltac auto_plus := myauto ltac:(fun _ => eauto 10).

Hint Extern 1 (@le nat _ _ _) => simpl; math. (*todo:needed?*)
Hint Extern 1 (@lt nat _ _ _) => simpl; math.
Hint Constructors inv.

(** useful facts *)

Fixpoint size h :=
  match h with
  | Empty => 1%nat
  | Node a x b => (1 + size a + size b)%nat
  end.

Lemma size_pos : forall h,
  (size h > 0%nat).
Proof. destruct h; simpl; math. Qed.

Lemma foreach_le_trans : forall (X Y : OS.T) (E : multiset OS.T),
  Y <= X -> foreach (is_le Y) E -> foreach (is_le X) E.
Proof. intros. apply~ foreach_weaken. intros_all. apply~ le_trans. Qed.

Lemma foreach_ge_trans : forall (X Y : OS.T) (E : multiset OS.T),
  X <= Y -> foreach (is_ge Y) E -> foreach (is_ge X) E.
Proof. intros. apply~ foreach_weaken. intros_all. apply~ le_trans. Qed.

Hint Extern 1 (foreach (is_le ?X) ?E) =>
  let go Y := (apply (@foreach_le_trans X Y)) in
  match goal with 
  | H: ?Y <= X, H': foreach (is_le ?Y) E |- _ => go Y
  | H: ?Y <= X |- _ => go Y 
  end.

Hint Extern 1 (foreach (is_ge ?X) ?E) =>
  let go Y := (apply (@foreach_ge_trans X Y)) in
  match goal with
  | H: X <= ?Y, H': foreach (is_ge ?Y) E |- _ => go Y
  | H: X <= ?Y |- _ => go Y
  end.

Lemma min_of_last : forall X A,
   foreach (is_ge X) A -> min_of ('{X} \u \{} \u A) X.
Proof.
  introv H. split~. introv M. multiset_in M.
    apply le_refl.
    apply~ H.
Qed.

Hint Resolve min_of_last.

Ltac norm :=
  repeat match goal with
  | H: foreach _ (_ \u _) |- _ => applys_to H foreach_union_inv; destruct H
  | H: foreach _ (\{_}) |- _ => rewrite foreach_single_eq in H
  | H: is_le ?X ?Y |- _ => unfold is_le in H
  | H: is_ge ?X ?Y |- _ => unfold is_ge in H
  end.

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

Lemma partition_spec : Spec partition p e |R>>
  forall P E, rep p P -> rep e E -> 
  R (fun r:heap*heap => let (e1,e2) := r in
     exists E1 E2, rep e1 E1 /\ rep e2 E2 /\ 
     E = E1 \u E2 /\
     foreach (is_le P) E1 /\
     foreach (is_ge P) E2 /\
     size e1 <= size e /\
     size e2 <= size e).
Proof.
  xinduction (fun (p:O.t) (e:heap) => size e). 
  xcf. intros p e IH P E RP RE. xmatch.
  xgo. inverts RE. exists___. splits*.
  inverts RE as RA RB RX. xapp~. xif.
  (* case left *)
   xmatch. subst t. xgo. inverts RB. exists___. splits*.
  inverts RB. xapp~. xif.
  (* case left/left *)
  xapp~. clear IH. (* todo: xapp as *)
  destruct _x7 as [sma big]. intuit P_x7.
  xgo. subst. norm. exists___. splits; auto_plus. auto*.
  (* case left/right *)
  xapp~. clear IH. applys_to P_x5 nle_to_sle. 
  destruct _x6 as [sma big]. intuit P_x6.
  xgo. subst. norm. exists___. splits; auto_plus. auto*.
  (* case right *)
  applys_to P_x1 nle_to_sle. xmatch. subst t. 
  xgo. inverts RA. exists___. splits*.
  inverts RA. xapp~. xif.
  (* case right/left *)
  xapp~. clear IH.
  destruct _x4 as [sma big]. intuit P_x4.
  xgo. subst. norm. exists___. splits; auto_plus. auto*.
  (* case right/right *)
  xapp~. clear IH. applys_to P_x2 nle_to_sle. 
  destruct _x3 as [sma big]. intuit P_x3.
  xgo. subst. norm. exists___. splits; auto_plus. auto*.
Qed.

Hint Extern 1 (RegisterSpec partition) => Provide partition_spec.

Lemma merge_spec : RepTotal merge (E1;heap) (E2;heap) >>
  E1 \u E2 ; heap.
Proof.
  xinduction (fun e1 e2 => (size e1 + size e2)%nat).
  xcf. introv IH Rep1 Rep2. xmatch.
  xgo. inverts Rep1. equates* 1.
  xcleanpat. inverts Rep1. xlet as. xapp~. 
   intros [f1 f2] H. intuit H. xgo~; try (simpl; math).
    constructors~. subst. permut_simpl.
Qed.
   
Hint Extern 1 (RegisterSpec merge) => Provide merge_spec.

Lemma insert_spec : RepTotal insert (X;O.t) (E;heap) >>
  \{X} \u E ; heap.
Proof.
  xcf. introv RepX RepE. xlet as. xapp~. 
  intros [f1 f2] H. intuit H. xgo*.
Qed.

Hint Extern 1 (RegisterSpec insert) => Provide insert_spec.

Lemma find_min_spec : RepSpec find_min (E;heap) |R>>
  E <> \{} -> R (min_of E ;; O.t).
Proof.
  xinduction size.
  xcf. intros e IH E RepE HasE. inverts RepE. xgo.
  inverts H. xgo. eauto.
  xgo. math. constructors~. intros K. multiset_inv.  
  ximpl as x (X&RepX&MinX). destruct MinX as (InXA&InfX).
   esplit. splits_all~. multiset_in InXA; auto.
   asserts: (X <= Y). applys~ H2.
   intros Z HZ. sets_eq A: (\{Y0} \u A0 \u B0). multiset_in HZ. 
     auto.
     apply~ InfX.
     subst~. apply~ (le_trans Y). apply~ H3.
Qed.

Hint Extern 1 (RegisterSpec find_min) => Provide find_min_spec.

Lemma delete_min_spec : RepSpec delete_min (E;heap) |R>>
  E <> \{} -> R (removed_min E ;; heap).
Proof. 
  xinduction size. 
  xcf. intros IH e E RepE HasE. xmatch_nocases.
  inverts RepE as RA RB RY LA LB; xpat.
  inverts RA as RC RD RX LC LD; xpat.
  xgo. esplit; split~. exists* __.
  xcase.
  xgo. inverts RC. norm. esplit; split~.
    exists Y0. splits~. split~. introv M. multiset_in M.
      auto.
      apply le_refl.
      apply~ LD.
      apply~ le_trans. apply~ LB.
    auto*.
  xgo~. intro_subst_hyp. inverts RC. false~ C. multiset_inv.
  destruct P_x1 as (A' & RepA' & X & InfX & EqX). subst A0. norm.
  exists ('{Y} \u ('{Y0} \u A' \u B0) \u B). split.
  equates 1. applys~ (>>> inv_node A' (\{Y} \u B0 \u B)).
    (* todo: bug in tactic*) permut_simpl. apply union_comm.
  exists X. split. split~.
   applys_to InfX proj2. introv M. multiset_in M; auto~.
     eapply le_trans. apply H5. apply~ LD. 
     apply~ le_trans. apply~ le_trans. apply~ LB.
   auto*.
Qed.

Hint Extern 1 (RegisterSpec delete_min) => Provide delete_min_spec.

End SplayHeapSpec.

