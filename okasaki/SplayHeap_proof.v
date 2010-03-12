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
Definition is_gt (X Y:T) := X < Y.

Inductive inv : heap -> multiset T -> Prop :=
  | inv_empty : 
      inv Empty \{} 
  | inv_node : forall a y b A Y B E,
      inv a A -> inv b B -> rep y Y ->
      foreach (is_le Y) A -> foreach (is_gt Y) B ->
      E = (\{Y} \u A \u B) ->
      inv (Node a y b) E.

Instance heap_rep : Rep heap (multiset T).
Proof.
  apply (Build_Rep inv).
  induction x; introv HX HY; inverts HX; inverts HY; prove_rep.
Defined.

(** termination relation *)

Fixpoint tree_size h :=
  match h with
  | Empty => 1%nat
  | Node a x b => (1 + tree_size a + tree_size b)%nat
  end.

Lemma tree_size_pos : forall h,
  (tree_size h > 0%nat).
Proof. destruct h; simpl; math. Qed.

(** automation *)

Hint Extern 1 (_ = _ :> multiset _) => permut_simpl : multiset.

Definition U := multiset T.

Ltac myauto cont := 
  match goal with 
  | |- _ = _ :> multiset T => try solve [ change (multiset T) with U; cont tt ]
  | |- _ => cont tt
  end. 

Ltac auto_tilde ::= myauto ltac:(fun _ => eauto).
Ltac auto_star ::= try solve [ intuition (eauto with multiset) ].

(** useful facts *)

Hint Constructors inv.
Hint Extern 1 (@rep heap _ _ _ _) => simpl.
Hint Extern 1 (@rep heaps _ _ _ _) => simpl.

Lemma foreach_gt_trans : forall (X Y : OS.T) (E : multiset OS.T),
  foreach (is_gt Y) E -> X <= Y -> foreach (is_gt X) E.
Proof. intros. apply~ foreach_weaken. intros_all. Admitted.

Hint Resolve foreach_gt_trans.

Hint Extern 2 (_ <= ?X) =>
  match goal with H: foreach (is_le X) _ |- _ => eapply H end.

Hint Extern 2 (?X < _) =>
  match goal with H: foreach (is_gt X) _ |- _ => eapply H end.

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
  auto. intros_all. fset_inv.
Qed.

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Lemma partition_spec : Spec partition p e |R>>
  forall P E, rep p P -> rep e E -> 
  R (fun r:heap*heap => let (e1,e2) := r in
     exists E1 E2, rep e1 E1 /\ rep e2 E2 /\ 
     E = E1 \u E2 /\
     foreach (is_le P) E1 /\
     foreach (is_gt P) E2 /\
     tree_size e1 <= tree_size e /\
     tree_size e2 <= tree_size e).
Proof. Admitted.

Hint Extern 1 (RegisterSpec partition) => Provide partition_spec.

Lemma merge_spec : RepTotal merge (E1;heap) (E2;heap) >>
  E1 \u E2 ; heap.
Proof.
  xinduction (fun e1 e2 => (tree_size e1 + tree_size e2)%nat).
  xcf. introv IH Rep1 Rep2. xmatch.
  xgo. inverts Rep1. equates* 1.
  xcleanpat. inverts Rep1. xlet as. xapp~. (* todo *)
   intros [f1 f2] (F1&F2&RepF1&RepF2&F12&Ord1&Ord2&Siz1&Siz2).
      (* todo: déconstruire automatiquement *)
    xgo~; try (simpl; math).
    constructors~. subst. permut_simpl.
Qed.
   
Hint Extern 1 (RegisterSpec merge) => Provide merge_spec.

Lemma insert_spec : RepTotal insert (X;O.t) (E;heap) >>
  \{X} \u E ; heap.
Proof.
  xcf. introv RepX RepE. xlet as. xapp~. 
  intros [f1 f2] (F1&F2&R). xgo*.
Qed.

Hint Extern 1 (RegisterSpec insert) => Provide insert_spec.

Lemma min_of_last : forall X A,
   foreach (is_gt X) A -> min_of ('{X} \u \{} \u A) X.
Proof.
  introv H. split~. introv M. multiset_in M.
    apply le_refl.
    apply~ H.
Qed.

Hint Resolve min_of_last.

Lemma find_min_spec : RepSpec find_min (E;heap) |R>>
  E <> \{} -> R (min_of E ;; O.t).
Proof.
  xinduction tree_size.
  xcf. intros e IH E RepE HasE. inverts RepE. xgo.
  inverts H. xgo. eauto.
  xgo. math. constructors~. intros K. fset_inv.  
  ximpl as x (X&RepX&MinX). destruct MinX as (InXA&InfX).
   esplit. splits_all~. skip.
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
  xinduction tree_size. 
  xcf. intros IH e E RepE HasE. inverts RepE; xmatch_nocases.
  xgo. inverts H. xgo. eauto 8 with multiset.
  xcase_one_real. inverts H4. xgo.
    exists ('{Y} \u B0 \u B). split. constructors~.
     rew_foreach* H2. exists Y0. esplit.
      split. auto.
        asserts: (Y0 <= Y). rew_foreach H2. destruct H2 as [M _]. apply~ M.
        lets: (le_trans Y). introv M. multiset_in M.
          auto.
          apply le_refl. 
          apply~ lt_to_le.
          apply~ H4. apply~ lt_to_le. 
      auto*.
  xgo~. math.
  intros K. fset_inv. (* simplifies*)
  destruct P_x1 as (A' & RepA' & X & InfX & EqX).
  exists ('{Y} \u ('{Y0} \u A' \u B0) \u B). split.
  equates 1. applys~ (>>> inv_node A' (\{Y} \u B0 \u B)).
   constructors~. skip. skip. skip. permut_simpl. rewrite union_comm. auto.
  (* todo: bug in tactic*)
   exists X. split. split. destruct InfX.
 skip.
introv M. skip.
  rewrite EqX. permut_simpl.
Qed.

Hint Extern 1 (RegisterSpec delete_min) => Provide delete_min_spec.

End SplayHeapSpec.

