Set Implicit Arguments.
Require Import FuncTactics LibCore.
Require Import DequeSig_ml DequeSig_proof.
Require Import BankersDeque_ml.

Module CatenableListImplSpec (Q:MLQueue) (QS:QueueSigSpec with Module Q:=Q)
  <: CatenableListSigSpec.

(** instantiations *)

Module Import C <: MLCatenableList := MLCatenableListImpl.
Import MLCatenableListImpl.

(** invariant *)

Inductive inv `{Rep a A} (c:cat a) (L:list A) :=
  | inv_empty :
      inv Empty nil
  | inv_struct : forall x q X Ls L,
      rep x X ->
      rep (H := Build_Rep inv) q Ls ->
      L =' X :: Ls ->
      Forall (<> nil) Ls.
      
Global Instance deque_rep `{Rep a A} : Rep (cat a) (list A) :=
  inv 0.

(** automation *)

Hint Constructors Forall2.
Hint Resolve Forall2_last.
Hint Extern 1 (@rep (cat _) _ _ _ _) => simpl.
Hint Unfold inv.

Ltac auto_tilde ::= eauto with maths.

Section Polymorphic.
Variables (a A : Type) (RA:Rep a A).

  (* todo: avoid the following lines *)
Hint Extern 1 (RegisterSpec Q.is_empty) => Provide (QS.is_empty_spec (H:=RA)).
Hint Extern 1 (RegisterSpec Q.snoc) => Provide (QS.snoc_spec (H:=RA)).
Hint Extern 1 (RegisterSpec Q.head) => Provide (QS.head_spec (H:=RA)).
Hint Extern 1 (RegisterSpec Q.tail) => Provide (QS.tail_spec (H:=RA)).

(** useful facts *)

Lemma to_empty : forall L,
  rep Empty L -> L = nil.
Proof. introv RL. inverts RL as _ M. inverts~ M. Qed.

Lemma to_not_empty : forall c L,
  rep c L -> L <> nil -> c <> Empty.
Proof.
  introv RL NE K. subst. apply NE. apply~ to_empty.
Qed.

Lemma from_empty : forall c,
  rep c nil -> c = Empty.
Proof.
  introv RC. inverts RC as.
  introv _ ID. inverts~ ID.
  introv ? ? Df ? ? ?. inverts Df; false.
Qed.

(** verification *)

Lemma empty_spec : 
  rep (@empty a) (@nil A).
Proof.
  generalizes RA A. apply (empty_cf a). xgo.
  intros. simpl. rew_list~.
Qed.

Hint Extern 1 (rep empty _) => apply empty_spec.

Lemma is_empty_spec : 
  RepTotal is_empty (L;cat a) >> bool_of (L = nil).
Proof.
  xcf. intros (((lenf,f),lenr),r) Q RQ. xgo.
  unfolds. extens. iff Z; fold_prop; subst.
  apply~ empty_from_len.
  intuit RQ. inverts H. destruct (nil_eq_app_rev_inv H5). subst~.
Qed. 

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Lemma link_spec : 
  RepSpec link (L1;cat a) (L2;cat a) |R>>
    L1 <> nil -> L2 <> nil -> R (L1 ++ L2 ; cat a).
Proof.
Qed.

Hint Extern 1 (RegisterSpec link) => Provide link_spec.

Lemma link_all_spec : 
  RepSpec link_all (Ls;queue (cat a)) |R>>
    Ls <> nil -> R (concat Ls ; cat a).
Proof.
Qed.

Hint Extern 1 (RegisterSpec link_all) => Provide link_all_spec.

Lemma append_spec : 
  RepTotal append (L1;cat a) (L2;cat a) >> (L1++L2) ; cat a.
Proof.
Qed.

Hint Extern 1 (RegisterSpec append) => Provide append_spec.

Lemma cons_spec : 
  RepTotal cons (X;a) (L;cat a) >> (X::L) ; cat a.
Proof.
Qed.

Hint Extern 1 (RegisterSpec cons) => Provide cons_spec.

Lemma snoc_spec : 
  RepTotal snoc (L;cat a) (X;a) >> (L&X) ; cat a.
Proof.
Qed.

Hint Extern 1 (RegisterSpec snoc) => Provide snoc_spec.

Lemma head_spec : 
  RepSpec head (L;cat a) |R>>
     L <> nil -> R (is_head L ;; a).
Proof.
Qed.

Hint Extern 1 (RegisterSpec head) => Provide head_spec.

Lemma tail_spec :
  RepSpec tail (L;cat a) |R>> 
     L <> nil -> R (is_tail L ;; cat a).
Proof.
Qed.

Hint Extern 1 (RegisterSpec tail) => Provide tail_spec.

End Polymorphic.

End CatenableListImplSpec.

