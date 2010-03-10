Set Implicit Arguments.
Require Import FuncTactics LibCore.
Require Import QueueSig_ml QueueSig_proof.
Require Import BankersQueue_ml.


Module BankersQueueSpec <: QueueSigSpec.

(** instantiations *)

Module Import Q <: MLQueue := MLBankersQueue.
Import MLBankersQueue.

(** invariant *)

Definition inv (d:int) `{Rep a_ A} (q:queue a_) (Q:list A) :=
  let '(lenf,f,lenr,r) := q in 
     Forall2 rep (f ++ rev r) Q
  /\ lenf = length f
  /\ lenr = length r
  /\ lenr <= lenf + d.

Global Instance queue_rep `{Rep a_ A} : Rep (queue a_) (list A) :=
  inv 0.

(** automation *)

Hint Constructors Forall2.
Hint Resolve Forall2_last.
Hint Extern 1 (@rep (queue _) _ _ _ _) => simpl.
Hint Unfold inv.

Ltac auto_tilde ::= eauto with maths.

Section Polymorphic.
Variables (a_ A : Type) (RA:Rep a_ A).

(** useful facts *)

Lemma empty_from_lenf : forall f lenr r Q,
  rep (0, f, lenr, r) Q -> Q = nil.
Proof.
  introv (H&LF&LR&LE). 
  rewrite~ (@length_zero_inv _ r) in H.
  rewrite~ (@length_zero_inv _ f) in H.
  inverts~ H.
Qed.

Lemma empty_from_f : forall lenf lenr r Q,
  rep (lenf, nil, lenr, r) Q -> Q = nil.
Proof.
  introv (H&LF&LR&LE). rew_list in LF. 
  apply~ empty_from_lenf. 
Qed.

Lemma empty_to_lenf : forall lenf f lenr r,
  rep (lenf, f, lenr, r) nil -> lenf = 0.
Proof.
  introv (H&LF&LR&LE). inverts H.
  destruct (nil_eq_app_rev_inv H1). subst~.
Qed.

(** verification *)

Lemma empty_spec : 
  rep (@empty a_) (@nil A).
Proof.
  generalizes RA A. apply (empty_cf a_). xgo.
  intros. simpl. rew_list~.
Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma is_empty_spec : 
  RepTotal is_empty (Q;queue a_) >> bool_of (Q = nil).
Proof.
  xcf. intros (((lenf,f),lenr),r) Q RQ. xgo.
  unfolds. extens. iff Z; fold_prop; subst.
  apply~ empty_from_lenf. apply~ empty_to_lenf.
Qed. 

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Lemma check_spec : 
  Spec check (q:queue a_) |R>>
    forall Q, inv 1 q Q ->
    R (Q ; queue a_).
Proof.
  xcf. intros (((lenf,f),lenr),r) Q K. xgo.
  destructs K. subst. simple~.
  destructs K. simpl. rew_list~.
Qed.

Hint Extern 1 (RegisterSpec check) => Provide check_spec.

Lemma snoc_spec : 
  RepTotal snoc (Q;queue a_) (X;a_) >> (Q & X) ; queue a_.
Proof.
  xcf. intros (((lenf,f),lenr),r) x. introv (H&LF&LR&LE) RX.
  xgo~; ximpl_nointros. unfolds. rew_list. rewrite~ <- app_assoc. 
Qed.

Hint Extern 1 (RegisterSpec snoc) => Provide snoc_spec.

Lemma head_spec : 
  RepSpec head (Q;queue a_) |R>>
     Q <> nil -> R (is_head Q ;; a_).
Proof.
  xcf. intros (((lenf,f),lenr),r) Q RQ NE. xgo.
  apply NE. apply~ empty_from_f.
  intuit RQ. inverts* H.
Qed.

Hint Extern 1 (RegisterSpec head) => Provide head_spec.

Lemma tail_spec :
  RepSpec tail (Q;queue a_) |R>> 
     Q <> nil -> R (is_tail Q ;; queue a_).
Proof.
  xcf. intros (((lenf,f),lenr),r) Q RQ NE. xmatch.
  apply NE. apply~ empty_from_f.
  intuit RQ. rew_list in *. inverts H. xapp~. ximpl~.
Qed.

Hint Extern 1 (RegisterSpec tail) => Provide tail_spec.

End Polymorphic.

End BankersQueueSpec.
