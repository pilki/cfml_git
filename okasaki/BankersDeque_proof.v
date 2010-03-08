Set Implicit Arguments.
Require Import FuncTactics LibCore.
Require Import DequeSig_ml DequeSig_proof.
Require Import BankersDeque_ml.

Definition C := 2.

Lemma c_val : c = C.
Proof. xgo~. Qed.


Module BankersQueueSpec <: QueueSigSpec.

(** instantiations *)

Module Import Q <: MLDeque := MLBankersDeque.
Import MLBankersDeque.

(** invariant *)

Definition inv (d:int) `{Rep a_ A} (q:deque a_) (Q:list A) :=
  let '(lenf,f,lenr,r) := q in 
     Forall2 rep (f ++ rev r) Q
  /\ lenf = length f
  /\ lenr = length r
  /\ lenf <= C*lenr + 1 + d
  /\ lenr <= C*lenf + 1 + d.

Global Instance deque_rep `{Rep a_ A} : Rep (deque a_) (list A) :=
  inv 0.

(** automation *)

Lemma c_val2 : c = 2.
Proof. rewrite~ c_val. Qed.
Hint Rewrite c_val2 : rew_maths.

Hint Constructors Forall2.
Hint Resolve Forall2_last.
Hint Extern 1 (@rep (deque _) _ _ _ _) => simpl.
Hint Unfold inv.

Ltac auto_tilde ::= eauto with maths.

Section Polymorphic.
Variables (a_ A : Type) (RA:Rep a_ A).

(** useful facts *)

Lemma empty_from_len : forall f lenf lenr r Q,
  rep (lenf, f, lenr, r) Q -> lenf + lenr = 0 -> Q = nil.
Proof.
  introv (H&LF&LR&CF&CR) L.  
  rewrite~ (@length_zero_inv _ r) in H.
  rewrite~ (@length_zero_inv _ f) in H.
  inverts~ H.
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
  RepTotal is_empty (Q;deque a_) >> bool_of (Q = nil).
Proof.
  xcf. intros (((lenf,f),lenr),r) Q RQ. xgo.
  unfolds. extens. iff Z; fold_prop; subst.
  apply~ empty_from_len.
  intuit RQ. inverts H. destruct (nil_eq_app_rev_inv H5). subst~.
Qed. 

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Lemma check_spec : 
  Spec check (q:deque a_) |R>>
    forall Q, inv 1 q Q ->
    R (Q ; deque a_).
Proof.
  xcf. intros (((lenf,f),lenr),r) Q K. xgo.
  destructs K. subst. simple~.
  destructs K. simpl. rew_list~.
Qed.

Hint Extern 1 (RegisterSpec check) => Provide check_spec.

Lemma snoc_spec : 
  RepTotal snoc (Q;deque a_) (X;a_) >> (Q & X) ; deque a_.
Proof.
  xcf. intros (((lenf,f),lenr),r) x. introv (H&LF&LR&LE) RX.
  xgo~; ximpl_nointros. unfolds. rew_list. rewrite~ <- app_assoc. 
Qed.

Hint Extern 1 (RegisterSpec snoc) => Provide snoc_spec.

Lemma head_spec : 
  RepSpec head (Q;deque a_) |R>>
     Q <> (@nil A) -> R (is_head Q ;; a_).
Proof.
  xcf. intros (((lenf,f),lenr),r) Q RQ NE. xgo.
  apply NE. apply~ empty_from_f.
  intuit RQ. inverts* H.
Qed.

Hint Extern 1 (RegisterSpec head) => Provide head_spec.

Lemma tail_spec :
  RepSpec tail (Q;deque a_) |R>> 
     Q <> nil -> R (is_tail Q ;; deque a_).
Proof.
  xcf. intros (((lenf,f),lenr),r) Q RQ NE. xmatch.
  apply NE. apply~ empty_from_f.
  intuit RQ. rew_list in *. inverts H. xapp~. ximpl~.
Qed.

Hint Extern 1 (RegisterSpec tail) => Provide tail_spec.

End Polymorphic.

End BankersQueueSpec.
