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

Global Instance repr `{Rep a_ A} : Rep (queue a_) (list A) :=
  inv 0.

(** automation *)

Hint Constructors Forall2.
Hint Resolve Forall2_last.
Hint Unfold is_head is_tail.
Hint Extern 1 (@rep (queue _) _ _ _ _) => simpl.
Hint Unfold inv.

Ltac auto_tilde ::= auto with maths.

(** useful facts *)

(** verification *)

Section Polymorphic.
Variables (a_ A : Type) (RA:Rep a_ A).

Lemma empty_spec : 
  rep (@empty a_) (@nil A).
Proof.
  generalizes RA A. apply (empty_cf a_). xgo.
  intros. simpl. rew_list~.
Qed.

Lemma is_empty_spec : 
  RepTotal is_empty (Q;queue a_) >> bool_of (Q = nil).
Proof.
  xcf. intros (((lenf,f),lenr),r) Q (H&LF&LR&LE). xgo.
  unfolds. extens. iff Z; fold_prop.
  rewrite~ (@length_zero_inv _ r) in H.
   rewrite~ (@length_zero_inv _ f) in H. inverts~ H.
  subst. inverts H. destruct (nil_eq_app_rev_inv H1). subst~.
Qed.

Lemma check_spec : 
  Spec check (q:queue a_) |R>>
    forall Q, inv 1 q Q ->
    R (Q ; queue a_).
Proof.
  xcf. intros (((lenf,f),lenr),r) Q K. xgo.
  destructs K. subst. simple~.
  destructs K. simpl. rew_list. rewrite~ length_rev.
Qed.

Hint Extern 1 (RegisterSpec check) => Provide check_spec.

Lemma snoc_spec : 
  RepTotal snoc (Q;queue a_) (X;a_) >> (Q & X) ; queue a_.
Proof.
  xcf. intros (((lenf,f),lenr),r) x. introv (H&LF&LR&LE) RX.
  xgo~; ximpl. unfolds. rew_list. rewrite~ <- app_assoc. 
Qed.

(* -- todo
Lemma head_spec : 
  RepSpec head (Q;queue a_) |R>>
     Q <> (@nil A) -> R (is_head Q ;; a_).
Proof.
  xcf. intros (lenf, r] q. introv H NE.
  simpl in H.
 xgo; rew_list in H.
  rewrite~ M in H. inverts~ H.
  inverts~ H.
Qed.

Lemma tail_spec :
  RepSpec tail (Q;queue a_) |R>> 
     Q <> nil -> R (is_tail Q ;; queue a_).
Proof.
  xcf. intros [f r] q. introv [H M] NE. xmatch.
  xgo. rewrite~ M in H. inverts~ H.
  inverts H. xgo~.
Qed.


End Polymorphic.
*)
