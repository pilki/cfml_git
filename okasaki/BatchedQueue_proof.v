Set Implicit Arguments.
Require Import FuncTactics LibCore.
Require Import QueueSig_ml QueueSig_proof.
Require Import BatchedQueue_ml.

Module BatchedQueueSpec <: QueueSigSpec.

(** instantiations *)

Module Import Q <: MLQueue := MLBatchedQueue.
Import MLBatchedQueue.

(** invariant *)

Global Instance repr `{Rep a_ A} : Rep (queue a_) (list A) :=
  fun (q:queue a_) (Q:list A) =>
  let (f,r) := q in 
     Forall2 rep (f ++ rev r) Q
  /\ (f = nil -> r = nil).

(** automation *)

Hint Constructors Forall2.
Hint Resolve Forall2_last.
Hint Unfold is_head is_tail.
Hint Extern 1 (@rep (queue _) _ _ _ _) => simpl; rew_list.

Ltac auto_star ::= try solve [ rew_list in *; intuition (eauto) ].


(** useful facts *)

(** verification *)

Section Polymorphic.
Variables (a_ A : Type) (RA:Rep a_ A).

Lemma empty_spec : 
  rep (@empty a_) (@nil A).
Proof.
  generalizes RA A. apply (empty_cf a_). xgo.
  intros. simpl. rew_list*. (*todo: rew_list~*)
Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma is_empty_spec : 
  RepTotal is_empty (Q;queue a_) >> bool_of (Q = nil).
Proof.
  xcf. intros (f0,r0) l [H M]. xgo.
  rewrite~ M in H. inverts~ H.
  intro_subst_hyp. inverts H as K.
   destruct (nil_eq_app_rev_inv K). false.
Qed.

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Lemma checkf_spec : 
  Spec checkf (q:queue a_) |R>>
    forall Q, (let (f,r) := q in Forall2 rep (f ++ rev r) Q) ->
    R (Q ; queue a_).
Proof.
  xcf. intros (f,r) l K. xgo; rew_list in K.
  auto~. split; auto_false.
Qed.

Hint Extern 1 (RegisterSpec checkf) => Provide checkf_spec.

Lemma snoc_spec : 
  RepTotal snoc (Q;queue a_) (X;a_) >> (Q & X) ; queue a_.
Proof.
  xcf. intros [f r] x. introv [H M] RX. xgo~.
  rew_list. rewrite~ <- app_assoc.
Qed.

Hint Extern 1 (RegisterSpec snoc) => Provide snoc_spec.

Lemma head_spec : 
  RepSpec head (Q;queue a_) |R>>
     Q <> (@nil A) -> R (is_head Q ;; a_).
Proof.
  xcf. intros [f r] q. introv [H M] NE. xgo; rew_list in H.
  rewrite~ M in H. inverts~ H.
  inverts~ H.
Qed.

Hint Extern 1 (RegisterSpec head) => Provide head_spec.

Lemma tail_spec :
  RepSpec tail (Q;queue a_) |R>> 
     Q <> nil -> R (is_tail Q ;; queue a_).
Proof.
  xcf. intros [f r] q. introv [H M] NE. xmatch.
  xgo. rewrite~ M in H. inverts~ H.
  inverts H. xgo~.
  (*todo: use ximpl for ( ; ) ==> ( ;; ) *)
Qed.

Hint Extern 1 (RegisterSpec tail) => Provide tail_spec.

End Polymorphic.


