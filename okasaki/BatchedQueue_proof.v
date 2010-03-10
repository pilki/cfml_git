Set Implicit Arguments.
Require Import FuncTactics LibCore.
Require Import QueueSig_ml QueueSig_proof.
Require Import BatchedQueue_ml.

Module BatchedQueueSpec <: QueueSigSpec.

(** instantiations *)

Module Import Q <: MLQueue := MLBatchedQueue.
Import MLBatchedQueue.

(** invariant *)

Global Instance queue_rep `{Rep a A} : Rep (queue a) (list A) :=
  fun (q:queue a) (Q:list A) =>
  let (f,r) := q in 
     Forall2 rep (f ++ rev r) Q
  /\ (f = nil -> r = nil).

(** automation *)

Hint Constructors Forall2.
Hint Resolve Forall2_last.
Hint Extern 1 (@rep (queue _) _ _ _ _) => simpl.
Ltac auto_tilde ::= eauto.

(** useful facts *)

(** verification *)

Section Polymorphic.
Variables (a A : Type) (RA:Rep a A).

Lemma empty_spec : 
  rep (@empty a) (@nil A).
Proof.
  generalizes RA A. apply (empty_cf a). xgo.
  intros. simpl. rew_list~. 
Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma is_empty_spec : 
  RepTotal is_empty (Q;queue a) >> bool_of (Q = nil).
Proof.
  xcf. intros (f0,r0) l [H M]. xgo.
  rewrite~ M in H. inverts~ H.
  intro_subst_hyp. inverts H as K.
   destruct (nil_eq_app_rev_inv K). false.
Qed.

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Lemma checkf_spec : 
  Spec checkf (q:queue a) |R>>
    forall Q, (let (f,r) := q in Forall2 rep (f ++ rev r) Q) ->
    R (Q ; queue a).
Proof.
  xcf. intros (f,r) l K. xgo; rew_list in K.
  simpl. rew_list~. split; auto_false.
Qed.

Hint Extern 1 (RegisterSpec checkf) => Provide checkf_spec.

Lemma snoc_spec : 
  RepTotal snoc (Q;queue a) (X;a) >> (Q & X) ; queue a.
Proof.
  xcf. intros [f r] x. introv [H M] RX. xgo~. 
  rewrite~ app_rev_cons. ximpl~.
Qed.

Hint Extern 1 (RegisterSpec snoc) => Provide snoc_spec.

Lemma head_spec : 
  RepSpec head (Q;queue a) |R>>
     Q <> nil -> R (is_head Q ;; a).
Proof.
  xcf. intros [f r] q. introv [H M] NE. xgo; rew_list in H.
  rewrite~ M in H. inverts~ H.
  inverts~ H.
Qed.

Hint Extern 1 (RegisterSpec head) => Provide head_spec.

Lemma tail_spec :
  RepSpec tail (Q;queue a) |R>> 
     Q <> nil -> R (is_tail Q ;; queue a).
Proof.
  xcf. intros [f r] q. introv [H M] NE. xmatch.
  xgo. rewrite~ M in H. inverts~ H.
  inverts H. xgo~. ximpl~.
Qed.

Hint Extern 1 (RegisterSpec tail) => Provide tail_spec.

End Polymorphic.

End BatchedQueueSpec.