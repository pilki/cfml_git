Set Implicit Arguments.
Require Import FuncTactics LibCore.
Require Import QueueSig_ml QueueSig_proof.
Require Import RealTimeQueue_ml.


Module RealTimeQueueSpec <: QueueSigSpec.

(** instantiations *)

Module Import Q <: MLQueue := MLRealTimeQueue.
Import MLRealTimeQueue.

(** invariant *)

Definition inv (d:int) `{Rep a_ A} (q:queue a_) (Q:list A) :=
  let '(f,r,s) := q in 
     Forall2 rep (f ++ rev r) Q
  /\ length s = length f - length r + d :> int.

Global Instance queue_rep `{Rep a_ A} : Rep (queue a_) (list A) :=
  inv 0.

(** automation *)

Hint Constructors Forall2.
Hint Resolve Forall2_last.
Hint Unfold is_head is_tail.
Hint Extern 1 (@rep _ _ _ _ _) => simpl.
Hint Unfold inv.

Ltac auto_tilde ::= auto with maths.


Section Polymorphic.
Variables (a_ A : Type) (RA:Rep a_ A).
Implicit Types Q : list A.

(** useful facts *)

Lemma repr_nil_inv : forall r s Q,
  rep (nil,r,s) Q -> Q = nil.
Proof.
  introv [H M]. rew_list in *. 
  rewrite~ (@length_zero_inv _ r) in H. inverts~ H.
Qed.

Lemma repr_nil : forall f r s,
  rep (f,r,s) nil -> f = nil.
Proof. introv [H M]. destruct f. auto. inverts H. Qed.

(** verification *)

Lemma empty_spec : 
  rep (@empty a_) (@nil A).
Proof.
  generalizes RA A. apply (empty_cf a_). xgo.
  intros. simpl. rew_list*.
Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma is_empty_spec : 
  RepTotal is_empty (Q;queue a_) >> bool_of (Q = nil).
Proof.
  xcf. intros ((f,r),s) Q RQ. xgo.
  apply* repr_nil_inv. 
  intro_subst_hyp. false C. rewrite~ (repr_nil RQ).
Qed.

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Lemma rotate_spec : 
  Spec rotate (q:queue a_) |R>>
    let '(f,r,s) := q in (* todo: bug dispaly let '(f,r,s) := q in *)
    length r = length f + 1 :> int ->
    R (fun o => o = f ++ rev r ++ s).
Proof.
  intros.
  sets m: (unproj31 (list a_) (list a_) (@list_sub a_)).
  xinduction m. unfold m. prove_wf. (* todo: tactic *)
  xcf. 
  intros_all. destruct x as ((x1,x2),x3). auto*.
  intros ((f,r),s) IH L. xgo. 
  rew_list in *. rewrite~ (@length_zero_inv _ _p0).
  unfolds~.
  rew_list~ in L.
  subst _x1. rew_list~.
  destruct f; destruct r; rew_length in L.
   math. applys* C. math. applys* C0.
Qed.

Hint Extern 1 (RegisterSpec rotate) => Provide rotate_spec.

Lemma exec_spec : 
  Spec exec (q:queue a_) |R>>
    forall Q, inv 1 q Q -> 
    R (Q ; queue a_).
Proof.
  xcf. intros ((f0,r0),s0) l [H M].
  xgo; rew_length in M; auto~.
  substs f'. constructor; rew_list~.
Qed.

Hint Extern 1 (RegisterSpec exec) => Provide exec_spec.

Lemma snoc_spec : 
  RepTotal snoc (Q;queue a_) (X;a_) >> (Q & X) ; queue a_.
Proof.
  xcf. introv RQ RX. xmatch. xapp (Q & X). inverts RQ. constructor.
  rew_list. rewrite~ <- app_assoc.
  rew_length~.
Qed.

Hint Extern 1 (RegisterSpec snoc) => Provide snoc_spec.

Lemma head_spec : 
  RepSpec head (Q;queue a_) |R>>
     Q <> (@nil A) -> R (is_head Q ;; a_).
Proof.
  xcf. intros ((f,r),s) Q. introv RQ NE. xgo.
  false (repr_nil_inv RQ).
  destruct RQ as [H M]. rew_list in H. inverts* H.
Qed.

Hint Extern 1 (RegisterSpec head) => Provide head_spec.

Lemma tail_spec :
  RepSpec tail (Q;queue a_) |R>> 
     Q <> nil -> R (is_tail Q ;; queue a_).
Proof.
  xcf. intros ((f,r),s) Q. introv RQ NE. xmatch.
  false (repr_nil_inv RQ).
  destruct RQ as [H M]. rew_list in *.
  inverts H. xapp~ l2. intros_all*. (* todo: improve *)
Qed.

Hint Extern 1 (RegisterSpec tail) => Provide tail_spec.

End Polymorphic.

End RealTimeQueueSpec.





