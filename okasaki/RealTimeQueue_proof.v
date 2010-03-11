Set Implicit Arguments.
Require Import FuncTactics LibCore.
Require Import QueueSig_ml QueueSig_proof.
Require Import RealTimeQueue_ml.

Module RealTimeQueueSpec <: QueueSigSpec.

(** instantiations *)

Module Import Q <: MLQueue := MLRealTimeQueue.
Import MLRealTimeQueue.

(** invariant *)

Definition inv (d:int) `{Rep a A} (q:queue a) (Q:list A) :=
  let '(f,r,s) := q in 
     rep (f ++ rev r) Q
  /\ length s = length f - length r + d :> int.

Global Instance queue_rep `{Rep a A} : Rep (queue a) (list A).
Proof. 
  intros. apply (Build_Rep (inv 0)).
  destruct x as ((f,r),s).
  introv KX KY. intuit KX. intuit KY. prove_rep.
Defined.

(** automation *)

Hint Constructors Forall2.
Hint Resolve Forall2_last.
Hint Extern 1 (@rep _ _ _ _ _) => simpl.
Hint Unfold inv.

Ltac auto_tilde ::= auto with maths.

(** useful facts *)

Section Polymorphic.
Variables (a A : Type) (RA:Rep a A).
Implicit Types Q : list A.

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
  rep (@empty a) (@nil A).
Proof.
  generalizes RA A. apply (empty_cf a). xgo.
  intros. simpl. rew_list*.
Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma is_empty_spec : 
  RepTotal is_empty (Q;queue a) >> bool_of (Q = nil).
Proof.
  xcf. intros ((f,r),s) Q RQ. xgo.
  apply* repr_nil_inv. 
  intro_subst_hyp. false C. rewrite~ (repr_nil RQ).
Qed.

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Lemma rotate_spec : 
  Spec rotate (q:queue a) |R>>
    let '(f,r,s) := q in (* todo: bug dispaly let '(f,r,s) := q in *)
    length r = length f + 1 :> int ->
    R (fun o => o = f ++ rev r ++ s).
Proof.
  intros.
  sets m: (unproj31 (list a) (list a) (@list_sub a)).
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
  Spec exec (q:queue a) |R>>
    forall Q, inv 1 q Q -> 
    R (Q ; queue a).
Proof.
  xcf. intros ((f0,r0),s0) l [H M].
  xgo; rew_length in M; auto~.
  substs f'. constructor; rew_list~.
Qed.

Hint Extern 1 (RegisterSpec exec) => Provide exec_spec.

Lemma snoc_spec : 
  RepTotal snoc (Q;queue a) (X;a) >> (Q & X) ; queue a.
Proof.
  xcf. introv RQ RX. xmatch. xapp (Q & X). inverts RQ. constructor.
  rew_list. rewrite~ <- app_assoc.
  rew_length~.
Qed.

Hint Extern 1 (RegisterSpec snoc) => Provide snoc_spec.

Lemma head_spec : 
  RepSpec head (Q;queue a) |R>>
     Q <> nil -> R (is_head Q ;; a).
Proof.
  xcf. intros ((f,r),s) Q. introv RQ NE. xgo.
  false (repr_nil_inv RQ).
  destruct RQ as [H M]. rew_list in H. inverts* H.
Qed.

Hint Extern 1 (RegisterSpec head) => Provide head_spec.

Lemma tail_spec :
  RepSpec tail (Q;queue a) |R>> 
     Q <> nil -> R (is_tail Q ;; queue a).
Proof.
  xcf. intros ((f,r),s) Q. introv RQ NE. xmatch.
  false (repr_nil_inv RQ).
  destruct RQ as [H M]. rew_list in *.
  inverts H. xapp~ l2. intros_all*. (* todo: improve *)
Qed.

Hint Extern 1 (RegisterSpec tail) => Provide tail_spec.

End Polymorphic.

End RealTimeQueueSpec.





