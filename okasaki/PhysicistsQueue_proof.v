Set Implicit Arguments.
Require Import FuncTactics LibCore.
Require Import QueueSig_ml QueueSig_proof.
Require Import PhysicistsQueue_ml.

Module PhysicistsQueueSpec <: QueueSigSpec.

(** instantiations *)

Module Import Q <: MLQueue := MLPhysicistsQueue.

(** invariant *)

Definition inv (wok rok : bool) `{Rep a A} (q:queue a) (Q:list A) :=
  let '(w,lenf,f,lenr,r) := q in exists g,
     rep (f ++ rev r) Q
  /\ f = w ++ g 
  /\ lenf = length f
  /\ lenr = length r
  /\ lenr <= lenf + (if rok then 0 else 1)
  /\ if wok then (w = nil -> f = nil) else True.

(** model *)

Global Instance queue_rep `{Rep a A} : Rep (queue a) (list A).
Proof. 
  intros. apply (Build_Rep (inv true true)).
  destruct x as ((((w,lenf),f),lenr),r).
  introv KX KY. intuit KX. intuit KY. prove_rep.
Defined.

(** automation *)

Hint Constructors Forall2.
Hint Resolve Forall2_last.
Hint Unfold inv.

Ltac auto_tilde ::= auto 8 with maths.
Ltac auto_star ::= eauto with maths.

(** useful facts *)

Section Polymorphic.
Variables (a A : Type) (RA:Rep a A).

Lemma rep_not_nil : forall w lenf f lenr r Q,
  rep (w,lenf,f,lenr,r) Q -> Q <> nil -> w <> nil.
Proof.
  introv (g&RQ&DF&LF&LR&LE&LZ) NE NZ. destruct Q. false.
  inverts RQ. specializes~ LZ __. subst.
  destruct (app_eq_nil_inv LZ). subst g.
  destruct r. false. rew_length in LE. math.
Qed.

(** verification *)

Lemma empty_spec : 
  rep (@empty a) (@nil A).
Proof.
  generalizes RA A. apply (empty_cf a). xgo.
  intros. exists (@nil a). rew_list~.
Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma is_empty_spec : 
  RepTotal is_empty (Q;queue a) >> bool_of (Q = nil).
Proof.
  xcf. intros ((((w,lenf),f),lenr),r) Q (g&RQ&DF&LF&LR&LE&LZ). xgo.
  unfolds. iff Z; fold_prop.
  subst f lenf. rew_length in LF.
  rewrite~ (@length_zero_inv _ r) in RQ.
   rewrite~ (@length_zero_inv _ g) in RQ.
   rewrite~ (@length_zero_inv _ w) in RQ.
   inverts~ RQ.
  subst Q. inverts RQ. destruct (nil_eq_app_rev_inv H0).
   rewrite~ H in LF.
Qed.

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Lemma checkw_spec : 
  Spec checkw (q:queue a) |R>>
    forall Q, inv false true q Q ->
    R (Q ;- queue a).
Proof.
  xcf. intros ((((w,lenf),f),lenr),r) Q K. xgo.
  intuit K. exists (@nil a). rew_list in *. substs~.
  intuit K. exists x. splits~. intro_subst_hyp. false~ C. 
Qed.

Hint Extern 1 (RegisterSpec checkw) => Provide checkw_spec.

Lemma check_spec : 
  Spec check (q:queue a) |R>>
    forall Q, inv false false q Q -> R (Q ;- queue a).
Proof.
  xcf. intros ((((w,lenf),f),lenr),r) Q (g&RQ&DF&LF&LR&LE&_).
  xgo; try ximpl; eauto.
  subst. exists g. splits*. 
  apply refl_equal.
  subst f'. exists (rev r). rew_list~.
Qed.

Hint Extern 1 (RegisterSpec check) => Provide check_spec.

Lemma snoc_spec : 
  RepTotal snoc (Q;queue a) (X;a) >> (Q & X) ;- queue a.
Proof.
  xcf. intros ((((w,lenf),f),lenr),r) x. introv (g&RQ) RX.
  xgo~; try ximpl; eauto. intuit. exists g. splits~.
   rewrite~ app_rev_cons. rew_length~.
Qed.

Hint Extern 1 (RegisterSpec snoc) => Provide snoc_spec.

Lemma head_spec : 
  RepSpec head (Q;queue a) |R>>
     Q <> nil -> R (is_head Q ;; a).
Proof.
  xcf. intros ((((w,lenf),f),lenr),r) Q RQ NE.
  forwards*: rep_not_nil. destruct Q. false. intuit RQ.
  subst f. xgo. inverts* H0.
Qed.

Hint Extern 1 (RegisterSpec head) => Provide head_spec.

Lemma tail_spec :
  RepSpec tail (Q;queue a) |R>> 
     Q <> nil -> R (is_tail Q ;; queue a).
Proof.
  xcf. intros ((((w,lenf),f),lenr),r) Q RQ NE.
  xmatch.
  xgo. forwards*: rep_not_nil.
  xcleanpat. intuit RQ. subst f. rew_list in *. inverts H.
   xapp_noapply. fapplys HR; eauto. ximpl*.
   xapp~. subst. exists x0. splits~. rewrite* app_assoc. rew_list~.
   ximpl*.
Qed.

Hint Extern 1 (RegisterSpec tail) => Provide tail_spec.

End Polymorphic.

End PhysicistsQueueSpec.