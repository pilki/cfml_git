Set Implicit Arguments.
Require Import FuncTactics LibCore.
Require Import QueueSig_ml QueueSig_proof.
Require Import PhysicistsQueue_ml.


Module PhysicistsQueueSpec <: QueueSigSpec.

(** instantiations *)

Module Import Q <: MLQueue := MLPhysicistsQueue.
Import MLPhysicistsQueue.

(** invariant *)

Definition inv (wok rok:bool) `{Rep a_ A} (q:queue a_) (Q:list A) :=
  let '(w,lenf,f,lenr,r) := q in exists g,
     Forall2 rep (f ++ rev r) Q
  /\ f = w ++ g 
  /\ lenf = length f
  /\ lenr = length r
  /\ lenr <= lenf + (if rok then 0 else 1)
  /\ if wok then (w = nil -> f = nil) else True.

Global Instance repr `{Rep a_ A} : Rep (queue a_) (list A) :=
  inv true true.

(** automation *)

Hint Constructors Forall2.
Hint Resolve Forall2_last.
Hint Unfold is_head is_tail.
Hint Extern 1 (@rep (queue _) _ _ _ _) => simpl.
Hint Unfold inv.

Ltac auto_tilde ::= auto 8 with maths.

(** useful facts *)

(** verification *)

Section Polymorphic.
Variables (a_ A : Type) (RA:Rep a_ A).

Lemma empty_spec : 
  rep (@empty a_) (@nil A).
Proof.
  generalizes RA A. apply (empty_cf a_). xgo.
  intros. exists (@nil a_). rew_list~.
Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma is_empty_spec : 
  RepTotal is_empty (Q;queue a_) >> bool_of (Q = nil).
Proof.
  xcf. intros ((((w,lenf),f),lenr),r) Q (g&RQ&DF&LF&LR&LE&LZ). xgo.
  unfolds. extens. iff Z; fold_prop.
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
  Spec checkw (q:queue a_) |R>>
    forall Q, inv false true q Q ->
    R (Q ; queue a_).
Proof.
  xcf. intros ((((w,lenf),f),lenr),r) Q K. xgo.
  intuit K. exists (@nil a_). rew_list in *. substs~.
  intuit K. exists x. splits~. intro_subst_hyp. false~ C. 
Qed.

Hint Extern 1 (RegisterSpec checkw) => Provide checkw_spec.

Hint Rewrite length_rev : rew_list.

Lemma check_spec : 
  Spec check (q:queue a_) |R>>
    forall Q, inv false false q Q ->
    R (Q ; queue a_).
Proof.
  xcf. intros ((((w,lenf),f),lenr),r) Q (g&RQ&DF&LF&LR&LE&_).
    (*todo: bug si l'hypothèse True est ds le contexte *)
  xgo; ximpl.
  subst. exists g. splits*. math.
  apply refl_equal.
  subst f'. exists (rev r). rew_list~.
Qed.

Hint Extern 1 (RegisterSpec check) => Provide check_spec.

Lemma snoc_spec : 
  RepTotal snoc (Q;queue a_) (X;a_) >> (Q & X) ; queue a_.
Proof.
  xcf. intros ((((w,lenf),f),lenr),r) x. introv (g&RQ) RX.
  xgo~; ximpl. intuit. exists g. rew_list. splits~.
   rewrite~ <- app_assoc.
Qed.

Hint Extern 1 (RegisterSpec snoc) => Provide snoc_spec.

Lemma rep_not_nil : forall w lenf f lenr r Q,
  rep (w,lenf,f,lenr,r) Q -> Q <> nil -> w <> nil.
Proof.
  introv (g&RQ&DF&LF&LR&LE&LZ) NE NZ. destruct Q. false.
  inverts RQ. specializes~ LZ __. subst.
  destruct (app_eq_nil_inv LZ). subst g.
  destruct r. false. rew_length in LE. math.
Qed.


Lemma head_spec : 
  RepSpec head (Q;queue a_) |R>>
     Q <> (@nil A) -> R (is_head Q ;; a_).
Proof.
  xcf. intros ((((w,lenf),f),lenr),r) Q RQ NE.
  forwards*: rep_not_nil. destruct Q. false. intuit RQ.
  subst f. xgo. inverts* H0.
Qed.

Hint Extern 1 (RegisterSpec head) => Provide head_spec.

Lemma tail_spec :
  RepSpec tail (Q;queue a_) |R>> 
     Q <> nil -> R (is_tail Q ;; queue a_).
Proof.
  xcf. intros ((((w,lenf),f),lenr),r) Q RQ NE.
  forwards*: rep_not_nil. destruct Q. false. intuit RQ.
  subst f. xmatch. xcleanpat. rew_list in *. xapp~. calc_partial_eq tt.
  subst. xapp~. (* todo: pb de xauto qui fait reflequal *)
  inverts H0. exists x. rewrite app_assoc. splits*. rew_length~. math.
  ximpl as l Hl. eauto. (* todo: [ximpl*] *)
Qed.

Hint Extern 1 (RegisterSpec tail) => Provide tail_spec.

End Polymorphic.


