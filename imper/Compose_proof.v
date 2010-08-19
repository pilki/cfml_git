Set Implicit Arguments.
Require Import CFPrim Compose_ml.


(********************************************************************)
(* ** A naive statement for Compose *)

Lemma compose_spec_direct : forall A B C,
  Spec compose (g:val) (f:val) (x:A) |R>>
     forall H (Q:B->hprop) (Q':C->hprop),
     app_1 f x H Q ->
     (forall y, app_1 g y (Q y) Q') ->
     R H Q'.
Proof.
  xcf. introv Hf Hg. xlet as y. apply Hf. apply Hg.
Qed.

(*
Lemma spec_elim_1_1 : forall A1 B (K: A1 -> ~~B -> Prop) f,
  spec_1 K f -> forall x1 (H : hprop) (Q : B->hprop),
  (forall R, is_local R -> K x1 R -> R H Q) ->
  app_1 f x1 H Q.
*)

(********************************************************************)
(* ** Verification of Compose *)

Lemma compose_spec : forall A B C,
  Spec compose g f x |R>>
     forall (Kf : A->~~B->Prop) (Kg : B->~~C->Prop),
     Spec_1 f Kf -> Spec_1 g Kg ->
     forall Q H Q',
     (forall R', is_local R' -> Kf x R' -> R' H Q) ->
     (forall y R', is_local R' -> Kg y R' -> R' (Q y) Q') ->
     R H Q'.
Proof.
  xcf. introv Hf Hg. introv Mf Mg.
  xlet as y.
  apply Mf. xlocal. apply (proj2 Hf).
  apply Mg. xlocal. apply (proj2 Hg).
Qed.
  
Hint Extern 1 (RegisterSpec compose) => Provide compose_spec.

(********************************************************************)
(*

Lemma compose_spec_1' : forall A B C,
  Spec compose g f x |R>>
     forall (Kf : A->~~B->Prop) (Kg : B->~~C->Prop),
     Spec_1 f Kf -> Spec_1 g Kg ->
     Kf x (fun H Q => forall Q',
          (forall y R, is_local R -> Kg y R -> R (Q y) Q') ->
          R H Q').
Proof.
  intros. xweaken compose_spec_1. skip.
  simpl. intros g f x R LR. intros M. introv Sf Sg.
  specializes M Sf Sg.
  applys (proj1 Sf). apply (spec_elim_1 Sf x).
  intros H Q Af. intros Q' N.
  applys M.
    intros R' LR' MR'.
    apply N.
 

Lemma compose_spec_2 : forall A B C,
  Spec compose g f x |R>>
     forall (Kf : A->~~B->Prop) (Kg : B->~~C->Prop),
     Spec_1 f Kf -> Spec_1 g Kg ->
     forall Q H Q',
     (forall R', is_local R' -> Kf x R' -> R' H Q) ->
     (forall y R', is_local R' -> Kg y R' -> R' (Q y) Q') ->
     R H Q'.
Proof.
  xcf. introv Hf Hg. introv Mf Mg.
  xlet as y.
  apply Mf. xlocal. apply (proj2 Hf).
  apply Mg. xlocal. apply (proj2 Hg).
Qed.

Def R' H Q :=
  R H Q'


     Kf x (fun H Q => forall Q',
          (forall y R, is_local R -> Kg y R -> R (Q y) Q') ->
          R H Q').
*)


(********************************************************************)
(* ** A test case for compose *)

Lemma incr_ret_spec : 
   Spec incr_ret r |R>> forall n, n >= 0 ->
      R (r ~> Ref Id n) (\= r \*+ r ~> Ref Id (n+1)).
Proof.
  xcf. intros. xapp. xret.
Qed.

Lemma decr_ret_spec : 
   Spec decr_ret r |R>> forall n, n > 0 ->
      R (r ~> Ref Id n) (\= r \*+ r ~> Ref Id (n-1)).
Proof.
  xcf. intros. xapp. xret.
Qed.

Lemma test_spec :
  Spec test r |R>> forall n, n >= 0 ->
    R (r ~> Ref Id n) (\= r \*+ r ~> Ref Id n).
Proof.
  xcf. intros. xapp incr_ret_spec decr_ret_spec; try clears R. (* todo *)
  intros R LR HR. apply~ (HR n).
  simpl. intros y R LR HR.
   apply~ CFHeaps.local_intro_prop. intro_subst.
   apply HR. math.
  hsimpl.
  intros r. hsimpl. math.
Qed.



(********************************************************************) 
(********************************************************************)
(* ** Verification of Compose *)

Lemma compose_spec : forall A B C,
  Spec compose g f x |R>>
     forall (Kf : A->~~B->Prop) (Kg : B->~~C->Prop),
     Spec_1 f Kf -> Spec_1 g Kg ->
     Kf x (fun H Q => forall Q',
          (forall y R, is_local R -> Kg y R -> R (Q y) Q') ->
          R H Q').
Proof.
  xcf. skip.
  introv Hf Hg.
  applys (proj1 Hf). apply (spec_elim_1 Hf).
  intros H Q Pf Q' Mg.  
  xlet as y. apply Pf.
  xuntag. apply Mg. xlocal. apply (proj2 Hg).
Qed.

Hint Extern 1 (RegisterSpec compose) => Provide compose_spec.


(********************************************************************)
(* ** A test case for compose *)

Lemma incr_ret_spec : 
   Spec incr_ret r |R>> forall n, n >= 0 ->
      R (r ~> Ref Id n) (\= r \*+ r ~> Ref Id (n+1)).
Proof.
  xcf. intros. xapp. xret.
Qed.

Lemma decr_ret_spec : 
   Spec decr_ret r |R>> forall n, n > 0 ->
      R (r ~> Ref Id n) (\= r \*+ r ~> Ref Id (n-1)).
Proof.
  xcf. intros. xapp. xret.
Qed.

Lemma test_spec :
  Spec test r |R>> forall n, n >= 0 ->
    R (r ~> Ref Id n) (\= r \*+ r ~> Ref Id n).
Proof.
  xcf. intros. xapp incr_ret_spec decr_ret_spec. auto.
  simpl. intros y R LR HR. 
  apply~ CFHeaps.local_intro_prop. intro_subst.
  apply HR. math.
  intros r. hsimpl. math.
Qed.



(********************************************************************)
(* ** Remark: a simpler statement for Compose *)

Lemma compose_spec' : forall A B C,
  Spec compose g f x |R>>
     forall (Kf : A->~~B->Prop),
     Spec_1 f Kf -> 
     Kf x (fun H Q => forall (Q'':C->hprop),
          (forall y:B, app_1 g y (Q y) Q'') ->
          R H Q'').
Proof.
  xcf. skip. (* todo *)
  introv Hf.
  applys (proj1 Hf). apply (spec_elim_1 Hf).
  intros H Q Pf Q'' Mg.  
  xlet as y. apply Pf. apply Mg.
Qed.











