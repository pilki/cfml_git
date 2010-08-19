Set Implicit Arguments.
Require Import CFPrim Landin_ml.


Definition sframe (I:hprop) A B (K:A->~~B->Prop) :=
  fun x R => K x (fun H Q => R (H \* I) (Q \*+ I)). 

Lemma sframe_is_spec_1 : forall (I:hprop) A B (K:A->~~B->Prop),
  is_spec_1 K -> is_spec_1 (sframe I K).
Proof.
  introv SK. introv M1 WR. 
  applys SK. apply M1. 
  intros H Q MR. applys~ WR.
Qed.

Ltac xisspec_core ::=
  solve [ 
    let K := fresh "TEMP" in
    lets K: sframe_is_spec_1; unfold is_spec_1, is_spec_0 in *;
    intros_all; unfolds rel_le, pred_le; auto; auto* ].



(********************************************************************)
(* ** Landin's knot *)

Lemma landin_spec : forall A B,
  Spec landin bigf |Rmain>>
    forall C (lt:binary (C*A)) (Wf: wf lt) (L:C->A->~~B->Prop),
    (forall y, is_spec_1 (L y)) ->
    (forall I:hprop, Spec bigf f x |R>> forall y,
        (Spec f x' |R'>> forall y', lt (y',x') (y,x) -> sframe I (L y') x' R') ->
        sframe I (L y) x R) ->
    Rmain [] (fun f => Hexists I, I \* 
            [Spec f x |R>> forall y, sframe I (L y) x R]).
Proof.
  xcf. introv W Is Hbigf. xapp.
  (* verification of G *)
  xfun (fun g => Spec g x |R>> forall (K:A->~~B->Prop) f',
     is_spec_1 K -> let K' := sframe (r ~> Ref Id f') K in
     spec_1 K' f' -> K' x R). 
     intros SK K' Sf'. unfold K', sframe.
     applys SK. apply (spec_elim_1 Sf' x).
     intros H Q Happ. xapp. intro_subst. 
     rewrite star_comm. apply Happ.
  (* verification of f *)
  xfun (fun f => Spec f x |R>> forall y f',
     let I := (r ~> Ref Id f') in
     (Spec f' x' |R'>> forall y', lt (y',x') (y,x) -> sframe I (L y') x' R') ->
     sframe I (L y) x R).
    intros I Sf'. applys Is.
      apply (spec_elim_2 (Hbigf I) g x y). xweaken.
       simpl. intros x' R LR SK. unfold sframe in SK|-*.
       apply SK; [ xisspec | apply Sf' ].
      intros H Q Happ. apply Happ.
  (* tight the knot *)
  xapp. xret. hsimpl (r ~> Ref Id f).
  (* prove the spec of the result by induction *)
  xinduction_heap W. xweaken~.
Qed.





(*bin*)
 (* intros_all. applys~ sframe_is_spec_1.*)
 (*ntros_all. applys sframe_is_spec_1. auto. apply H. auto.*)
(*intros_all. applys sframe_is_spec_1. auto. apply H. auto. auto.*)



