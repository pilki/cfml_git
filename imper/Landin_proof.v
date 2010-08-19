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



(********************************************************************)
(* ** Landin's knot *)

Lemma landin_spec : forall A B,
  Spec landin bigf |Rmain>>
    forall C (lt:binary (C*A)) (Wf: wf lt) (L:C->A->~~B->Prop),
    (forall I:hprop, Spec bigf f x |R>> forall y,
        (Spec f x' |R'>> forall y', lt (y',x') (y,x) -> sframe I (L y') x' R') ->
        sframe I (L y) x R) ->
    Rmain [] (fun f => Hexists I, I \* 
            [Spec f x |R>> forall y, sframe I (L y) x R]).
Proof.
  xcf. introv W Hbigf.
  xapp.
  (* verification of G *)
  xfun (fun g => Spec g x |R>> forall (K:A->~~B->Prop) f',
     is_spec_1 K ->
     let K' := sframe (r ~> Ref Id f') K in
     spec_1 K' f' -> 
     K' x R).
     intros_all. applys~ sframe_is_spec_1.
     intros SK K' Sf'. unfold K', sframe.
     applys SK. apply (spec_elim_1 Sf' x).
     intros H Q Happ. xapp. intro_subst. 
     rewrite star_comm. apply Happ.
  (* verification of f *)
  xfun 
    


lets: spec_elim_1.

Qed.





