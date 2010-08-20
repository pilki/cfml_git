Set Implicit Arguments.
Require Import CFPrim ListIterators_ml LibList.
Module LI := ListIterators_ml.



(********************************************************************)
(** Spec map simple *)

Hint Constructors Forall2.

Lemma map_spec : forall a b,
  Spec LI.map (f:val) (l:list a) |R>> forall A B L (T:htype A a) (U:htype B b) (I:A->B->Prop),
    (Spec f x |R'>> forall X, In X L -> keep R' (x ~> T X) (fun y => Hexists Y, (y ~> U Y) \* [I X Y])) ->
    keep R (l ~> List T L) (fun m => Hexists M, m ~> List U M \* [Forall2 I L M]).
Proof.
  intros. xinduction (unproj22 val (@list_sub a)).
  xcf. intros f l IH. introv Hf. (* todo: avec xintros ? *)
  xmatch.
  (* base case *)
  xret.
  hchange (@unfocus_nil' _ L _ T). hextract. subst L. hsimpl (@nil B).
    hchange (@focus_nil _ _ U). hchange (@focus_nil _ _ T). hsimpl.
    auto.
  (* rec case *)
  xchange (@focus_cons' _ a0 l0). xextract as X L' E. subst L.
  xapp. simple~.
  intros Y IXY. xlet as m. xapp.
    simpl. auto.
    xweaken. intros_all. applys H1. apply H0. auto. (* clean *)
     simpl. intros_all. apply H1. auto.
    xret. hextract as M ILM. hsimpl (Y::M).
      hchange (@unfocus_cons _ r m _ Y M). 
       hchange (@unfocus_cons _ a0 l0 _ X L'). hsimpl.
      auto.
Qed.
  












