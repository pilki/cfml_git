Set Implicit Arguments.
Require Import CFPrim Swap_ml.


(* todo: swap for strong references *)

(********************************************************************)
(* ** Swap for non-aliased references *)

Lemma swap_spec : forall a,
  Spec swap i j |R>> forall A (T:htype A a) X Y,
   R (i ~> Ref T X \* j ~> Ref T Y)  
   (# i ~> Ref T Y \* j ~> Ref T X).
Proof.
  xcf. intros.
  xchange (@focus_ref i). xextract as x.
  xchange (@focus_ref j). xextract as y.
  xapp. intro_subst.
  xapp. intro_subst.
  xapp. xapp.
  intros _. (* todo avec le hchange *)  
  hchange (@unfocus_ref i _ y).
  hchange (@unfocus_ref j _ x).
  hsimpl.
Qed.

Lemma swap_spec' : forall a,
  Spec swap i j |R>> forall A (T:htype A a) X,
    i = j -> keep R (i ~> Ref T X) (#[]).
Proof.
  xcf. introv E. subst j.
  xchange (@focus_ref i). xextract as x.
  xapp. intro_subst.
  xapp. intro_subst.
  xapp. xapp. intros _.
  hchange (@unfocus_ref i _ x).
  hsimpl. 
Qed.




(********************************************************************)
(* ** Swap for strong aliased references *)

(*
Lemma swap_spec : forall a b,
  Spec swap i j |R>> forall A B (T:htype A a) (U:htype B b) X Y,
   R (i ~> Ref T X \* j ~> Ref U Y)  
   (# i ~> Ref U Y \* j ~> Ref T X).
Proof.
  xcf. intros.
  xchange (@focus_ref i). xextract as x.
  xchange (@focus_ref j). xextract as y.
  xapp. intro_subst.
  xapp. intro_subst.


*)


(* 
spec alias () |R>>
  R [] (fun p => let (n,a) := p in  (*todo:notation*)
        [n = 1] \* a ~> Ref (Ref Id) 3)
*)
     
