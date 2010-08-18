Set Implicit Arguments.
Require Import CFPrim Loops_ml.


(********************************************************************)
(* ** For loops *)

Lemma loop_for_spec : 
  Spec loop_for a b body |R>>
       (a > (b)%Z -> R [] (#[])) 
    /\ (a <= (b)%Z -> forall I,
          (Spec body i |R>> a <= i <= b -> R (I i) (# I(i+1))) ->
          R (I a) (# I ((b)%Z+1))).
Proof.
  xcf. intros. split; intros Cmp. 
  (* case a > b *)
  xfun (fun f => Spec f i |R>> i > b -> R [] (#[])).
    intros Gt. xif. math. xret. xsimpl.
  xapp~. hsimpl.
  (* case a <= b *)
  intros I Hbody.
  xfun_induction (fun f => Spec f i |R>> a <= i <= b+1 -> R (I i) (# I (b+1))) (upto (b+1)).
    intros IH Le. xif.
      xapp. math.
       xapp; auto with maths.
      xret. math_rewrite (i = b+1). auto.
  xapp. math. xsimpl.
Qed.

(* details of xfun_induction:  
  xfun_noxbody (fun f => Spec f i |R>> a <= i <= b+1 -> R (I i) (# I (b+1))).
    apply (spec_induction_1_noheap (lt:=upto (b+1))). prove_wf. xbody. 
*)    

(********************************************************************)
(* ** While loops *)

Lemma loop_while : 
  Spec loop_while cond body |R>>
    forall A (I:A->hprop) (J:A->bool->hprop) (lt:binary A) X0 (Q:unit->hprop),
      wf lt -> 
      (Spec cond () |R'>> forall X, R' (I X) (J X)) ->
      (Spec body () |R'>> forall X, R' (J X true) (# Hexists Y, (I Y) \* [lt Y X])) ->
      (forall X, J X false ==> Q tt) ->
      R (I X0) Q.
Proof.
  xcf. introv W Hc Hb Ho.
  xfun_induction_heap (fun f => Spec f () |R>> forall X, R (I X) Q) lt.
    intros IH. xlet. xapp y. xif.
      xseq. xapp y. xextract. intros y' Lt. xapp~ y'. hsimpl.
      xret. destruct _x1; tryfalse. hchange (Ho y). hsimpl.
  xapp X0. hsimpl.
Qed.

(*
xfun_noxbody (fun f => Spec f () |R>> forall X, R (I X) Q).
    apply (spec_induction_1_noarg (lt:=lt)). auto. xisspec. xbody.
*)


(*TODO
Notation "'While' Q1 'Do' Q2 'Done'" :=
  (!While (fun H Q => exists A, exists I, exists J, exists R,
       wf R 
     /\ (exists x, H ==> I x)
     /\ (forall x, Q1 (I x) (J x)
                /\ Q2 (J x true) (# Hexists y, (I y) \* [R y x])
                /\ (J x false) ==> Q1 tt)
  (at level 69) : charac.

--
tactic : if J is not of type "A->bool->hprop"
then J' may be of type "A->bool" or "A->Prop" and then J is
   fun X b => (b = bool_of (J' X)) \* (I X)
--
*)



