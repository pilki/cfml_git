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
  xfun_noxbody (fun f => Spec f i |R>> a <= i <= b+1 -> R (I i) (# I (b+1))).
    apply (spec_induction_1_noheap (lt:=upto (b+1))). prove_wf.
    xbody. intros IH Le. 
    xif.
      xapp. math.
       xapp; auto with maths.
      xret. math_rewrite (i = b+1). auto.
  xapp. math. xsimpl.
Qed.
    

(********************************************************************)
(* ** While loops *)




(*
Notation "'For' i '=' a 'To' b 'Do' Q1 'Done'" :=
  (!For (fun H Q => (a > (b)%Z -> H ==> (Q tt)) /\ (a <= (b)%Z -> exists H', exists I,
       (H ==> I a \* H') 
    /\ (forall i, a <= i /\ i <= (b)%Z -> Q1 (I i) (# I(i+1))) 
    /\ (I ((b)%Z+1) \* H' ==> Q tt))))
  (at level 69, i ident) : charac.

Notation "'While' Q1 'Do' Q2 'Done'" :=
  (!While (fun H Q => exists H', exists A, exists I, exists R,
       wf R 
     /\ (exists x, H ==> I x \* H')
     /\ (forall x, local (fun Hl Ql => exists Q', 
            Q1 Hl Q'
         /\ Q2 (Q' true) (# Hexists y, (I y) \* [R y x])
         /\ (Q' false \* H' ==> Ql tt)) (I x) Q)))
  (at level 69) : charac.
*)