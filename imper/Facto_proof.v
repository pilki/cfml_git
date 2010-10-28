Set Implicit Arguments.
Require Import CFLib Facto_ml.

Ltac auto_tilde ::= auto with maths.


(********************************************************************)
(* ** Mathematical factorial function *)

Parameter fact : int -> int.
Parameter fact_zero : fact 0 = 1.
Parameter fact_succ : forall n, n > 0 ->
  fact n = n * fact (n-1).
Lemma fact_one : fact 1 = 1.
Proof. rewrite~ fact_succ. math_rewrite (1-1=0). rewrite~ fact_zero. Qed.


(********************************************************************)
(* ** Factorial function: recursive implementation *)

Lemma facto_rec_spec : Spec facto_rec n |R>>
  n >= 0 -> R [] (\= fact n).
Proof.
  apply (spec_induction_1_noheap (lt:=downto 0)). prove_wf.
  xcf. intros. xif. xret.
  xif_after. xret. xsimpl. rewrite~ fact_zero.
  xif_after. xapp~. intro_subst. xret. hsimpl. rewrite~ <- fact_succ.
Qed.


(********************************************************************)
(* ** Factorial function: for-loop implementation *)

Lemma facto_for_spec : Spec facto_for n |R>>
  n >= 0 -> R [] (\= fact n).
Proof.
  xcf. intros. xapp. xseq . xfor.
  xgeneralize (forall i, 0 < i <= n+1 -> S i (r ~~> fact (i-1)) (# r ~~> fact n)).
    xapply_local~ Inv. hsimpl. simpl. rewrite~ fact_zero. 
    intros i. induction_wf IH: (int_upto_wf (n+1)) i. introv Gt.
    apply HS. clear HS. split; intros C.
    xseq. xapps. xapp. xapply_local~ IH. 
    hsimpl. math_rewrite (i+1-1 = i). rewrite~ (@fact_succ i). ring.
    hsimpl. xret. hsimpl. fequals. math.
  xapp. hsimpl.
Qed.


(********************************************************************)
(* ** Factorial function: while-loop implementation *)

Lemma facto_while_spec : Spec facto_while n |R>>
  n >= 0 -> R [] (\= fact n).
Proof.
  xcf. intros. xapp. xapp. xwhile.  
  xgeneralize (forall i:int, R ([0 <= i <= n] \* m ~~> (i+1) \* r ~~> (fact i)) 
                                              (# m ~~> (n+1) \* r ~~> (fact n))).
    xapply_local~ (Inv 0). hsimpl. rewrite~ fact_zero. math.
    intros i. induction_wf IH: (int_upto_wf (n+1)) i. xextract as Gt.
    apply HR. clear HR. xif. xapps. xret.
    xif_after. xseq. xapps. xapps. xapps. xapps. xapp.
     xapply_local~ (IH (i+1)); hsimpl~.
     rewrite~ (@fact_succ (i+1)). math_rewrite (i+1-1=i). ring.
    xif_after. xret. math_rewrite (i=n). hsimpl.
  xapp. hsimpl.
Qed.



