Set Implicit Arguments.
Require Import LibCore CFPrim Facto_ml.


(********************************************************************)
(* ** Factorial function *)

Ltac auto_tilde ::= auto with maths.

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
  (* todo: xinduction (). *) skip_goal.
  xcf. intros. xif. xret. hsimpl. rewrite~ fact_zero.
  xapp~. intro_subst. xret. hsimpl. rewrite~ <- fact_succ.
Qed.

(********************************************************************)
(* ** Factorial function: for-loop implementation *)

Lemma facto_for_spec : Spec facto_for n |R>>
  n >= 0 -> R [] (\= fact n).
Proof.
  xcf. intros. xapp. xseq. 
  xfor (fun i => r ~> RefOn (fact (i-1))).
  math_rewrite (n = 0). simpl. rewrite~ fact_zero.
  simpl. rewrite~ fact_zero.
  xapp. intro_subst. xapp. xsimpl. 
   math_rewrite (i+1-1=i). rewrite~ (@fact_succ i). rewrite~ Zmult_comm.
  xapp. xsimpl. subst. fequal~.
Qed.

(********************************************************************)
(* ** Factorial function: while-loop implementation *)

Lemma facto_while_spec : Spec facto_while n |R>>
  n >= 0 -> R [] (\= fact n).
Proof.
  xcf. intros. xapp. xapp. xseq.
  xwhile (fun i => m ~> RefOn (i+1) \* r ~> RefOn (fact i) \* [0<=i<=n]) (upto n) 0.
  rewrite~ fact_zero.
  math.
  intros. exists (\= (X+1 '<= n) \*+ m ~> RefOn (X+1) \*+ r ~> RefOn (fact X)). splits.
  xapp. intro_subst. xret. hsimpl~.
    xapp. intro_subst. intros. xclean.
    xapp. intro_subst. 
    xapp.
    xapp. intro_subst.
    xapp. hsimpl. rewrite (@fact_succ (X+1)). math_rewrite (X+1-1=X). rewrite~ Zmult_comm.
      math.
      unfolds. math.
      math.    
  hextract. xclean. math_rewrite (X = n). auto.
  xapp. xsimpl~.
Qed.

