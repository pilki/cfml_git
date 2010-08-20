Set Implicit Arguments.
Require Import LibCore CFPrim Facto_ml.

Opaque Ref.

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
  apply (spec_induction_1_noheap (lt:=downto 0)). prove_wf.
  xcf. intros. xif. xret. hsimpl. rewrite~ fact_zero.
  xapp~. intro_subst. xret. hsimpl. rewrite~ <- fact_succ.
Qed.

(********************************************************************)
(* ** Factorial function: for-loop implementation *)

Lemma facto_for_spec : Spec facto_for n |R>>
  n >= 0 -> R [] (\= fact n).
Proof.
  xcf. intros. xapp. xseq. 
  xfor_general (fun i => r ~> Ref Id (fact (i-1))).
    hsimpl. math_rewrite (n = 0). simpl. rewrite~ fact_zero.
    simpl. rewrite~ fact_zero.
    xapp. intro_subst. xapp. hsimpl. rewrite~ Zmult_comm.
     rewrite~ <- (@fact_succ i). fequal~.
  xapp. xsimpl. subst. fequal~.
Qed.

(********************************************************************)
(* ** Factorial function: while-loop implementation *)

Lemma facto_while_spec : Spec facto_while n |R>>
  n >= 0 -> R [] (\= fact n).
Proof.
  xcf. intros. xapp. xapp. xseq.
  xwhile (fun i => m ~> Ref Id (i+1) \* r ~> Ref Id (fact i) \* [0<=i<=n])
         (fun i => i+1 <= n) (upto n) 0 as i.
    rewrite~ fact_zero. 
    auto~.
    intros [L U]. xapp. intro_subst. xret. hsimpl~. xclean. iff*.
    intros [L U] Le.
      xapp. intro_subst.
      xapp. intro_subst. 
      xapp.
      xapp. intro_subst.
      xapp. hsimpl. rewrite~ Zmult_comm. rewrite (@fact_succ (i+1)). fequals_rec; auto~.    
      auto~.
      auto~.
      auto~.    
    hextract. xclean. math_rewrite (i = n). auto.
  xapp. xsimpl~.
Qed.
 
(* todo: make shorter! *)



