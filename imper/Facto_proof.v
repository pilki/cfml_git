Set Implicit Arguments.
Require Import LibCore CFPrim Facto_ml.


(********************************************************************)
(* ** Factorial function *)

Parameter fact : int -> int.
Parameter fact_zero : fact 0 = 1.
Parameter fact_succ : forall n, n > 0 ->
  fact n = n * fact (n-1).

Ltac auto_tilde ::= auto with maths.

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
