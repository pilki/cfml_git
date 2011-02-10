Set Implicit Arguments.
Require Import CFLib Facto_ml.

Ltac auto_tilde ::= auto with maths.


(********************************************************************)
(* ** Mathematical factorial function *)

Parameter fact : int -> int.
Parameter fact_zero : fact 0 = 1.
Parameter fact_succ : forall n, n > 0 ->
  fact n = n * fact (n-1).
Parameter fact_one : fact 1 = 1.


(********************************************************************)
(* ** Factorial function: recursive implementation

Lemma :
  forall n,
  let R := fun P Q => AppReturns facto_rec n P Q in
  downto 0 n n' -> n >= 0 -> R [] (fun x => [x = fact n]).

 *)

Lemma facto_rec_spec : Spec facto_rec n |R>>
  (n >= 0 -> R [] (\= fact n)).
Proof. 
  xinduction (downto 0). 
  xcf. intros. xif.
  xret. xsimpl. rewrite~ fact_zero.
  xapps~. xret. hsimpl. rewrite~ <- fact_succ.
Qed.


(********************************************************************)
(* ** Factorial function: for-loop implementation *)



Lemma facto_for_spec : Spec facto_for n |R>>
  n >= 0 -> R [] (\= fact n).
Proof.
  xcf. intros. xapp. xseq. xfor.
  xgeneralize (forall i, 0 < i <= n+1 -> S i (r ~~> fact (i-1)) (# r ~~> fact n)).
    xapply_local~ Inv. hsimpl. simpl. rewrite~ fact_zero. 
    intros i. induction_wf IH: (int_upto_wf (n+1)) i. introv Gt.
    apply HS. clear HS. split; intros C.
    xseq. xapps. xapp. xapply_local~ IH.
    hsimpl. math_rewrite (i+1-1 = i). rewrite~ (@fact_succ i). ring.
    hsimpl. xret. hsimpl. fequals. math.
  xapp. hsimpl~.
Qed.

(********************************************************************)
(* ** Factorial function: for-loop implementation, with invariant *)

Lemma facto_for_spec' : Spec facto_for n |R>>
  n >= 0 -> R [] (\= fact n).
Proof.
  xcf. intros. xapp. xseq.
  xfor_inv_gen (fun i:int => [0 < i <= n+1] \* (r ~~> fact (i-1))) as i.
  hsimpl. simpl. rewrite~ fact_zero. math.
  xapps. xapps. hsimpl.
    math_rewrite (i+1-1 = i). rewrite~ (@fact_succ i). ring.
    math.
  math_rewrite (n = 0). hsimpl.
      math_rewrite (0+1-1=0). rewrite~ fact_zero.
      math.
  xapps. hsimpl. subst. fequals. math.
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
    apply (rm HR). xlet. xapps. xret. xifs.
    xseq. xapps. xapps. xapps. xapps. xapp.
     xapply_local~ (IH (i+1)); hsimpl~.
      rewrite~ (@fact_succ (i+1)). math_rewrite (i+1-1=i). ring.
    math_rewrite (i=n). xret~.
  xapp. hsimpl~.
Qed.


(********************************************************************)
(* ** Factorial function: while-loop implementation, invariant *)

Lemma facto_while_spec' : Spec facto_while n |R>>
  n >= 0 -> R [] (\= fact n).
Proof.
  xcf. intros. xapp. xapp. xseq. (* todo: xwhile_inv *)
  eapply (@while_loop_cf_to_inv _ (fun i:int => [0 <= i <= n] \* m ~~> (i+1) \* r ~~> (fact i)) (upto (n+1))).
  prove_wf.
  exists 0. hsimpl. rewrite~ fact_zero. math.
  intros i. xextract as C. apply local_erase. esplit. splits 3%nat.
    xapps. xret.
    xextract. intros. xclean.  (* todo: simplify this *)
     xapps. xapps. xapps. xapps. xapps. hsimpl. rewrite~ (@fact_succ (i+1)). math_rewrite (i+1-1=i). ring. 
     auto with maths.
     math. hextract. xclean. math_rewrite (i = n). xok.
  xapps. hsimpl~.
Qed.

  




