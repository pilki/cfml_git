Set Implicit Arguments.

Require Import LibTactics List.

Ltac forwards_nounfold_then Ei cont ::=
  let args := ltac_args Ei in
  let args := (eval simpl in (args ++ ((boxer ___)::nil))) in
  build_app args cont;
  fast_rm_inside Ei.

Require Import CFLib Facto_ml.

Notation "'While' Q1 'Do' Q2 '_Done'" :=
  (!While (fun H Q => forall R:~~unit, is_local R ->
        (forall H Q, (If_ Q1 Then (Q2 ;; R) Else (Ret tt)) H Q -> R H Q)
        -> R H Q))
  (at level 69, Q2 at level 68, only parsing) : charac.

Lemma while_loop_cf_to_inv : 
   forall (A:Type) (I:A->hprop) (J:A->bool->hprop) (lt:binary A),
   forall (F1:~~bool) (F2:~~unit) H (Q:unit->hprop),
   wf lt -> 
   (exists X0, H ==> (I X0)) ->
   (forall X, F1 (I X) (J X)
              /\ F2 (J X true) (# Hexists Y, (I Y) \* [lt Y X])
              /\ J X false ==> Q tt) ->
  (While F1 Do F2 _Done) H Q.
Proof.
  introv W (X0&I0) M. apply local_erase.
  introv LR HR. applys* local_weaken (rm I0). gen X0. 
  intros X. induction_wf IH: W X.
  destruct (M X) as (M1&M2&M3).
  applys HR. xlet*. xif. xseq*. xextract as Y L.
  xapply_local* IH; hsimpl.
  xret. destruct x; auto_false.
Qed.


Notation "'For' i '=' a 'To' b 'Do' Q1 '_Done'" :=
  (!For (fun H Q => forall S:int->~~unit, is_local_1 S ->
        (forall i H Q,  
             (i <= (b)%Z -> (Q1 ;; S (i+1)) H Q)
          /\ (i > b%Z -> (Ret tt) H Q) 
          -> S i H Q)
       -> S a H Q))
  (at level 69, i ident, a at level 0, b at level 0) : charac.


Lemma for_loop_cf_to_inv : 
   forall I H',
   forall (a:int) (b:int) (F:int->~~unit) H (Q:unit->hprop),
   (a > (b)%Z -> H ==> (Q tt)) ->
   (a <= (b)%Z ->
          (H ==> I a \* H') 
       /\ (forall i, a <= i /\ i <= (b)%Z -> F i (I i) (# I(i+1))) 
       /\ (I ((b)%Z+1) \* H' ==> Q tt)) ->
  (For i = a To b Do F i _Done) H Q.
Proof.
  introv M1 M2. apply local_erase. intros S LS HS.
  tests (a > b) as C. 
  apply (rm HS). split; intros C'. math. xret~.
  forwards (Ma&Mb&Mc): (rm M2). math.
   cuts P: (forall i, a <= i <= b+1 -> S i (I i) (# I (b+1))).
     xapply_local P. math. hchanges Ma. hchanges Mc.
   intros i. induction_wf IH: (int_upto_wf (b+1)) i. intros Bnd.
   applys (rm HS). split; intros C'.
     xseq. eapply Mb. math. xapply_local IH; auto with maths; hsimpl.
  xret. math_rewrite~ (i = b +1).  
Qed.

Lemma for_loop_cf_to_inv_gen : 
   forall I H',
   forall (a:int) (b:int) (F:int->~~unit) H,
   (a <= (b)%Z ->
          (H ==> I a \* H') 
       /\ (forall i, a <= i /\ i <= (b)%Z -> F i (I i) (# I(i+1)))) ->
   (a > (b)%Z -> H ==> I ((b)%Z+1) \* H') ->
  (For i = a To b Do F i _Done) H (# I ((b)%Z+1) \* H').
Proof. intros. applys* for_loop_cf_to_inv. Qed.

Lemma for_loop_cf_to_inv_up : 
   forall I H',
   forall (a:int) (b:int) (F:int->~~unit) H (Q:unit->hprop),
   (a <= (b)%Z) ->
   (H ==> I a \* H') ->
   (forall i, a <= i /\ i <= (b)%Z -> F i (I i) (# I(i+1))) ->
   (I ((b)%Z+1) \* H' ==> Q tt) ->
   (For i = a To b Do F i _Done) H Q.
Proof. intros. applys* for_loop_cf_to_inv. intros. math. Qed.



Ltac auto_tilde ::= auto with maths.


(********************************************************************)
(* ** Mathematical factorial function *)

Parameter fact : int -> int.
Parameter fact_zero : fact 0 = 1.
Parameter fact_succ : forall n, n > 0 ->
  fact n = n * fact (n-1).
Lemma fact_one : fact 1 = 1.
Proof. rewrite~ fact_succ. math_rewrite (1-1=0). rewrite~ fact_zero. Qed.
(*

(********************************************************************)
(* ** Factorial function: recursive implementation *)

Lemma facto_rec_spec : Spec facto_rec n |R>>
  n >= 0 -> R [] (\= fact n).
Proof.
  apply (spec_induction_1_noheap (lt:=downto 0)). prove_wf.
  xcf. intros. xif.
  xret. xsimpl. rewrite~ fact_zero.
  xapp~. intro_subst. xret. hsimpl. rewrite~ <- fact_succ.
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

*)
(********************************************************************)
(* ** Factorial function: for-loop implementation, with invariant *)

Lemma for_loop_cf_to_inv_gen' : 
   forall I H',
   forall (a:int) (b:int) (F:int->~~unit) H Q,
   (a <= (b)%Z -> H ==> I a \* H') ->
   (forall i, a <= i <= (b)%Z -> F i (I i) (# I(i+1))) ->
   (a > (b)%Z -> H ==> I ((b)%Z+1) \* H') ->  
   (# (I ((b)%Z+1) \* H')) ===> Q ->
  (For i = a To b Do F i _Done) H Q.
Proof. intros. applys* for_loop_cf_to_inv. intros C. hchange (H2 C). hchange (H3 tt). hsimpl. Qed.

Ltac xfor_inv_gen_base I i C :=
  eapply (@for_loop_cf_to_inv_gen' I); 
  [ intros C
  | intros i C
  | intros C
  | apply rel_le_refl ].

Tactic Notation "xfor_inv_gen_base" constr(I) "as" ident(i) ident(C) :=
  xfor_inv_gen_base I i C.


Lemma facto_for_spec : Spec facto_for n |R>>
  n >= 0 -> R [] (\= fact n).
Proof.
  xcf. intros. xapp. xseq.
  xfor_inv_gen_base (fun i:int => [0 < i <= n+1] \* (r ~~> fact (i-1))) as i C.
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
  xcf. intros. xapp. xapp. 
xuntag. apply while_loop_cf_to_inv.

 xwhile.  
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



