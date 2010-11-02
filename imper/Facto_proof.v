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
   forall (a:int) (b:int) (F:~~unit) H (Q:unit->hprop),
   (a > (b)%Z -> H ==> (Q tt)) ->
   (a <= (b)%Z ->
          (H ==> I a \* H') 
       /\ (forall i, a <= i /\ i <= (b)%Z -> F (I i) (# I(i+1))) 
       /\ (I ((b)%Z+1) \* H' ==> Q tt)) ->
  (For i = a To b Do F _Done) H Q.
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



(********************************************************************)
(* ** Loop invariants for while-loops *)

Definition while_loop_cf (F1:~~bool) (F2:~~unit) :=
  local (fun (H:hprop) (Q:unit->hprop) => forall R:~~unit, is_local R ->
    (forall H Q, (exists Q', F1 H Q' 
       /\ (local (fun H Q => exists Q', F2 H Q' /\ R (Q' tt) Q) (Q' true) Q)
       /\ Q' false ==> Q tt) -> R H Q) 
    -> R H Q).

Definition while_loop_inv (F1:~~bool) (F2:~~unit) :=
  local (fun (H:hprop) (Q:unit->hprop) => 
    exists A:Type, exists I:A->hprop, exists J:A->bool->hprop, exists lt:binary A,
      wf lt 
   /\ (exists X0, H ==> (I X0))
   /\ (forall X, F1 (I X) (J X)
              /\ F2 (J X true) (# Hexists Y, (I Y) \* [lt Y X])
              /\ J X false ==> Q tt)).

Lemma while_loop_cf_to_inv : forall (F1:~~bool) (F2:~~unit),
  while_loop_inv F1 F2 ===> while_loop_cf F1 F2.
Proof. 
  intros. apply local_weaken_body. intros H Q (A&I&J&lt&W&(X0&I0)&M).
  introv LR HR. applys* local_weaken I0. clear I0. gen X0. 
  intros X. induction_wf IH: W X.
  destruct (M X) as (M1&M2&M3).
  applys HR. exists (J X). splits~.
  apply local_erase. esplit. split. apply M2. 
  apply~ local_extract_exists. intros x.
   rewrite star_comm. apply~ CFHeaps.local_intro_prop'.
Qed. 


(********************************************************************)
(* ** Loop invariants for for-loops *)

Definition for_loop_cf (a:int) (b:int) (F:~~unit) :=
  local (fun (H:hprop) (Q:unit->hprop) => forall S:int->~~unit, is_local_1 S ->
     (forall i H Q,  
          ((i <= (b)%Z -> (local (fun H Q => exists Q', F H Q' /\ S (i+1) (Q' tt) Q) H Q))
       /\ (i > b%Z -> H ==> Q tt)) 
       -> S i H Q)
    -> S a H Q).

Definition for_loop_inv (a:int) (b:int) (F:~~unit) :=
  local (fun (H:hprop) (Q:unit->hprop) => 
      (a > (b)%Z -> H ==> (Q tt)) 
   /\ (a <= (b)%Z -> exists H', exists I,
          (H ==> I a \* H') 
       /\ (forall i, a <= i /\ i <= (b)%Z -> F (I i) (# I(i+1))) 
       /\ (I ((b)%Z+1) \* H' ==> Q tt))).

Lemma for_loop_cf_to_inv : forall (a:int) (b:int) (F:~~unit),
  for_loop_inv a b F ===> for_loop_cf a b F.
Proof. 
  intros. apply local_weaken_body. intros H Q (Mgt&Mle). introv LS HS.
  tests (a > b) as C. apply HS. split. math. auto.
  clear Mgt. specializes Mle. math. destruct Mle as (H'&I&M1&M2&M3).
  applys~ (@local_wframe unit) (# I (b+1)); [| intros u; destruct~ u ]. 
  clear M1. asserts L: (a <= a <= b+1). math. generalize L.
  set (a' := a) at 1. generalize a as i. unfold a'.
  intros i. induction_wf IH: (int_upto_wf (b+1)) i. intros Bnd.
  applys HS. split; intros C'.
    apply local_erase. esplit. split.
      apply M2; auto with maths.
      forwards: IH (i+1); auto with maths.
    math_rewrite~ (i = b +1).
Qed. 



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
  xcf. intros. xif.
  xret. xsimpl. rewrite~ fact_zero.
  xapp~. intro_subst. xret. hsimpl. rewrite~ <- fact_succ.
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
  xapp. hsimpl~.
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



