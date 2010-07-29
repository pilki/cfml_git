Set Implicit Arguments.
Require Import LibCore CFPrim Facto_ml.



Lemma hsimpl_to_qunit : forall (H:hprop) (Q:unit->hprop),
  Q = (fun _ => H) ->
  H ==> Q tt.
Proof. intros. subst. auto. Qed.
Hint Resolve hsimpl_to_qunit.

(*
Lemma temp2 : forall (H:hprop),
  H ==> (fun _ => H) tt.
Proof. auto. Qed.
*)

Notation "'While' Q1 'Do' Q2 'Done'" :=
  (!While (fun H Q => exists A, exists I, exists R,
       wf R 
     /\ (exists x, H ==> I x)
     /\ (forall x, local (fun Hl Ql => exists Q', 
            Q1 Hl Q'
         /\ Q2 (Q' true) (# Hexists y, (I y) \* [R y x])
         /\ (Q' false ==> Ql tt)) (I x) Q)))
  (at level 69) : charac.

Lemma xfor_frame : forall I H' a b H Q (Pof:(int->hprop)->Prop),
  (forall H', Pof I -> Pof (I \*+ H')) ->
  (a > (b)%Z -> H ==> (Q tt)) ->
  ((a <= (b)%Z) -> 
      (H ==> I a \* H') 
   /\ (Pof I)
   /\ (I ((b)%Z+1) \* H' ==> Q tt)) ->
  local (fun H Q => (a > (b)%Z -> H ==> (Q tt)) /\ (a <= (b)%Z -> exists I,
     H ==> I a /\ Pof I /\ (I ((b)%Z+1) ==> Q tt))) H Q.
Proof.
  introv L M1 M2. apply local_erase. split. auto.
  introv M3. intuit (M2 M3). exists (I \*+ H'). splits*.
Qed.

Lemma xfor_frame_le : forall I H' a b H Q (Pof:(int->hprop)->Prop),
  (a <= (b)%Z) -> 
  (H ==> I a \* H') ->
  (Pof I) ->
  (I ((b)%Z+1) \* H' ==> Q tt) ->
  local (fun H Q => (a > (b)%Z -> H ==> (Q tt)) /\ (a <= (b)%Z -> exists I, 
     H ==> I a /\ Pof I /\ (I ((b)%Z+1) ==> Q tt))) H Q.
Proof.
  introv M1 M2 M3 M4. apply~ (>>> local_wframe unit __ H' (fun _:unit => I (b+1))).
  apply local_erase. split. intros. false. math.
  intros. exists* I. intros t. destruct t. auto.
Qed.

Ltac xfor_frame_side tt := 
  let H' := fresh in let PH' := fresh in
  let i := fresh in let Pi := fresh in
  intros H' PH' i Pi; eapply local_frame; 
   [try xlocal | apply PH'; apply Pi ].

Ltac xfor_core I ::= 
  let Hi := fresh "Hfor" in
  eapply (@xfor_frame I); 
  [ try solve [ xfor_frame_side tt ]
  | intros Hfor; try solve [ false; math ]
  | intros Hfor; splits (3%nat); 
     [ hsimpl 
     | xfor_bounds_intro tt
     | hsimpl ] 
  ].

Ltac xfor_le_core I ::=
  eapply (@xfor_frame_le I);
  [ try math
  | hsimpl
  | xfor_bounds_intro tt
  | hsimpl ].


Lemma xwhile_frame : forall A I (R:binary A) H' H Q Qf (F1:~~bool) (F2:~~unit),
  is_local F1 -> 
  is_local F2 -> 
  wf R ->
  (exists x, H ==> I x \* H') ->
  (forall x, local (fun Hl Ql => exists Q', 
            F1 Hl Q'
         /\ F2 (Q' true) (# Hexists y, (I y) \* [R y x])
         /\ (Q' false ==> Ql tt)) (I x) Qf) ->
  (Qf \*+ H' ===> Q) ->
  local (fun H Q => exists A, exists I, exists R:binary A,
       wf R 
     /\ (exists x, H ==> I x)
     /\ (forall x, local (fun Hl Ql => exists Q', 
            F1 Hl Q'
         /\ F2 (Q' true) (# Hexists y, (I y) \* [R y x])
         /\ (Q' false ==> Ql tt)) (I x) Q )) H Q.
Proof.
  introv L1 L2 M1 (X0,M2) M3 M4. 
  apply* local_wframe.
  apply local_erase.
  exists A I R. splits*.
Qed.

Ltac xwhile_body_manual :=
  let x := fresh "X" in intros x; xextract;
  pose ltac_mark; intros; apply local_erase; gen_until_mark.

Lemma esplit_boolof : forall (b:bool) (H:hprop) (P:(bool->hprop)->Prop),
  P (\= b \*+ H) -> ex P.
Proof. intros. exists (\= b \*+ H). applys_eq H0 1. extens~. Qed.

Ltac xwhile_body_handle :=
  intros; eapply esplit_boolof; splits.

Ltac xwhile_core I R X ::= 
  first [ eapply (@xwhile_frame _ I R)
        | eapply (@xwhile_frame _ I (measure R))];
  [ xlocal
  | xlocal
  | try prove_wf
  | exists X; instantiate; hsimpl 
  | try xwhile_body_manual (* ; try xwhile_body_handle*)
  | hsimpl ].

Ltac xwhile_manual_core I R ::= 
  first [ eapply (@xwhile_frame _ I R)
        | eapply (@xwhile_frame _ I (measure R))];
  [ xlocal
  | xlocal
  | idtac
  | idtac
  | try xwhile_body_manual
  | idtac ].


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

