Set Implicit Arguments.
Require Import LibCore CFPrim Facto_ml.


Lemma xfor_frame__ : forall I H' a b H Q (Fof:int->~~unit),
  (forall i, is_local (Fof i)) ->
  (a > (b)%Z -> H ==> (Q tt)) ->
  ((a <= (b)%Z) -> 
      (H ==> I a \* H') 
   /\ (forall i, a <= i /\ i <= (b)%Z -> (Fof i) (I i) (# I(i+1))) 
   /\ (I ((b)%Z+1) \* H' ==> Q tt)) ->
  local (fun H Q => (a > (b)%Z -> H ==> (Q tt)) /\ (a <= (b)%Z -> exists I,
     H ==> I a /\ (forall i, a <= i /\ i <= (b)%Z -> (Fof i) (I i) (# I(i+1))) /\ (I ((b)%Z+1) ==> Q tt))) H Q.
Proof.
  introv L M1 M2. apply local_erase. split. auto.
  introv M3. intuit (M2 M3). exists (I \*+ H'). splits*.
  intros i Hi. specializes H1 Hi. apply* local_wframe.
Qed.

Lemma xfor_frame_le__ : forall I H' a b H Q (Fof:int->~~unit),
  (a <= (b)%Z) -> 
  (H ==> I a \* H') ->
  (forall i, a <= i /\ i <= (b)%Z -> (Fof i) (I i) (# I(i+1))) ->
  (I ((b)%Z+1) \* H' ==> Q tt) ->
  local (fun H Q => (a > (b)%Z -> H ==> (Q tt)) /\ (a <= (b)%Z -> exists I,
     H ==> I a /\ (forall i, a <= i /\ i <= (b)%Z -> (Fof i) (I i) (# I(i+1))) /\ (I ((b)%Z+1) ==> Q tt))) H Q.
Proof.
  introv M1 M2 M3 M4. apply~ (>>> local_wframe unit __ H' (fun _:unit => I (b+1))).
  apply local_erase. split. intros. false. math.
  intros. exists* I. intros t. destruct t. auto.
Qed.

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
Print facto_for_cf.
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

Lemma facto_for_spec : Spec facto_for n |R>>
  n >= 0 -> R [] (\= fact n).
Proof.
Print facto_for_cf.
  xcf. intros. xapp. xseq. 
  xfor (fun i => r ~> RefOn (fact (i-1))).
  math_rewrite (n = 0). simpl. rewrite~ fact_zero.
  simpl. rewrite~ fact_zero.
  xapp. intro_subst. xapp. xsimpl. 
   math_rewrite (i+1-1=i). rewrite~ (@fact_succ i). rewrite~ Zmult_comm.
  xapp. xsimpl. subst. fequal~.
Qed.

