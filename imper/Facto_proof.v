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

Lemma while_loop_cf_to_inv' : 
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

Ltac applys_base E ::= 
  match type of E with
  | list Boxer => applys_build E
  | _ => first [ rapply E | applys_build E ]
  end; fast_rm_inside E.

Lemma while_loop_cf_to_inv : 
   forall (A:Type) (I:A->hprop) (lt:binary A) (W:wf lt),
   forall (F1:~~bool) (F2:~~unit) H (Q:unit->hprop),
   (exists X0, H ==> (I X0)) ->
   (forall X, local (fun H Q => exists Q',
        F1 H Q' 
     /\ F2 (Q' true) (# Hexists Y, (I Y) \* [lt Y X])
     /\ Q' false ==> Q tt) (I X) Q) ->
  (While F1 Do F2 _Done) H Q.
(*
Proof.
  introv W (X0&I0) M. apply local_erase.
  introv LR HR. applys* local_weaken (rm I0). gen X0. 
  intros X. induction_wf IH: W X. 
  rewrite LR. introv Hh.
  lets (H1&H2&Q1&H'&?&(Q'&?&?&?)&?): (>>> (rm M) X Hh).
  exists (H1 \* H2) [] (Q1 \*+ H2) H'. splits~.
  rew_heap~.
  applys HR. xextract. xlet (Q' \*+ H2). skip. (* todo: F1 local *)
  xif. xseq  (#Hexists Y, I Y \* [lt Y X] \* H2). skip. 
  intros Y L. xapply_local* IH; hsimpl.
  xret. destruct x; auto_false. hsimpl. 
Qed.
*)
Admitted.

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

Lemma for_loop_cf_to_inv_gen' : 
   forall I H',
   forall (a:int) (b:int) (F:int->~~unit) H,
   (a <= (b)%Z ->
          (H ==> I a \* H') 
       /\ (forall i, a <= i /\ i <= (b)%Z -> F i (I i) (# I(i+1)))) ->
   (a > (b)%Z -> H ==> I ((b)%Z+1) \* H') ->
  (For i = a To b Do F i _Done) H (# I ((b)%Z+1) \* H').
Proof. intros. applys* for_loop_cf_to_inv. Qed.

Lemma for_loop_cf_to_inv_gen : 
   forall I H',
   forall (a:int) (b:int) (F:int->~~unit) H Q,
   (a <= (b)%Z -> H ==> I a \* H') ->
   (forall i, a <= i <= (b)%Z -> F i (I i) (# I(i+1))) ->
   (a > (b)%Z -> H ==> I ((b)%Z+1) \* H') ->  
   (# (I ((b)%Z+1) \* H')) ===> Q ->
  (For i = a To b Do F i _Done) H Q.
Proof. intros. applys* for_loop_cf_to_inv. intros C. hchange (H2 C). hchange (H3 tt). hsimpl. Qed.

Ltac xfor_inv_gen_base I i C :=
  eapply (@for_loop_cf_to_inv_gen I); 
  [ intros C
  | intros i C
  | intros C
  | apply rel_le_refl ].

Tactic Notation "xfor_inv_gen" constr(I) "as" ident(i) ident(C) :=
  xfor_inv_gen_base I i C.
Tactic Notation "xfor_inv_gen" constr(I) "as" ident(i) :=
  let C := fresh "C" i in xfor_inv_gen I as i C.
Tactic Notation "xfor_inv_gen" constr(I) :=
  let i := fresh "i" in xfor_inv_gen I as i.

Lemma for_loop_cf_to_inv_up : 
   forall I H',
   forall (a:int) (b:int) (F:int->~~unit) H (Q:unit->hprop),
   (a <= (b)%Z) ->
   (H ==> I a \* H') ->
   (forall i, a <= i /\ i <= (b)%Z -> F i (I i) (# I(i+1))) ->
   ((# I ((b)%Z+1) \* H') ===> Q) ->
   (For i = a To b Do F i _Done) H Q.
Proof. intros. applys* for_loop_cf_to_inv. intros. math. Qed.

Ltac xfor_inv_base I i C :=
  eapply (@for_loop_cf_to_inv_up I); 
  [ 
  | 
  | intros i C
  | apply rel_le_refl ].

Tactic Notation "xfor_inv" constr(I) "as" ident(i) ident(C) :=
  xfor_inv_gen_base I i C.
Tactic Notation "xfor_inv" constr(I) "as" ident(i) :=
  let C := fresh "C" i in xfor_inv I as i C.
Tactic Notation "xfor_inv" constr(I) :=
  let i := fresh "i" in xfor_inv I as i.


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

*)

(********************************************************************)
(* ** Factorial function: while-loop implementation, invariant *)

Ltac xok_core cont ::= 
  solve [ cbv beta; apply rel_le_refl
        | apply pred_le_refl
        | apply hsimpl_to_qunit; reflexivity
        | hextract; hsimpl; cont tt ].


Lemma facto_while_spec' : Spec facto_while n |R>>
  n >= 0 -> R [] (\= fact n).
Proof.
  xcf. intros. xapp. xapp. xseq.
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

  



