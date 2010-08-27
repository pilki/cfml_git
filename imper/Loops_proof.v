Set Implicit Arguments.
Require Import CFPrim Loops_ml.


(********************************************************************)
(* ** For loops *)

Lemma loop_for_spec : 
  Spec loop_for a b body |R>>
       (a > (b)%Z -> R [] (#[])) 
    /\ (a <= (b)%Z -> forall I,
          (Spec body i |R>> a <= i <= b -> R (I i) (# I(i+1))) ->
          R (I a) (# I ((b)%Z+1))).
Proof.
  xcf. intros. split; intros Cmp. 
  (* case a > b *)
  xfun (fun f => Spec f i |R>> i > b -> R [] (#[])).
    intros Gt. xif. math. xret. xsimpl.
  xapp~. hsimpl.
  (* case a <= b *)
  intros I Hbody.
  xfun_induction (fun f => Spec f i |R>> a <= i <= b+1 -> R (I i) (# I (b+1))) (upto (b+1)).
    intros IH Le. xif.
      xapp. math.
       xapp; auto with maths.
      xret. math_rewrite (i = b+1). auto.
  xapp. math. xsimpl.
Qed.

(* details of xfun_induction:  
  xfun_noxbody (fun f => Spec f i |R>> a <= i <= b+1 -> R (I i) (# I (b+1))).
    apply (spec_induction_1_noheap (lt:=upto (b+1))). prove_wf. xbody. 
*)    

(********************************************************************)
(* ** While loops *)

Definition loop_cf' (F1:~~bool) (F2:~~unit) :=
  fun H Q => exists A:Type, exists I:A->hprop, exists J:A->bool->hprop, exists lt:binary A,
      wf lt 
   /\ (exists X0, H ==> (I X0))
   /\ (forall X, F1 (I X) (J X)) 
   /\ (forall X, F2 (J X true) (# Hexists Y, (I Y) \* [lt Y X])) 
   /\ (forall X, J X false ==> Q tt).

Notation "'Local' H0 Q0 'as' H Q 'in' F" := (local (fun H Q => F) H0 Q0)
  (at level 99, H0 at level 0, Q0 at level 0, H ident, Q ident).

Definition loop_cf (F1:~~bool) (F2:~~unit) :=
  fun (H:hprop) (Q:unit->hprop) => forall R:~~unit, is_local R ->
    (forall H Q, (exists Q', F1 H Q' 
       /\ (Local (Q' true) Q as H Q in exists H'', F2 H (#H'') /\ R H'' Q)
       /\ Q' false ==> Q tt) -> R H Q) 
    -> R H Q.

Lemma local_weaken_formula : forall B (F1 F2:~~B) H Q,
  local F1 H Q -> (F1 ===> F2) -> local F2 H Q.
Proof.
  introv M W. introv Hh.
  destruct (M h Hh) as (?&?&?&?&?&?&?).
  exists___. splits; [ | apply W; apply H1 |]. eauto. eauto. 
Qed.



Lemma loop_while : 
  Spec loop_while cond body |R>> forall H Q,
    (forall R':~~unit, is_local R' ->
     (exists Q', app_1 cond tt H Q' 
       /\ (Local (Q' true) Q as H Q in exists Q'', app_1 body tt H Q'' /\ R' (Q'' tt) Q)
       /\ Q' false ==> Q tt) )
    -> R H Q.
Proof.
  xintros. 
   introv M. applys app_spec_2 loop_while_cf.
    intros_all. subst. applys* H1.
  intros. subst x1 x2.
  apply local_erase. intros aux.
  lets U: M (app_1 (B:=unit) aux tt) __. xlocal. clear M.
  destruct U as (Q'&M1&M2&M3).
  exists (fun f => app_1 f tt H Q). split; [ | intros N; apply N ].
  intros G. 
  applys app_spec_1. apply G. intros_all. subst. applys* H1.
  intros. subst _x0.
  xlet Q'. apply M1.
  xif. 
  applys local_weaken_formula M2. intros H'' Q''.
   introv (Y&N1&N2). exists (Y tt). split. applys_eq N1 1. apply~ func_ext_1. intros a. destruct a. auto. apply N2.
  destruct _x1. false. xret. auto.
Qed.
  
 
 skip. intros cond body H Q. intros (Q'&M1&M2).
  lets: loop_while_cf.
  apply spec_ap
  dest

  xcf. skip. intros.
  introv W Hc Hb Ho.
  xfun_induction_heap (fun f => Spec f () |R>> forall X, R (I X) Q) lt.
    intros IH. xlet. xapp y. xif.
      xseq. xapp y. xextract. intros y' Lt. xapp~ y'. hsimpl.
      xret. destruct _x1; tryfalse. hchange (Ho y). hsimpl.
  xapp X0. hsimpl.
Qed.



Axiom local_extract_exists : forall B (F:~~B) A (J:A->hprop) Q,
  is_local F ->
  (forall x, F (J x) Q) -> 
  F (heap_is_pack J) Q.

Lemma loop_inv : forall (F1:~~bool) (F2:~~unit),
  loop_cf' F1 F2 ===> loop_cf F1 F2.
Proof.
  intros F1 F2 H Q (A&I&J&lt&Wlt&(X0&M0)&M1&M2&M3) R LR W.
  applys~ local_weaken M0. generalize X0.
  intros X. induction_wf IH: Wlt X.
  apply W. exists (J X). splits~.
  apply local_erase. esplit. split. apply M2.
  apply~ local_extract_exists. intros x.
  rewrite star_comm. apply~ CFHeaps.local_intro_prop.
Qed.

Lemma loop_while : 
  Spec loop_while cond body |R>>
    forall A (I:A->hprop) (J:A->bool->hprop) (lt:binary A) X0 (Q:unit->hprop),
      wf lt -> 
      (Spec cond () |R'>> forall X, R' (I X) (J X)) ->
      (Spec body () |R'>> forall X, R' (J X true) (# Hexists Y, (I Y) \* [lt Y X])) ->
      (forall X, J X false ==> Q tt) ->
      R (I X0) Q.
Proof.
  xcf. introv W Hc Hb Ho.
  xfun_induction_heap (fun f => Spec f () |R>> forall X, R (I X) Q) lt.
    intros IH. xlet. xapp y. xif.
      xseq. xapp y. xextract. intros y' Lt. xapp~ y'. hsimpl.
      xret. destruct _x1; tryfalse. hchange (Ho y). hsimpl.
  xapp X0. hsimpl.
Qed.



Lemma loop_while : 
  Spec loop_while cond body |R>>
    forall A (I:A->hprop) (J:A->bool->hprop) (lt:binary A) X0 (Q:unit->hprop),
      wf lt -> 
      (Spec cond () |R'>> forall X, R' (I X) (J X)) ->
      (Spec body () |R'>> forall X, R' (J X true) (# Hexists Y, (I Y) \* [lt Y X])) ->
      (forall X, J X false ==> Q tt) ->
      R (I X0) Q.
Proof.
  xcf. introv W Hc Hb Ho.
  xfun_induction_heap (fun f => Spec f () |R>> forall X, R (I X) Q) lt.
    intros IH. xlet. xapp y. xif.
      xseq. xapp y. xextract. intros y' Lt. xapp~ y'. hsimpl.
      xret. destruct _x1; tryfalse. hchange (Ho y). hsimpl.
  xapp X0. hsimpl.
Qed.

(*
xfun_noxbody (fun f => Spec f () |R>> forall X, R (I X) Q).
    apply (spec_induction_1_noarg (lt:=lt)). auto. xisspec. xbody.
*)


(*TODO
Notation "'While' Q1 'Do' Q2 'Done'" :=
  (!While (fun H Q => exists A, exists I, exists J, exists R,
       wf R 
     /\ (exists x, H ==> I x)
     /\ (forall x, Q1 (I x) (J x)
                /\ Q2 (J x true) (# Hexists y, (I y) \* [R y x])
                /\ (J x false) ==> Q1 tt)
  (at level 69) : charac.

--
tactic : if J is not of type "A->bool->hprop"
then J' may be of type "A->bool" or "A->Prop" and then J is
   fun X b => (b = bool_of (J' X)) \* (I X)
--
*)



