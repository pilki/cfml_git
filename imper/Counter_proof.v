Set Implicit Arguments.
Require Import CFLib Counter_ml.
Require Import MutableList_ml MutableList_proof.


(********************************************************************)
(* ** Counter function *)

(** Concrete specification of a counter function *)

Definition CounterSpec I f :=
  Spec f () |R>> forall m, R (I m) (\=(m+1) \*+ (I (m+1))).

Definition Counter (n:int) (f:func) : hprop := 
  Hexists I:int->hprop, I n \* [CounterSpec I f].

(** Abstract specification of a counter function *)

Lemma Counter_apply : forall f n,
  AppReturns f tt (f ~> Counter n) (\= (n+1) \*+ f ~> Counter (n+1)).
Proof.
  intros. hdata_simpl Counter. xextract as I Sf.
  xapply_local (spec_elim_1 Sf tt n); hsimpl~.
Qed.

(** Verification of the counter generator *)

Lemma make_counter_spec : 
  Specs make_counter () >> [] (~> Counter 0).
Proof.
  xcf. xapps. sets I: (fun n:int => r ~~> n).
  xfun (CounterSpec I). unfold I. xgo*.
  xret. hdata_simpl Counter. hsimpl~ I.
Qed.


(********************************************************************)
(* ** Ignore function *)

Lemma ignore_spec : forall a,
  Specs ignore (x:a) >> [] (#[]).
Proof. intros. xcf. intros. xret~. Qed.

Hint Extern 1 (RegisterSpec ignore) => Provide ignore_spec.


(********************************************************************)
(* ** Iterating calls to an imperative list of counter functions *)

Lemma step_all_imper_spec : 
  Spec step_all_imper (l:loc) |R>> forall L, 
    R (l ~> MList Counter L) (# l ~> MList Counter (LibList.map (fun i => i+1) L)).
Proof.
  xcf. intros. xfun (fun g => Spec g f |R>> forall (Q':int->hprop) H (Q:unit->hprop),
    (App f tt;) H Q' -> (forall x, Q' x ==> Q tt) -> R H Q).
    intros M W. xlet. apply M. xapp. hsimpl. applys pred_le_trans (W _x3). hsimpl.
    renames _f0 to g, S_f0 to Sg.
  lets K: (>> (spec_elim_2 (@miter_spec func int)) [] []). xapply K; try hsimpl.
  introv In Ic. induction L; intros. apply In.
  rewrite map_cons. eapply Ic. 
    intros f. xapp. apply Counter_apply. intros r.
     hextract. apply hsimpl_to_qunit. reflexivity. hsimpl. hsimpl. 
    apply IHL.
Qed.






