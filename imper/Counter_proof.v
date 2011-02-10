Set Implicit Arguments.
Require Import CFLib Counter_ml.



(********************************************************************)
(* ** Counter function *)

Definition CounterSpec I f :=
  Spec f () |R>> forall m, R (I m) (\=(m+1) \*+ (I (m+1))).

Definition Counter (n:int) (f:func) : hprop := 
  Hexists I:int->hprop, I n \* [CounterSpec I f].

Lemma Counter_apply : forall f n,
  AppReturns f tt (f ~> Counter n) (\= (n+1) \*+ f ~> Counter (n+1)).
Proof.
  intros. hdata_simpl Counter. xextract as I Sf.
  xapply_local (spec_elim_1 Sf tt n); hsimpl~.
Qed.

Lemma make_counter_spec : 
  Specs make_counter () >> [] (~> Counter 0).
Proof.
  xcf. xapps. sets I: (fun n:int => r ~~> n).
  xfun (CounterSpec I). unfold I. xgo*.
  xret. hdata_simpl Counter. hsimpl~ I.
Qed.



(********************************************************************)
(* ** List iterator *)

Lemma iter_spec : forall A,
  Spec iter (f:func) (l0:list A) | R>>
    forall H (Q:unit->hprop),
    (forall (S:list A -> _ -> _ -> Prop),
       is_local_1 S ->
       (forall l H' Q',
          match l with
          | nil => (Ret tt) H' Q'
          | x::l' => ((App f x;) ;; S l') H' Q'
          end -> S l H' Q') ->
       S l0 H Q) ->
    R H Q.
Proof.
  intros. xintros. intros f l0. introv M.
  sets_eq S: (app_2 (A1:=func) (A2:=list A) (B:=unit) iter f).
  apply M; clear M H Q. rewrite EQS. intros_all. xlocal.
  intros l H' Q' HS. rewrite EQS. eapply app_spec_2.
  xcf. intros. subst. xmatch; auto.
Qed.

Hint Extern 1 (RegisterSpec iter) => Provide iter_spec.


(********************************************************************)
(* ** Ignore function *)

Lemma ignore_spec : forall a,
  Specs ignore (x:a) >> [] (#[]).
Proof. intros. xcf. intros. xret~. Qed.

Hint Extern 1 (RegisterSpec ignore) => Provide ignore_spec.


(********************************************************************)
(* ** Iterating calls to counter functions *)

Lemma step_all_spec : 
  Spec step_all (l:list func) |R>> forall L, 
    R (l ~> List Counter L) (# l ~> List Counter (LibList.map (fun i => i+1) L)).
Proof.
  xcf. intros. 
  xfun (fun g => Spec g f |R>> forall (Q':int->hprop) H (Q:unit->hprop),
     (App f tt;) H Q' -> (forall x, Q' x ==> Q tt) -> R H Q).
     intros M W. xlet. apply M. xapp. hsimpl.
      applys pred_le_trans (W _x3). hsimpl.
     renames _f0 to g, S_f0 to Sg.
  apply (spec_elim_2 (@iter_spec func)). intros S LS HS.
  gen l. induction_wf: (@list_sub_wf int) L. intros.
  apply HS. clear HS. destruct l.
  (* case nil *)
  xret. hchange (@unfocus_nil' _ L _ Counter). hextract. subst.
  hchange (@focus_nil _ _ Counter). hsimpl.
  (* case cons *)
  xchange (focus_cons' f l) as n L' E. 
  xseq (# f ~> Counter (n + 1) \* l ~> List Counter L'). 
  eapply (spec_elim_1 Sg). xapply_local Counter_apply; xauto~. intros. xsimpl.
  subst L. xapply_local~ (>> IH L'). hsimpl.
  rew_map. hchange (unfocus_cons f l (n+1)). hsimpl.
Qed.



