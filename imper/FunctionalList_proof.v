
Set Implicit Arguments.
Require Import CFLib FunctionalList_ml LibList.
Module FL := FunctionalList_ml.
Opaque List.


(** Iterating over a functional list of counter functions *)
open FunctionalList
let step_all_func (l : (unit->int) list) = 
  iter (fun f -> ignore (f())) l


(********************************************************************)
(* ** Iterating calls to a functional list of counter functions *)

Lemma step_all_func_spec : 
  Spec step_all_func (l:list func) |R>> forall L, 
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


Require Import FunctionalList_ml FunctionalList_proof.








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
(** CPS-append *)


Lemma append_spec : forall A B,
  Spec FL.append (x:list A) (y:list A) (k:func) |R>>  (*todo R:~~B*)
     App k (x++y); ===> (R:~~B).
     (* @app_1 (list A) B k (x++y) ===> R. *)
     (* forall H Q, @app_1 (list A) B k (x++y) H Q -> R H Q. *)
Proof.
  intros. xinduction (unproj31 (list A) func (@list_sub A)).
  xcf. introv IH. intros H Q Ak. xmatch.
  apply Ak.
  xfun (fun k' => Spec k' z |R>> 
    App k (a::z); ===> (R:~~B)). auto.
  xapp.
    auto.
    apply (proj2 S_f0). rew_app in Ak. apply Ak.
    hsimpl.
    hsimpl.
Qed.
 (* todo: use xapp_noframe for unification *)
  
Lemma append_spec' : forall A B,
  Spec FL.append x y k |R>> forall (K:list A->~~B->Prop),
     Spec_1 k K -> forall H Q,
     (forall R', is_local R' -> K (x++y) R' -> R' H Q) ->
     R H Q.
Proof.
  intros. xinduction (unproj31 (list A) func (@list_sub A)).
  xcf. introv IH Sk Rk. xmatch.
  apply Rk. xlocal. rew_list. applys (spec_elim_1 Sk).
  xfun (fun k' => Spec k' z |R>> 
     forall H Q,
     (forall R', is_local R' -> K (a::z) R' -> R' H Q) ->
     R H Q).
     introv Rk'. xapp_manual. applys~ Rk' R. hsimpl.
  xapp_manual. 
  specializes KR S_f0. auto.
  apply KR. simpl. intros R' LR' M. apply M.
   intros R'' LR'' N. applys~ Rk R''. hsimpl.
Qed.

(*
Lemma append_spec : forall A B,
  Spec FL.append x y k |R>> forall (K:list A->~~B->Prop),
     Spec_1 k K -> K (x++y) R.
Proof.
  intros. xinduction (unproj31 (list A) func (@list_sub A)).
  xcf. intros_all. applys (proj1 H2) H0. apply~ H. (* todo: auto *)
  introv IH Sk. applys (proj1 Sk). apply (proj2 Sk). (* todo: tactic *) 
  intros H Q App1. xmatch.
  rew_list in App1. apply App1.
  xfun (fun k' => Spec k' z |R>> K (a::z) R).
    intros_all. applys~ (proj1 Sk) H2.
    applys (proj1 Sk). apply (proj2 Sk).
    intros H' Q' App2. auto.
  xapp_manual.
  specializes KR S_f0. auto. skip.
  
Qed.
*)

(********************************************************************)
(** Spec map simple *)

Hint Constructors Forall2.

Lemma map_spec : forall a b,
  Spec FL.map (f:func) (l:list a) |R>> forall A B L (T:htype A a) (U:htype B b) (I:A->B->Prop),
    (Spec f x |R'>> forall X, In X L -> keep R' (x ~> T X) (fun y => Hexists Y, (y ~> U Y) \* [I X Y])) ->
    keep R (l ~> List T L) (fun m => Hexists M, m ~> List U M \* [Forall2 I L M]).
Proof.
  intros. xinduction (unproj22 func (@list_sub a)).
  xcf. intros f l IH. introv Hf. (* todo: avec xintros ? *)
  xmatch.
  (* base case *)
  xret.
  hchange (@unfocus_nil' _ L _ T). hextract. subst L. hsimpl~ (@nil B).
    hchange (@focus_nil _ _ U). hchange (@focus_nil _ _ T). hsimpl.
  (* rec case *)
  xchange (@focus_cons' _ a0 l0). xextract as X L' E. subst L.
  xapp. simple~.
  intros Y IXY. xlet as m. xapp.
    simpl. auto.
    xweaken. intros_all. applys H1. apply H0. auto. (* clean *)
     simpl. intros_all. apply H1. auto.
    xret. hextract as M ILM. hsimpl (Y::M).
      hchange (@unfocus_cons _ r m _ Y M). 
       hchange (@unfocus_cons _ a0 l0 _ X L'). hsimpl.
      auto.
Qed.
  









