Set Implicit Arguments.
Require Import CFLib Counter_ml.


Notation "'LetFuncs' f1 ':=' Q1 'in' Q2" :=
  (!F (fun H Q => forall f1, exists P1,
     (Q1 -> P1 f1) /\ (P1 f1 -> Q2 H Q)))
  (at level 69, f1 ident) : charac.

Notation "'LetFun' f [ A1 ] x1 ':=' Q 'in' F" :=
  (LetFunc f := (Body f [ A1 ] x1 => Q) in F)
  (at level 69, f ident, x1 ident) : charac.
  (* todo : other arities *)


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
  xfun (CounterSpec I). xgo*. unfold I. hsimpl.
  xret. hdata_simpl Counter. hsimpl~ I.
Qed.



(********************************************************************)
(* ** List iterator *)

Lemma iter_spec : forall A,
  Spec iter (f:func) (l:list A) | R>>
    forall H (Q:unit->hprop),
    (forall (S:list A -> _ -> _ -> Prop),
       is_local_1 S ->
       (forall H Q, H ==> Q tt -> S nil H Q) ->
       (forall H Q x l,
          (localize H Q (fun (H:hprop) (Q:unit->hprop) => 
             exists Q':unit->hprop,
             app_1 f x H Q' /\ S l (Q' tt) Q) -> S (x::l) H Q)) ->
      S l H Q) -> 
   R H Q.
Proof.
  intros. xintros. intros f l H Q M.
(*
  specializes M (@app_2 Func (list A) unit iter f).  
  forwards J: (iter_cf (K:= fun f' l' R => f' = f -> l' = l -> R H Q));
   [ | | ]. skip. skip. lets: (spec_elim_2 J).
*)
 sets_eq S: (app_2 (A1:=val) (A2:=list A) (B:=unit) iter f). 
 (*   specializes M S. *)
  (* gen M. induction_wf IH: (@list_sub_wf A) l. intros M. apply M. *)
  apply M; clear M H Q.
  rewrite EQS. intros. xlocal.
  intros H Q v.
    rewrite EQS. eapply app_spec_2. xcf. intros. subst.
    xmatch. xret~.
  intros H Q x t J.
    rewrite EQS. eapply app_spec_2. xcf. intros. subst.
   xmatch.
   applys local_weaken_formula J. clears H Q. intros H Q. intros (Q'&J1&J2). 
   exists (Q' tt). split. skip. (* todo : fix apply J1. *) apply J2.
Qed.

Hint Extern 1 (RegisterSpec iter) => Provide iter_spec.




Definition counter_spec I f :=
  Spec f () |R>> forall n, R (I n) (\=n \*+ (I (n+1))).

Definition Counter (n:int) (f:func) :=
  Hexists I:int->hprop, (I n) \* [counter_spec I f].

Lemma gensym_spec : Spec gensym () |R>>
  R [] (fun f => f ~> Counter 0).
Proof.
  unfold Counter, hdata. xgo.
  sets I: (fun n:int => x ~> Ref Id n).
  xfun (counter_spec I). xgo*. xret. hsimpl~ I.
Qed.

Definition localize B (H:hprop) (Q:B->hprop) (R:~~B) :=
  local R H Q.

Lemma local_weaken_formula : forall B (F1 F2:~~B) H Q,
  local F1 H Q -> (F1 ===> F2) -> local F2 H Q.
Proof.
  introv M W. introv Hh.
  destruct (M h Hh) as (?&?&?&?&?&?&?).
  exists___. splits; [ | apply W; apply H1 |]. eauto. eauto. 
Qed.

Lemma app_spec_2' : forall A1 A2 B f (v1:A1) (v2:A2) (H:hprop) (Q : B->hprop),
  spec_2 (fun x1 x2 R => x1 = v1 -> x2 = v2 -> 
    (forall H Q, R H Q -> app_2 f v1 v2 H Q) -> R H Q) f ->
  app_2 f v1 v2 H Q.
Proof. introv S. forwards~ K : (spec_elim_2 S). Qed.
(* to simpler *)


Lemma iter_spec' : forall A,
  Spec iter (f:func) (l:list A) | R>>
    forall H (Q:unit->hprop),
    (forall (S:list A -> _ -> _ -> Prop),
       (forall l, is_local (S l)) ->
       (match l with 
       | nil => H ==> Q tt
       | x::l' =>      
          localize H Q (fun (H:hprop) (Q:unit->hprop) => 
             exists Q':unit->hprop,
             app_1 f x H Q' /\ S l (Q' tt) Q)
       end -> S l H Q) -> 
      S l H Q) -> 
   R H Q.
Proof.
Admitted.
(*
  intros. xintros. intros f l H Q M.
(*
  specializes M (@app_2 Func (list A) unit iter f).  
  forwards J: (iter_cf (K:= fun f' l' R => f' = f -> l' = l -> R H Q));
   [ | | ]. skip. skip. lets: (spec_elim_2 J).
*)
 sets_eq S: (app_2 (A1:=val) (A2:=list A) (B:=unit) iter f). 
 (*   specializes M S. *)
  (* gen M. induction_wf IH: (@list_sub_wf A) l. intros M. apply M. *)
  apply M; clear M.
  intros v.
    rewrite EQS. eapply app_spec_2. xcf. intros. subst.
    xmatch. xret~.
  intros x t J.
    rewrite EQS. eapply app_spec_2. xcf. intros. subst.
   xmatch.
   applys local_weaken_formula J. clears H Q. intros H Q. intros (Q'&J1&J2). 
   exists (Q' tt). split. skip. (* todo : fix apply J1. *) apply J2.
Qed.
*)



Lemma iter_spec : forall A,
  Spec iter (f:func) (l:list A) | R>>
    forall H (Q:unit->hprop),
    (forall (S:list A -> _ -> _ -> Prop),
       (forall l, is_local (S l)) ->
       (forall H Q, H ==> Q tt -> S nil H Q) ->
       (forall H Q x l,
          (localize H Q (fun (H:hprop) (Q:unit->hprop) => 
             exists Q':unit->hprop,
             app_1 f x H Q' /\ S l (Q' tt) Q) -> S (x::l) H Q)) ->
      S l H Q) -> 
   R H Q.
Proof.
  intros. xintros. intros f l H Q M.
(*
  specializes M (@app_2 Func (list A) unit iter f).  
  forwards J: (iter_cf (K:= fun f' l' R => f' = f -> l' = l -> R H Q));
   [ | | ]. skip. skip. lets: (spec_elim_2 J).
*)
 sets_eq S: (app_2 (A1:=val) (A2:=list A) (B:=unit) iter f). 
 (*   specializes M S. *)
  (* gen M. induction_wf IH: (@list_sub_wf A) l. intros M. apply M. *)
  apply M; clear M H Q.
  rewrite EQS. intros. xlocal.
  intros H Q v.
    rewrite EQS. eapply app_spec_2. xcf. intros. subst.
    xmatch. xret~.
  intros H Q x t J.
    rewrite EQS. eapply app_spec_2. xcf. intros. subst.
   xmatch.
   applys local_weaken_formula J. clears H Q. intros H Q. intros (Q'&J1&J2). 
   exists (Q' tt). split. skip. (* todo : fix apply J1. *) apply J2.
Qed.

Hint Extern 1 (RegisterSpec iter) => Provide iter_spec.


Lemma hsimpl_to_qunit' : forall (H:hprop),
  H ==> (fun _ => H) tt.
Proof. intros. subst. auto. Qed.
Hint Resolve hsimpl_to_qunit'.

Lemma test_spec : 
  Spec test (l:list func) |R>>
    forall L, 
    R (l ~> List Counter L) (# l ~> List Counter (LibList.map (fun i => i+1) L)).
Proof.
  xcf. intros l L. 
  xfun (fun g => Spec g f |R>> 
     forall (Q':int->hprop) H (Q:unit->hprop),
     app_1 f tt H Q' -> 
     (forall x, Q' x ==> Q tt) ->
     R H Q).
     intros M W. xlet. apply M. xret~.
   renames _f0 to g, S_f0 to Sg.
  xuntag. apply ( spec_elim_2 (@iter_spec func)).
  intros S LS Jn Jc.
  gen L. induction l as [|f l]; intros L.
  apply Jn. clear Jn Jc.
   hchange (@unfocus_nil' _ L _ Counter).
   hextract. subst. Opaque List.
   hchange (@focus_nil _ _ Counter). hsimpl.
 apply Jc. clear Jn Jc.
  unfold localize.  
  xchange (focus_cons' f l).
   xextract as n L' E. subst L.
   unfold Counter at 1.
   unfold hdata at 1.
   xextract as I HI. unfolds in HI.
   apply local_erase. esplit. split.
   eapply (spec_elim_1 Sg).
change (app_1 (B:=Z) f tt)
 with (tag tag_apply None (app_1 (B:=Z) f tt)).
xapp.
intros x. simpl. hextract. apply~ hsimpl_to_qunit.
 simpl. eapply local_wframe.
auto. apply ( IHl L'). hsimpl.
 hsimpl.
Qed.



 xuntag. 

 let f := spec_goal_fun tt in
      xfind f; let H := fresh in intro H.
Ieapply spec_elim_1.      
xapp_spec_core H idcont.
; clear H

xapp_core __ idcont.  
xapp_manual.

    apply (spec_elim_1 HI).
 (* todo: add tags*)
  apply (spec_elim_1 Sg).
  xchange (focus_cons' f l). 

 (* todo*)

  xextract I.
 
  


 hsimpl.  destruct  appl.
 apply H.
  apply local_erase. n a pply spec_elim
  xapp_manual.
  apply KR; clear KR. intros S Jn Jc. 
  
  destruct l.
  

Qed.

(*
  (* gen M. induction_wf IH: (@list_sub_wf A) l. intros M. apply M. *)
  apply M.
  intros v.
    rewrite EQS. eapply app_spec_2. xcf. intros. subst.
    xmatch. xret~.
  intros x t J.
     rewrite EQS. eapply app_spec_2. xcf. intros. subst.
     xmatch.
    eapply local_weaken_formula. apply J. clears H Q. intros H Q.
    intros (Q'&J1&J2). 
    exists (Q' tt). split. skip. (* todo : fix apply J1. *) apply J2.
Qed
     rewrite EQS. eapply app_spec_2. xcf. intros. subst.
     xmatch.
    eapply local_weaken_formula. apply J. clears H Q. intros H Q.
    intros (Q'&J1&J2). 
    exists (Q' tt). split. skip. (* todo : fix apply J1. *) apply J2.
Qed.*)

  rewrite 

QeEQS.
  forwards J: iter_cf. skip. skip.
  
eapply (spec_elim_2 J).
 eapply app_spec_2.
  apply 
  xcf. intros. subst. 
  xmatch. xret. auto.
subst. xmatch. xret~.  
  forwards J: (iter_cf (K:= fun f' l' R => f' = f -> l' = l -> R H Q));
   [ | | apply~ (spec_elim_2 J) ].
  intros_all~.

; [ | | lets: (sp_elim_2 J) ].
skip.
skip.
.

eapply app_spec_2. 
apply spec_intro_2. skip. skip. intros.
apply H0.
 skip.
  sets_eq S: (app_2 (A1:=val) (A2:=list A) (B:=unit) iter f). 
 (*   specializes M S. *)
  (* gen M. induction_wf IH: (@list_sub_wf A) l. intros M. apply M. *)
  apply M.
  intros v.
    rewrite EQS. eapply app_spec_2. xcf. intros. subst.
    xmatch. xret~.
  intros x t J.
    rewrite EQS. eapply app_spec_2. xcf. intros. subst.
   xmatch.
   applys local_weaken_formula J. clears H Q. intros H Q. intros (Q'&J1&J2). 
   exists (Q' tt). split. skip. (* todo : fix apply J1. *) apply J2.
Qed.

Lemma test_spec : 
  Spec test (l:list func) |R>>
    forall L, 
    R (l ~> List Counter L) (l ~> List Counter (map S L)).


(*
  (* gen M. induction_wf IH: (@list_sub_wf A) l. intros M. apply M. *)
  apply M.
  intros v.
    rewrite EQS. eapply app_spec_2. xcf. intros. subst.
    xmatch. xret~.
  intros x t J.
     rewrite EQS. eapply app_spec_2. xcf. intros. subst.
     xmatch.
    eapply local_weaken_formula. apply J. clears H Q. intros H Q.
    intros (Q'&J1&J2). 
    exists (Q' tt). split. skip. (* todo : fix apply J1. *) apply J2.
Qed.*)

  rewrite EQS.
  forwards J: iter_cf. skip. skip.
  
eapply (spec_elim_2 J).
 eapply app_spec_2.
  apply 
  xcf. intros. subst. 
  xmatch. xret. auto.
subst. xmatch. xret~.

 apply M.
 
 induction l; intros.
  apply M.
  intros V. rewrite EQS. eapply app_spec_2. xcf. intros. subst. xmatch. xret~.

  intros x l V. rewrite EQS. eapply app_spec_2. xcf. intros. subst. xmatch.  
  eapply local_weaken_formula. apply V. clears H Q. intros H Q.
  intros (Q'&J1&J2). 
  exists (Q' tt). split. skip. (* todo : fix apply J1. *)
  apply J2.

  
  eapply M.
  Qed.
  




(* Details of the proof:

  xcf. xgo. 
  xfun (counter_spec (fun n => x ~> RefOn n)).
    xapp. intro_subst. xapp. xret. ximpl~.
  xret. ximpl~.

*)

(* details of hsimpl:

hsimpl_setup tt.
hsimpl_step tt.
apply hsimpl_cancel_eq_1.
eapply refl_equal.
hsimpl_step tt.
hsimpl_step tt.
hsimpl_step tt.

*)



Lemma iter_spec : forall A,
  Spec iter (f:func) (l:list A) | R>>
    forall H (Q:unit->hprop),
    (forall (S:list A -> _ -> _ -> Prop),
       (forall H Q, H ==> Q tt -> S nil H Q) ->
       (forall H Q x l,
          (localize H Q (fun (H:hprop) (Q:unit->hprop) => 
             exists Q':unit->hprop,
             app_1 f x H Q' /\ S l (Q' tt) Q) -> S (x::l) H Q)) ->
      S l H Q) -> 
   R H Q.
Proof.
  intros. xintros. intros f l H Q M.
(*
  specializes M (@app_2 Func (list A) unit iter f).  
  forwards J: (iter_cf (K:= fun f' l' R => f' = f -> l' = l -> R H Q));
   [ | | ]. skip. skip. lets: (spec_elim_2 J).
*)
 sets_eq S: (app_2 (A1:=val) (A2:=list A) (B:=unit) iter f). 
 (*   specializes M S. *)
  (* gen M. induction_wf IH: (@list_sub_wf A) l. intros M. apply M. *)
  apply M; clear M H Q.
  intros H Q v.
    rewrite EQS. eapply app_spec_2. xcf. intros. subst.
    xmatch. xret~.
  intros H Q x t J.
    rewrite EQS. eapply app_spec_2. xcf. intros. subst.
   xmatch.
   applys local_weaken_formula J. clears H Q. intros H Q. intros (Q'&J1&J2). 
   exists (Q' tt). split. skip. (* todo : fix apply J1. *) apply J2.
Qed.



Lemma iter_spec : forall A,
  Spec iter (f:func) (l:list A) | R>>
    forall H (Q:unit->hprop),
    (forall (S:list A -> _ -> _ -> Prop),
       (forall, H ==> Q tt -> S nil H Q) ->
       (forall x l,
          (localize H Q (fun (H:hprop) (Q:unit->hprop) => 
             exists Q':unit->hprop,
             app_1 f x H Q' /\ S l (Q' tt) Q) -> S (x::l) H Q)) ->
      S l H Q) -> 
   R H Q.
Proof.
  intros. xintros. intros f l H Q M.
(*
  specializes M (@app_2 Func (list A) unit iter f).  
  forwards J: (iter_cf (K:= fun f' l' R => f' = f -> l' = l -> R H Q));
   [ | | ]. skip. skip. lets: (spec_elim_2 J).
*)
 sets_eq S: (app_2 (A1:=val) (A2:=list A) (B:=unit) iter f). 
 (*   specializes M S. *)
  (* gen M. induction_wf IH: (@list_sub_wf A) l. intros M. apply M. *)
  apply M; clear M.
  intros v.
    rewrite EQS. eapply app_spec_2. xcf. intros. subst.
    xmatch. xret~.
  intros x t J.
    rewrite EQS. eapply app_spec_2. xcf. intros. subst.
   xmatch.
   applys local_weaken_formula J. clears H Q. intros H Q. intros (Q'&J1&J2). 
   exists (Q' tt). split. skip. (* todo : fix apply J1. *) apply J2.
Qed.

Hint Extern 1 (RegisterSpec iter) => Provide iter_spec.
