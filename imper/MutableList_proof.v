Set Implicit Arguments.
Require Import LibCore CFLib MutableList_ml LibList.


(********************************************************************)
(* ** Representation predicate and focus lemmas for mutable lists *)

Fixpoint MList A a (T:A->a->hprop) (L:list A) (l:loc) : hprop :=
  match L with
  | nil => [l = null]
  | X::L' => l ~> Mlist T (MList T) X L'
  end.

Lemma MList_nil : forall l (A a : Type) (T:A->a->hprop),
  l ~> MList T nil = [l = null].
Proof. intros. hdata_simpl Mlist. auto. Qed.

Lemma MList_unnil : forall (A a : Type) (T:A->a->hprop),
  [] ==> null ~> MList T nil.
Proof. intros. rewrite MList_nil. hsimpl~. Qed.

Lemma MList_cons : forall l (A a : Type) (T:A->a->hprop) X L',
  l ~> MList T (X::L') = 
  Hexists x l', l ~> Mlist Id Id x l' \* x ~> T X \* l' ~> MList T L'.
Proof. intros. simpl. hdata_simpl. rewrite~ Mlist_convert. Qed.

Lemma MList_uncons : forall l a x l' (A : Type) (T:A->a->hprop) X L',
  l ~> Mlist Id Id x l' \* x ~> T X \* l' ~> MList T L' ==> 
  l ~> MList T (X::L').
Proof. intros. rewrite MList_cons. hsimpl. Qed.

Lemma MList_null : forall A L (a : Type) (T:A->a->hprop),
  null ~> MList T L = [L = nil].
Proof.
  intros. destruct L; simpl; hdata_simpl.
  apply pred_le_extens; xsimpl~.
  apply pred_le_extens.
    unfold Mlist. hdata_simpl. hextract. 
     rewrite heap_is_single_null_eq_false. hextract.
    hextract.
Qed.  

Lemma MList_null_keep : forall A L (a : Type) (T:A->a->hprop),
  null ~> MList T L ==> null ~> MList T L \* [L = nil].
Proof.
  intros. destruct L.
  hsimpl~.
  rewrite MList_null. hsimpl.
Qed.

Lemma MList_not_null_keep : forall l A L (a : Type) (T:A->a->hprop),
  l <> null -> 
  l ~> MList T L ==> l ~> MList T L \* [L <> nil].
Proof.
  intros. destruct L.
  hchanges -> (MList_nil l T).
  hsimpl. auto_false.
Qed.

Lemma MList_not_null : forall l A L (a : Type) (T:A->a->hprop),
  l <> null -> 
  l ~> MList T L ==> Hexists x l' X L', [L = X::L'] \*
    l ~> Mlist Id Id x l' \* x ~> T X \* l' ~> MList T L'.
Proof.
  intros. hchange~ (@MList_not_null_keep l). hextract.
  destruct L; tryfalse.
  hchange (MList_cons l). hextract. hsimpl~.
Qed.
  
Lemma Mlist_not_null : forall l a (x:a) l',
  l ~> Mlist Id Id x l' ==> l ~> Mlist Id Id x l' \* [l <> null].
Proof.
  intros. test (l = null); [ subst | hsimpl~ ].
  hdata_simpl Mlist. hextract.
  rewrite heap_is_single_null_eq_false. hsimpl.
Qed.

Implicit Arguments MList_uncons [a A].
Implicit Arguments MList_null_keep [A].
Implicit Arguments MList_not_null_keep [A a].
Implicit Arguments MList_not_null [A a].

Global Opaque MList.


(********************************************************************)
(* ** CPS-append *)

Lemma cps_mappend_spec : forall a b A,
  Spec cps_mappend (x:loc) (y:loc) (k:func) |R>>
     forall (L M:list A) (T:A->a->hprop) H (Q:b->hprop),
     (forall z, AppReturns k z (z ~> MList T (L++M) \* H) Q) ->
     R (x ~> MList T L \* y ~> MList T M \* H) Q.
Proof.
  intros. xinduct (unproj41 loc loc func (@list_sub A)).
  xcf. intros x y k L IH M T H Q Sk. xapps. xif.
  xchange MList_null as E. subst. apply Sk.
   (* ideally should be: xchange (MList_not_null x) as v l' V L' E; auto. *)
    xchange_debug (MList_not_null x). auto. hsimpl. xextract. intros v l' V L' E.
  subst L. 
   xfun (fun k' => Spec k' z |R>> 
     R (x ~> Mlist Id Id v l' \* v ~> T V \* z ~> MList T (L'++M) \* H) Q).
     xapp. xchange (>> MList_uncons x a A) as. applys_eq Sk 2. apply pred_le_extens; hsimpl.
   xapps. xapp~ (x ~> Mlist Id Id v l' \* v ~> T V \* H).
    intros. xapply_local* (spec_elim_1_1 Sf). xsimpl. xok.
Qed.

Hint Extern 1 (RegisterSpec cps_mappend) => Provide cps_mappend_spec.

(********************************************************************)
(* ** Imperative functional list iterator *)

Lemma miter_spec : forall a A,
  Spec miter (f:func) (m:loc) | R>>
    forall (T:A->a->hprop) H H' (L L':list A),
    (forall (I:list A -> list A -> hprop -> hprop -> Prop), 
       (forall H, I nil nil H H) ->
       (forall H'' H H' X X' L L',
          (forall x, (App f x;) (H \* x ~> T X) (# H'' \* x ~> T X')) ->
          I L L' H'' H' ->
          I (X::L) (X'::L') H H') ->
       I L L' H H') ->
    R (H \* m ~> MList T L) (# H' \* m ~> MList T L'). 
Proof.
  intros. xcf. introv M. xapp. xwhile.
  sets I: (fun L L' H H' => forall m, 
     R (H \* m ~> MList T L \* h ~> Ref Id m) (# H' \* m ~> MList T L')).
  specializes M I. unfold I in M at 4.
  apply M; clears H.
  (* nil *)
  intros. unfolds. intros. apply HR. xchange (@MList_nil m) as M. subst_hyp M.
  xlet. xapps. xapps. xextracts. xif. xret_gc. hchanges (MList_unnil).
  (* cons *)
  introv B1 B2. unfolds. intros. apply HR. xchange (@MList_cons m) as x m'.
   xchange (@Mlist_not_null m). xextract as N.
  xlet. xapps. xapps. xextracts. xif. 
  xseq. xapps. xapp_spec (@_get_hd_spec a loc). intro_subst.
  xseq. xapplys B1. apply hsimpl_to_qunit. reflexivity.
   (* xseq (# H'' \* m' ~> MList T L0 \* x ~> T X' \* h ~> Ref Id m \* m ~> Mlist Id Id x m').*)
  xapps. xapps. xapps. unfold I in B2. xapply B2. hsimpl. hsimpl.
  hchange (@MList_uncons m). hsimpl.
Qed.

Hint Extern 1 (RegisterSpec miter) => Provide miter_spec.


(********************************************************************)
(* ** Length *)

Lemma mlength_spec : forall a,
  Spec mlength (l:mlist a) |R>> forall A (T:A->a->hprop) (L:list A),
     R (l ~> MList T L) (\= (length L : int)).
Proof.
  xcf. intros. xapp. xapp. 
  xwhile. xgeneralize (forall L (k:int) l,
    R (n ~~> k \* h ~~> l \* l ~> MList T L) 
      (# n ~~> (k + length L) \* h ~~> null \* l ~> MList T L)).
   applys (>> Inv l). hsimpl.
   clear l L. intros L. induction_wf IH: (@list_sub_wf A) L; intros. 
   applys (rm HR). xlet. xapps. xapps. xifs.
   (* case cons *)
   (* TODO xchange (MList_not_null l) as x l' X L' EL. auto *)
   xchange_debug (MList_not_null l). auto. hsimpl. xextract. intros x l' X L' EL.
   xapps. xapps. xapps. xapp. subst L. xapply_local~ (>> IH L' l').
   hsimpl. intros _. hchanges (MList_uncons l). rew_length. math.
   (* case nil *)
   subst. xchange MList_null_keep as M. subst. 
    xrets. rew_length. math.
  xapp. hsimpl~.
Qed.

Hint Extern 1 (RegisterSpec mlength) => Provide mlength_spec.

(********************************************************************)
(* ** In-place reversal *)

Lemma rev_spec : forall a,
  Spec inplace_rev (l:mlist a) |R>> forall A (T:A->a->hprop) (L:list A),
     R (l ~> MList T L) (~> MList T (LibList.rev L)).
Proof.
  xcf. intros. xapps. xapps.
  xwhile. xgeneralize (forall Lf Lr lf lr,
    R (f ~~> lf \* lf ~> MList T Lf \* r ~~> lr \* lr ~> MList T Lr) 
      (# Hexists l', f ~~> null \* r ~~> l' \* l' ~> MList T (rev Lf ++ Lr))).
    applys Inv L (@nil A) l null. hchange (MList_unnil T). hsimpl.
    intros Lf. induction_wf IH: (@list_sub_wf A) Lf.
    intros. applys (rm HR). xlet. xapps. xapps. xifs.
    (* case cons *)
    (* TODO xchange (MList_not_null lf) as x lf' X Lf' EL. auto. *)
    xchange_debug (MList_not_null lf). auto. hsimpl. xextract. intros x lf' X Lf' EL.
    xseq. xapps. xapps. xapps. xapp. xapp. xapp.
    xchange (>> MList_uncons lf a A). subst Lf.
    xapply_local~ (>> (rm IH) Lf' (X::Lr) lf' lf). hsimpl. xsimpl. rew_rev~.
    (*case nil *)
    xret. hchange MList_null. xsimpl. subst~. 
  xextract as l'. xgc. xapp. rew_app. hextract. subst. hsimpl.
Qed.

Hint Extern 1 (RegisterSpec rev) => Provide rev_spec.

