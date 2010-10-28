Set Implicit Arguments.
Require Import LibCore CFLib MutableList_ml LibList.
Module ML := MutableList_ml.
Opaque MList Ref MListSeg.

(*todo:remove
Ltac xapps_core spec args solver ::=
  let cont1 tt :=
    xapp_with spec args solver in
  let cont2 tt :=
    instantiate; xextract; try intro_subst in    
  match ltac_get_tag tt with
  | tag_let_trm => xlet; [ cont1 tt | cont2 tt ]
  | tag_seq =>     xseq; [ cont1 tt | cont2 tt ]
  end.
*)


Lemma himpl_extens : forall H1 H2 : hprop,
  H1 ==> H2 -> H2 ==> H1 -> H1 = H2.
Proof. intros. unfold hprop. extens*. Qed.

Lemma himpl_proj1 : forall H1 H2 : hprop,
  H1 = H2 -> H1 ==> H2.
Proof. intros. subst~. Qed.

Lemma himpl_proj2 : forall H1 H2 : hprop,
  H1 = H2 -> H2 ==> H1.
Proof. intros. subst~. Qed.
(*
Lemma himpl_id : forall H1 H2 : hprop,
  H1 ==> H2 -> H1 ==> H2.
Proof. auto. Qed.
Implicit Arguments himpl_id [H1 H2].
*)

Implicit Arguments himpl_proj1 [H1 H2].
Implicit Arguments himpl_proj2 [H1 H2].
Implicit Arguments himpl_extens [H1 H2].


Ltac hchange_apply L cont :=
  eapply hchange_lemma; 
    [ apply L | cont tt | ].

Ltac hchange_forwards L modif cont :=
  let K := fresh "TEMP" in
  forwards_nounfold K: L; 
  match modif with
  | __ => hchange_apply K cont
  | _ => hchange_apply (@modif _ _ K) cont
  end; clear K.

Ltac hchange_core E modif :=
  match E with
(*  | ?H ==> ?H' => hchange_with_core H H' *)
  | _ => hchange_forwards E modif ltac:(fun _ => instantiate; hsimpl)
  end.

Tactic Notation "hchange_debug" constr(E) :=
  hchange_forwards E __ ltac:(idcont).
Tactic Notation "hchange_debug" "->" constr(E) :=
  hchange_forwards E himpl_proj1 ltac:(idcont).
Tactic Notation "hchange_debug" "<-" constr(E) :=
  hchange_forwards himpl_proj2 ltac:(idcont).

Tactic Notation "hchange" constr(E) :=
  hchange_core E __.
Tactic Notation "hchange" "->" constr(E) :=
  hchange_core E himpl_proj1.
Tactic Notation "hchange" "<-" constr(E) :=
  hchange_core E himpl_proj2.


Tactic Notation "hchange" "~" constr(E) :=
  hchange E; auto~.
Tactic Notation "hchange" "*" constr(E) :=
  hchange E; auto*.







Ltac xchange_apply L cont :=
   eapply xchange_lemma; 
     [ try xlocal | apply L | cont tt | ].

(* note: modif should be himpl_proj1 or himpl_proj2 *)
Ltac xchange_forwards L modif cont :=
  let K := fresh "TEMP" in
  forwards_nounfold K: L; 
  match modif with
  | __ => xchange_apply K cont
  | _ => xchange_apply (@modif _ _ K) cont
  end; clear K.

Ltac xchange_with H H' :=
  eapply xchange_lemma with (H1:=H) (H1':=H'); 
    [ try xlocal | | hsimpl | ].

Ltac xchange_core E modif :=
  match E with
  | ?H ==> ?H' => xchange_with_core H H'
  | _ => xchange_forwards E modif ltac:(fun _ => instantiate; hsimpl)
  end.

Tactic Notation "xchange_debug" constr(E) :=
  xchange_forwards E __ ltac:(idcont).
Tactic Notation "xchange_debug" "->" constr(E) :=
  xchange_forwards E himpl_proj1 ltac:(idcont).
Tactic Notation "xchange_debug" "<-" constr(E) :=
  xchange_forwards himpl_proj2 ltac:(idcont).

Tactic Notation "xchange" constr(E) :=
  xchange_core E __.
Tactic Notation "xchange" "->" constr(E) :=
  xchange_core E himpl_proj1.
Tactic Notation "xchange" "<-" constr(E) :=
  xchange_core E himpl_proj2.


Tactic Notation "xchange" "~" constr(E) :=
  xchange E; auto~.


Lemma heap_is_single_null_eq_false : forall A (v:A),
  heap_is_single null v = [False].
Proof. intros.  Transparent heap_is_empty_st heap_is_single. unfold heap_is_single.
 unfold hprop. extens. intros. unfold heap_is_empty_st. auto*.
Opaque heap_is_single heap_is_empty_st.
Qed.

Lemma heap_is_single_null_to_false : forall A (v:A),
  heap_is_single null v ==> [False].
Proof. introv Hh. forwards*: heap_is_single_null. Qed. 


(********************************************************************)
(* ** Representation predicate for mutable lists *)

Fixpoint MList A a (T:A->a->hprop) (L:list A) (l:loc) : hprop :=
  match L with
  | nil => [l = null]
  | X::L' => l ~> Mlist T (MList T) X L'
  end.

Section MListProp.
Variables (A a : Type) (T:A->a->hprop).

Lemma MList_nil : forall l,
  l ~> MList T nil = [l = null].
Proof. intros. hdata_simpl Mlist. auto. Qed.

Lemma MList_cons : forall l X L',
  l ~> MList T (X::L') = 
  Hexists x l', l ~> Mlist Id Id x l' \* x ~> T X \* l' ~> MList T L'.
Proof. intros. simpl. hdata_simpl. rewrite~ Mlist_convert. Qed.

Lemma MList_null : forall L,
  null ~> MList T L = [L = nil].
Proof.
  intros. destruct L; simpl; hdata_simpl.
  apply himpl_extens; xsimpl~.
  apply himpl_extens.
    unfold Mlist. hdata_simpl. hextract. 
     rewrite heap_is_single_null_eq_false. hextract. false.
    hextract. false.
Qed.  

Lemma MList_not_null : forall l L,
  l <> null -> 
  l ~> MList T L ==> l ~> MList T L \* [L <> nil].
Proof.
  intros. destruct L.
  hchange -> (MList_nil l). hextract. false.
  hsimpl. auto_false.
Qed.




(*------------------------------------------------------------------*)
(* ** MLists *)


Lemma focus_mnil : forall A a (T:A->a->hprop),
  [] ==> null ~> MList T nil.
Proof. intros. simpl. hdata_simpl. hsimpl~. Qed.

Lemma unfocus_mnil : forall (l:loc) A a (T:A->a->hprop),
  l ~> MList T nil ==> [l = null].
Proof. intros. simpl. hdata_simpl. hsimpl~. Qed.

Lemma unfocus_mnil' : forall A (L:list A) a (T:A->a->hprop),
  null ~> MList T L ==> [L = nil].
Proof.
  intros. destruct L.
  simpl. unfold hdata. hextract. hsimpl~. 
  unfold hdata, MList. hchange focus_ref2_null. hextract. false.
Qed.

Lemma unfocus_mnil'' : forall (l:loc) A (L:list A) a (T:A->a->hprop),
  l ~> MList T L ==> [l = null <-> L = nil] \* l ~> MList T L.
Proof. skip. (*todo*) Qed.

Lemma focus_mcons : forall (l:loc) a A (X:A) (L':list A) (T:A->a->hprop),
  (l ~> MList T (X::L')) ==>
  Hexists x l', (x ~> T X) \* (l' ~> MList T L') \* (l ~> Ref Id (x,l')).
Proof.
  intros. simpl. hdata_simpl. hchange (@focus_ref2 l). hextract. hsimpl.
Qed.

Lemma focus_mcons' : forall (l:loc) a A (L:list A) (T:A->a->hprop),
  [l <> null] \* (l ~> MList T L) ==> 
  Hexists x l', Hexists X L', 
    [L = X::L'] \*  (l ~> Ref Id (x,l')) \* (x ~> T X) \* (l' ~> MList T L').
Proof.
  intros. destruct L. lets: (@unfocus_mnil l _ _ T). (* Show Existentials. *)
  hextract. false~.
  hchange (@focus_mcons l). hextract as x l' E. hsimpl~.  
Qed.

Lemma unfocus_mcons : forall (l:loc) a (x:a) (l':loc) A (X:A) (L':list A) (T:A->a->hprop),
  (l ~> Ref Id (x,l')) \* (x ~> T X) \* (l' ~> MList T L') ==> 
  (l ~> MList T (X::L')).
Proof.
  intros. simpl. hdata_simpl. hchange (@unfocus_ref2 l _ x _ l'). hsimpl.
Qed.

Global Opaque MList.

Implicit Arguments unfocus_mnil [ ].
Implicit Arguments unfocus_mcons [ a A ].
Implicit Arguments focus_mcons [ a A ].



(********************************************************************)
(* ** Destructive append *)

Lemma append_spec : forall a,
  Spec ML.append (l1:mlist a) (l2:mlist a) |R>> forall A (T:A->a->hprop) (L1 L2:list A),
     R (l1 ~> MList T L1 \* l2 ~> MList T L2) (~> MList T (L1 ++ L2)).
Proof.
  xcf. intros. xapps. xif.
  xret. hchange unfocus_mnil'. hextract. subst. auto.
  xchange (unfocus_mnil'' l1). xextract as N. asserts* NL1: (L1 <> nil). clear N. 
  xapp.
  xseq (Hexists (e:loc), Hexists X LX, l1 ~> MListSeg e T LX 
     \* l2 ~> MList T L2 \* e ~> MList T (X::nil) \* h ~> Ref Id e \* [L1 = LX&X]).
  xwhile_manual (fun L12 => Hexists (L11:list A) (e:loc),
    l1 ~> MListSeg e T L11 \* h ~> Ref Id e \* e ~> MList T L12 \* [L1 = L11 ++ L12] \* [L12 <> nil])
    (fun L12 => forall X:A, L12 <> X::nil) (@list_sub A) L1 as L12.
   hchange (focus_msnil l1 T). hsimpl~ (@nil A) l1.
   xextract as L11 e E NL12. xapps. 
    sets_eq R:L12; destruct R as [|X L12']. false.
    xchange (focus_mcons e). xextract as x t.
    xapps. xapps. intros Hb. xret.
    hchange (unfocus_mcons e x t X L12'). hsimpl~.
      applys bool_of_impl_neg Hb. iff M.
        intros Y EY. inversions EY. false.
        intros EY. subst. false.
   xextract as L11 e E NL12 TL12. 
    xapps. 
    sets_eq R:L12; destruct R as [|X L12']. false.
    xchange (focus_mcons e). xextract as x t.
    xapps. xapp. intros _.
    hchange (focus_msnil t T).
    hchange (unfocus_mscons e x t t X nil).
    hchange (focus_msapp l1 e). hsimpl.
      auto.
      intros Y. subst. false.
      rew_app~.
   hextract as L11 e E1 N2 E2. xclean. 
    rew_classic in E2. destruct E2 as [x E2]. rew_classic in E2.
    subst L12. subst L1. hsimpl~.
  intros e X LX E. subst L1. xapps. hdata_simpl.
  xchange (focus_mcons e). xextract as x t.
   xapp. xret_gc. 
   hchange (unfocus_mcons e x l2 X L2 T).
   hchange (mlist_to_mlistseg e).   
   hchange (focus_msapp l1 e).
   hchange (mlistseg_to_mlist l1). rew_app. hsimpl.  
Admitted.
(*save time of Qed.*)




(********************************************************************)
(* ** Length *)
(*
Lemma mlength_spec : forall a,
  Spec mlength (l:mlist a) |R>> forall A (T:A->a->hprop) (L:list A),
     R (l ~> List T L) (\= (length L : int)).
Proof.
  xcf. unfold mlist. intros.
  xapp. xapp. xseq (Hexists l', n ~> @RefOn int (length L) \* p ~> RefOn l' \* l' ~> List T nil).
    (* todo : xseq automatic if xwhile *)
  xuntag. apply local_erase. exists (list A) (fun L' => Hexists k:int, Hexists l',
     n ~> RefOn k \* p ~> RefOn l' \* l' ~> List T L' \* [k + length L' = length L]) (@list_sub A).
  splits. prove_wf. exists L. hsimpl. math.
  intros L'. xextract. intros k l' E. apply local_erase. 
  skip.
  intros l'. xgc. xapp. xsimpl. auto. 
Qed.
*)


(********************************************************************)
(* ** In place reversal *)


(*-------------

Lemma rev_spec : forall a,
  Spec ListRev_ml.rev (l:mlist a) |R>> forall A (T:A->a->hprop) (L:list A),
     R (l ~> List T L) (~> List T (LibList.rev L)).
Proof.
  xcf. intros.
  xapp. 
  xapp. xchange (focus_nil T). xchange (@unfocus_ref r _ null).
  xseq.
  (* todo: xwhile loops *)
  xwhile_core_debug (fun L1 => Hexists L2, 
     f ~> Ref (List T) L1 \* r ~> Ref (List T) L2 \* [L = rev L2 ++ L1]) (@list_sub A) L.
    prove_wf.
    exists L. hchange (@unfocus_ref f _ l). hsimpl. rew_list~.
    intros L1. xextract as L2 E. xchange (@focus_ref f). xextract as fl. xcond.
      xapp. intro_subst. xapp. intros b. hextract as Eb. subst b. hsimpl. xclean.
      intros Eb. xclean. xchange~ (@focus_cons' fl). xextract as x fl' X L'. intro_subst.
      xapp. intro_subst. 
      xapp. intro_subst.
      xmatch.
      xchange (@focus_ref r). xextract as b. 
      xapp. intro_subst.
      xlet as rl'. xapp. simpl.
      xapp. 
      xapp. intros _.
      hchange (@unfocus_cons rl' _ x b A).
      hchange (@unfocus_ref r _ rl').
      hchange (@unfocus_ref f _ fl').
      hsimpl. auto. rew_list~. 
     hextract as F. xclean. subst fl.
     hchange (unfocus_nil'). hextract. subst L1. rew_list in E. 
      rewrite <- (@rev_rev _ L2). rewrite <- E. hsimpl.
  xchange (@focus_ref r). xlocal. (* todo: why? *)
  xextract as x. xapp. intros z. hextract. subst. hsimpl.
Qed.







  (*
   eapply (@xwhile_frame _ (fun L' => Hexists k l',
     n ~> RefOn k \* p ~> RefOn l' \* l' ~> List T L' \* [k + length L' = length L]) (@list_sub _)).

  xwhile_manual (fun L' => Hexists k l',
     n ~> RefOn k \* p ~> RefOn l' \* l' ~> List T L' \* [k + length L' = length L])
     (@list_sub A). L
  *)



-------------*)














