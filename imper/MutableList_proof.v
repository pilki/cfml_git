Set Implicit Arguments.

Require Import List LibTactics.
Ltac forwards_nounfold_then Ei cont :=
  let args := ltac_args Ei in
  let args := (eval simpl in (args ++ ((boxer ___)::nil))) in
  build_app args cont.



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
    [ applys L | cont tt | ].

Ltac hchange_forwards L modif cont :=
  forwards_nounfold_then L ltac:(fun K =>
  match modif with
  | __ => 
     match type of K with
     | _ = _ => hchange_apply (@himpl_proj1 _ _ K) cont
     | _ => hchange_apply K cont
     end
  | _ => hchange_apply (@modif _ _ K) cont
  end).

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
     [ try xlocal | applys L | cont tt | ].

(* note: modif should be himpl_proj1 or himpl_proj2 *)
Ltac xchange_forwards L modif cont :=
  forwards_nounfold_then L ltac:(fun K =>
  match modif with
  | __ => 
     match type of K with
     | _ = _ => xchange_apply (@himpl_proj1 _ _ K) cont
     | _ => xchange_apply K cont
     end
  | _ => xchange_apply (@modif _ _ K) cont
  end).
(*
  let K := fresh "TEMP" in
  forwards_nounfold K: L; 
  match modif with
  | __ => 
     match type of K with
     | _ = _ => xchange_apply (@himpl_proj1 _ _ K) cont
     | _ => xchange_apply K cont
     end
  | _ => xchange_apply (@modif _ _ K) cont
  end; clear K.
*)

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



Tactic Notation "xchange" constr(E) "as" := 
  xchange E; try xextract.
Tactic Notation "xchange" constr(E) "as" simple_intropattern(I1) := 
  xchange E; try xextract as I1.
Tactic Notation "xchange" constr(E) "as" simple_intropattern(I1) simple_intropattern(I2) := 
  xchange E; try xextract as I1 I2.
Tactic Notation "xchange" constr(E) "as" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) := 
  xchange E; try xextract as I1 I2 I3.
Tactic Notation "xchange" constr(E) "as" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) := 
  xchange E; try xextract as I1 I2 I3 I4. 
Tactic Notation "xchange" constr(E) "as" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5) := 
  xchange E; try xextract as I1 I2 I3 I4 I5. 



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

Lemma MList_nil : forall l (A a : Type) (T:A->a->hprop),
  l ~> MList T nil = [l = null].
Proof. intros. hdata_simpl Mlist. auto. Qed.

Lemma MList_cons : forall l (A a : Type) (T:A->a->hprop) X L',
  l ~> MList T (X::L') = 
  Hexists x l', l ~> Mlist Id Id x l' \* x ~> T X \* l' ~> MList T L'.
Proof. intros. simpl. hdata_simpl. rewrite~ Mlist_convert. Qed.

Lemma MList_uncons : forall l a x l' (A : Type) (T:A->a->hprop) X L',
  l ~> Mlist Id Id x l' \* x ~> T X \* l' ~> MList T L' ==> 
  l ~> MList T (X::L').
Proof. intros. rewrite MList_cons. hsimpl. Qed.

Implicit Arguments MList_uncons [a A].

Lemma MList_null : forall A L (a : Type) (T:A->a->hprop),
  null ~> MList T L = [L = nil].
Proof.
  intros. destruct L; simpl; hdata_simpl.
  apply himpl_extens; xsimpl~.
  apply himpl_extens.
    unfold Mlist. hdata_simpl. hextract. 
     rewrite heap_is_single_null_eq_false. hextract. false.
    hextract. false.
Qed.  

Lemma MList_null_keep : forall A L (a : Type) (T:A->a->hprop),
  null ~> MList T L ==> null ~> MList T L \* [L = nil].
Proof.
  intros. destruct L.
  hsimpl. auto.
  hchange MList_null. hextract. false.
Qed.

Lemma MList_not_null_kepp : forall l A L (a : Type) (T:A->a->hprop),
  l <> null -> 
  l ~> MList T L ==> l ~> MList T L \* [L <> nil].
Proof.
  intros. destruct L.
  hchange -> (MList_nil l T). hextract. false.
  hsimpl. auto_false.
Qed.

Implicit Arguments MList_not_null_kepp [A a].

Lemma MList_not_null : forall l A L (a : Type) (T:A->a->hprop),
  l <> null -> 
  l ~> MList T L ==> Hexists x l' X L', [L = X::L'] \*
    l ~> Mlist Id Id x l' \* x ~> T X \* l' ~> MList T L'.
Proof.
  intros. hchange~ (MList_not_null_kepp l). hextract. 
  destruct L; tryfalse.
  hchange (MList_cons l). hextract. hsimpl~.
Qed.
  
Implicit Arguments MList_not_null [A a].







Notation "l '~~>' v" := (l ~> Ref Id v)
  (at level 32, no associativity) : heap_scope.

Ltac asserts_apply_core E cont := 
  let H := fresh "TEMP" in asserts H: E; [ | applys H; cont tt ].

Tactic Notation "asserts_apply" constr(E) :=
  asserts_apply_core E idcont.

Tactic Notation "asserts_apply" "~" constr(E) :=
  asserts_apply_core E ltac:(fun _ => auto_tilde).
Tactic Notation "asserts_apply" "*" constr(E) :=
  asserts_apply_core E ltac:(fun _ => auto_star).

Tactic Notation "xapply_local" constr(E) :=
  forwards_nounfold_then E ltac:(fun K => 
    eapply local_wframe; [xlocal | sapply K | | ]).

Tactic Notation "xapply_local" "~" constr(E) :=
  xapply_local E; auto_tilde.
Tactic Notation "xapply_local" "*" constr(E) :=
  xapply_local E; auto_star.

(*todo*)
Tactic Notation "xapply_local_pre" constr(E) :=
  eapply local_weaken_pre; [xlocal | sapply E | ].

Tactic Notation "xgeneralize" constr(E) "as" ident(H) :=
  cuts H: E; [ eapply local_weaken_pre; [xlocal | | ] | ].

Tactic Notation "xgeneralize" constr(E) :=
  let H := fresh "Inv" in xgeneralize E as H.


Ltac xwhile_intros tt :=
  let R := fresh "R" in let LR := fresh "L" R in
  let HR := fresh "H" R in 
  apply local_erase; intros R LR HR.

Ltac xwhile_pre cont :=
  match ltac_get_tag tt with
  | tag_seq => xseq; [ cont tt | ]
  | tag_while => cont tt
  end.

Tactic Notation "xwhile" :=
  xwhile_pre ltac:(fun _ => xwhile_intros tt).
Tactic Notation "xwhile" constr(E) :=
  xwhile_pre ltac:(fun _ => xwhile_intros tt; xgeneralize E).

Global Opaque loc.



Notation "'Lets' x ':=' F1 'in' F2" :=
  (!T (fun H Q => exists Q1, F1 H Q1 /\ forall x, F2 (Q1 x) Q))
  (at level 69, a at level 0, x ident, right associativity,
  format "'[v' '[' 'Lets'  x  ':='  F1  'in' ']'  '/'  '[' F2 ']' ']'") : charac.
(* todo: coqbug: pas de warning si un autre format existe déjà *)


Notation "'While' Q1 'Do' Q2 'Done'" :=
  (!While (fun H Q => forall R:~~unit, is_local R ->
        (forall H Q, (If_ Q1 Then (Q2 ;; R) Else (Ret tt)) H Q -> R H Q)
        -> R H Q))
  (at level 69) : charac.

Tactic Notation "xif_after" ident(H) :=
  xif_after H.

Tactic Notation "xif_after" :=
  let H := fresh "H" in xif_after H.

 
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
   applys (>>> Inv l). hsimpl.
   clear l L. intros L. induction_wf IH: (@list_sub_wf A) L; intros.
   apply HR. clear HR. xif. xapps. xapp.
   (* case cons *)
   xextract as E. xchange (MList_not_null l) as x l' X L' EL. auto.
   xapps. xapps. xapps. xapp. subst L. xapply_local~ (>>> IH L' l').
   hsimpl. intros _. hchange (MList_uncons l x l' T). hsimpl. rew_length. math.
   (* case nil *)
   xextract as E. subst. xchange MList_null_keep as M. subst. 
    xret. xsimpl. rew_length. math.
  xapp. hsimpl.
Qed.




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














