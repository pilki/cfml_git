Set Implicit Arguments.
Require Import LibCore CFPrim MutableList_ml LibList.
Module ML := MutableList_ml.
Opaque MList Ref MListSeg.

(*todo:remove*)
Ltac xapps_core spec args solver ::=
  let cont1 tt :=
    xapp_with spec args solver in
  let cont2 tt :=
    instantiate; xextract; try intro_subst in    
  match ltac_get_tag tt with
  | tag_let_trm => xlet; [ cont1 tt | cont2 tt ]
  | tag_seq =>     xseq; [ cont1 tt | cont2 tt ]
  end.


(********************************************************************)
(* ** Accessors *)

Lemma is_nil_spec : forall a,
  Spec is_nil (l:mlist a) |R>> forall A (T:A->a->hprop) (L:list A),
     keep R (l ~> MList T L) (\[ bool_of (L = nil) ]).
Proof.
  xcf. intros. xapp. intros b. hextract.
  hchange (unfocus_mnil'' l). hextract. subst b. hsimpl. xclean. iff*.
Qed.

Lemma head_spec : forall a,
  Spec ML.head (l:mlist a) |R>> forall (x:a) (t:mlist a),
    keep R (l ~> Ref Id (x,t)) (\= x).
Proof. 
  xcf. intros. xapps. xret.
Qed.

Lemma tail_spec : forall a,
  Spec ML.tail (l:mlist a) |R>> forall (x:a) (t:mlist a),
    keep R (l ~> Ref Id (x,t)) (\= t).
Proof. 
  xcf. intros. xapps. xret.
Qed.

Lemma set_head_spec : forall a,
  Spec ML.set_head (l:mlist a) (x:a) |R>> forall (x':a) (t:mlist a),
    R (l ~> Ref Id (x',t)) (# l ~> Ref Id (x,t)).
Proof. 
  xcf. intros. xapps. xmatch. xapp. hsimpl.
Qed.

Lemma set_tail_spec : forall a,
  Spec ML.set_tail (l:mlist a) (t:mlist a) |R>> forall (x:a) (t':mlist a),
    R (l ~> Ref Id (x,t')) (# l ~> Ref Id (x,t)).
Proof. 
  xcf. intros. xapps. xmatch. xapp. hsimpl.
Qed.


Hint Extern 1 (RegisterSpec is_nil) => Provide is_nil_spec.
Hint Extern 1 (RegisterSpec ML.head) => Provide head_spec.
Hint Extern 1 (RegisterSpec ML.tail) => Provide tail_spec.
Hint Extern 1 (RegisterSpec ML.set_head) => Provide set_head_spec.
Hint Extern 1 (RegisterSpec ML.set_tail) => Provide set_tail_spec.



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














