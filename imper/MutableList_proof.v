Set Implicit Arguments.
Require Import LibCore CFPrim MutableList_ml LibList.

Opaque List Ref.



(*------------------------------------------------------------------*)
(* ** MListsSeg *)
(*--todo: define MList as MListSeg null *)

Fixpoint MListSeg (e:loc) A a (T:A->a->hprop) (L:list A) (l:loc) : hprop :=
  match L with
  | nil => [l = e]
  | X::L' => l ~> Ref2 T (MListSeg e T) X L'
  end.

Lemma focus_msnil : forall (e:loc) A a (T:A->a->hprop),
  [] ==> e ~> MListSeg e T nil.
Proof. intros. simpl. hdata_simpl. hsimpl~. Qed.

Lemma unfocus_msnil : forall (l e:loc) A a (T:A->a->hprop),
  l ~> MListSeg e T nil ==> [l = e].
Proof. intros. simpl. hdata_simpl. hsimpl~. Qed.

Lemma unfocus_msnil' : forall A (L:list A) (e:loc) a (T:A->a->hprop),
  null ~> MListSeg e T L ==> [L = nil] \* [e = null].
Proof.
  intros. destruct L.
  simpl. unfold hdata. xsimpl~. 
  unfold hdata, MListSeg. hchange focus_ref2_null. hextract. false.
Qed.

Lemma focus_mscons : forall (l e:loc) a A (X:A) (L':list A) (T:A->a->hprop),
  (l ~> MListSeg e T (X::L')) ==>
  Hexists x l', (x ~> T X) \* (l' ~> MListSeg e T L') \* (l ~> Ref Id (x,l')).
Proof.
  intros. simpl. hdata_simpl. hchange (@focus_ref2 l). xsimpl.
Qed.

Lemma focus_mscons' : forall (l e:loc) a A (L:list A) (T:A->a->hprop),
  [l <> e] \* (l ~> MListSeg e T L) ==> 
  Hexists x l', Hexists X L', 
    [L = X::L'] \*  (l ~> Ref Id (x,l')) \* (x ~> T X) \* (l' ~> MListSeg e T L').
Proof.
  intros. destruct L. lets: (@unfocus_msnil l e _ _ T). (* Show Existentials. *)
  hextract. false~.
  hchange (@focus_mscons l e). hextract as x l' E. hsimpl~.  
Qed.

Lemma unfocus_mscons : forall (l:loc) a (x:a) (l' e:loc) A (X:A) (L':list A) (T:A->a->hprop),
  (l ~> Ref Id (x,l')) \* (x ~> T X) \* (l' ~> MListSeg e T L') ==> 
  (l ~> MListSeg e T (X::L')).
Proof.
  intros. simpl. hdata_simpl. hchange (@unfocus_ref2 l _ x _ l'). hsimpl.
Qed.

Opaque MListSeg.



(********************************************************************)
(* ** Accessors *)

Lemma unfocus_mnil'' : forall (l:loc) A (L:list A) a (T:A->a->hprop),
  l ~> MList T L ==> [l = null <-> L = nil] \* l ~> MList T L.
Proof. skip. (*todo*) Qed.

(*
Implicit Arguments focus_mnil.
Implicit Arguments unfocus_mnil.
Implicit Arguments unfocus_mnil'.
Implicit Arguments focus_mcons.
Implicit Arguments focus_mcons'.
Implicit Arguments unfocus_mcons.
*)

Lemma is_nil_spec : forall a,
  Spec is_nil (l:mlist a) |R>> forall A (T:A->a->hprop) (L:list A),
     keep R (l ~> MList T L) (\[ bool_of (L = nil) ]).
Proof.
  xcf. intros. xapp. intros b. hextract.
  hchange (unfocus_mnil'' l). hextract. subst b. hsimpl. xclean. iff*.
Qed.

Module ML := MutableList_ml.

Tactic Notation "xapps" :=
  xapp; try intro_subst.

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

Implicit Arguments unfocus_msnil [ ].
Implicit Arguments focus_mscons [ a A ].
Implicit Arguments unfocus_mscons [ a A ].
Implicit Arguments unfocus_mcons [ a A ].
Implicit Arguments focus_mcons [ ].

Lemma focus_msapp : forall (l l' e:loc) a A (L L':list A) (T:A->a->hprop),
  l ~> MListSeg l' T L \* l' ~> MListSeg e T L' ==> l ~> MListSeg e T (L++L').
Proof.
  intros l l' e a A L L' T. gen l. induction L as [|X R]; intros.
  hchange (unfocus_msnil l). hextract. subst. auto.
  rew_app. hchange (focus_mscons l). hextract as x r. hchange (IHR r).
   hchange (unfocus_mscons l x r e X (R++L')). hsimpl.
Qed.

(*
Lemma focus_msapp' : forall (l e:loc) a A (L:list A) (T:A->a->hprop),
  l ~> MListSeg e T L ==> l ~> MListSeg l T nil \* l ~> MListSeg e T L.
Proof. 
  intros. hchange (focus_msnil l T). hsimpl.
Qed.
*)

Axiom mlistseg_to_mlist : forall (l:loc) a A (T:htype A a) L,
   l ~> MListSeg null T L ==> l ~> MList T L.
Axiom mlist_to_mlistseg : forall (l:loc) a A (T:htype A a) L,
   l ~> MList T L ==> l ~> MListSeg null T L.

Opaque MList.

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
    destruct L12 as [|X L12']. false.
    hchange (focus_mscons l1 e _ _ X L12' T).

   skip. 
   hextract as L11 e E1 E2. xclean. 
    rew_classic in E2. destruct E2 as [x E2]. rew_classic in E2.
    subst L12. subst L1. hsimpl~.
  intros e X LX E. subst L1. xapps. hdata_simpl.
  xchange (focus_mcons e). xextract as x t.
   xapp. xret_gc. 
   hchange (unfocus_mcons e x l2 X L2 T).
   hchange (mlist_to_mlistseg e).   
   hchange (focus_msapp l1 e).
   hchange (mlistseg_to_mlist l1). rew_app. hsimpl.  
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














