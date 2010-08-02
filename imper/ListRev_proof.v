Set Implicit Arguments.
Require Import LibTactics. Import List.
Tactic Notation "forwards_nounfold" simple_intropattern(I) ":" constr(Ei) :=
  let args := ltac_args Ei in
  let args := (eval simpl in (args ++ ((boxer ___)::nil))) in
  build_app args ltac:(fun R => lets_base I R).

Require Import LibCore CFPrim ListRev_ml MyLib_ml.


Tactic Notation "hextract" "as" simple_intropattern(I1) := 
  hextract as; intros I1.
Tactic Notation "hextract" "as" simple_intropattern(I1) simple_intropattern(I2) := 
  hextract as; intros I1 I2.
Tactic Notation "hextract" "as" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) := 
  hextract as; intros I1 I2 I3.
Tactic Notation "hextract" "as" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) := 
  hextract as; intros I1 I2 I3 I4. 



Ltac hchange_debug H :=
  let K := fresh "TEMP" in
  forwards_nounfold K: H; eapply hchange_lemma; 
    [ apply K
    | clear K
    | clear K ].

Ltac hchange_core H ::=
  let K := fresh "TEMP" in
  forwards_nounfold K: H; eapply hchange_lemma; 
    [ apply K
    | clear K; instantiate; try hsimpl
    | clear K; instantiate ].

Ltac xchange_lemma_core L ::=
  let K := fresh "TEMP" in
  forwards_nounfold K: L; eapply xchange_lemma; 
    [ clear K; try apply local_is_local
    | apply K
    | clear K; instantiate; hsimpl
    | clear K ].

(*
Definition pred_le' := pred_le.
Lemma pred_le_change : pred_le = pred_le'.
Proof. auto. Qed.
Opaque pred_le'.

Ltac xchange_lemma_core L ::=
  let K := fresh "TEMP" in
  let K' := fresh "TEMP" in
  lets K: L; 
  rewrite pred_le_change in K;
  forwards K': K;
  rewrite <- pred_le_change in K;
  clear K;
  eapply xchange_lemma; 
    [ clear K'; try apply local_is_local
    | apply K'
    | clear K'; instantiate; try hsimpl
    | clear K' ].
*)



Opaque Ref.
Transparent Ref. 
Axiom focus_ref_null : forall a A (T:htype A a) V,
  null ~> Ref T V ==> [False]. (* todo *)

Lemma focus_ref : forall (l:loc) a A (T:htype A a) V,
  l ~> Ref T V ==> Hexists v, l ~> Ref Id v \* v ~> T V.
Proof. intros. unfold Ref, hdata. unfold Id. hextract.
hsimpl x x. auto. Qed.
Opaque Ref. 

(* todo: move and generalize to phy_eq *)

Parameter ml_is_null_spec : 
  Spec ml_is_null l |R>> R [] (\[ bool_of (l = null)]).

Hint Extern 1 (RegisterSpec ml_is_null) => Provide ml_is_null_spec.

(** Pairs *)

Definition Pair A1 A2 a1 a2 (T1:A1->a1->hprop) (T2:A2->a2->hprop) P p :=
  let '(X1,X2) := P in let '(x1,x2) := p in x1 ~> T1 X1 \* x2 ~> T2 X2.

Lemma focus_pair : forall a1 a2 (p:a1*a2) A1 A2 (T1:htype A1 a1) (T2:htype A2 a2) V1 V2,
  p ~> Pair T1 T2 (V1,V2) ==> let '(x1,x2) := p in x1 ~> T1 V1 \* x2 ~> T2 V2.
Proof. auto. Qed.

Lemma unfocus_pair : forall a1 (x1:a1) a2 (x2:a2) A1 A2 (T1:htype A1 a1) (T2:htype A2 a2) V1 V2,
  x1 ~> T1 V1 \* x2 ~> T2 V2 ==> (x1,x2) ~> Pair T1 T2 (V1,V2).
Proof. intros. unfold Pair. hdata_simpl. auto. Qed.

Opaque Pair.

(** Lists *)

Fixpoint List A a (T:A->a->hprop) (L:list A) (l:loc) : hprop :=
  match L with
  | nil => [l = null]
  | X::L' => l ~> Ref (Pair T (List T)) (X,L')
  end.

Lemma focus_nil : forall A a (T:A->a->hprop),
  [] ==> null ~> List T nil.
Proof. intros. simpl. hdata_simpl. hsimpl~. Qed.

Lemma unfocus_nil : forall (l:loc) A a (T:A->a->hprop),
  l ~> List T nil ==> [l = null].
Proof. intros. simpl. hdata_simpl. hsimpl~. Qed.

Lemma unfocus_nil' : forall A (L:list A) a (T:A->a->hprop),
  null ~> List T L ==> [L = nil].
Proof.
  intros. destruct L.
  simpl. unfold hdata. xsimpl~. 
  unfold hdata, List. hchange (focus_ref_null). hextract. false.
Qed.

Lemma focus_cons : forall (l:loc) a A (X:A) (L':list A) (T:A->a->hprop),
  (l ~> List T (X::L')) ==>
  Hexists x l', (x ~> T X) \* (l' ~> List T L') \* (l ~> Ref Id (x,l')).
Proof.
  intros. simpl. hdata_simpl. hchange (@focus_ref l). hextract as [x l']. 
  hchange (@focus_pair _ _ (x,l')). hsimpl.
Qed.

Lemma focus_cons' : forall (l:loc) a A (L:list A) (T:A->a->hprop),
  [l <> null] \* (l ~> List T L) ==> 
  Hexists x l', Hexists X L', 
    [L = X::L'] \*  (l ~> Ref Id (x,l')) \* (x ~> T X) \* (l' ~> List T L').
Proof.
  intros. destruct L.
  lets: (@unfocus_nil l _ _ T).   Show Existentials. hextract. false~.
  hchange (@focus_cons l). hextract as x l' E. hsimpl~.  
Qed.

Lemma unfocus_cons : forall (l:loc) a (x:a) (l':loc) A (X:A) (L':list A) (T:A->a->hprop),
  (l ~> Ref Id (x,l')) \* (x ~> T X) \* (l' ~> List T L') ==> 
  (l ~> List T (X::L')).
Proof.
  intros. simpl. hdata_simpl. hchange (@unfocus_pair _ x _ l').
  hchange (@unfocus_ref l _ (x,l')). hsimpl.
Qed.


(*****************)

Require Import LibList.
Implicit Arguments list_sub [[A]].


Definition Void {a A} (v:a) (V:A) := [].

Opaque heap_is_empty.
Opaque List.


(* todo: move to cf prim*)
Notation "x ''=' y :> A" := (istrue (@eq A x y))
  (at level 70, y at next level, only parsing) : comp_scope.
Notation "x ''<>' y :> A" := (istrue (~ (@eq A x y)))
  (at level 69, y at next level, only parsing) : comp_scope.


Tactic Notation "xchange" "~" constr(E) :=
  xchange E; auto~.


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
  xchange (@focus_ref r). xlocal. (* why? *)
  xextract as x. xapp. intros z. hextract. subst. hsimpl.
Qed.





(*****************)
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


  (*
   eapply (@xwhile_frame _ (fun L' => Hexists k l',
     n ~> RefOn k \* p ~> RefOn l' \* l' ~> List T L' \* [k + length L' = length L]) (@list_sub _)).

  xwhile_manual (fun L' => Hexists k l',
     n ~> RefOn k \* p ~> RefOn l' \* l' ~> List T L' \* [k + length L' = length L])
     (@list_sub A). L
  *)

















