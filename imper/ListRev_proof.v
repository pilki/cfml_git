Set Implicit Arguments.
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
  forwards K: H; eapply hchange_lemma; 
    [ apply K
    | clear K
    | clear K ].

Ltac hchange_core H ::=
  let K := fresh "TEMP" in
  forwards K: H; eapply hchange_lemma; 
    [ apply K
    | clear K; instantiate; try hsimpl
    | clear K; instantiate ].

Ltac xchange_lemma_core L ::=
  let K := fresh "TEMP" in
  forwards K: L; eapply xchange_lemma; 
    [ clear K; try apply local_is_local
    | apply K
    | clear K; instantiate; hsimpl
    | clear K ].


Opaque Ref.
Transparent Ref. 
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

Lemma focus_cons : forall (l:loc) a A (X:A) (L':list A) (T:A->a->hprop),
  (l ~> List T (X::L')) ==>
  Hexists x l', (x ~> T X) \* (l' ~> List T L') \* (l ~> Ref Id (x,l')).
Proof.
  intros. simpl. hdata_simpl. hchange (@focus_ref l). hextract as [x l']. 
  hchange (@focus_pair _ _ (x,l')). hsimpl.
Qed.

Lemma unfocus_cons : forall (l:loc) (l':loc) a (x:a) A (X:A) (L':list A) (T:A->a->hprop),
  (x ~> T X) \* (l' ~> List T L') \* (l ~> Ref Id (x,l')) ==> 
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




Lemma rev_spec : forall a,
  Spec ListRev_ml.rev (l:mlist a) |R>> forall A (T:A->a->hprop) (L:list A),
     R (l ~> List T L) (~> List T (LibList.rev L)).
Proof.
  xcf. intros.
  xapp. xchange (focus_nil T). xchange (@unfocus_ref r _ null).
  xseq.
  xwhile_core_debug (fun L1 => l ~> List T L1 \* Hexists L2, r ~> Ref (List T) L2 \* [L = rev L2 ++ L1]) (@list_sub A) L.
    prove_wf.
    exists L. hsimpl. rew_list~.
    
   



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

















