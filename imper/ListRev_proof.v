Set Implicit Arguments.
Require Import LibCore CFPrim ListRev_ml MyLib_ml.

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
  | nil => [True]
  | X::L' => l ~> Ref (Pair T (List T)) (X,L')
  end.

(*****************)

Require Import LibList.
Implicit Arguments list_sub [[A]].
Opaque Ref.

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
    | clear K; try hsimpl
    | clear K; try hsimpl].

Ltac xchange_lemma_core L ::=
  let K := fresh "TEMP" in
  forwards K: L; eapply xchange_lemma; 
    [ clear K; try apply local_is_local
    | apply K
    | clear K; hsimpl
    | clear K ].

Transparent Ref. 
Lemma focus_ref : forall (l:loc) a A (T:htype A a) V,
  l ~> Ref T V ==> Hexists v, l ~> Ref Id v \* v ~> T V.
Proof. intros. unfold Ref, hdata. unfold Id. hextract.
hsimpl x x. auto. Qed.
Opaque Ref. 

Definition Void {a A} (v:a) (V:A) := [].

Lemma rev_spec : forall a,
  Spec ListRev_ml.rev (l:mlist a) |R>> forall A (T:A->a->hprop) (L:list A),
     R (l ~> List T L) (~> List T (LibList.rev L)).
Proof.
  xcf. intros.
  xapp.
  xchange (r ~> Ref Id null ==> r ~> Ref (List T) nil). 
     hchange (>>> unfocus_ref r null (@Void a loc)). unfold hdata, Void. hsimpl.
     forwards K: (@focus_ref l). eapply hchange_lemma.
.
  
  eapply hchange_lemma. eapply H. clear H.²
    hchange.
  xseq.
  xwhile_core_debug (fun L1 => l ~> List T L1 \* Hexists L2, r ~> Ref (List T) L2 \* [L = rev L2 ++ L1]) (@list_sub A) L.
   prove_wf.
   exists L. hsimpl. hsimpl. 



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

















