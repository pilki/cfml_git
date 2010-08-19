Set Implicit Arguments.
Require Import CFPrim ListIterators_ml LibList.
Module LI := ListIterators_ml.


(*------------------------------------------------------------------*)
(* ** Lists *)

Fixpoint List A a (T:A->a->hprop) (L:list A) (l:list a) : hprop :=
  match L,l with
  | nil, nil => [l = nil]
  | X::L', x::l' => x ~> T X \* l' ~> List T L'
  | _,_=> [False]
  end.

Lemma focus_nil : forall A a (T:A->a->hprop),
  [] ==> nil ~> List T nil.
Proof. intros. simpl. hdata_simpl. hsimpl~. Qed.

Lemma unfocus_nil : forall a (l:list a) A (T:A->a->hprop),
  l ~> List T nil ==> [l = nil].
Proof. intros. simpl. hdata_simpl. destruct l. auto. hextract. false. Qed.

Lemma unfocus_nil' : forall A (L:list A) a (T:A->a->hprop),
  nil ~> List T L ==> [L = nil].
Proof.
  intros. destruct L.
  simpl. hdata_simpl. hextract. hsimpl. auto. (* todo simplify *)
  simpl. hdata_simpl. hextract. false.
Qed.

Lemma focus_cons : forall a (l:list a) A (X:A) (L':list A) (T:A->a->hprop),
  (l ~> List T (X::L')) ==>
  Hexists x l', (x ~> T X) \* (l' ~> List T L') \* [l = x::l'].
Proof.
  intros. simpl. hdata_simpl. destruct l.
  hextract. false.
  hsimpl. auto.
Qed.

Lemma focus_cons' : forall a (x:a) (l:list a) A (L:list A) (T:A->a->hprop),
  (x::l) ~> List T L ==> 
  Hexists X L', [L = X::L'] \* (x ~> T X) \* (l ~> List T L').
Proof.
  intros. destruct L.
  simpl. hdata_simpl. hextract. false.
  simpl. hdata_simpl. hsimpl. auto.
Qed.

Lemma unfocus_cons : forall a (x:a) (l:list a) A (X:A) (L:list A) (T:A->a->hprop),
  (x ~> T X) \* (l ~> List T L) ==> 
  ((x::l) ~> List T (X::L)).
Proof.
  intros. simpl. hdata_simpl. hsimpl.
Qed.

Opaque List.


(********************************************************************)
(** Spec map simple *)

Hint Constructors Forall2.

Lemma map_spec : forall a b,
  Spec LI.map (f:val) (l:list a) |R>> forall A B L (T:htype A a) (U:htype B b) (I:A->B->Prop),
    (Spec f x |R'>> forall X, In X L -> keep R' (x ~> T X) (fun y => Hexists Y, (y ~> U Y) \* [I X Y])) ->
    keep R (l ~> List T L) (fun m => Hexists M, m ~> List U M \* [Forall2 I L M]).
Proof.
  intros. xinduction (unproj22 val (@list_sub a)).
  xcf. intros f l IH. introv Hf. (* todo: avec xintros ? *)
  xmatch.
  (* base case *)
  xret.
  hchange (@unfocus_nil' _ L _ T). hextract. subst L. hsimpl (@nil B).
    hchange (@focus_nil _ _ U). hchange (@focus_nil _ _ T). hsimpl.
    auto.
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
  












