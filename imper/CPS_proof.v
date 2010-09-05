Set Implicit Arguments.
Require Import LibCore CFPrim CPS_ml LibList.
Opaque Ref.

(* temporary *)
Notation "'Let' x ':=' F1 'in' F2" :=
  (!T (fun H Q => exists Q1, F1 H Q1 /\ forall x, F2 (Q1 x) Q))
  (at level 69, x ident) : charac.


(*------------------------------------------------------------------*)
(* ** Mutable lists *)

(* Definition of [l ~> Mlist L], same as [Mlist L l] *)
 
Fixpoint Mlist A (L:list A) (l:loc) : hprop :=
  match L with
  | nil => [l = null]
  | X::L' => Hexists l', l ~~> (X,l') \* l' ~> Mlist L'
  end.

Lemma unfocus_mnil : forall A (L:list A),
  null ~> @Mlist A L ==> [L = nil].
Proof.
  intros. destruct L; simpl.
  xsimpl~.
  hdata_simpl. hextract. hchange focus_ref_null. hextract. false.
Qed.

Lemma focus_mcons : forall (l:loc) A (L:list A),
  [l <> null] \* (l ~> Mlist L) ==> Hexists (X:A) (l':loc) (L':_),
    [L = X::L'] \*  (l ~~> (X,l')) \* (l' ~> Mlist L').
Proof.
  intros. destruct L. 
  hextract. false~.
  simpl. hdata_simpl. hextract as E l'. hsimpl~.
Qed.

Lemma unfocus_mcons : forall (l:loc) A (X:A) (l':loc) (L':list A),
  (l ~~> (X,l')) \* (l' ~> Mlist L') ==> (l ~> Mlist (X::L')).
Proof.
  intros. simpl. hdata_simpl. hsimpl. 
Qed.

Opaque Mlist.
Implicit Arguments unfocus_mnil [ A].
Implicit Arguments unfocus_mcons [ A ].
Implicit Arguments focus_mcons [ A ].



(*------------------------------------------------------------------*)
(* ** tail and set_tail *)

Lemma tail_spec : forall A,
  Spec CPS_ml.tail (l:mlist A) |R>> forall (X:A) (t:mlist A),
    keep R (l ~~> (X,t)) (\= t).
Proof. 
  xcf. intros. xapps. xret.
Qed.

Lemma set_tail_spec : forall A,
  Spec CPS_ml.set_tail (l:mlist A) (t:mlist A) |R>> forall (x:A) (t':mlist A),
    R (l ~~> (x,t')) (# l ~~> (x,t)).
Proof. 
  xcf. intros. xapps. xmatch. xapp. hsimpl.
Qed.

Hint Extern 1 (RegisterSpec CPS_ml.tail) => Provide tail_spec.
Hint Extern 1 (RegisterSpec CPS_ml.set_tail) => Provide set_tail_spec.


(*------------------------------------------------------------------*)
(* ** CPS append *)

Lemma append_spec : forall A B,
  Spec CPS_ml.append (x:loc) (y:loc) (k:Func) |R>> 
     forall (L M:list A) H (Q:B->hprop),
     (forall z, AppReturns k z (z ~> Mlist (L++M) \* H) Q) ->
     R (x ~> Mlist L \* y ~> Mlist M \* H) Q.
Proof.
  intros. xinduct (unproj41 loc loc Func (@list_sub A)).
  xcf. intros x y k L IH. introv Sk.
  xapps. xif. xchange (unfocus_mnil L) as. intro_subst. apply Sk.
  xchange~ (focus_mcons x) as v l' L' E. subst L.
   xfun (fun k' => Spec k' z |R>> 
     R (x ~~> (v,l') \* z ~> Mlist (L'++M) \* H) Q).
     xapp. xchange~ (unfocus_mcons x v z). rew_list in Sk. apply Sk.
   xapps. xapp~ (x~~>(v,l') \* H). intros. xapp_hyp. hsimpl.
Qed.




