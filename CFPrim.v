Set Implicit Arguments.
Require Export LibInt LibArray CFSpec CFPrint CFTactics.


(* todo: move *)
Implicit Arguments list_sub [[A]].



Hint Resolve (0%nat) : typeclass_instances.
Hint Resolve (0%Z) : typeclass_instances.
Hint Resolve @nil : typeclass_instances.
Hint Resolve true : typeclass_instances.
Hint Resolve @None : typeclass_instances.
Hint Resolve @pair : typeclass_instances.

Ltac inhab :=
  constructor; intros; try solve 
    [ eauto 10 with typeclass_instances 
    | constructor; eauto 10 with typeclass_instances 
    | apply arbitrary 
    | apply @arbitrary; eauto 10 with typeclass_instances ].

Instance inhabited_Z : Inhabited Z.
Admitted.


(********************************************************************)
(** Pure Representation for base types *)


Hint Extern 1 (@rep _ _ _ _ _) => simpl.

Hint Resolve @rep_unique : rep.

Ltac prove_rep := 
  fequals_rec; 
  try match goal with |- @eq (?T ?A) _ _ => let U := fresh in sets U:(T A) end;
  intuition eauto with rep.
  (* todo : appliquer directement rep_unique sur les buts ? *)

Instance int_rep : Rep int int.
Proof. apply (Build_Rep eq). congruence. Defined.

Instance bool_rep : Rep bool bool.
Proof. apply (Build_Rep eq). congruence. Defined.

Instance list_rep : forall `{Rep a A}, Rep (list a) (list A).
Proof.
  intros. apply (Build_Rep (fun l L => Forall2 rep l L)).
  induction x; introv H1 H2; inverts H1; inverts H2; prove_rep. 
Defined.

Lemma list_rep_cons : forall `{Rep a A} l L x X,
  rep l L -> rep x X -> rep (x::l) (X::L).
Proof. intros. constructors~. Qed.

Hint Resolve @list_rep_cons.

Instance prod_rep : forall `{Rep a1 A1} `{Rep a2 A2},
  Rep (a1 * a2) (A1 * A2).
Proof.
  intros. apply (Build_Rep (fun p P => match p,P with 
   (x,y),(X,Y) => rep x X /\ rep y Y end)).
  intros [x1 x2] [X1 X2] [Y1 Y2] H1 H2; prove_rep.
Defined.

Instance option_rep : forall `{Rep a A},
  Rep (option a) (option A).
Proof.
  intros. apply (Build_Rep (fun o O => match o,O with 
    | None, None => True
    | Some x, Some X => rep x X
    | _,_ => False end)).
  intros [x|] [X|] [Y|] H1 H2; prove_rep.
Defined.

Hint Extern 1 (@rep (list _) _ _ _ _) => simpl.
Hint Extern 1 (@rep (prod _ _) _ _ _ _) => simpl.
Hint Extern 1 (@rep (option _) _ _ _ _) => simpl.


(* todo: move *)
Definition nref := loc.
Parameter null : loc.
Parameter ml_is_null : val.


(********************************************************************)
(** Imperative Representation for base types *)

(*------------------------------------------------------------------*)
(* ** Basics *)

Definition htype A a := A -> a -> hprop.

(** For pure values *)

Definition Id {A:Type} (X:A) (x:A) := 
  [ X = x ].

(** Void *)

Definition Void {a A} (v:a) (V:A) := [].

(*------------------------------------------------------------------*)
(* ** References *)

Definition Ref a A (T:htype A a) (V:A) (l:loc) :=
  Hexists v, heap_is_single l v \* v ~> T V.

Notation "l '~~>' v" := (l ~> Ref Id v)
  (at level 32, no associativity).
Notation "'~~>' v" := (~> Ref Id v)
  (at level 32, no associativity) : heap_scope.
(*
Lemma focus_ref_core : forall (l:loc) a A (T:htype A a) V,
  l ~> Ref T V ==> Hexists v, l> v \* v ~> T V.
Proof. auto. Qed.
*)

Lemma focus_ref : forall (l:loc) a A (T:htype A a) V,
  l ~> Ref T V ==> Hexists v, l ~~> v \* v ~> T V.
Proof. intros. unfold Ref, hdata. unfold Id. hextract.
hsimpl x x. auto. Qed.

Lemma unfocus_ref : forall (l:loc) a (v:a) A (T:htype A a) V,
  l ~~> v \* v ~> T V ==> l ~> Ref T V.
Proof. intros. unfold Ref. hdata_simpl. xsimpl~. Qed.

Axiom focus_ref_null : forall a A (T:htype A a) V,
  null ~> Ref T V ==> [False]. (* todo *)

Opaque Ref.



   (*--todo: Record ref A := { content : A }. *)

(*------------------------------------------------------------------*)
(* ** Tuple 2 *)

Definition Tup2 A1 A2 a1 a2 (T1:A1->a1->hprop) (T2:A2->a2->hprop) P p :=
  let '(X1,X2) := P in let '(x1,x2) := p in x1 ~> T1 X1 \* x2 ~> T2 X2.

Lemma focus_tup2 : forall a1 a2 (p:a1*a2) A1 A2 (T1:htype A1 a1) (T2:htype A2 a2) V1 V2,
  p ~> Tup2 T1 T2 (V1,V2) ==> let '(x1,x2) := p in x1 ~> T1 V1 \* x2 ~> T2 V2.
Proof. auto. Qed.

Lemma unfocus_tup2 : forall a1 (x1:a1) a2 (x2:a2) A1 A2 (T1:htype A1 a1) (T2:htype A2 a2) V1 V2,
  x1 ~> T1 V1 \* x2 ~> T2 V2 ==> (x1,x2) ~> Tup2 T1 T2 (V1,V2).
Proof. intros. unfold Tup2. hdata_simpl. auto. Qed.

Opaque Tup2.

(*------------------------------------------------------------------*)
(* ** Tuple 3 *)

Definition Tup3 A1 A2 A3 a1 a2 a3 (T1:A1->a1->hprop) (T2:A2->a2->hprop) (T3:A3->a3->hprop) P p :=
  let '(X1,X2,X3) := P in let '(x1,x2,x3) := p in x1 ~> T1 X1 \* x2 ~> T2 X2 \* x3 ~> T3 X3.

Lemma focus_tup3 : forall a1 a2 a3 (p:a1*a2*a3) A1 A2 A3 (T1:htype A1 a1) (T2:htype A2 a2) (T3:A3->a3->hprop) V1 V2 V3,
  p ~> Tup3 T1 T2 T3 (V1,V2,V3) ==> let '(x1,x2,x3) := p in x1 ~> T1 V1 \* x2 ~> T2 V2 \* x3 ~> T3 V3.
Proof. auto. Qed.

Lemma unfocus_tup3 : forall a1 (x1:a1) a2 (x2:a2) a3 (x3:a3) A1 A2 A3 (T1:htype A1 a1) (T2:htype A2 a2) (T3:A3->a3->hprop) V1 V2 V3,
  x1 ~> T1 V1 \* x2 ~> T2 V2 \* x3 ~> T3 V3 ==> (x1,x2,x3) ~> Tup3 T1 T2 T3 (V1,V2,V3).
Proof. intros. unfold Tup3. hdata_simpl. auto. Qed.

Opaque Tup3.

(*------------------------------------------------------------------*)
(* ** Ref-Tuple 3  -- todo ?

Definition RefTup3 A1 A2 A3 a1 a2 a3 (T1:A1->a1->hprop) (T2:A2->a2->hprop) (T3:A3->a3->hprop) P l :=
  l ~> Ref (Tup3 T1 T2 T3) P.

Lemma focus_reftup3 : forall (l:loc) a1 a2 a3 A1 A2 A3 (T1:htype A1 a1) (T2:htype A2 a2) (T3:A3->a3->hprop) V1 V2 V3,
  l ~> RefTup3 T1 T2 T3 (V1,V2,V3) ==> Hexists (x1:a1) (x2:a2) (x3:a3),
  l ~> Ref Id (x1,x2,x3) \* x1 ~> T1 V1 \* x2 ~> T2 V2 \* x3 ~> T3 V3.
Proof.
  intros. unfold RefTup3. hdata_simpl. hchange (@focus_ref l). hextract as. 
  intros p [[x1 x2] x3] H. hchange (focus_tup3 p). destruct p as [[y1 y2] y3].
  inversions H. hsimpl~. 
Qed.

Lemma unfocus_reftup3 : forall (l:loc) a1 (x1:a1) a2 (x2:a2) a3 (x3:a3) A1 A2 A3 (T1:htype A1 a1) (T2:htype A2 a2) (T3:A3->a3->hprop) V1 V2 V3,
  l ~> Ref Id (x1,x2,x3) \* x1 ~> T1 V1 \* x2 ~> T2 V2 \* x3 ~> T3 V3 ==>
  l ~> RefTup3 T1 T2 T3 (V1,V2,V3).
Proof.
  intros. unfold RefTup3. hdata_simpl. hchange (unfocus_tup3 x1 x2 x3). 
  hchange (@unfocus_ref l _ (x1,x2,x3)). hsimpl.
Qed.

Opaque RefTup3.
*)

(*------------------------------------------------------------------*)
(* ** Record 2 *)

Definition Ref2 A1 A2 a1 a2 (T1:A1->a1->hprop) (T2:A2->a2->hprop) (V1:A1) (V2:A2) l :=
  l ~> Ref (Tup2 T1 T2) (V1,V2).

Lemma focus_ref2 : forall (l:loc) a1 a2 A1 A2 (T1:htype A1 a1) (T2:htype A2 a2) V1 V2,
  l ~> Ref2 T1 T2 V1 V2 ==> Hexists (x1:a1) (x2:a2),
  l ~> Ref Id (x1,x2) \* x1 ~> T1 V1 \* x2 ~> T2 V2 .
Proof.
  intros. unfold Ref2. hdata_simpl. hchange (@focus_ref l).
  hextract as [x1 x2]. hchange (focus_tup2 (x1,x2)). hsimpl.
Qed.

Lemma unfocus_ref2 : forall (l:loc) a1 (x1:a1) a2 (x2:a2) A1 A2 (T1:htype A1 a1) (T2:htype A2 a2) V1 V2,
  l ~> Ref Id (x1,x2) \* x1 ~> T1 V1 \* x2 ~> T2 V2 ==>
  l ~> Ref2 T1 T2 V1 V2.
Proof.
  intros. unfold Ref2. hdata_simpl. hchange (unfocus_tup2 x1 x2). 
  hchange (@unfocus_ref l _ (x1,x2)). hsimpl.
Qed.

Lemma focus_ref2_null : forall a1 a2 A1 A2 (T1:htype A1 a1) (T2:htype A2 a2) V1 V2,
  null ~> Ref2 T1 T2 V1 V2 ==> [False]. 
Proof.
  intros. unfold hdata, Ref2. hchange focus_ref_null. hsimpl. 
Qed.

Opaque Ref2.

(*------------------------------------------------------------------*)
(* ** Record 3 *)

Definition Ref3 A1 A2 A3 a1 a2 a3 (T1:A1->a1->hprop) (T2:A2->a2->hprop) (T3:A3->a3->hprop) (V1:A1) (V2:A2) (V3:A3) l :=
  l ~> Ref (Tup3 T1 T2 T3) (V1,V2,V3).

Lemma focus_ref3 : forall (l:loc) a1 a2 a3 A1 A2 A3 (T1:htype A1 a1) (T2:htype A2 a2) (T3:A3->a3->hprop) V1 V2 V3,
  l ~> Ref3 T1 T2 T3 V1 V2 V3 ==> Hexists (x1:a1) (x2:a2) (x3:a3),
  l ~> Ref Id (x1,x2,x3) \* x1 ~> T1 V1 \* x2 ~> T2 V2 \* x3 ~> T3 V3.
Proof.
  intros. unfold Ref3. hdata_simpl. hchange (@focus_ref l).
  hextract as [[x1 x2] x3]. hchange (focus_tup3 (x1,x2,x3)). hsimpl.
Qed.

Lemma unfocus_ref3 : forall (l:loc) a1 (x1:a1) a2 (x2:a2) a3 (x3:a3) A1 A2 A3 (T1:htype A1 a1) (T2:htype A2 a2) (T3:A3->a3->hprop) V1 V2 V3,
  l ~> Ref Id (x1,x2,x3) \* x1 ~> T1 V1 \* x2 ~> T2 V2 \* x3 ~> T3 V3 ==>
  l ~> Ref3 T1 T2 T3 V1 V2 V3.
Proof.
  intros. unfold Ref3. hdata_simpl. hchange (unfocus_tup3 x1 x2 x3). 
  hchange (@unfocus_ref l _ (x1,x2,x3)). hsimpl.
Qed.

Lemma focus_ref3_null : forall a1 a2 a3 A1 A2 A3 (T1:htype A1 a1) (T2:htype A2 a2) (T3:htype A3 a3) V1 V2 V3,
  null ~> Ref3 T1 T2 T3 V1 V2 V3 ==> [False]. 
Proof.
  intros. unfold hdata, Ref3. hchange focus_ref_null. hsimpl. 
Qed.

Opaque Ref3.


(*------------------------------------------------------------------*)
(* ** Lists *)

Fixpoint List A a (T:A->a->hprop) (L:list A) (l:list a) : hprop :=
  match L,l with
  | nil, nil => [l = nil] (* %todo: True*)
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


(*------------------------------------------------------------------*)
(* ** MLists *)

Fixpoint MList A a (T:A->a->hprop) (L:list A) (l:loc) : hprop :=
  match L with
  | nil => [l = null]
  | X::L' => l ~> Ref2 T (MList T) X L'
  end.

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
  simpl. unfold hdata. xsimpl~. 
  unfold hdata, MList. hchange focus_ref2_null. hextract. false.
Qed.

Lemma unfocus_mnil'' : forall (l:loc) A (L:list A) a (T:A->a->hprop),
  l ~> MList T L ==> [l = null <-> L = nil] \* l ~> MList T L.
Proof. skip. (*todo*) Qed.

Lemma focus_mcons : forall (l:loc) a A (X:A) (L':list A) (T:A->a->hprop),
  (l ~> MList T (X::L')) ==>
  Hexists x l', (x ~> T X) \* (l' ~> MList T L') \* (l ~> Ref Id (x,l')).
Proof.
  intros. simpl. hdata_simpl. hchange (@focus_ref2 l). xsimpl.
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

Opaque MList.

Implicit Arguments unfocus_mnil [ ].
Implicit Arguments unfocus_mcons [ a A ].
Implicit Arguments focus_mcons [ a A ].

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

Implicit Arguments unfocus_msnil [ ].
Implicit Arguments focus_mscons [ a A ].
Implicit Arguments unfocus_mscons [ a A ].

Lemma focus_msapp : forall (l l' e:loc) a A (L L':list A) (T:A->a->hprop),
  l ~> MListSeg l' T L \* l' ~> MListSeg e T L' ==> l ~> MListSeg e T (L++L').
Proof.
  intros l l' e a A L L' T. gen l. induction L as [|X R]; intros.
  hchange (unfocus_msnil l). hextract. subst. auto.
  rew_app. hchange (focus_mscons l). hextract as x r. hchange (IHR r).
   hchange (unfocus_mscons l x r e X (R++L')). hsimpl.
Qed.

Axiom mlistseg_to_mlist : forall (l:loc) a A (T:htype A a) L,
   l ~> MListSeg null T L ==> l ~> MList T L.
Axiom mlist_to_mlistseg : forall (l:loc) a A (T:htype A a) L,
   l ~> MList T L ==> l ~> MListSeg null T L.
(*todo*)

Opaque MListSeg.



(*------------------------------------------------------------------*)
(* ** Tools for stdio *)

Definition list_dyn A (L:list A) :=
  LibList.map dyn L.

Lemma list_dyn_nil : forall A,
  list_dyn (@nil A) = nil.
Proof. auto. Qed.

Lemma list_dyn_cons : forall A X (L:list A),
  list_dyn (X::L) = (dyn X)::(list_dyn L).
Proof. auto. Qed.

Lemma list_dyn_last : forall A X (L:list A),
  list_dyn (L&X) = (list_dyn L)&(dyn X).
Proof. intros. unfold list_dyn. rew_list~. Qed.

Hint Rewrite list_dyn_nil : rew_app.
Hint Rewrite list_dyn_nil : rew_map.
Hint Rewrite list_dyn_nil : rew_list.
Hint Rewrite list_dyn_cons : rew_app.
Hint Rewrite list_dyn_cons : rew_map.
Hint Rewrite list_dyn_cons : rew_list.
Hint Rewrite list_dyn_last : rew_app.
Hint Rewrite list_dyn_last : rew_map.
Hint Rewrite list_dyn_last : rew_list.



(************************************************************)
(** Axiomatic specification of the primitive functions *)


(* todo: move *)
Notation "x ''=' y :> A" := (istrue (@eq A x y))
  (at level 70, y at next level, only parsing) : comp_scope.
Notation "x ''<>' y :> A" := (istrue (~ (@eq A x y)))
  (at level 69, y at next level, only parsing) : comp_scope.


(* todo?
Parameter ml_is_null_spec : 
  Spec ml_is_null l |R>> R [] (\[ bool_of (l = null)]).

Hint Extern 1 (RegisterSpec ml_is_null) => Provide ml_is_null_spec.
 *)


(** Pointers *)

Parameter ml_phy_eq : val.
Parameter ml_phy_eq_spec : Pure ml_phy_eq x y >> = (x '= y :> loc).
Hint Extern 1 (RegisterSpec ml_phy_eq) => Provide ml_phy_eq_spec.

Parameter ml_phy_neq : val.
Parameter ml_phy_neq_spec : Pure ml_phy_neq x y >> = (x '<> y :> loc).
Hint Extern 1 (RegisterSpec ml_phy_neq) => Provide ml_phy_neq_spec.

(** Arithmetic *)

Parameter ml_plus : val.
Parameter ml_plus_spec : Pure ml_plus x y >> = (x + y)%Z.
Hint Extern 1 (RegisterSpec ml_plus) => Provide ml_plus_spec.

Parameter ml_minus : val.
Parameter ml_minus_spec : Pure ml_minus x y >> = (x - y)%Z.
Hint Extern 1 (RegisterSpec ml_minus) => Provide ml_minus_spec.

Parameter ml_eqb : val.
Parameter ml_eqb_int_spec : Pure ml_eqb (x:int) (y:int) >> = (x == y).
Hint Extern 1 (RegisterSpec ml_eqb) => Provide ml_eqb_int_spec.

Parameter ml_leq : val.
Parameter ml_leq_spec : Pure ml_leq x y >> = (x <= y)%I.
Hint Extern 1 (RegisterSpec ml_leq) => Provide ml_leq_spec.

Parameter ml_geq : val.
Parameter ml_geq_spec : Pure ml_geq x y >> = (x >= y)%I.
Hint Extern 1 (RegisterSpec ml_geq) => Provide ml_geq_spec.

Parameter ml_lt : val.
Parameter ml_lt_spec : Pure ml_lt x y >> = (x < y)%I.
Hint Extern 1 (RegisterSpec ml_lt) => Provide ml_lt_spec.

Parameter ml_gt : val.
Parameter ml_gt_spec : Pure ml_gt x y >> = (x > y)%I.
Hint Extern 1 (RegisterSpec ml_gt) => Provide ml_gt_spec.

Parameter ml_and : val.
Parameter ml_and_spec : Pure ml_and x y >> = (x && y).
Hint Extern 1 (RegisterSpec ml_and) => Provide ml_and_spec.

Parameter ml_or : val.
Parameter ml_or_spec : Pure ml_or x y >> = (x || y).
Hint Extern 1 (RegisterSpec ml_and) => Provide ml_or_spec.

Parameter ml_min_int : int.
Parameter ml_max_int : int.
Parameter ml_rand_int : val.

(** Pairs *)

Parameter ml_fst : val.
Parameter ml_fst_spec : forall a1 a2,
  Spec ml_fst (p:a1*a2) |R>> 
    pure R (= fst p).
Hint Extern 1 (RegisterSpec ml_fst) => Provide ml_fst_spec.

Parameter ml_snd : val.
Parameter ml_snd_spec : forall a1 a2,
  Spec ml_snd (p:a1*a2) |R>> 
    pure R (= snd p).
Hint Extern 1 (RegisterSpec ml_snd) => Provide ml_snd_spec.

(** IO *)

Parameter Channel : forall (L:list dynamic) (l:loc), hprop.

Notation "l ~>> L" := (l ~> Channel L)
  (at level 32, no associativity).

Parameter stdin : loc.
Parameter stdout : loc.

Parameter ml_read_int : val.
Parameter ml_read_int_spec :
  Spec ml_read_int () |R>> forall L (n:int),
    R (stdin ~>> (dyn n::L)) (\=n \*+ stdin ~>> L).
Hint Extern 1 (RegisterSpec ml_read_int) => Provide ml_read_int_spec.

Parameter ml_print_int : val.
Parameter ml_print_int_spec :
  Spec ml_print_int (n:int) |R>> forall L,
    R (stdout ~>> L) (# stdout ~>> L & (dyn n)).
Hint Extern 1 (RegisterSpec ml_print_int) => Provide ml_print_int_spec.


(** References *)

Parameter ml_ref : val.
Parameter ml_get : val.
Parameter ml_set : val.
Parameter ml_incr : val.
Parameter ml_decr : val.

Parameter ml_ref_spec : forall a,
  Spec ml_ref (v:a) |R>> 
    R [] (~~> v).

Parameter ml_get_spec : forall a,
  Spec ml_get (l:loc) |R>> 
    forall (v:a), keep R (l ~~> v) (\=v).

Parameter ml_set_spec : forall a,
  Spec ml_set (l:loc) (v:a) |R>> 
    forall (v':a), R (l ~> Ref Id v') (# l ~> Ref Id v).

Parameter ml_incr_spec : 
  Spec ml_incr (l:loc) |R>> 
    forall n, R (l ~~> n) (# l ~~> (n+1)).
 
Parameter ml_decr_spec : 
  Spec ml_decr (l:loc) |R>> 
    forall n, R (l ~~> n) (# l ~~> (n-1)).

Hint Extern 1 (RegisterSpec ml_ref) => Provide ml_ref_spec.
Hint Extern 1 (RegisterSpec ml_get) => Provide ml_get_spec.
Hint Extern 1 (RegisterSpec ml_set) => Provide ml_set_spec.
Hint Extern 1 (RegisterSpec ml_incr) => Provide ml_incr_spec.
Hint Extern 1 (RegisterSpec ml_decr) => Provide ml_decr_spec.

(** Strong References --todo unify ? *)
Parameter ml_sset : val.
Parameter ml_sset_spec : forall a a',
  Spec ml_sset (l:loc) (v:a) |R>> 
    forall (v':a'), R (l ~~> v') (# l ~~> v).
Hint Extern 1 (RegisterSpec ml_sset) => Provide ml_sset_spec.


(** Derived specifications for references *)

Lemma ml_ref_spec_linear : forall A a,
  Spec ml_ref (v:a) |R>> forall (V:A) (T:htype A a),
    R (v ~> T V) (~> Ref T V).
Proof.
  intros. applys spec_weaken_1 ml_ref_spec.
  intros_all. unfolds rel_le, pred_le. auto*. (* xisspec *)
  introv L M. intros.
  applys local_wframe. auto. eauto.
  hsimpl. intros l.
  hchange~ (@unfocus_ref l _ x1). hsimpl.
Qed.

(*
Lemma ml_get_spec_linear : forall A a,
  Spec ml_get (l:loc) |R>> 
    forall (V:A) (T:htype A a), 
    R (l ~> Ref T V) (fun v => l ~> RefOn v \* T V v).
Proof.
  intros. applys spec_weaken_1 ml_get_spec.
  intros_all. unfolds rel_le, pred_le. auto*. (* xisspec *)
  introv L M. intros. unfold hdata.
  unfold Ref. hclean. intros v.
  specializes M v.
  applys local_wframe. auto. eauto. hsimpl.
  intros l. (* unfold starpost. todo: as notation *) 
  simpl. unfold hdata.
  (* todo: tactic hsimpl_left should do it *)
  hsimpl. apply heap_extract_prop. intro_subst. auto.
Qed.
*)

(** List *)

Parameter ml_list_iter : val.

(** Arrays *)

Parameter ml_array_make : val.
Parameter ml_array_get : val.
Parameter ml_array_set : val.
Parameter ml_array_init : val.
Parameter ml_array_length : val.


(*
Definition ArrayOn A (v:array A) (l:loc) : hprop.
Admitted. (* := l ~~> v.*)
*)

Axiom array_make : forall A (n:int) (v:A), array A.

Class Dup a A (T:htype A a) : Prop := { 
  dup : forall X x, T X x ==> [] }.

Parameter Array : forall a A (T:htype A a) (M:array A) (l:loc), hprop.

Require Import LibBag.

Definition Read B (R:~~B) := 
  fun H Q => R H (Q \*+ H).

Notation "m \( x )" := (LibBag.read m x)
  (at level 29, format "m \( x )") : container_scope.
Notation "m \( x := v )" := (update m x v)
  (at level 29, format "m \( x := v )") : container_scope.

Open Scope container_scope.

(* BIN
Parameter ml_array_make_spec : forall a A,
  Spec ml_array_make (n:int) (v:a) |R>> 
    forall (V:A) (T:htype A a) (t:array A), Dup T ->
    R (T V v) (fun l => l ~> Array T (array_make n V)).

Parameter ml_array_get_spec : forall a A `{Inhab A},
  Spec ml_array_get (l:loc) (i:int) |R>> 
    forall (T:htype A a) (t:array A), Dup T -> index t i ->
    Read (R:~~a) (l ~> Array T t) (T (t`[i])).

Parameter ml_array_set_spec : forall a A `{Inhab A},
  Spec ml_array_set (l:loc) (i:int) (v:a) |R>> 
    forall (V:A) (T:htype A a) (t:array A), Dup T -> index t i -> 
    R (l ~> Array T t \* T V v) (# l ~> Array T (t`[i:=V])).
*)


Definition Base A (X:A) (x:A) := 
  [ x = X ].

Implicit Arguments Base [[A]].

Parameter ml_array_make_spec : forall A,
  Spec ml_array_make (n:int) (v:A) |R>> 
     R [] (fun l => Hexists t, l ~> Array Base t \* [t = array_make n v]).

Parameter ml_array_get_spec : forall `{Inhabited A},
  Spec ml_array_get (l:loc) (i:int) |R>> 
    forall (t:array A), index t i ->
    Read (R:~~A) (l ~> Array Base t) (\= t\(i)).

Parameter ml_array_set_spec : forall A,
  Spec ml_array_set (l:loc) (i:int) (v:A) |R>> 
    forall (t:array A), index t i -> 
    R (l ~> Array Base t) (# Hexists t', l ~> Array Base t' \* [t' = t\(i:=v)]).


Parameter ml_array_length_spec : forall A,
  Spec ml_array_length (l:loc) |R>> forall (t:array A),
    Read R (l ~> Array Base t) (\= LibArray.length t).



Hint Extern 1 (RegisterSpec ml_array_make) => Provide ml_array_make_spec.
Hint Extern 1 (RegisterSpec ml_array_get) => Provide ml_array_get_spec.
Hint Extern 1 (RegisterSpec ml_array_set) => Provide ml_array_set_spec.
Hint Extern 1 (RegisterSpec ml_array_length) => Provide ml_array_length_spec.



(*

Parameter ml_array_make_spec : forall a,
  Spec ml_array_make (n:int) (v:a) |R>> 
    R [] (_~> ArrayOn (Array.make n V)).

Parameter ml_array_get_spec : forall a A,
  Spec ml_array_get (l:loc) (i:int) |R>> 
    index t i -> read R (l ~> ArrayOn t) (= t\[i]).

Parameter ml_array_set_spec : forall a,
  Spec ml_array_set (l:loc) (i:int) (v:a) |R>> 
    index t i -> R (l ~> ArrayOn t) (# l ~> ArrayOn t'[i:=v]).

*)





Opaque Zplus.
Opaque Ref.


(*
let incr r = 
   r := !r + 1

let not b =
  if b then false else true

let fst (x,y) = x
let snd (x,y) = y
*)






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

Notation "'Func'" := val.


(*

Lemma focus_mcons : forall (l:loc) A (X:A) (L':list A),
  (l ~> Mlist (X::L')) ==>
  Hexists l', (l ~~> (X,l')) \* (l' ~> Mlist L').
Proof.
  intros. simpl. hdata_simpl. auto. 
Qed.
*)


Notation "'AppReturns'" := app_1.
Ltac xinduct E := xinduction_heap E.



Tactic Notation "xchange" constr(E) "as" := 
  xchange E; xextract.
Tactic Notation "xchange" constr(E) "as" simple_intropattern(I1) := 
  xchange E; xextract as I1.
Tactic Notation "xchange" constr(E) "as" simple_intropattern(I1) simple_intropattern(I2) := 
  xchange E; xextract as I1 I2.
Tactic Notation "xchange" constr(E) "as" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) := 
  xchange E; xextract as I1 I2 I3.
Tactic Notation "xchange" constr(E) "as" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) := 
  xchange E; xextract as I1 I2 I3 I4. 

Tactic Notation "xchange" "~" constr(E) "as" := 
  xchange~ E; xextract.
Tactic Notation "xchange" "~" constr(E) "as" simple_intropattern(I1) := 
  xchange~ E; xextract as I1.
Tactic Notation "xchange" "~" constr(E) "as" simple_intropattern(I1) simple_intropattern(I2) := 
  xchange~ E; xextract as I1 I2.
Tactic Notation "xchange" "~" constr(E) "as" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) := 
  xchange~ E; xextract as I1 I2 I3.
Tactic Notation "xchange" "~" constr(E) "as" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) := 
  xchange~ E; xextract as I1 I2 I3 I4. 

Tactic Notation "xapp_hyp" :=
  eapply local_weaken; 
    [ xlocal
    | let f := spec_goal_fun tt in let H := get_spec_hyp f in 
      apply (proj2 H) (* todo generalize to arities*)
    | hsimpl
    | hsimpl ].


Notation "'LetFuncs' a f1 ':=' Q1 'in' F" :=
  (!!F a fun H Q => forall f1, exists P1,
     (Q1 -> P1 f1) /\ (P1 f1 -> F H Q))
  (at level 69, a at level 0, f1 ident, only parsing) : charac.

Notation "'LetFun_' a f x ':=' Q 'in' F" :=
  (LetFuncs a f := (Body f x => Q) in F)
  (at level 69, a at level 0, f ident, x ident) : charac.



Notation "'LetFuncss' f1 ':=' Q1 'in' F" :=
  (!F fun H Q => forall f1, exists P1,
     (Q1 -> P1 f1) /\ (P1 f1 -> F H Q))
  (at level 69, f1 ident, only parsing) : charac.

Notation "'LetFun' f x ':=' Q 'in' F" :=
  (LetFuncss f := (Body f x => Q) in F)
  (at level 69, f ident, x ident) : charac.



