Set Implicit Arguments.
Require Export LibInt LibArray CFSpec CFPrint.


(********************************************************************)
(** Imperative Representation for base types *)

Global Opaque heap_is_empty hdata heap_is_single heap_is_empty_st. 
  (* todo: check needed *)

Global Opaque Zplus. (* todo: move *)

Transparent hdata. (* todo: should use hdata_simpl instead *)


(*------------------------------------------------------------------*)
(* ** References *)

(* TODO: ideally, references should be treated simply
   as a record with a single field, so the following
   material would be generated automatically. *)

Definition Ref a A (T:htype A a) (V:A) (l:loc) :=
  Hexists v, heap_is_single l v \* v ~> T V.

Notation "l '~~>' v" := (l ~> Ref Id v)
  (at level 32, no associativity) : heap_scope.
Notation "'~~>' v" := (~> Ref Id v)
  (at level 32, no associativity) : heap_scope.
(*
 Notation "l '~~>' v" := (hdata (Ref Id v) l)
  (at level 32, no associativity) : heap_scope.
*)

Lemma focus_ref : forall (l:loc) a A (T:htype A a) V,
  l ~> Ref T V ==> Hexists v, l ~~> v \* v ~> T V.
Proof. intros. unfold Ref, hdata. unfold Id. hextract. hsimpl~. Qed.

Lemma unfocus_ref : forall (l:loc) a (v:a) A (T:htype A a) V,
  l ~~> v \* v ~> T V ==> l ~> Ref T V.
Proof. intros. unfold Ref. hdata_simpl. hsimpl. subst~. Qed.

Lemma heap_is_single_impl_null : forall (l:loc) A (v:A),
  heap_is_single l v ==> heap_is_single l v \* [l <> null].
Proof.
  intros. intros h Hh. forwards*: heap_is_single_null. exists___*.
Qed.

Lemma focus_ref_null : forall a A (T:htype A a) V,
  null ~> Ref T V ==> [False].
Proof.
  intros. unfold Ref, hdata. hextract as v.
  hchanges (@heap_is_single_impl_null null).
Qed.

Global Opaque Ref.
Implicit Arguments focus_ref [a A].
Implicit Arguments unfocus_ref [a A].


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

Global Opaque Tup2.

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

Global Opaque Tup3.


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
Proof. intros. simpl. hdata_simpl. destruct l. auto. hsimpl. Qed.

Lemma unfocus_nil' : forall A (L:list A) a (T:A->a->hprop),
  nil ~> List T L ==> [L = nil].
Proof.
  intros. destruct L.
  simpl. hdata_simpl. hsimpl~.
  simpl. hdata_simpl. hsimpl.
Qed.

Lemma focus_cons : forall a (l:list a) A (X:A) (L':list A) (T:A->a->hprop),
  (l ~> List T (X::L')) ==>
  Hexists x l', (x ~> T X) \* (l' ~> List T L') \* [l = x::l'].
Proof. intros. simpl. hdata_simpl. destruct l; hsimpl~. Qed.

Lemma focus_cons' : forall a (x:a) (l:list a) A (L:list A) (T:A->a->hprop),
  (x::l) ~> List T L ==> 
  Hexists X L', [L = X::L'] \* (x ~> T X) \* (l ~> List T L').
Proof. intros. destruct L; simpl; hdata_simpl; hsimpl~. Qed.

Lemma unfocus_cons : forall a (x:a) (l:list a) A (X:A) (L:list A) (T:A->a->hprop),
  (x ~> T X) \* (l ~> List T L) ==> 
  ((x::l) ~> List T (X::L)).
Proof. intros. simpl. hdata_simpl. hsimpl. Qed.

Global Opaque List.


(************************************************************)
(** Axiomatic specification of the primitive functions *)

(** Pointer comparison *)

Parameter ml_phy_eq : func.
Parameter ml_phy_eq_spec : Pure ml_phy_eq x y >> = (x '= y :> loc).
Hint Extern 1 (RegisterSpec ml_phy_eq) => Provide ml_phy_eq_spec.

Parameter ml_phy_neq : func.
Parameter ml_phy_neq_spec : Pure ml_phy_neq x y >> = (x '<> y :> loc).
Hint Extern 1 (RegisterSpec ml_phy_neq) => Provide ml_phy_neq_spec.

(** Arithmetic *)

Parameter ml_plus : func.
Parameter ml_plus_spec : Pure ml_plus x y >> = (x + y)%Z.
Hint Extern 1 (RegisterSpec ml_plus) => Provide ml_plus_spec.

Parameter ml_minus : func.
Parameter ml_minus_spec : Pure ml_minus x y >> = (x - y)%Z.
Hint Extern 1 (RegisterSpec ml_minus) => Provide ml_minus_spec.

Parameter ml_eqb : func.
Parameter ml_eqb_int_spec : Pure ml_eqb (x:int) (y:int) >> = (x '= y).
Hint Extern 1 (RegisterSpec ml_eqb) => Provide ml_eqb_int_spec.

Parameter ml_leq : func.
Parameter ml_leq_spec : Pure ml_leq x y >> = (x <= y)%I.
Hint Extern 1 (RegisterSpec ml_leq) => Provide ml_leq_spec.

Parameter ml_geq : func.
Parameter ml_geq_spec : Pure ml_geq x y >> = (x >= y)%I.
Hint Extern 1 (RegisterSpec ml_geq) => Provide ml_geq_spec.

Parameter ml_lt : func.
Parameter ml_lt_spec : Pure ml_lt x y >> = (x < y)%I.
Hint Extern 1 (RegisterSpec ml_lt) => Provide ml_lt_spec.

Parameter ml_gt : func.
Parameter ml_gt_spec : Pure ml_gt x y >> = (x > y)%I.
Hint Extern 1 (RegisterSpec ml_gt) => Provide ml_gt_spec.

Parameter ml_and : func.
Parameter ml_and_spec : Pure ml_and x y >> = (x && y).
Hint Extern 1 (RegisterSpec ml_and) => Provide ml_and_spec.

Parameter ml_or : func.
Parameter ml_or_spec : Pure ml_or x y >> = (x || y).
Hint Extern 1 (RegisterSpec ml_and) => Provide ml_or_spec.

(** Pairs *)

Parameter ml_fst : func.
Parameter ml_fst_spec : forall a1 a2,
  Spec ml_fst (p:a1*a2) |R>> 
    pure R (= fst p).
Hint Extern 1 (RegisterSpec ml_fst) => Provide ml_fst_spec.

Parameter ml_snd : func.
Parameter ml_snd_spec : forall a1 a2,
  Spec ml_snd (p:a1*a2) |R>> 
    pure R (= snd p).
Hint Extern 1 (RegisterSpec ml_snd) => Provide ml_snd_spec.

(** References *)

Parameter ml_ref : func.
Parameter ml_get : func.
Parameter ml_set : func.
Parameter ml_incr : func.
Parameter ml_decr : func.

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

(** Group of References *)

Require Import CFTactics.

Lemma ml_ref_spec_group : forall a,
  Spec ml_ref (v:a) |R>> forall (M:map loc a),
    R (Group (Ref Id) M) (fun l => Group (Ref Id) (M\(l:=v))).
Proof.
  intros. xweaken. intros v R LR HR M. simpls.
  xframe - []. eauto. intros l. 
  hchange Group_add. hsimpl. hsimpl.
Qed.

Lemma ml_get_spec_group : forall `{Inhab a},
  Spec ml_get (l:loc) |R>> forall (M:map loc a), l \indom M ->
    keep R (Group (Ref Id) M) (\= M\(l)).
Proof.
  intros. xweaken. intros l R LR HR M IlM. simpls.
  rewrite~ (Group_rem l M). xapply_local (HR (M\(l))); hsimpl~. 
Qed.

Lemma ml_set_spec_group :  forall `{Inhab a},
  Spec ml_set (l:loc) (v:a) |R>> forall (M:map loc a), l \indom M ->
    R (Group (Ref Id) M) (# Group (Ref Id) (M\(l:=v))).
Proof.
  intros. xweaken. intros l v R LR HR M IlM. simpls.
  rewrite~ (Group_rem l M).
  xapply_local (HR (M\(l))). hsimpl.
  intros _. hchanges~ (Group_add' l M).
Qed.


(** Strong References *) (* todo: unify with normal ref? *)

Parameter ml_sset : func.
Parameter ml_sset_spec : forall a a',
  Spec ml_sset (l:loc) (v:a) |R>> 
    forall (v':a'), R (l ~~> v') (# l ~~> v).
Hint Extern 1 (RegisterSpec ml_sset) => Provide ml_sset_spec.

(** Arrays *)

Parameter ml_array_make : func.
Parameter ml_array_get : func.
Parameter ml_array_set : func.
Parameter ml_array_init : func.
Parameter ml_array_length : func.

Parameter Array : forall a A (T:htype A a) (M:array A) (l:loc), hprop.

Require Import LibBag.

Parameter ml_array_make_spec : forall a,
  Spec ml_array_make (n:int) (v:a) |R>> 
     R [] (~> Array Id (LibArray.make n v)).

Parameter ml_array_get_spec : forall a,
  Spec ml_array_get (l:loc) (i:int) |R>> 
    forall `{Inhab a} (t:array a), index t i ->
    keep R (l ~> Array Id t) (\= t\(i)).

Parameter ml_array_set_spec : forall a,
  Spec ml_array_set (l:loc) (i:int) (v:a) |R>> 
    forall (t:array a), index t i -> 
    R (l ~> Array Id t) (# l ~> Array Id (t\(i:=v))).

Parameter ml_array_length_spec : forall a,
  Spec ml_array_length (l:loc) |R>> forall (t:array a),
    keep R (l ~> Array Id t) (\= LibArray.length t).

Hint Extern 1 (RegisterSpec ml_array_make) => Provide ml_array_make_spec.
Hint Extern 1 (RegisterSpec ml_array_get) => Provide ml_array_get_spec.
Hint Extern 1 (RegisterSpec ml_array_set) => Provide ml_array_set_spec.
Hint Extern 1 (RegisterSpec ml_array_length) => Provide ml_array_length_spec.

(** Lists *)

Parameter ml_list_iter : func.


(********************************************************************)
(** IO manipulations *)

(*------------------------------------------------------------------*)
(* ** IO representation *)

Parameter Channel : forall (L:list dynamic) (l:loc), hprop.

Notation "l ~>> L" := (l ~> Channel L)
  (at level 32, no associativity).

Parameter stdin : loc.
Parameter stdout : loc.


(*------------------------------------------------------------------*)
(* ** IO primitives *)

Parameter ml_read_int : func.
Parameter ml_read_int_spec :
  Spec ml_read_int () |R>> forall L (n:int),
    R (stdin ~>> (dyn n::L)) (\=n \*+ stdin ~>> L).
Hint Extern 1 (RegisterSpec ml_read_int) => Provide ml_read_int_spec.

Parameter ml_print_int : func.
Parameter ml_print_int_spec :
  Spec ml_print_int (n:int) |R>> forall L,
    R (stdout ~>> L) (# stdout ~>> L & (dyn n)).
Hint Extern 1 (RegisterSpec ml_print_int) => Provide ml_print_int_spec.


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
