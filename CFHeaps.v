Set Implicit Arguments.
Require Export LibCore LibEpsilon Shared LibMap.


(********************************************************************)
(* ** Heaps *)

(*------------------------------------------------------------------*)
(* ** Representation of values packed with their type *)

(** Representation of heap items *)

Record dynamic := dyn { 
  dyn_type : Type; 
  dyn_value : dyn_type }.

Implicit Arguments dyn [[dyn_type]].

Lemma dyn_inj : forall A (x y : A),
  dyn x = dyn y -> x = y. 
Proof. introv H. inverts~ H. Qed.

Lemma dyn_inj_type : forall A1 A2 (x1:A1) (x2:A2),
  dyn x1 = dyn x2 -> A1 = A2.
Proof. introv H. inverts~ H. Qed.

Lemma dyn_eta : forall d, 
  d = dyn (dyn_value d).
Proof. intros. destruct~ d. Qed.


(*------------------------------------------------------------------*)
(* ** Representation of partial functions *)

(** Type of partial functions from A to B *)

Definition pfun (A B : Type) :=
  A -> option B.

(** Finite domain of a partial function *)

Definition pfun_finite (A B : Type) (f : pfun A B) :=
  exists L : list A, forall x, f x <> None -> Mem x L.

(** Disjointness of domain of two partial functions *)

Definition pfun_disjoint (A B : Type) (f1 f2 : pfun A B) :=
  forall x, f1 x = None \/ f2 x = None.

(** Disjoint union of two partial functions *)

Definition pfun_union (A B : Type) (f1 f2 : pfun A B) :=
  fun x => match f1 x with
           | Some y => Some y
           | None => f2 x
           end.

(** Finiteness of union *)

Lemma pfun_union_finite : forall (A B : Type) (f1 f2 : pfun A B),
  pfun_finite f1 -> pfun_finite f2 -> pfun_finite (pfun_union f1 f2).
Proof.
  introv [L1 F1] [L2 F2]. exists (L1 ++ L2). introv M.
  specializes F1 x. specializes F2 x. unfold pfun_union in M. 
  apply Mem_app_or. destruct~ (f1 x).
Qed.

(** Symmetry of disjointness *)

Lemma pfun_disjoint_sym : forall (A B : Type),
  sym (@pfun_disjoint A B).
Proof.
  introv H. unfolds pfun_disjoint. intros z. specializes H z. intuition.
Qed.

(** Commutativity of disjoint union *)

Tactic Notation "cases" constr(E) := 
  let H := fresh "Eq" in cases E as H.

Lemma pfun_union_comm : forall (A B : Type) (f1 f2 : pfun A B),
  pfun_disjoint f1 f2 -> 
  pfun_union f1 f2 = pfun_union f2 f1.
Proof. 
  introv H. extens. intros x. unfolds pfun_disjoint, pfun_union.
  specializes H x. cases (f1 x); cases (f2 x); auto. destruct H; false. 
Qed.

(*------------------------------------------------------------------*)
(* ** Representation of heaps *)

(** Representation of locations *)

Definition loc : Type := nat.

Global Opaque loc.

(** The null location *)

Definition null : loc := 0%nat.

(** Representation of heaps *)

Inductive heap : Type := heap_of {
  heap_data :> pfun loc dynamic;
  heap_finite : pfun_finite heap_data }.

Implicit Arguments heap_of [].  

(** Proving heaps equals *)

Lemma heap_eq : forall f1 f2 F1 F2,
  (forall x, f1 x = f2 x) ->
  heap_of f1 F1 = heap_of f2 F2.
Proof.
  introv H. asserts: (f1 = f2). extens~. subst. 
  fequals. (* note: involves proof irrelevance *)
Qed.

(** Disjoint heaps *)

Definition heap_disjoint (h1 h2 : heap) : Prop :=
  pfun_disjoint h1 h2.

Notation "\# h1 h2" := (heap_disjoint h1 h2)
  (at level 40, h1 at level 0, h2 at level 0, no associativity).

(** Union of heaps *)

Program Definition heap_union (h1 h2 : heap) : heap :=
  heap_of (pfun_union h1 h2) _.
Next Obligation. destruct h1. destruct h2. apply~ pfun_union_finite. Qed.

Notation "h1 \+ h2" := (heap_union h1 h2)
   (at level 51, right associativity).

(** Empty heap *)

Program Definition heap_empty : heap :=
  heap_of (fun l => None) _.
Next Obligation. exists (@nil loc). auto_false. Qed.

(** Singleton heap *)

Program Definition heap_single (l:loc) A (v:A) : heap := 
  heap_of (fun l' => If l = l' then Some (dyn v) else None) _.
Next Obligation.
  exists (l::nil). intros. case_if. 
    subst~.
    false.
Qed.

(*------------------------------------------------------------------*)
(* ** Properties on heaps *)

(** Disjointness *)

Lemma heap_disjoint_sym : forall h1 h2,
  heap_disjoint h1 h2 -> heap_disjoint h2 h1.
Proof. intros [f1 F1] [f2 F2]. apply pfun_disjoint_sym. Qed.

Lemma heap_disjoint_comm : forall h1 h2,
  \# h1 h2 = \# h2 h1.
Proof. lets: heap_disjoint_sym. extens*. Qed. 

Lemma heap_disjoint_empty_l : forall h,
  heap_disjoint heap_empty h.
Proof. intros [f F] x. simple~. Qed.

Lemma heap_disjoint_empty_r : forall h,
  heap_disjoint h heap_empty.
Proof. intros [f F] x. simple~. Qed.

Hint Resolve heap_disjoint_sym heap_disjoint_empty_l heap_disjoint_empty_r.

Lemma heap_disjoint_union_eq_r : forall h1 h2 h3,
  heap_disjoint h1 (heap_union h2 h3) =
  (heap_disjoint h1 h2 /\ heap_disjoint h1 h3).
Proof.
  intros [f1 F1] [f2 F2] [f3 F3].
  unfolds heap_disjoint, heap_union. simpls.
  unfolds pfun_disjoint, pfun_union. extens. iff M [M1 M2].
  split; intros x; specializes M x; 
   destruct (f2 x); intuition; tryfalse.
  intros x. specializes M1 x. specializes M2 x. 
   destruct (f2 x); intuition.
Qed.

Lemma heap_disjoint_union_eq_l : forall h1 h2 h3,
  heap_disjoint (heap_union h2 h3) h1 =
  (heap_disjoint h1 h2 /\ heap_disjoint h1 h3).
Proof.
  intros. rewrite heap_disjoint_comm. 
  apply heap_disjoint_union_eq_r.
Qed.

Definition heap_disjoint_3 h1 h2 h3 :=
  heap_disjoint h1 h2 /\ heap_disjoint h2 h3 /\ heap_disjoint h1 h3.

Notation "\# h1 h2 h3" := (heap_disjoint_3 h1 h2 h3)
  (at level 40, h1 at level 0, h2 at level 0, h3 at level 0, no associativity).

Lemma heap_disjoint_3_unfold : forall h1 h2 h3,
  \# h1 h2 h3 = (\# h1 h2 /\ \# h2 h3 /\ \# h1 h3).
Proof. auto. Qed.

(** Union *)

Lemma heap_union_neutral_l : forall h,
  heap_union heap_empty h = h.
Proof. 
  intros [f F]. unfold heap_union, pfun_union, heap_empty. simpl.
  apply~ heap_eq.
Qed.

Lemma heap_union_neutral_r : forall h,
  heap_union h heap_empty = h.
Proof. 
  intros [f F]. unfold heap_union, pfun_union, heap_empty. simpl.
  apply heap_eq. intros x. destruct~ (f x).
Qed.

Lemma heap_union_comm : forall h1 h2,
  heap_disjoint h1 h2 ->
  heap_union h1 h2 = heap_union h2 h1.
Proof.
  intros [f1 F1] [f2 F2] H. simpls. apply heap_eq. simpl.
  intros. rewrite~ pfun_union_comm.
Qed.

Lemma heap_union_assoc : 
  LibOperation.assoc heap_union.
Proof.
  intros [f1 F1] [f2 F2] [f3 F3]. unfolds heap_union. simpls.
  apply heap_eq. intros x. unfold pfun_union. destruct~ (f1 x).
Qed.

(** Hints and tactics *)

Hint Resolve heap_union_neutral_l heap_union_neutral_r.

Hint Rewrite 
  heap_disjoint_union_eq_l
  heap_disjoint_union_eq_r
  heap_disjoint_3_unfold : rew_disjoint.

Tactic Notation "rew_disjoint" :=
  autorewrite with rew_disjoint in *.
Tactic Notation "rew_disjoint" "*" :=
  rew_disjoint; auto_star.


(********************************************************************)
(* ** Predicate on Heaps *)

(*------------------------------------------------------------------*)
(* ** Definition of heap predicates *)

(** [hprop] is the type of predicates on heaps *)

Definition hprop := heap -> Prop.

(** Empty heap *)

Definition heap_is_empty : hprop := 
  fun h => h = heap_empty.

(** Singleton heap *)

Definition heap_is_single (l:loc) A (v:A) : hprop := 
  fun h => h = heap_single l v /\ l <> null.

(** Heap union *)

Definition heap_is_star (H1 H2 : hprop) : hprop := 
  fun h => exists h1 h2, H1 h1 
                      /\ H2 h2 
                      /\ heap_disjoint h1 h2 
                      /\ h = heap_union h1 h2.

(** Lifting of existentials *)

Definition heap_is_pack A (Hof : A -> hprop) : hprop := 
  fun h => exists x, Hof x h.

(** Lifting of predicates *)

Definition heap_is_empty_st (H:Prop) : hprop :=
  fun h => h = heap_empty /\ H.

Opaque heap_union heap_single heap_is_star heap_is_pack.


(*------------------------------------------------------------------*)
(* ** Notation for heap predicates *)

Notation "[]" := (heap_is_empty) 
  (at level 0) : heap_scope.

Open Scope heap_scope.
Bind Scope heap_scope with hprop.
Delimit Scope heap_scope with h.

Notation "[ L ]" := (heap_is_empty_st L) 
  (at level 0, L at level 99) : heap_scope.

Notation "\[ P ]" := (fun v => heap_is_empty_st (P v)) 
  (at level 0, P at level 99) : heap_scope.

Notation "\= V" := (fun X => [X = V])
  (at level 40) : heap_scope.

Notation "H1 '\*' H2" := (heap_is_star H1 H2)
  (at level 41, right associativity) : heap_scope.

Notation "'Hexists' x1 , H" := (heap_is_pack (fun x1 => H))
  (at level 39, x1 ident, H at level 50) : heap_scope.
Notation "'Hexists' x1 x2 , H" := (Hexists x1, Hexists x2, H)
  (at level 39, x1 ident, x2 ident, H at level 50) : heap_scope.
Notation "'Hexists' x1 x2 x3 , H" := (Hexists x1, Hexists x2, Hexists x3, H)
  (at level 39, x1 ident, x2 ident, x3 ident, H at level 50) : heap_scope.
Notation "'Hexists' x1 x2 x3 , H" := (Hexists x1, Hexists x2, Hexists x3, Hexists x4, H)
  (at level 39, x1 ident, x2 ident, x3 ident, x4 ident, H at level 50) : heap_scope.
Notation "'Hexists' x1 x2 x3 x4 , H" := 
  (Hexists x1, Hexists x2, Hexists x3, Hexists x4, H)
  (at level 39, x1 ident, x2 ident, x3 ident, x4 ident, H at level 50) : heap_scope.
Notation "'Hexists' x1 x2 x3 x4 x5 , H" := 
  (Hexists x1, Hexists x2, Hexists x3, Hexists x4, Hexists x5, H)
  (at level 39, x1 ident, x2 ident, x3 ident, x4 ident, x5 ident, H at level 50) : heap_scope.

Notation "'Hexists' x1 : T1 , H" := (heap_is_pack (fun x1:T1 => H))
  (at level 39, x1 ident, H at level 50, only parsing) : heap_scope.
Notation "'Hexists' ( x1 : T1 ) , H" := (Hexists x1:T1,H)
  (at level 39, x1 ident, H at level 50, only parsing) : heap_scope.
Notation "'Hexists' ( x1 : T1 ) ( x2 : T2 ) , H" := 
  (Hexists x1:T1, Hexists x2:T2, H)
  (at level 39, x1 ident, x2 ident, H at level 50) : heap_scope.
Notation "'Hexists' ( x1 : T1 ) ( x2 : T2 ) ( x3 : T3 ) , H" := 
  (Hexists x1:T1, Hexists x2:T2, Hexists x3:T3, H)
  (at level 39, x1 ident, x2 ident, x3 ident, H at level 50) : heap_scope.
Notation "'Hexists' ( x1 : T1 ) ( x2 : T2 ) ( x3 : T3 ) ( x4 : T4 ) , H" := 
  (Hexists x1:T1, Hexists x2:T2, Hexists x3:T3, Hexists x4:T4, H)
  (at level 39, x1 ident, x2 ident, x3 ident, x4 ident, H at level 50) : heap_scope.
Notation "'Hexists' ( x1 : T1 ) ( x2 : T2 ) ( x3 : T3 ) ( x4 : T4 ) ( x5 : T5 ) , H" := 
  (Hexists x1:T1, Hexists x2:T2, Hexists x3:T3, Hexists x4:T4, Hexists x5:T5, H)
  (at level 39, x1 ident, x2 ident, x3 ident, x4 ident, x5 ident, H at level 50) : heap_scope.

Notation "Q \*+ H" :=
  (fun x => heap_is_star (Q x) H)
  (at level 40) : heap_scope.

Notation "# H" := (fun _:unit => H)
  (at level 39, H at level 99) : heap_scope.


(*------------------------------------------------------------------*)
(* ** Basic properties of heap predicates *)

Lemma heap_is_empty_prove : 
  [] heap_empty.
Proof. hnfs~. Qed.

Lemma heap_is_empty_st_prove : forall (P:Prop),
  P -> [P] heap_empty.
Proof. intros. hnfs~. Qed.

Hint Resolve heap_is_empty_prove heap_is_empty_st_prove.

Lemma heap_is_single_null : forall (l:loc) A (v:A) h,
  heap_is_single l v h -> l <> null.
Proof. unfolds* heap_is_single. Qed.

Lemma heap_is_single_null_eq_false : forall A (v:A),
  heap_is_single null v = [False].
Proof.
  intros. unfold heap_is_single.
  unfold hprop. extens. intros. unfold heap_is_empty_st. auto*.
Qed.

Lemma heap_is_single_null_to_false : forall A (v:A),
  heap_is_single null v ==> [False].
Proof. introv Hh. forwards*: heap_is_single_null. Qed. 

Global Opaque heap_is_empty_st heap_is_single. 


(*------------------------------------------------------------------*)
(* ** Properties of [star] *)

Section Star.
Transparent heap_is_star heap_union.

Lemma star_comm : comm heap_is_star. 
Proof. 
  intros H1 H2. unfold hprop, heap_is_star. extens. intros h.
  iff (h1&h2&M1&M2&D&U); rewrite~ heap_union_comm in U; exists* h2 h1.
Qed.

Lemma star_neutral_l : neutral_l heap_is_star [].
Proof.
  intros H. unfold hprop, heap_is_star. extens. intros h.
  iff (h1&h2&M1&M2&D&U) M. 
  hnf in M1. subst h1 h. rewrite~ heap_union_neutral_l.
  exists heap_empty h. splits~. 
Qed.

Lemma star_neutral_r : neutral_r heap_is_star [].
Proof.
  apply neutral_r_from_comm_neutral_l.
  apply star_comm. apply star_neutral_l.
Qed.

Lemma star_assoc : LibOperation.assoc heap_is_star. 
Proof. 
  intros H1 H2 H3. unfold hprop, heap_is_star. extens. intros h. split.
  intros (h1&h'&M1&(h2&h3&M3&M4&D'&U')&D&U). subst h'.
   exists (heap_union h1 h2) h3. rewrite heap_disjoint_union_eq_r in D.
   splits.
    exists h1 h2. splits*.
    auto.
    rewrite* heap_disjoint_union_eq_l.
    rewrite~ <- heap_union_assoc.
  intros (h'&h3&(h1&h2&M3&M4&D'&U')&M2&D&U). subst h'.
   exists h1 (heap_union h2 h3). rewrite heap_disjoint_union_eq_l in D.
   splits.
    auto.
    exists h2 h3. splits*.
    rewrite* heap_disjoint_union_eq_r.
    rewrite~ heap_union_assoc.
Qed. (* later: exploit symmetry in the proof *)

Lemma star_comm_assoc : comm_assoc heap_is_star.
Proof. apply comm_assoc_prove. apply star_comm. apply star_assoc. Qed.

Lemma starpost_neutral : forall B (Q:B->hprop),
  Q \*+ [] = Q.
Proof. extens. intros. (* unfold starpost. *) rewrite~ star_neutral_r. Qed.

Lemma star_cancel : forall H1 H2 H2',
  H2 ==> H2' -> H1 \* H2 ==> H1 \* H2'.
Proof. introv W (h1&h2&?). exists* h1 h2. Qed.

Lemma heap_star_prop_elim : forall (P:Prop) H h,
  ([P] \* H) h -> P /\ H h.
Proof.
  introv (?&?&N&?&?&?). destruct N. subst. rewrite~ heap_union_neutral_l.
Qed.

Lemma heap_extract_prop : forall (P:Prop) H H',
  (P -> H ==> H') -> ([P] \* H) ==> H'.
Proof. introv W Hh. applys_to Hh heap_star_prop_elim. auto*. Qed.

Lemma heap_weaken_pack : forall A (x:A) H J,
  H ==> J x -> H ==> (heap_is_pack J).
Proof. introv W h. exists x. apply~ W. Qed.

End Star.

(*------------------------------------------------------------------*)
(* ** Normalization of [star] *)

Hint Rewrite 
  star_neutral_l star_neutral_r starpost_neutral : rew_heap.
Hint Rewrite <- star_assoc : rew_heap.

Tactic Notation "rew_heap" :=
  autorewrite with rew_heap.
Tactic Notation "rew_heap" "in" "*" :=
  autorewrite with rew_heap in *.
Tactic Notation "rew_heap" "in" hyp(H) :=
  autorewrite with rew_heap in H.

Tactic Notation "rew_heap" "~" :=
  rew_heap; auto_tilde.
Tactic Notation "rew_heap" "~" "in" "*" :=
  rew_heap in *; auto_tilde.
Tactic Notation "rew_heap" "~" "in" hyp(H) :=
  rew_heap in H; auto_tilde.

Tactic Notation "rew_heap" "*" :=
  rew_heap; auto_star.
Tactic Notation "rew_heap" "*" "in" "*" :=
  rew_heap in *; auto_star.
Tactic Notation "rew_heap" "*" "in" hyp(H) :=
  rew_heap in H; auto_star.


(********************************************************************)
(* ** Specification predicates for values *)

(** Type of post-conditions on values of type B *)

Notation "'~~' B" := (hprop->(B->hprop)->Prop) 
  (at level 8, only parsing) : type_scope.

(** Type for imperative data structures *)

Definition htype A a := A -> a -> hprop.

(** Label for imperative data structures *)

Definition hdata (A:Type) (S:A->hprop) (x:A) : hprop :=
  S x.

Notation "'~>' S" := (hdata S)
  (at level 32, no associativity) : heap_scope.

Notation "x '~>' S" := (hdata S x)
  (at level 33, no associativity) : heap_scope.

(** Specification of pure functions: 
    [pure F P] is equivalent to [F [] \[P]] *)

Definition pure B (R:~~B) := 
  fun P => R [] \[P].

(** Specification of functions that keep their input: 
    [keep F H Q] is equivalent to [F H (Q \*+ H)] *)

Notation "'keep' R H Q" :=
  (R H (Q \*+ H)) (at level 25, R at level 0, H at level 0, Q at level 0).

(* Note: tactics need to be updated if a definition is used instead of notation
   Definition keep B (R:~~B) := fun H Q => R H (Q \*+ H). *)


(********************************************************************)
(* ** Simplification for hdata *)

Lemma hdata_fun : forall a (S:a->hprop) x,
  (x ~> (fun y => S y)) = (S x).
Proof. auto. Qed.

Ltac hdata_simpl_core :=
  repeat rewrite hdata_fun.

Tactic Notation "hdata_simpl" := 
  hdata_simpl_core.
Tactic Notation "hdata_simpl" constr(E) := 
  unfold E; hdata_simpl.


(********************************************************************)
(* ** Special cases for hdata *)

(*------------------------------------------------------------------*)
(* ** Id *)

Definition Id {A:Type} (X:A) (x:A) := 
  [ X = x ].
 
(* TEMP
Lemma Id_focus : forall A (x n : A),
  x ~> Id n ==> [x = n].
Proof. intros. unfold Id. hdata_simpl. hextract. hsimpl~. Qed.

Lemma Id_unfocus : forall A (x : A),
  [] ==> x ~> Id x.
Proof. intros. unfold Id. hdata_simpl. hextract. hsimpl~. Qed.

Implicit Arguments Id_focus [A].
Implicit Arguments Id_unfocus [A].
*)


(*------------------------------------------------------------------*)
(* ** Any *)

(** [x ~> Any tt] describes the fact that x points towards something
    whose value is not relevant. In other words, the model is unit.
    Note: [[True]] is used in place of [[]] to avoid confusing tactics. *)

Definition Any {A:Type} (X:unit) (x:A) := 
  [True].


(********************************************************************)
(* ** Simplification and unification tactics for star *)

Ltac check_goal_himpl tt :=
  match goal with 
  | |- @rel_le unit _ _ _ => let t := fresh "_tt" in intros t; destruct t
  | |- @rel_le _ _ _ _ => let r := fresh "r" in intros r
  | |- pred_le _ _ => idtac
  end.

Ltac protect_evars_in H :=
   match H with context [ ?X ] =>
     let go tt := 
       match X with
       | _ \* _ => fail 1
       | X => fail 1 
       | ?x ~> ?R => 
           match x with
           | x => idtac             
           | _ => fail 20 "Uninstantiated argument at left of ~>"
           end;
           let TR := type of R in
           let K := fresh "TEMP" in 
           sets_eq K: (R : ltac_tag_subst TR)
       | [ ?R ] => 
           let TR := type of R in
           let K := fresh "TEMP" in 
           sets_eq K: (R : ltac_tag_subst TR)
       | _ => let K := fresh "TEMP" in
              sets_eq K: (X : ltac_tag_subst hprop)
       end in
     match type of X with 
     | hprop => go tt
     | heap -> Prop => go tt
     end
  end.


Ltac protect_evars_debug :=
  match goal with |- _ ==> ?H => protect_evars_in H end.

Ltac protect_evars tt :=
  do 5 try match goal with |- ?H1 ==> ?H2 =>
     first [ protect_evars_in H1 | protect_evars_in H2 ]; instantiate
  end.

Ltac unprotect_evars tt :=
  repeat match goal with H : ltac_tag_subst _ |- _ => 
    subst H end;
  unfold ltac_tag_subst.

Hint Rewrite <- star_assoc : hsimpl_assoc.
Hint Rewrite star_neutral_l star_neutral_r : hsimpl_neutral.

Lemma hextract_start : forall H H',
  [] \* (H \* []) ==> H' -> H ==> H'.
Proof. intros. rew_heap in *. auto. Qed.

Lemma hextract_keep : forall H1 H2 H3 H',
  (H1 \* H2) \* H3 ==> H' -> H1 \* (H2 \* H3) ==> H'.
Proof. intros. rew_heap in *. auto. Qed.

Lemma hextract_prop : forall H1 H2 H' (P:Prop),
  (P -> H1 \* H2 ==> H') -> H1 \* ([P] \* H2) ==> H'.
Proof.
  introv W. intros h Hh.
  destruct Hh as (h1&h2'&?&(h2&h3&(?&?)&?&?&?)&?&?).
  apply~ W. exists h1 h3. subst h h2 h2'.
  splits~. rewrite~ heap_union_neutral_l.
Qed.

Lemma hextract_id : forall A (x X : A) H1 H2 H',
  (x = X -> H1 \* H2 ==> H') -> H1 \* (x ~> Id X \* H2) ==> H'.
Proof. intros. unfold Id. apply~ hextract_prop. Qed.

Lemma hextract_exists : forall A H1 H2 H' (J:A->hprop),
  (forall x, H1 \* J x \* H2 ==> H') -> H1 \* (heap_is_pack J \* H2) ==> H'.
Proof.  
  introv W. intros h Hh.
  destruct Hh as (h1&h2'&?&(h2&h3&(?&?)&?&?&?)&?&?).
  applys~ W x. exists h1 (heap_union h2 h3). subst h h2'.
  splits~. exists h2 h3. splits~.
Qed.

Ltac hextract_setup tt :=
  lets: ltac_mark;
  apply hextract_start;
  protect_evars tt; 
  autorewrite with hsimpl_assoc.

Ltac hextract_cleanup tt :=
  autorewrite with hsimpl_assoc;
  autorewrite with hsimpl_neutral;
  unprotect_evars tt; 
  gen_until_mark.

Ltac hextract_relinearize tt :=
  match goal with |- ?H \* (_ \* _) ==> _ =>
    let T := fresh "TEMP" in 
    sets T: H; 
    autorewrite with hsimpl_assoc; 
    subst T
  end.

Ltac hextract_step tt :=
  match goal with |- ?HA \* (?H \* ?HR) ==> ?H' =>
  first [ apply hextract_prop; intros
        | apply hextract_id; intros
        | apply hextract_exists; intros; hextract_relinearize tt
        | apply hextract_keep ]
  end.

Ltac post_impl_intro tt :=
  match goal with 
  | |- @rel_le unit _ _ _ => let t := fresh "_tt" in intros t; destruct t
  | |- @rel_le _ _ _ _ => let r := fresh "r" in intros r
  end.

Ltac hextract_main tt :=
  check_goal_himpl tt;
  hextract_setup tt;
  (repeat (hextract_step tt));
  hextract_cleanup tt.

Ltac hextract_core :=
  hextract_main tt.

Ltac hextract_if_needed tt :=
  match goal with |- ?H ==> _ => match H with
  | context [ heap_is_pack _ ] => hextract_core
  | context [ [ _ ] ] => hextract_core
  end end.

Tactic Notation "hextract" := 
  hextract_core; intros.
Tactic Notation "hextract" "as" := 
  hextract_core.
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
Tactic Notation "hextract" "as" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5) := 
  hextract as; intros I1 I2 I3 I4 I5. 
Tactic Notation "hextract" "as" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) := 
  hextract as; intros I1 I2 I3 I4 I5 I6. 
Tactic Notation "hextract" "as" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) := 
  hextract as; intros I1 I2 I3 I4 I5 I6 I7. 


Lemma hextract_demo_1 : forall n J H2 H3 H4 H',
  H4 \* (Hexists y, [y = 2]) \* (Hexists x, [n = x + x] \* J x \* H2) \* H3 ==> H'.
Proof.
  intros. dup 3.
  (* details *)
  hextract_setup tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  try hextract_step tt.
  hextract_cleanup tt.
  intros.
  skip.
  (* short *)
  hextract. skip.
  (* if needed *)
  hextract_if_needed tt. intros.
  try hextract_if_needed tt. skip.
Qed.

Lemma hextract_demo_2 : forall H1 H' (G:Prop),
  (forall H2, H1 \* (Hexists y, [y = 2]) \* H2 ==> H' -> G) ->
  G.
Proof.
  introv W. eapply W. dup.
  (* details *)
  hextract_setup tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  try hextract_step tt.
  hextract_cleanup tt.
  intros y Hy.
  skip.
  (* short *)
  hextract. skip.
Admitted.


Inductive Hsimpl_hint : list Boxer -> Type :=
  | hsimpl_hint : forall (L:list Boxer), Hsimpl_hint L.

Ltac hsimpl_hint_put L := 
  lets: (hsimpl_hint L).

Ltac hsimpl_hint_next cont :=
  match goal with H: Hsimpl_hint ((boxer ?x)::?L) |- _ =>
    clear H; hsimpl_hint_put L; cont x end.

Ltac hsimpl_hint_remove :=
  match goal with H: Hsimpl_hint _ |- _ => clear H end.

Lemma demo_hsimpl : exists n, n = 3.
Proof.
  hsimpl_hint_put (>>> 3 true).
  hsimpl_hint_next ltac:(fun x => exists x).
  hsimpl_hint_remove.
  auto.
Qed.


Lemma hsimpl_start : forall H1 H2,
  H1 \* [] ==> [] \* (H2 \* []) -> H1 ==> H2.
Proof. intros. rew_heap in *. auto. Qed.

Lemma hsimpl_keep : forall H1 H2 H3 H4,
  H1 ==> (H2 \* H3) \* H4 -> H1 ==> H2 \* (H3 \* H4).
Proof. intros. rew_heap in *. auto. Qed.

Lemma hsimpl_extract_prop : forall H1 H2 H3 (P:Prop),
  H1 ==> H2 \* H3 -> P -> H1 ==> H2 \* ([P] \* H3).
Proof.
  introv W HP PH1. destruct (W _ PH1) as (h1&h2&?&?&?&?).
  exists h1 h2. splits~. exists heap_empty h2. splits~.
Qed.

Lemma hsimpl_extract_id : forall A (x X : A) H1 H2 H3,
  H1 ==> H2 \* H3 -> x = X -> H1 ==> H2 \* (x ~> Id X \* H3).
Proof. intros. unfold Id. apply~ hsimpl_extract_prop. Qed.

Lemma hsimpl_extract_exists : forall A (x:A) H1 H2 H3 (J:A->hprop),
  H1 ==> H2 \* J x \* H3 -> H1 ==> H2 \* (heap_is_pack J \* H3).
Proof.
  introv W. intros h1 PH1. destruct (W _ PH1) as (h2&h4&?&(hx&h3&?&?&?&?)&?&?).
  exists h2 (heap_union hx h3). subst h1 h4. splits~.
  exists hx h3. splits~. exists~ x.
Qed.

Lemma hsimpl_cancel_1 : forall H HA HR HT,
  HT ==> HA \* HR -> H \* HT ==> HA \* (H \* HR).
Proof. intros. rewrite star_comm_assoc. apply~ star_cancel. Qed.

Lemma hsimpl_cancel_2 : forall H HA HR H1 HT,
  H1 \* HT ==> HA \* HR -> H1 \* H \* HT ==> HA \* (H \* HR).
Proof. intros. rewrite (star_comm_assoc H1). apply~ hsimpl_cancel_1. Qed.

Lemma hsimpl_cancel_3 : forall H HA HR H1 H2 HT,
  H1 \* H2 \* HT ==> HA \* HR -> H1 \* H2 \* H \* HT ==> HA \* (H \* HR).
Proof. intros. rewrite (star_comm_assoc H2). apply~ hsimpl_cancel_2. Qed.

Lemma hsimpl_cancel_4 : forall H HA HR H1 H2 H3 HT,
  H1 \* H2 \* H3 \* HT ==> HA \* HR -> H1 \* H2 \* H3 \* H \* HT ==> HA \* (H \* HR).
(*Proof. intros. rewrite (star_comm_assoc H3). apply~ hsimpl_cancel_3. Qed.*)
Admitted. (* skip proof for faster compilation *)

Lemma hsimpl_cancel_5 : forall H HA HR H1 H2 H3 H4 HT,
  H1 \* H2 \* H3 \* H4 \* HT ==> HA \* HR -> H1 \* H2 \* H3 \* H4 \* H \* HT ==> HA \* (H \* HR).
(*Proof. intros. rewrite (star_comm_assoc H4). apply~ hsimpl_cancel_4. Qed.*)
Admitted.

Lemma hsimpl_cancel_6 : forall H HA HR H1 H2 H3 H4 H5 HT,
  H1 \* H2 \* H3 \* H4 \* H5 \* HT ==> HA \* HR -> H1 \* H2 \* H3 \* H4 \* H5 \* H \* HT ==> HA \* (H \* HR).
(*Proof. intros. rewrite (star_comm_assoc H5). apply~ hsimpl_cancel_5. Qed.*)
Admitted.

Lemma hsimpl_cancel_eq_1 : forall H H' HA HR HT,
  H = H' -> HT ==> HA \* HR -> H \* HT ==> HA \* (H' \* HR).
Proof. intros. subst. apply~ hsimpl_cancel_1. Qed.

Lemma hsimpl_cancel_eq_2 : forall H H' HA HR H1 HT,
  H = H' -> H1 \* HT ==> HA \* HR -> H1 \* H \* HT ==> HA \* (H' \* HR).
Proof. intros. subst. apply~ hsimpl_cancel_2. Qed.

Lemma hsimpl_cancel_eq_3 : forall H H' HA HR H1 H2 HT,
  H = H' -> H1 \* H2 \* HT ==> HA \* HR -> H1 \* H2 \* H \* HT ==> HA \* (H' \* HR).
Proof. intros. subst. apply~ hsimpl_cancel_3. Qed.

Lemma hsimpl_cancel_eq_4 : forall H H' HA HR H1 H2 H3 HT,
  H = H' -> H1 \* H2 \* H3 \* HT ==> HA \* HR -> H1 \* H2 \* H3 \* H \* HT ==> HA \* (H' \* HR).
Proof. intros. subst. apply~ hsimpl_cancel_4. Qed.

Lemma hsimpl_cancel_eq_5 : forall H H' HA HR H1 H2 H3 H4 HT,
  H = H' -> H1 \* H2 \* H3 \* H4 \* HT ==> HA \* HR -> H1 \* H2 \* H3 \* H4 \* H \* HT ==> HA \* (H' \* HR).
Proof. intros. subst. apply~ hsimpl_cancel_5. Qed.

Lemma hsimpl_cancel_eq_6 : forall H H' HA HR H1 H2 H3 H4 H5 HT,
  H = H' -> H1 \* H2 \* H3 \* H4 \* H5 \* HT ==> HA \* HR -> H1 \* H2 \* H3 \* H4 \* H5 \* H \* HT ==> HA \* (H' \* HR).
Proof. intros. subst. apply~ hsimpl_cancel_6. Qed.

Ltac hsimpl_setup tt :=
  apply hsimpl_start;
  protect_evars tt; 
  autorewrite with hsimpl_assoc.

Ltac hsimpl_try_same tt :=
  first 
  [ apply hsimpl_cancel_1
  | apply hsimpl_cancel_2
  | apply hsimpl_cancel_3
  | apply hsimpl_cancel_4
  | apply hsimpl_cancel_5
  | apply hsimpl_cancel_6 ].

Ltac hsimpl_find_same H HL :=
  match HL with
  | H \* _ => apply hsimpl_cancel_1
  | _ \* H \* _ => apply hsimpl_cancel_2
  | _ \* _ \* H \* _ => apply hsimpl_cancel_3
  | _ \* _ \* _ \* H \* _ => apply hsimpl_cancel_4
  | _ \* _ \* _ \* _ \* H \* _ => apply hsimpl_cancel_5
  | _ \* _ \* _ \* _ \* _ \* H \* _ => apply hsimpl_cancel_6
  end.

Ltac hsimpl_find_data H HL :=
  match H with hdata _ ?l =>
  match HL with
  | hdata _ l \* _ => apply hsimpl_cancel_eq_1
  | _ \* hdata _ l \* _ => apply hsimpl_cancel_eq_2
  | _ \* _ \* hdata _ l \* _ => apply hsimpl_cancel_eq_3
  | _ \* _ \* _ \* hdata _ l \* _ => apply hsimpl_cancel_eq_4
  | _ \* _ \* _ \* _ \* hdata _ l \* _ => apply hsimpl_cancel_eq_5
  | _ \* _ \* _ \* _ \* _ \* hdata _ l \* _ => apply hsimpl_cancel_eq_6
  end end; [ fequal; fequal | ].

Ltac hsimpl_extract_exists_with_hints tt :=
  match goal with |- ?HL ==> ?HA \* (heap_is_pack ?J \* ?HR) =>
    hsimpl_hint_next ltac:(fun x =>
      match x with
      | __ => eapply hsimpl_extract_exists
      | _ => apply (@hsimpl_extract_exists _ x)
      end)
  end.

Ltac hsimpl_extract_exists_step tt :=
  first [ hsimpl_extract_exists_with_hints tt
        | eapply hsimpl_extract_exists ];
   autorewrite with hsimpl_assoc.

Ltac hsimpl_step tt :=
  match goal with |- ?HL ==> ?HA \* (?H \* ?HR) =>
    first  (* hsimpl_find_same H HL |*)
          [ hsimpl_try_same tt 
          | hsimpl_find_data H HL;
            [ first [ eassumption | symmetry; eassumption | idtac ]
            | ]
          | apply hsimpl_extract_prop
          | apply hsimpl_extract_id
          | hsimpl_extract_exists_step tt
          | apply hsimpl_keep ]
  end.

Ltac hsimpl_cleanup tt :=
  autorewrite with hsimpl_neutral;
  unprotect_evars tt;
  try apply pred_le_refl;
  try hsimpl_hint_remove.

Ltac hsimpl_main tt :=
  check_goal_himpl tt;
  hsimpl_setup tt;
  (repeat (hsimpl_step tt));
  hsimpl_cleanup tt.

Tactic Notation "hsimpl" := hsimpl_main tt.
Tactic Notation "hsimpl" "~" := hsimpl; auto_tilde.
Tactic Notation "hsimpl" "*" := hsimpl; auto_star.
Tactic Notation "hsimpl" constr(L) :=
  match type of L with 
  | list Boxer => hsimpl_hint_put L
  | _ => hsimpl_hint_put (boxer L :: nil)
  end; hsimpl.
Tactic Notation "hsimpl" constr(X1) constr(X2) :=
  hsimpl (>>> X1 X2).
Tactic Notation "hsimpl" constr(X1) constr(X2) constr(X3) :=
  hsimpl (>>> X1 X2 X3).

Tactic Notation "hsimpl" "~" constr(L) :=
  hsimpl L; auto~.
Tactic Notation "hsimpl" "~" constr(X1) constr(X2) :=
  hsimpl X1 X2; auto~.
Tactic Notation "hsimpl" "~" constr(X1) constr(X2) constr(X3) :=
  hsimpl X1 X2 X3; auto~.


Lemma hsimpl_demo : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* H3 \* H4 ==> H4 \* H3 \* H5 \* H2.
Proof.
  intros. dup. 
  (* details *)
  hsimpl_setup tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_cleanup tt.
  skip.
  (* short *)
  hsimpl. skip.
Qed.

Lemma hsimpl_demo_2 : forall (l1 l2:loc) S1 S2 H1 H2 H3 H',
  (forall X S1' HG, X ==> H1 \* l1 ~> S1' \* H2 \* HG -> X ==> H') ->
  H1 \* l1 ~> S1 \* l2 ~> S2 \* H3 ==> H'.
Proof.
  intros. dup.
  (* details *) 
  eapply H.
  hsimpl_setup tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_cleanup tt.
  skip.
  (* short *)
  eapply H.
  hsimpl. skip.
Admitted.

Lemma hsimpl_demo_3 : forall (l1 l2:loc) S1 S2 H1 H2 H',
  (forall X S1' HG, X ==> H1 \* l1 ~> S1' \* HG -> HG = HG -> X ==> H') ->
  H1 \* l1 ~> S1 \* l2 ~> S2 \* H2 ==> H'.
Proof.
  intros. dup.
  (* details *)
  eapply H.  
  hsimpl_setup tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_cleanup tt.
  auto.
  (* short *)
  eapply H.
  hsimpl.
  auto.
Admitted.

Lemma hsimpl_demo_4 : forall n m J H2 H3 H4,
  n = m + m ->
  H2 \* J m \* H3 \* H4 ==> H4 \* (Hexists y, y ~> Id 2) \* (Hexists x, [n = x + x] \* J x \* H2) \* H3.
Proof.
  intros. dup.
  (* details *)
  hsimpl_setup tt.
  hsimpl_step tt.
  hsimpl_step tt. 
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_cleanup tt.
  auto.
  eauto.
  (* short *)
  hsimpl.
  auto.
  eauto.
Qed.

Lemma hsimpl_demo_5 : forall n J H,
  n = 2 ->
  J n \* H ==> H \* Hexists y, [y <> 3] \* J y.
Proof.
  intros. dup 3.
  hsimpl. math.
  hsimpl n. math.
  hsimpl 2. subst~. math.
Qed.

Lemma heap_weaken_star : forall H1' H1 H2 H3,
  (H1 ==> H1') -> (H1' \* H2 ==> H3) -> (H1 \* H2 ==> H3).
Proof.
  introv W M (h1&h2&N). intuit N. apply M. exists~ h1 h2.
Qed. (* todo: move *)

Lemma hsimpl_to_qunit : forall (H:hprop) (Q:unit->hprop),
  Q = (fun _ => H) ->
  H ==> Q tt.
Proof. intros. subst. auto. Qed. (* todo: needed? *)
Hint Resolve hsimpl_to_qunit.


(*------------------------------------------------------------------*)
(* ** Tactic [hchange] *)

Lemma hchange_lemma : forall H1 H1' H H' H2,
  (H1 ==> H1') -> (H ==> H1 \* H2) -> (H1' \* H2 ==> H') -> (H ==> H').
Proof.
  intros. applys* (@pred_le_trans heap) (H1 \* H2). 
  applys* (@pred_le_trans heap) (H1' \* H2). hsimpl~. 
Qed.

Ltac hchange_apply L cont :=
  eapply hchange_lemma; 
    [ applys L | cont tt | ].

Ltac hchange_forwards L modif cont :=
  forwards_nounfold_then L ltac:(fun K =>
  match modif with
  | __ => 
     match type of K with
     | _ = _ => hchange_apply (@pred_le_proj1 _ _ _ K) cont
     | _ => hchange_apply K cont
     end
  | _ => hchange_apply (@modif _ _ _ K) cont
  end).

Ltac hchange_core E modif :=
  match E with
  (*  | ?H ==> ?H' => hchange_with_core H H' *)
  | _ => hchange_forwards E modif ltac:(fun _ => instantiate; hsimpl)
  end.

Tactic Notation "hchange_debug" constr(E) :=
  hchange_forwards E __ ltac:(idcont).
Tactic Notation "hchange_debug" "->" constr(E) :=
  hchange_forwards E pred_le_proj1 ltac:(idcont).
Tactic Notation "hchange_debug" "<-" constr(E) :=
  hchange_forwards pred_le_proj2 ltac:(idcont).

Tactic Notation "hchange" constr(E) :=
  hchange_core E __.
Tactic Notation "hchange" "->" constr(E) :=
  hchange_core E pred_le_proj1.
Tactic Notation "hchange" "<-" constr(E) :=
  hchange_core E pred_le_proj2.

Tactic Notation "hchange" "~" constr(E) :=
  hchange E; auto~.
Tactic Notation "hchange" "*" constr(E) :=
  hchange E; auto*.



(********************************************************************)
(* ** Locality *)

(*------------------------------------------------------------------*)
(* ** Definition of [local] *)

(** "Local" = Frame rule + consequence rule + garbage collection *)

Definition local B (F:~~B) : ~~B :=
  fun (H:hprop) (Q:B->hprop) =>
    forall h, H h -> exists H1 H2 Q1 H',
       (H1 \* H2) h 
    /\ F H1 Q1
    /\ Q1 \*+ H2 ===> Q \*+ H'.

(** Characterization of "local" judgments *)

Definition is_local B (F:~~B) :=
  F = local F.

(** The weakening property is implied by locality *)

Definition weakenable B (F:~~B) :=
  forall H Q , F H Q ->
  forall H' Q', H' ==> H -> Q ===> Q' -> F H' Q'.


(*------------------------------------------------------------------*)
(* ** Properties of [local] *)

(** The [local] operator can be freely erased from a conclusion *)

Lemma local_erase : forall B (F:~~B), 
  forall H Q, F H Q -> local F H Q.
Proof.
  intros. exists H [] Q []. splits.
  rew_heap~. auto. auto.
Qed.

(** Nested applications [local] are redundant *)

Lemma local_local : forall B (F:~~B),
  local (local F) = local F.
Proof.
  extens. intros H Q. iff M. 
  introv PH.
  destruct (M _ PH) as (H1&H2&Q1&H'&PH12&N&Qle).
  destruct PH12 as (h1&h2&PH1&PH2&Ph12&Fh12).
  destruct (N _ PH1) as (H1'&H2'&Q1'&H''&PH12'&N'&Qle').
  exists H1' (H2' \* H2) Q1' (H' \* H''). splits.
   rewrite star_assoc.
   exists~ h1 h2.
   auto.
   intros x. specializes Qle x. specializes Qle' x. 
    rewrite star_assoc. applys heap_weaken_star Qle'.
    rewrite (star_assoc (Q x)). hsimpl. auto.
  apply~ local_erase.
Qed.

(** A definition whose head is [local] satisfies [is_local] *)

Lemma local_is_local : forall B (F:~~B),
  is_local (local F).
Proof. intros. unfolds. rewrite~ local_local. Qed.

Hint Resolve local_is_local.

(** Weaken and frame and gc property [local] *)

Lemma local_wgframe : forall B (F:~~B) H H1 H2 H' Q1 Q,
  is_local F -> 
  F H1 Q1 -> 
  H ==> H1 \* H2 -> 
  Q1 \*+ H2 ===> Q \*+ H' ->
  F H Q.
Proof.
  introv L M WH WQ. rewrite L. introv Ph.
  exists H1 H2 Q1 H'. splits; rew_heap~.
Qed.

(** Weaken and frame properties from [local] *)

Lemma local_wframe : forall B H1 H2 Q1 (F:~~B) H Q,
  is_local F -> 
  F H1 Q1 -> 
  H ==> H1 \* H2 -> 
  Q1 \*+ H2 ===> Q ->
  F H Q.
Proof.
  introv L M WH WQ. rewrite L. introv Ph.
  exists H1 H2 Q1 []. splits; rew_heap~.
Qed.

(** Weakening from [local] *)

Lemma local_weaken : forall B H' Q' (F:~~B) H Q,
  is_local F -> 
  F H' Q' -> 
  H ==> H' -> 
  Q' ===> Q ->
  F H Q.
Proof.
  intros. eapply local_wframe with (H2 := []); eauto; rew_heap~.
Qed.

Lemma local_weaken' : forall B (F:~~B),
  is_local F -> weakenable F.
Proof. intros_all. apply* local_weaken. Qed.
    (* todo: use only one lemma from the two above *)

Lemma local_weaken_pre : forall H' B (F:~~B) H Q,
  is_local F -> 
  F H' Q -> 
  H ==> H' -> 
  F H Q.
Proof. intros. apply* local_weaken. Qed.

(** Garbage collection on post-condition from [local] *)

Lemma local_gc_post : forall H' B Q' (F:~~B) H Q,
  is_local F -> 
  F H Q' ->
  Q' ===> Q \*+ H' ->
  F H Q.
Proof.
  introv L M W. rewrite L. introv Ph.
  exists H [] Q' H'. splits; rew_heap~.
Qed.

(** Garbage collection on precondition from [local] *)

Lemma local_gc_pre : forall HG H' B (F:~~B) H Q,
  is_local F -> 
  H ==> HG \* H' ->
  F H' Q ->
  F H Q.
Proof.
  introv L M W. rewrite L. introv Ph.
  exists H' HG Q HG. splits.
  rewrite star_comm. apply~ M.
  auto.
  auto.
Qed.

(** Extraction of premisses from [local] *)

Lemma local_intro_prop : forall B (F:~~B) (H:hprop) (P:Prop) Q,
  is_local F -> (forall h, H h -> P) -> (P -> F H Q) -> F H Q.
Proof.
  introv L W M. rewrite L. introv Hh. forwards~: (W h).
  exists H [] Q []. splits; rew_heap~.
Qed. 

Lemma local_intro_prop' : forall B (F:~~B) H (P:Prop) Q,
  is_local F -> (P -> F H Q) -> F ([P] \* H) Q.
Proof.
  introv L M. rewrite L. introv (h1&h2&(PH1&HP)&PH2&?&?).
  subst h1. rewrite heap_union_neutral_l in H1. subst h2.
  exists H [] Q []. splits; rew_heap~.
Qed.  
  (* todo: use only one lemma? *)

(** Extraction of existentials from [local] *)

Lemma local_extract_exists : forall B (F:~~B) A (J:A->hprop) Q,
  is_local F ->
  (forall x, F (J x) Q) -> 
  F (heap_is_pack J) Q.
Proof.
  introv L M. rewrite L. introv (x&Hx).
  exists (J x) [] Q []. splits~. rew_heap~.
Qed. 

(** Extraction of existentials below a star from [local] *)

Lemma local_intro_exists : forall B (F:~~B) H A (J:A->hprop) Q,
  is_local F -> 
  (forall x, F ((J x) \* H) Q) ->
   F (heap_is_pack J \* H) Q.
Proof.
  introv L M. rewrite L. introv (h1&h2&(X&HX)&PH2&?&?).
  exists (J X \* H) [] Q []. splits.
  rew_heap~. exists~ h1 h2.
  auto.
  auto.
Qed. 

(** Extraction of heap representation from [local] *)

Lemma local_name_heap : forall B (F:~~B) (H:hprop) Q,
  is_local F -> 
  (forall h, H h -> F (= h) Q) ->
  F H Q.
Proof.
  introv L M. rewrite L. introv Hh. exists (= h) [] Q []. splits~.
  exists h heap_empty. splits~.
Qed.

(** Weakening under a [local] modifier *)

Lemma local_weaken_body : forall (B:Type) (F F':~~B),
  (forall H Q, F H Q -> F' H Q) -> 
  local F ===> local F'.
Proof.
  introv M. intros H Q N. introv Hh.
  destruct (N _ Hh) as (H1&H2&Q1&H'&P1&P2&P3). exists___*.
Qed.


(********************************************************************)
(* ** Extraction tactic for local goals *)

Ltac xlocal_core tt :=
  first [ assumption | apply local_is_local ].
  (* match goal with |- is_local _ =>  end. *)

Tactic Notation "xlocal" :=
  xlocal_core tt.

Lemma hclean_start : forall B (F:~~B) H Q,
  is_local F -> F ([] \* (H \* [])) Q -> F H Q.
Proof. intros. rew_heap in *. auto. Qed.

Lemma hclean_step : forall B (F:~~B) H1 H2 H3 Q,
  F ((H1 \* H2) \* H3) Q -> F (H1 \* (H2 \* H3)) Q.
Proof. intros. rew_heap in *. auto. Qed.

Lemma hclean_prop : forall B (F:~~B) H1 H2 (P:Prop) Q,
  is_local F -> (P -> F (H1 \* H2) Q) -> F (H1 \* [P] \* H2) Q.
Proof.
  intros. rewrite star_comm_assoc. apply~ local_intro_prop'. 
Qed. 

Lemma hclean_id : forall A (x X : A) B (F:~~B) H1 H2 Q,
  is_local F -> (x = X -> F (H1 \* H2) Q) -> F (H1 \* x ~> Id X \* H2) Q.
Proof. intros. unfold Id. apply~ hclean_prop. Qed.

Lemma hclean_exists : forall B (F:~~B) H1 H2 A (J:A->hprop) Q,
  is_local F -> 
  (forall x, F (H1 \* (J x) \* H2) Q) ->
   F (H1 \* (heap_is_pack J \* H2)) Q.
Proof. 
  intros. rewrite star_comm_assoc. apply~ local_intro_exists.
  intros. rewrite~ star_comm_assoc.
Qed. 

Ltac hclean_onH cont :=
  match goal with
  | |- _ ?H ?Q => cont H
  | |- _ _ ?H ?Q => cont H
  | |- _ _ _ ?H ?Q => cont H
  | |- _ _ _ _ ?H ?Q => cont H
  | |- _ _ _ _ _ ?H ?Q => cont H
  | |- _ _ _ _ _ _ ?H ?Q => cont H
  end.

Ltac hclean_onQ cont :=
  match goal with
  | |- _ ?H ?Q => cont Q
  | |- _ _ ?H ?Q => cont Q
  | |- _ _ _ ?H ?Q => cont Q
  | |- _ _ _ _ ?H ?Q => cont Q
  | |- _ _ _ _ _ ?H ?Q => cont Q
  | |- _ _ _ _ _ _ ?H ?Q => cont Q
  end.

Ltac hclean_protect tt :=
  let Q' := fresh "TEMP" in
  hclean_onQ ltac:(fun Q => set (Q' := Q : ltac_tag_subst _));
  do 5 try (hclean_onH ltac:(fun H => protect_evars_in H); instantiate).

Ltac hclean_setup tt :=
  hclean_protect tt;
  apply hclean_start; [ try xlocal | ];
  autorewrite with hsimpl_assoc.

Ltac hclean_relinearize tt :=
  let go Hpre := match Hpre with ?H \* (_ \* _) =>
    let T := fresh "TEMP" in 
    sets T: H; 
    autorewrite with hsimpl_assoc; 
    subst T
    end in
  hclean_onH ltac:(go).
 
Ltac hclean_step tt :=
  let go H :=
    match H with ?HA \* ?HX \* ?HR => match HX with
    | [?P] => apply hclean_prop; [ try xlocal | intro ]
    | ?x ~> Id ?X => apply hclean_id; [ try xlocal | intro ]
    | heap_is_pack ?J => apply hclean_exists; [ try xlocal | intro; hclean_relinearize tt ]
    | _ => apply hclean_step
    end end in
  hclean_onH ltac:(go).

Ltac hclean_cleanup tt :=
  autorewrite with hsimpl_neutral;
  unprotect_evars tt.

Ltac hclean_main tt :=
  hclean_setup tt;
  pose ltac_mark; 
  (repeat (hclean_step tt));
  hclean_cleanup tt;
  gen_until_mark.

Tactic Notation "hclean" := hclean_main tt.
Tactic Notation "hclean" "~" := hclean; auto_tilde.
Tactic Notation "hclean" "*" := hclean; auto_star.

Lemma hclean_demo_1 : forall A (x X:A) H1 H2 H3 B (F:~~B) P Q,  
   is_local F ->
   F (H1 \* [] \* H2 \* [P] \* x ~> Id X \* H3) Q.
Proof.
  intros. dup.
  (* details *)
  hclean_setup tt.
  pose ltac_mark.
  hclean_step tt.
  hclean_step tt.
  hclean_step tt.
  hclean_step tt.
  hclean_step tt.
  hclean_step tt.
  try hclean_step tt.
  autorewrite with hsimpl_neutral.
  unprotect_evars tt.
  gen_until_mark.
  skip.
  (* short *)
  hclean.
  skip.
Qed.  


