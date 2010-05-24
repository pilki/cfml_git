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
(* ** Representation of heaps *)

(** Representation of locations *)

Definition loc : Type := nat.

(** Representation of heaps *)

Definition heap := option (map loc dynamic).

(*------------------------------------------------------------------*)
(* ** Construction of heaps *)

(** Empty heap *)

Definition heap_empty : heap := 
  Some empty.

(** Singleton heap *)

Definition heap_single (l:loc) A (v:A) : heap := 
  Some (single_bind l (dyn v)).

(** Heap union *)

Definition heap_union (h1 h2 : heap) : heap := 
  match h1,h2 with
  | Some m1, Some m2 => 
      If disjoint (dom m1) (dom m2)
         then Some (m1 \u m2)
         else None
  | _,_ => None
  end.


(********************************************************************)
(* ** Predicate on Heaps *)

(*------------------------------------------------------------------*)
(* ** Definition of heap predicates *)

(** [hprop] is the type of predicates on heaps *)

Definition hprop := heap -> Prop.

(** Empty heap *)

Definition heap_is_empty : hprop := 
  = heap_empty.

(** Singleton heap *)

Definition heap_is_single (l:loc) A (P:A->Prop) : hprop := 
  fun h => exists v, h = heap_single l v /\ P v.

(** Heap union *)

Definition heap_is_star (H1 H2 : hprop) : hprop := 
  fun h => exists h1 h2, h = heap_union h1 h2 /\ h <> None /\ H1 h1 /\ H2 h2.

(** Pack in heaps *)

Definition heap_is_pack A (Hof : A -> hprop) : hprop := 
  fun h => exists x, Hof x h.

(** Lifting of predicates *)

Definition heap_is_empty_st (H:Prop) : hprop :=
  fun h => h = heap_empty /\ H.

(** Star with post-conditions (predicates of type [B->hprop]) *)

Definition starpost B (Q:B->hprop) (H:hprop) : B->hprop :=
  fun x => heap_is_star (Q x) H.

(*------------------------------------------------------------------*)
(* ** Notation for heap predicates *)

Notation "[]" := (heap_is_empty) 
  (at level 0) : heap_scope.

Notation "[ L ]" := (heap_is_empty_st L) 
  (at level 0, L at level 99) : heap_scope.

Notation "\[ P ]" := (fun v => heap_is_empty_st (P v)) 
  (at level 0, P at level 99) : heap_scope.

Notation "H1 '\*' H2" := (heap_is_star H1 H2)
  (at level 40, left associativity) : heap_scope.
Notation "H1 '*' H2" := (heap_is_star H1 H2)
  (at level 40, left associativity, only parsing) : heap_scope.

Notation "l '~>|' P" := (heap_is_single l P)
  (at level 35, no associativity) : heap_scope.

Notation "l '~>' v" := (heap_is_single l (=v))
  (at level 35, no associativity) : heap_scope.

Notation "'Hexists' x , H" := (heap_is_pack (fun x => H))
  (at level 35, x ident, H at level 200) : heap_scope.

Notation "Q \*+ H" := (starpost Q H) (at level 40).

Open Scope heap_scope.
Bind Scope heap_scope with hprop.
Delimit Scope heap_scope with h.


(*------------------------------------------------------------------*)
(* ** Properties of [star] *)

Lemma star_neutral_l : neutral_l heap_is_star [].
Proof. skip. Qed.

Lemma star_neutral_r : neutral_r heap_is_star [].
Proof. skip. Qed.

Lemma star_comm : comm heap_is_star. 
Proof. skip. Qed.

Lemma star_assoc : LibOperation.assoc heap_is_star. 
Proof. skip. Qed.

Lemma starpost_neutral : forall B (Q:B->hprop),
  Q \*+ [] = Q.
Proof. extens. intros. unfold starpost. rewrite~ star_neutral_r. Qed.


(*------------------------------------------------------------------*)
(* ** Normalization of [star] *)

Hint Rewrite 
  star_neutral_l star_neutral_r star_assoc
  starpost_neutral : rew_heap.

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




(* todo: move *)

Lemma rel_le_refl : forall A B (P:A->B->Prop),
  rel_le P P.
Proof. intros_all~. Qed.
Hint Resolve rel_le_refl.

Lemma heap_weaken_star : forall H1' H1 H2 H3,
  (H1 ==> H1') -> (H1' * H2 ==> H3) -> (H1 * H2 ==> H3).
Proof.
  introv W M (h1&h2&N). intuit N. apply M. exists~ h1 h2.
Qed.


(********************************************************************)
(* ** Locality *)

(*------------------------------------------------------------------*)
(* ** Definition of [local] *)

(** Type of post-conditions on values of type B *)

Notation "'~~' B" := (hprop->(B->hprop)->Prop) 
  (at level 8, only parsing) : type_scope.

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
  destruct PH12 as (h1&h2&Ph12&Fh12&PH1&PH2).
  destruct (N _ PH1) as (H1'&H2'&Q1'&H''&PH12'&N'&Qle').
  exists H1' (H2' \* H2) Q1' (H' \* H''). splits.
   rewrite star_assoc.
   exists~ h1 h2.
   auto.
   intros x. specializes Qle x. specializes Qle' x. unfolds starpost.
    rewrite star_assoc. applys heap_weaken_star Qle'.
    rewrite (star_assoc (Q x)). 
    skip_cuts (Q1 x \* H2 ==> Q x \* H'). auto.
  apply~ local_erase.
Qed.

(** A definition whose head is [local] satisfies [is_local] *)

Lemma local_is_local : forall B (F:~~B),
  is_local (local F).
Proof. intros. unfolds. rewrite~ local_local. Qed.

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
    (* todo: use only one lemma *)

(** Garbage collection from [local] *)

Lemma local_gc : forall B H' Q' (F:~~B) H Q,
  is_local F -> 
  F H Q' ->
  Q' ===> Q \*+ H' ->
  F H Q.
Proof.
  introv L M W. rewrite L. introv Ph.
  exists H [] Q' H'. splits; rew_heap~.
Qed.

(** Extraction of premisses from [local] *)

Lemma local_intro_prop : forall B (F:~~B) H (P:Prop) Q,
  is_local F -> (P -> F H Q) -> F ([P] * H) Q.
Proof.
  introv L M. rewrite L. introv (h1&h2&?&?&(PH1&HP)&PH2).
  skip: (h = h2). (* todo heaps *) subst h2.
  exists H [] Q []. splits; rew_heap~.
Qed. 

(** Extraction of existential from [local] *)

Lemma local_intro_exists : forall B (F:~~B) H A (J:A->hprop) Q,
  is_local F -> 
  (forall x, F ((J x) * H) Q) ->
   F (heap_is_pack J * H) Q.
Proof.
  introv L M. rewrite L. introv (h1&h2&?&?&(X&HX)&PH2).
  exists (J X * H) [] Q []. splits.
  rew_heap~. exists~ h1 h2.
  auto.
  auto.
Qed. 





