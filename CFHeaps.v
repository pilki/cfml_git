Set Implicit Arguments.
Require Export LibCore LibEpsilon Shared LibMap.


(********************************************************************)
(* ** Heaps *)

(*------------------------------------------------------------------*)
(* ** Representation of heaps *)

(** Representation of locations *)

Definition loc : Type := nat.

(** Representation of heap items *)

Record dyn := { 
  dyn_type : Type; 
  dyn_value : dyn_type }.

(** Representation of heaps *)

Definition heap := option (map loc dyn).

(*------------------------------------------------------------------*)
(* ** Construction of heaps *)

(** Empty heap *)

Definition heap_empty : heap := 
  Some empty.

(** Singleton heap *)

Definition heap_single (l:loc) A (v:A) : heap := 
  Some (single_bind l (Build_dyn v)).

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

Notation "H1 '**' H2" := (heap_is_star H1 H2)
  (at level 40, left associativity) : heap_scope.
Notation "H1 '*' H2" := (heap_is_star H1 H2)
  (at level 40, left associativity, only parsing) : heap_scope.

Notation "l '~>|' P" := (heap_is_single l P)
  (at level 35, no associativity) : heap_scope.

Notation "l '~>' v" := (heap_is_single l (=v))
  (at level 35, no associativity) : heap_scope.

Notation "'Hexists' x , H" := (heap_is_pack (fun x => H))
  (at level 35, x ident, H at level 200) : heap_scope.

Notation "Q *** H" := (starpost Q H) (at level 40).

Open Scope heap_scope.


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
  Q *** [] = Q.
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
    exists H1 H2 Q1 H',
       H ==> H1 * H2
    /\ (forall h, H1 h -> exists H1', H1' h /\ F H1' Q1)
    /\ forall x, (Q1 x) * H2 ==> (Q x) * H'.

(** Characterization of "local" judgments *)

Definition is_local B (F:~~B) :=
  F = local F.

(** The weakening property is implied by locality *)

Definition weakenable B (F:~~B) :=
  forall H Q , F H Q ->
  forall H' Q', H' ==> H -> Q ===> Q' -> F H' Q'.


Lemma local_intro_exists : forall B (F:~~B) H1 H2 A (J:A->hprop) Q,
  is_local F -> (forall x, F (H1 * (J x) * H2) Q) ->
   F (H1 * heap_is_pack J * H2) Q.
Proof.
  introv L M. rewrite L.
  exists (H1 * heap_is_pack J * H2) [] Q []. splits.
  skip. (* heaps *)
  intros. intuit H. intuit H3. intuit H7.
  specializes M x3. subst x h. esplit. split; [| apply M].
  exists __ __. splits. eauto. eauto. 
  exists __ __. splits. eauto. eauto. eauto. eauto. eauto.  
  auto.
Qed. 


(*------------------------------------------------------------------*)
(* ** Properties of [local] *)

(** The [local] operator can be freely erased from a conclusion *)

Lemma local_erase : forall B (F:~~B), 
  forall H Q, F H Q -> local F H Q.
Proof.
  intros. exists H [] Q []. splits.
  rew_heap~. auto.
intros. exists H. split~.
auto.
Qed.


(** Nested applications [local] are redundant *)

Lemma local_local : forall B (F:~~B),
  local (local F) = local F.
Proof.
  extens. intros H Q. iff M. 
  destruct M as (H1&H2&Q1&H'&?&N&?).
  destruct N as (H1'&H2'&Q1'&H''&?&?&?).
  exists H1' (H2 ** H2') Q1' (H' ** H''). splits.
  eapply pred_le_trans. eauto.
   intros h Hh. hnf in Hh. destruct Hh as (h1&h2&?&?&?&?).
   subst h. applys_to H9 H4. intuit H9. subst h1.
   rewrite (star_comm H2). rewrite star_assoc.
   exists __ __. splits~. exists __ __. splits~.
  eauto.
  intros.
  skip. (* todo *)
  apply~ local_erase.
Qed.

(** A definition whose head is [local] satisfies [is_local] *)

Lemma local_is_local : forall B (F:~~B),
  is_local (local F).
Proof. intros. unfolds. rewrite~ local_local. Qed.
*)

(** Elimination lemma associated with the definition of [local] *)

Lemma local_elim : forall B (F:~~B) H H1 H2 H' Q1 Q,
  is_local F -> 
  F H1 Q1 -> 
  H ==> H1 ** H2 -> 
  Q1 *** H2 ===> Q *** H' ->
  F H Q.
Proof.
  introv L M WH WQ. rewrite L. exists H1 H2 Q1 H'. splits.
  auto. auto. intros. rew_heap~. apply WQ.
Qed.

(** Corrolary for the case where no garbage collection is required *)

Lemma local_frame : forall B (F:~~B) H H1 H2 Q1 Q,
  is_local F -> 
  F H1 Q1 -> 
  H ==> H1 ** H2 -> 
  Q1 *** H2 ===> Q ->
  F H Q.
Proof.
  intros. eapply local_elim with (H' := []); eauto. rew_heap~.
Qed.

(** Corrolary for the case where no frame is required *)

Lemma local_weaken : forall B (F:~~B) H H' Q Q',
  is_local F -> 
  F H' Q' -> 
  H ==> H' -> 
  Q' ===> Q ->
  F H Q.
Proof.
  intros. eapply local_frame with (H2 := []); eauto; rew_heap~.
Qed.

Lemma local_weaken' : forall B (F:~~B),
  is_local F -> weakenable F.
Proof. intros_all. apply* local_weaken. Qed.
  (* todo: use only one lemma *)


Definition local' B (F:~~B) : ~~B :=
  fun (H:hprop) (Q:B->hprop) =>
    exists H1 H2 P Q1 H',
       H ==> H1 * H2 * [P]
    /\ (P -> F H1 Q1)
    /\ forall x, (Q1 x) * H2 ==> (Q x) * H'.

Lemma local_intro_prop : forall B (F:~~B) H1 H2 (P:Prop) Q,
  is_local F -> (P -> F (H1 * H2) Q) -> F (H1 * [P] * H2) Q.
Proof.
  introv L M. rewrite L.
  skip_rewrite (local = local').
  exists (H1 * H2) [] P Q []. splits.
  skip. (* heaps *)
  auto.
  auto.
Qed. 

Lemma local_intro_exists : forall B (F:~~B) H1 H2 A (J:A->hprop) Q,
  is_local F -> (forall x, F (H1 * (J x) * H2) Q) ->
   F (H1 * heap_is_pack J * H2) Q.
Proof.
  introv L M. rewrite L.
  skip_rewrite (local = local').
  exists (H1 * H2) [] True Q []. splits.
  skip. (* heaps *)
  auto.
  auto.
Qed. 



f
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
    exists H1 H2 Q1 H',
       H ==> H1 * H2
    /\ F H1 Q1
    /\ forall x, (Q1 x) * H2 ==> (Q x) * H'.

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
  destruct M as (H1&H2&Q1&H'&?&N&?).
  destruct N as (H1'&H2'&Q1'&H''&?&?&?).
  exists H1' (H2 ** H2') Q1' (H' ** H''). splits.
  eapply pred_le_trans. eauto.
   intros h Hh. hnf in Hh. destruct Hh as (h1&h2&?&?&?&?).
   subst h. applys_to H9 H4. intuit H9. subst h1.
   rewrite (star_comm H2). rewrite star_assoc.
   exists __ __. splits~. exists __ __. splits~.
  eauto.
  intros.
  skip. (* todo *)
  apply~ local_erase.
Qed.

(** A definition whose head is [local] satisfies [is_local] *)

Lemma local_is_local : forall B (F:~~B),
  is_local (local F).
Proof. intros. unfolds. rewrite~ local_local. Qed.

(** Elimination lemma associated with the definition of [local] *)

Lemma local_elim : forall B (F:~~B) H H1 H2 H' Q1 Q,
  is_local F -> 
  F H1 Q1 -> 
  H ==> H1 ** H2 -> 
  Q1 *** H2 ===> Q *** H' ->
  F H Q.
Proof.
  introv L M WH WQ. rewrite L. exists H1 H2 Q1 H'. splits.
  auto. auto. intros. rew_heap~. apply WQ.
Qed.

(** Corrolary for the case where no garbage collection is required *)

Lemma local_frame : forall B (F:~~B) H H1 H2 Q1 Q,
  is_local F -> 
  F H1 Q1 -> 
  H ==> H1 ** H2 -> 
  Q1 *** H2 ===> Q ->
  F H Q.
Proof.
  intros. eapply local_elim with (H' := []); eauto. rew_heap~.
Qed.

(** Corrolary for the case where no frame is required *)

Lemma local_weaken : forall B (F:~~B) H H' Q Q',
  is_local F -> 
  F H' Q' -> 
  H ==> H' -> 
  Q' ===> Q ->
  F H Q.
Proof.
  intros. eapply local_frame with (H2 := []); eauto; rew_heap~.
Qed.

Lemma local_weaken' : forall B (F:~~B),
  is_local F -> weakenable F.
Proof. intros_all. apply* local_weaken. Qed.
  (* todo: use only one lemma *)


Definition local' B (F:~~B) : ~~B :=
  fun (H:hprop) (Q:B->hprop) =>
    exists H1 H2 P Q1 H',
       H ==> H1 * H2 * [P]
    /\ (P -> F H1 Q1)
    /\ forall x, (Q1 x) * H2 ==> (Q x) * H'.

Lemma local_intro_prop : forall B (F:~~B) H1 H2 (P:Prop) Q,
  is_local F -> (P -> F (H1 * H2) Q) -> F (H1 * [P] * H2) Q.
Proof.
  introv L M. rewrite L.
  skip_rewrite (local = local').
  exists (H1 * H2) [] P Q []. splits.
  skip. (* heaps *)
  auto.
  auto.
Qed. 

Lemma local_intro_exists : forall B (F:~~B) H1 H2 A (J:A->hprop) Q,
  is_local F -> (forall x, F (H1 * (J x) * H2) Q) ->
   F (H1 * heap_is_pack J * H2) Q.
Proof.
  introv L M. rewrite L.
  skip_rewrite (local = local').
  exists (H1 * H2) [] True Q []. splits.
  skip. (* heaps *)
  auto.
  auto.
Qed. 





