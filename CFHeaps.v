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

Definition heaps_union (hs : list heap) : heap :=
  LibList.fold_right heap_union heap_empty hs.

(** Heap well-defineteness *)

Definition heap_defined (h : heap) : Prop :=
  h <> None.
 
(** Heap disjointness *)

Definition heaps_disjoint (hs : list heap) : Prop :=
  heap_defined (heaps_union hs).

Notation "\# h1 h2" := (heaps_disjoint (h2::h1::nil))
  (at level 40, h1 at level 0, h2 at level 0, no associativity).
Notation "\# h1 h2 h3" := (heaps_disjoint (h3::h2::h1::nil))
  (at level 40, h1 at level 0, h2 at level 0, h3 at level 0, no associativity).

(*
Lemma test : forall h1 h2 h3, (\# h1 h2) = (\# h1 h2) /\ (\# h1 h2 h3) = (\# h1 h2 h3).
*)


(*------------------------------------------------------------------*)
(* ** Properties of operations on heaps *)

Lemma heap_union_neutral_l : 
  neutral_l heap_union heap_empty.
Proof. skip. Qed.

Lemma heap_union_neutral_r : 
  neutral_r heap_union heap_empty.
Proof. skip. Qed.

Lemma heap_union_comm : comm heap_union.
Proof. skip. Qed.

Lemma heap_disjoint_comm : forall h1 h2,
  \# h1 h2 = \# h2 h1.
Proof. skip. Qed.
  (*
  intros [|] [|]; unfold heap_disjoint, heap_defined; simpl; introv H.
  skip_rewrite (disjoint (dom_impl m0) (dom_impl m) = disjoint (dom_impl m) (dom_impl m0)).
  case_if. 
    skip_rewrite (m0 \u m = m \u m0). auto.
    false.
  auto.
  auto.
  auto.
  *)

Lemma heap_disjoint_empty_r : forall h,
  \# h heap_empty.
Proof. skip. Qed.

Lemma heap_disjoint_empty_l : forall h,
  \# heap_empty h.
Proof. intros. rewrite heap_disjoint_comm. apply heap_disjoint_empty_r. Qed.

Lemma heap_disjoint_union_inv : forall h1 h2 h3,
  \# h1 (heap_union h2 h3) = (\# h1 h2 /\ \# h1 h3).
Proof. skip. Qed.





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

Definition heap_is_single (l:loc) A (v:A) : hprop := 
  = heap_single l v.

(** Heap union *)

Definition heap_is_star (H1 H2 : hprop) : hprop := 
  fun h => exists h1 h2, \# h1 h2 /\ h = heap_union h1 h2 /\ H1 h1 /\ H2 h2.

(** Pack in heaps *)

Definition heap_is_pack A (Hof : A -> hprop) : hprop := 
  fun h => exists x, Hof x h.

(** Lifting of predicates *)

Definition heap_is_empty_st (H:Prop) : hprop :=
  fun h => h = heap_empty /\ H.

(** Star with post-conditions (predicates of type [B->hprop]) 

Definition starpost B (Q:B->hprop) (H:hprop) : B->hprop :=
  fun x => heap_is_star (Q x) H.
*)


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

(*bin
Notation "\= V" := (\[ = V])
  (at level 40) : heap_scope.
*)

Notation "\= V" := (fun X => [X = V])
  (at level 40) : heap_scope.

Notation "H1 '\*' H2" := (heap_is_star H1 H2)
  (at level 41, right associativity) : heap_scope.

Notation "l '~~>' v" := (heap_is_single l v)
  (at level 35, no associativity) : heap_scope.

Notation "'Hexists' x , H" := (heap_is_pack (fun x => H))
  (at level 39, x ident, H at level 50) : heap_scope.

Notation "'Hexists' x : T , H" := (heap_is_pack (fun x:T => H))
  (at level 39, x ident, H at level 50) : heap_scope.

Notation "Q \*+ H" :=
  (fun x => heap_is_star (Q x) H)
  (* (starpost Q H)  *)
  (at level 40) : heap_scope.

Notation "# H" := (fun _:unit => H)
  (at level 39, H at level 99) : heap_scope.


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

Lemma star_comm_assoc : comm_assoc heap_is_star.
Proof. skip. Qed.

Lemma starpost_neutral : forall B (Q:B->hprop),
  Q \*+ [] = Q.
Proof. extens. intros. (* unfold starpost. *) rewrite~ star_neutral_r. Qed.

Lemma star_cancel : forall H1 H2 H2',
  H2 ==> H2' -> H1 \* H2 ==> H1 \* H2'.
Proof. introv W (h1&h2&?). exists* h1 h2. Qed.

Lemma heap_star_prop_elim : forall (P:Prop) H h,
  ([P] \* H) h -> P /\ H h.
Proof.
  introv (?&?&?&?&N&?). destruct N. subst. rewrite~ heap_union_neutral_l.
Qed.

Lemma heap_extract_prop : forall (P:Prop) H H',
  (P -> H ==> H') -> ([P] \* H) ==> H'.
Proof. introv W Hh. applys_to Hh heap_star_prop_elim. auto*. Qed.

Lemma heap_weaken_pack : forall A (x:A) H J,
  H ==> J x -> H ==> (heap_is_pack J).
Proof. introv W h. exists x. apply~ W. Qed.


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

(** Label for data structures *)

Definition hdata (S:loc->hprop) (l:loc) : hprop :=
  S l.

Notation "'~>' S" := (hdata S)
  (at level 32, no associativity) : heap_scope.

Notation "l '~>' S" := (hdata S l)
  (at level 33, no associativity) : heap_scope.

(** Specification of pure functions: 
    [pure F P] is equivalent to [F [] \[P]] *)

Definition pure B (R:~~B) := 
  fun P => R [] \[P].

(** Representation predicate for pure data types *)

Class Rep a A := 
  { rep : a -> A -> Prop;
    rep_unique : forall x X Y, rep x X -> rep x Y -> X = Y }.

(** Heap representation for pure data types *)

Definition Pure `{Rep a A} (X:A) (x:a) := 
  [ rep x X ].

(** Specification of pure functions: 
    [pure F P] is equivalent to [F [] \[P]] *)

Definition read B (R:~~B) := 
  fun H Q => R H (Q \*+ H).


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
       | _ ~> _ => fail 1
       | X => fail 1 
       | _ => let K := fresh "TEMP" in sets_eq K: (X : ltac_tag_subst hprop)
       end in
     match type of X with 
     | hprop => go tt
     | heap -> Prop => go tt
     end
   end.

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
  destruct Hh as (h1&h2'&?&?&?&(h2&h3&?&?&(?&M)&?)).
  apply~ W. exists h1 h3. subst h h2 h2'.
  skip_rewrite (heap_union heap_empty h3 = h3) in H. (* todo*) 
  skip_rewrite (heap_union heap_empty h3 = h3). (* todo*) 
  splits~.
Qed.

Lemma hextract_exists : forall A H1 H2 H' (J:A->hprop),
  (forall x, H1 \* J x \* H2 ==> H') -> H1 \* (heap_is_pack J \* H2) ==> H'.
Proof.
  skip. (* todo *)
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

Tactic Notation "hextract" := hextract_core; intros.
Tactic Notation "hextract" "as" := hextract_core.

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
  skip. skip. (* heap *)
  splits~.
Qed.

Lemma hsimpl_extract_exists : forall A (x:A) H1 H2 H3 (J:A->hprop),
  H1 ==> H2 \* J x \* H3 -> H1 ==> H2 \* (heap_is_pack J \* H3).
Proof.
  skip. (* todo *)
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
Admitted.

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


(*
Ltac hsimpl_assoc_rhs tt :=
  let M := fresh "TEMP" in
  match goal with |- ?H ==> ?H' =>
    sets M: H'; autorewrite with hsimpl_assoc; subst M
  end.
hsimpl_assoc_rhs tt.*)

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

(*--deprecated
Ltac hsimpl_find_data H HL :=
  match H with hdata _ ?l =>
  match HL with
  | hdata _ l \* _ => apply hsimpl_cancel_1
  | _ \* hdata _ l \* _ => apply hsimpl_cancel_2
  | _ \* _ \* hdata _ l \* _ => apply hsimpl_cancel_3
  | _ \* _ \* _ \* hdata _ l \* _ => apply hsimpl_cancel_4
  | _ \* _ \* _ \* _ \* hdata _ l \* _ => apply hsimpl_cancel_5
  | _ \* _ \* _ \* _ \* _ \* hdata _ l \* _ => apply hsimpl_cancel_6
  end end.
*)

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
          | hsimpl_find_data H HL  
          | apply hsimpl_extract_prop
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


Lemma hsimpl_demo_2 : forall l1 l2 S1 S2 H1 H2 H3 H',
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

Lemma hsimpl_demo_3 : forall l1 l2 S1 S2 H1 H2 H',
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
  H2 \* J m \* H3 \* H4 ==> H4 \* (Hexists y, [y = 2]) \* (Hexists x, [n = x + x] \* J x \* H2) \* H3.
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


(* todo: move *)

Lemma rel_le_refl : forall A B (P:A->B->Prop),
  rel_le P P.
Proof. intros_all~. Qed.
Hint Resolve rel_le_refl.

Lemma heap_weaken_star : forall H1' H1 H2 H3,
  (H1 ==> H1') -> (H1' \* H2 ==> H3) -> (H1 \* H2 ==> H3).
Proof.
  introv W M (h1&h2&N). intuit N. apply M. exists~ h1 h2.
Qed.


(* todo *)
Lemma hsimpl_to_qunit : forall (H:hprop) (Q:unit->hprop),
  Q = (fun _ => H) ->
  H ==> Q tt.
Proof. intros. subst. auto. Qed.
Hint Resolve hsimpl_to_qunit.


(*------------------------------------------------------------------*)
(* ** Tactic [hchange] *)

Lemma hchange_lemma : forall H1 H1' H H' H2,
  (H1 ==> H1') -> (H ==> H1 \* H2) -> (H1' \* H2 ==> H') -> (H ==> H').
Proof.
  intros. applys* (@pred_le_trans heap) (H1 \* H2). 
  applys* (@pred_le_trans heap) (H1' \* H2). hsimpl~. 
Qed.

Ltac hchange_core H :=
  first [ apply (@hchange_lemma H)
        | applys hchange_lemma H ]; 
  hsimpl.

Tactic Notation "hchange" constr(H) :=
  hchange_core H.
Tactic Notation "hchange" "~" constr(H) :=
  hchange_core H; auto_tilde.
Tactic Notation "hchange" "*" constr(H) :=
  hchange_core H; auto_star.


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
  destruct PH12 as (h1&h2&Ph12&Fh12&PH1&PH2).
  destruct (N _ PH1) as (H1'&H2'&Q1'&H''&PH12'&N'&Qle').
  exists H1' (H2' \* H2) Q1' (H' \* H''). splits.
   rewrite star_assoc.
   exists~ h1 h2.
   auto.
   intros x. specializes Qle x. specializes Qle' x. (* unfolds starpost.*)
    rewrite star_assoc. applys heap_weaken_star Qle'.
    rewrite (star_assoc (Q x)). 
    skip_cuts (Q1 x \* H2 ==> Q x \* H'). auto.
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
    (* todo: use only one lemma *)

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

Lemma local_intro_prop : forall B (F:~~B) H (P:Prop) Q,
  is_local F -> (P -> F H Q) -> F ([P] \* H) Q.
Proof.
  introv L M. rewrite L. introv (h1&h2&?&?&(PH1&HP)&PH2).
  skip: (h = h2). (* todo heaps *) subst h2.
  exists H [] Q []. splits; rew_heap~.
Qed. 

(** Extraction of existential from [local] *)

Lemma local_intro_exists : forall B (F:~~B) H A (J:A->hprop) Q,
  is_local F -> 
  (forall x, F ((J x) \* H) Q) ->
   F (heap_is_pack J \* H) Q.
Proof.
  introv L M. rewrite L. introv (h1&h2&?&?&(X&HX)&PH2).
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
  introv L M. rewrite L. introv Hh. exists (= h) [] Q []. splits.
  exists h heap_empty. skip.
  apply~ M.
  auto.
Qed.


(********************************************************************)
(* ** Extraction tactic for local goals *)

Ltac xlocal_core tt :=
  match goal with |- is_local _ => skip end.

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
  intros. rewrite star_comm_assoc. apply~ local_intro_prop. 
Qed. 

Lemma hclean_exists : forall B (F:~~B) H1 H2 A (J:A->hprop) Q,
  is_local F -> 
  (forall x, F (H1 \* (J x) \* H2) Q) ->
   F (H1 \* (heap_is_pack J \* H2)) Q.
Proof. 
  intros. rewrite star_comm_assoc. apply~ local_intro_exists.
  intros. rewrite~ star_comm_assoc.
Qed. 

(*
Ltac hclean_on contH contQ :=
  match goal with
  | |- _ ?H ?Q => contH H; contQ Q
  | |- _ _ ?H ?Q => contH H; contQ Q
  | |- _ _ _ ?H ?Q => contH H; contQ Q
  | |- _ _ _ _ ?H ?Q => contH H; contQ Q
  end.
*)

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
  apply hclean_start; [ xlocal | ];
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
    | [?P] => apply hclean_prop; [ xlocal | intro ]
    | heap_is_pack ?J => apply hclean_exists; [ xlocal | intro; hclean_relinearize tt ]
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

Lemma hclean_demo_1 : forall H1 H2 H3 B (F:~~B) P Q,
   F (H1 \* [] \* H2 \* [P] \* H3) Q.
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
  autorewrite with hsimpl_neutral.
  unprotect_evars tt.
  gen_until_mark.
  skip.
  (* short *)
  hclean.
  skip.
Qed.  

