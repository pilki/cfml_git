Set Implicit Arguments.
Require Import LibCore Shared CFHeaps.


(********************************************************************)
(* ** Shared tactics *)

Ltac prepare_goal_hextract_himpl tt :=
  match goal with 
  | |- @rel_le unit _ _ _ => let t := fresh "_tt" in intros t; destruct t
  | |- @rel_le _ _ _ _ => let r := fresh "r" in intros r
  | |- pred_le _ _ => idtac
  end.

Ltac remove_empty_heaps_from H :=
  match H with context[ ?H1 \* [] ] =>
    rewrite (@star_neutral_r H1) end.
  
Ltac remove_empty_heaps_left tt :=
  repeat match goal with |- ?H1 ==> _ => remove_empty_heaps_from H1 end.

Ltac remove_empty_heaps_right tt :=
  repeat match goal with |- _ ==> ?H2 => remove_empty_heaps_from H2 end.

Ltac on_formula_pre cont :=
  match goal with
  | |- _ ?H ?Q => cont H
  | |- _ _ ?H ?Q => cont H
  | |- _ _ _ ?H ?Q => cont H
  | |- _ _ _ _ ?H ?Q => cont H
  | |- _ _ _ _ _ ?H ?Q => cont H
  | |- _ _ _ _ _ _ ?H ?Q => cont H
  end.

Ltac on_formula_post cont :=
  match goal with
  | |- _ ?H ?Q => cont Q
  | |- _ _ ?H ?Q => cont Q
  | |- _ _ _ ?H ?Q => cont Q
  | |- _ _ _ _ ?H ?Q => cont Q
  | |- _ _ _ _ _ ?H ?Q => cont Q
  | |- _ _ _ _ _ _ ?H ?Q => cont Q
  end.

Ltac remove_empty_heaps_formula tt :=
  repeat (on_formula_pre ltac:(remove_empty_heaps_from)).


(********************************************************************)
(* ** Extraction from [H1] in [H1 ==> H2] *)

(** Lemmas *)

Lemma hextract_start : forall H H',
  [] \* H ==> H' -> H ==> H'.
Proof. intros. rew_heap in *. auto. Qed.

Lemma hextract_stop : forall H H',
  H ==> H' -> H \* [] ==> H'.
Proof. intros. rew_heap in *. auto. Qed.

Lemma hextract_keep : forall H1 H2 H3 H',
  (H2 \* H1) \* H3 ==> H' -> H1 \* (H2 \* H3) ==> H'.
Proof. intros. rewrite (star_comm H2) in H. rew_heap in *. auto. Qed.

Lemma hextract_starify : forall H1 H2 H',
  H1 \* (H2 \* []) ==> H' -> H1 \* H2 ==> H'.
Proof. intros. rew_heap in *. auto. Qed.

Lemma hextract_assoc : forall H1 H2 H3 H4 H',
  H1 \* (H2 \* (H3 \* H4)) ==> H' -> H1 \* ((H2 \* H3) \* H4) ==> H'.
Proof. intros. rew_heap in *. auto. Qed.

Lemma hextract_prop : forall H1 H2 H' (P:Prop),
  (P -> H1 \* H2 ==> H') -> H1 \* ([P] \* H2) ==> H'.
Proof.
  introv W. intros h Hh.
  destruct Hh as (h1&h2'&?&(h2&h3&(?&?)&?&?&?)&?&?).
  apply~ W. exists h1 h3. subst h h2 h2'.
  splits~. rewrite~ heap_union_neutral_l.
Qed.

Lemma hextract_empty : forall H1 H2 H',
  (H1 \* H2 ==> H') -> H1 \* ([] \* H2) ==> H'.
Proof.
  introv W. intros h Hh. destruct Hh as (h1&h2'&?&(h2&h3&M&?&?&?)&?&?).
  apply~ W. inverts M. exists h1 h3. subst h h2'.
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

(** Tactics *)

Ltac hextract_setup tt :=
  prepare_goal_hextract_himpl tt;
  lets: ltac_mark;
  apply hextract_start.

Ltac hextract_cleanup tt :=
  apply hextract_stop;
  remove_empty_heaps_left tt;
  gen_until_mark.

Ltac hextract_step tt :=
  match goal with |- _ \* ?HN ==> _ => 
  match HN with 
  | ?H \* _ =>
     match H with
     | [] => apply hextract_empty
     | [_] => apply hextract_prop; intros
     | _ ~> Id _ => apply hextract_id; intros
     | heap_is_pack _ => apply hextract_exists; intros
     | _ \* _ => apply hextract_assoc
     | _ => apply hextract_keep
     end
  | [] => fail 1
  | ?H => apply hextract_starify
  end end.

Ltac hextract_main tt :=
  hextract_setup tt;
  (repeat (hextract_step tt));
  hextract_cleanup tt.

Ltac hextract_core :=
  hextract_main tt.

Ltac hextract_if_needed tt :=
  match goal with |- ?H ==> _ => match H with
  | context [ heap_is_pack _ ] => hextract_core
  | context [ _ ~> Id _ ] => hextract_core
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

(** Demos *)

Lemma hextract_demo_1 : forall n J H2 H3 H4 H',
  H4 \* (Hexists y, [y = 2]) \* 
   (Hexists x, [n = x + x] \* (J x \* x ~> Id 3) \* H2) \* H3 ==> H'.
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
  hextract_step tt.
  try hextract_step tt.
  hextract_cleanup tt.
  intros y Hy.
  skip.
  (* short *)
  hextract. skip.
Admitted.


(********************************************************************)
(* ** Simplification in [H2] on [H1 ==> H2] *)

(** Hints *)

Inductive Hsimpl_hint : list Boxer -> Type :=
  | hsimpl_hint : forall (L:list Boxer), Hsimpl_hint L.

Ltac hsimpl_hint_put L := 
  lets: (hsimpl_hint L).

Ltac hsimpl_hint_next cont :=
  match goal with H: Hsimpl_hint ((boxer ?x)::?L) |- _ =>
    clear H; hsimpl_hint_put L; cont x end.

Ltac hsimpl_hint_remove tt :=
  match goal with H: Hsimpl_hint _ |- _ => clear H end.

Lemma demo_hsimpl_hints : exists n, n = 3.
Proof.
  hsimpl_hint_put (>>> 3 true).
  hsimpl_hint_next ltac:(fun x => exists x).
  hsimpl_hint_remove tt.
Admitted.

(** Lemmas *)

Lemma hsimpl_start : forall H' H1,
  H' ==> [] \* H1 -> H' ==> H1.
Proof. intros. rew_heap in *. auto. Qed.

Lemma hsimpl_stop : forall H' H1,
  H' ==> H1 -> H' ==> H1 \* [].
Proof. intros. rew_heap in *. auto. Qed.

Lemma hsimpl_keep : forall H' H1 H2 H3,
  H' ==> (H2 \* H1) \* H3 -> H' ==> H1 \* (H2 \* H3).
Proof. intros. rewrite (star_comm H2) in H. rew_heap in *. auto. Qed.

Lemma hsimpl_assoc : forall H' H1 H2 H3 H4,
  H' ==> H1 \* (H2 \* (H3 \* H4)) -> H' ==> H1 \* ((H2 \* H3) \* H4).
Proof. intros. rew_heap in *. auto. Qed.

Lemma hsimpl_starify : forall H' H1 H2,
  H' ==> H1 \* (H2 \* []) -> H' ==> H1 \* H2.
Proof. intros. rew_heap in *. auto. Qed.

Lemma hsimpl_empty : forall H' H1 H2,
  H' ==> H1 \* H2 -> H' ==> H1 \* ([] \* H2).
Proof.
  introv W PH1. destruct (W _ PH1) as (h1&h2&?&?&?&?).
  exists h1 h2. splits~. exists heap_empty h2. splits~.
Qed.

Lemma hsimpl_prop : forall H' H1 H2 (P:Prop),
  H' ==> H1 \* H2 -> P -> H' ==> H1 \* ([P] \* H2).
Proof.
  introv W HP PH1. destruct (W _ PH1) as (h1&h2&?&?&?&?).
  exists h1 h2. splits~. exists heap_empty h2. splits~.
Qed.

Lemma hsimpl_id : forall A (x X : A) H' H1 H2,
  H' ==> H1 \* H2 -> x = X -> H' ==> H1 \* (x ~> Id X \* H2).
Proof. intros. unfold Id. apply~ hsimpl_extract_prop. Qed.

Lemma hsimpl_exists : forall A (x:A) H' H1 H2 (J:A->hprop),
  H' ==> H1 \* J x \* H2 -> H' ==> H1 \* (heap_is_pack J \* H2).
Proof.
  introv W. intros h' PH'. destruct (W _ PH') as (h2&h4&?&(hx&h3&?&?&?&?)&?&?).
  exists h2 (heap_union hx h3). subst h' h4. splits~.
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

Lemma hsimpl_start_1 : forall H1 H', 
  H1 \* [] ==> H' -> H1 ==> H'.
Proof. intros. rew_heap in H. auto. Qed.

Lemma hsimpl_start_2 : forall H1 H2 H', 
  H1 \* H2 \* [] ==> H' -> H1 \* H2 ==> H'.
Proof. intros. rew_heap in H. auto. Qed.

Lemma hsimpl_start_3 : forall H1 H2 H3 H', 
  H1 \* H2 \* H3 \* [] ==> H' -> H1 \* H2 \* H3 ==> H'.
Proof. intros. rew_heap in H. auto. Qed.

Lemma hsimpl_start_4 : forall H1 H2 H3 H4 H', 
  H1 \* H2 \* H3 \* H4 \* [] ==> H' -> H1 \* H2 \* H3 \* H4 ==> H'.
Proof. intros. rew_heap in H. auto. Qed.

Lemma hsimpl_start_5 : forall H1 H2 H3 H4 H5 H', 
  H1 \* H2 \* H3 \* H4 \* H5 \* [] ==> H' -> H1 \* H2 \* H3 \* H4 \* H5 ==> H'.
Proof. intros. rew_heap in H. auto. Qed.

Lemma hsimpl_start_6 : forall H1 H2 H3 H4 H5 H6 H', 
  H1 \* H2 \* H3 \* H4 \* H5 \* H6 \* [] ==> H' -> H1 \* H2 \* H3 \* H4 \* H5 \* H6 ==> H'.
Proof. intros. rew_heap in H. auto. Qed.

(** Tactics *)

Ltac hsimpl_left_empty tt :=
  match goal with |- ?HL ==> _ =>
  match HL with
  | [] => idtac
  | _ \* [] => idtac
  | _ \* _ \* [] => idtac
  | _ \* _ \* _ \* [] => idtac
  | _ \* _ \* _ \* _ \* [] => idtac
  | _ \* _ \* _ \* _ \* _ \* [] => idtac
  | _ \* _ \* _ \* _ \* _ \* _ \* [] => idtac
  | _ \* _ \* _ \* _ \* _ \* ?H => apply hsimpl_start_6
  | _ \* _ \* _ \* _ \* ?H => apply hsimpl_start_5
  | _ \* _ \* _ \* ?H => apply hsimpl_start_4
  | _ \* _ \* ?H => apply hsimpl_start_3
  | _ \* ?H => apply hsimpl_start_2
  | ?H => apply hsimpl_start_1
  end end.

Ltac hsimpl_setup tt :=
  prepare_goal_hextract_himpl tt;
  hsimpl_left_empty tt;
  apply hsimpl_start.

Ltac hsimpl_cleanup tt :=
  try apply hsimpl_stop;
  try apply hsimpl_stop;
  try apply pred_le_refl;
  try hsimpl_hint_remove tt;
  try remove_empty_heaps_right tt;
  try remove_empty_heaps_left tt.

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

Ltac hsimpl_find_data l HL cont :=
  match HL with
  | hdata _ l \* _ => apply hsimpl_cancel_eq_1
  | _ \* hdata _ l \* _ => apply hsimpl_cancel_eq_2
  | _ \* _ \* hdata _ l \* _ => apply hsimpl_cancel_eq_3
  | _ \* _ \* _ \* hdata _ l \* _ => apply hsimpl_cancel_eq_4
  | _ \* _ \* _ \* _ \* hdata _ l \* _ => apply hsimpl_cancel_eq_5
  | _ \* _ \* _ \* _ \* _ \* hdata _ l \* _ => apply hsimpl_cancel_eq_6
  end; [ cont tt | ].

Ltac hsimpl_extract_exists tt :=
  first [ 
    hsimpl_hint_next ltac:(fun x =>
      match x with
      | __ => eapply hsimpl_extract_exists
      | _ => apply (@hsimpl_extract_exists _ x)
      end)
  | eapply hsimpl_extract_exists ].

Ltac hsimpl_find_data_post tt :=
  fequal; fequal; 
  try solve [ eassumption | symmetry; eassumption ].

(* todo: better implemented in cps style ? *)

Ltac hsimpl_step tt :=
  match goal with |- ?HL ==> ?HA \* ?HN =>
  match HN with
  | ?H \* _ =>
    match H with
    | [] => apply hsimpl_empty
    | [_] => apply hsimpl_prop
    | heap_is_pack _ => hsimpl_extract_exists tt
    | _ \* _ => apply hsimpl_assoc
    | _ ~> Id _ => apply hsimpl_id
    | ?H => hsimpl_find_same H HL 
    | hdata _ ?l => hsimpl_find_data l HL ltac:(hsimpl_find_data_post)
    | ?H => apply hsimpl_keep
    end
  | [] => fail 1
  | _ => apply hsimpl_starify
  end end.

Ltac hsimpl_main tt :=
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


Lemma hsimpl_demo_1 : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* H3 \* H4 ==> H4 \* H3 \* H5 \* H2.
Proof.
  intros. dup. 
  (* details *)
  hsimpl_setup tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  try hsimpl_step tt.
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
  hsimpl_step tt.
  try hsimpl_step tt.
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
  hsimpl_step tt.
  try hsimpl_step tt.
  hsimpl_cleanup tt.
  skip.
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
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  try hsimpl_step tt.
  hsimpl_cleanup tt.
  auto.
  auto.
  auto.
  (* short *)
  hsimpl.
  auto.
  auto.
  auto.
Qed.


(********************************************************************)
(* ** Extraction tactic for local goals *)

(** Lemmas *)

Lemma hclean_start : forall B (F:~~B) H Q,
  is_local F -> F ([] \* H) Q -> F H Q.
Proof. intros. rew_heap in *. auto. Qed.

Lemma hclean_keep : forall B (F:~~B) H1 H2 H3 Q,
  F ((H2 \* H1) \* H3) Q -> F (H1 \* (H2 \* H3)) Q.
Proof. intros. rewrite (star_comm H2) in H. rew_heap in *. auto. Qed.

Lemma hclean_assoc : forall B (F:~~B) H1 H2 H3 H4 Q,
  F (H1 \* (H2 \* (H3 \* H4))) Q -> F (H1 \* ((H2 \* H3) \* H4)) Q.
Proof. intros. rew_heap in *. auto. Qed.

Lemma hclean_starify : forall B (F:~~B) H1 H2 Q,
  F (H1 \* (H2 \* [])) Q -> F (H1 \* H2) Q.
Proof. intros. rew_heap in *. auto. Qed.

Lemma hclean_empty : forall B (F:~~B) H1 H2 Q,
  is_local F -> (F (H1 \* H2) Q) -> F (H1 \* ([] \* H2)) Q.
Proof. intros. rew_heap. auto. Qed. 

Lemma hclean_prop : forall B (F:~~B) H1 H2 (P:Prop) Q,
  is_local F -> (P -> F (H1 \* H2) Q) -> F (H1 \* ([P] \* H2)) Q.
Proof.
  intros. rewrite star_comm_assoc. apply~ local_intro_prop'. 
Qed. 

Lemma hclean_id : forall A (x X : A) B (F:~~B) H1 H2 Q,
  is_local F -> (x = X -> F (H1 \* H2) Q) -> F (H1 \* (x ~> Id X \* H2)) Q.
Proof. intros. unfold Id. apply~ hclean_prop. Qed.

Lemma hclean_exists : forall B (F:~~B) H1 H2 A (J:A->hprop) Q,
  is_local F -> 
  (forall x, F (H1 \* ((J x) \* H2)) Q) ->
   F (H1 \* (heap_is_pack J \* H2)) Q.
Proof. 
  intros. rewrite star_comm_assoc. apply~ local_intro_exists.
  intros. rewrite~ star_comm_assoc.
Qed. 

(** Tactics *)

Ltac xlocal_core tt :=
  first [ assumption | apply local_is_local ].
  (* match goal with |- is_local _ =>  end. *)

Tactic Notation "xlocal" :=
  xlocal_core tt.

Ltac hclean_setup tt :=
  pose ltac_mark;
  apply hclean_start; [ try xlocal | ].

Ltac hclean_cleanup tt :=
  remove_empty_heaps_formula tt;
  gen_until_mark.

Ltac hclean_step tt :=
  let go HP :=
    match HP with _ \* ?HN => 
    match HN with
    | ?H \* _ =>
      match H with
      | [] => apply hclean_empty; try xlocal
      | [_] => apply hclean_prop; [ try xlocal | intro ]
      | heap_is_pack _ => apply hclean_exists; [ try xlocal | intro ]
      | _ ~> Id _ => apply hclean_id; [ try xlocal | intro ]
      | _ \* _ => apply hclean_assoc
      | _ => apply hclean_keep
      end 
    | [] => fail 1
    | _ => apply hclean_starify
    end end in
  on_formula_pre ltac:(go).


Ltac hclean_main tt :=
  hclean_setup tt;
  (repeat (hclean_step tt));
  hclean_cleanup tt.

Tactic Notation "hclean" := hclean_main tt.
Tactic Notation "hclean" "~" := hclean; auto_tilde.
Tactic Notation "hclean" "*" := hclean; auto_star.


Lemma hclean_demo_1 : forall A (x X:A) H1 H2 H3 B (F:~~B) Q,  
   is_local F ->
   F (H1 \* [] \* (H2 \* Hexists y:int, [y = y]) \* x ~> Id X \* H3) Q.
Proof.
  intros. dup.
  (* details *)
  hclean_setup tt.
  hclean_step tt.
  hclean_step tt.
  hclean_step tt.
  hclean_step tt.
  hclean_step tt.
  hclean_step tt.
  hclean_step tt.
  hclean_step tt.
  hclean_step tt.
  try hclean_step tt.  hclean_cleanup tt.
  skip.
  (* short *)
  hclean.
  skip.
Qed.  




