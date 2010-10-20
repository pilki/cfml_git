Set Implicit Arguments.
Require Export LibCore LibEpsilon Shared.
Require Export CFHeaps.


(********************************************************************)
(* ** Axioms *)

(** The type Func *)

Axiom val : Type. 

(** The type Func is inhabited *)

Axiom val_inhab : Inhab val. 
Existing Instance val_inhab.

(** The evaluation predicate for functions: [eval f v h v' h'] *)

Axiom eval : forall A B, val -> A -> heap -> B -> heap -> Prop.

(** Evaluation is deterministic *)

Axiom eval_deterministic : forall A B f (v:A) h (v1' v2':B) h1' h2',
  eval f v h v1' h1' -> eval f v h v2' h2' -> v1' = v2' /\ h1' = h2'.
  

(********************************************************************)
(* ** Definition and properties of AppPure *)

(** The predicate AppPure *)

Definition pureapp A B (f:val) (x:A) (P:B->Prop) := 
  exists v, forall h, eval f x h v h /\ P v.

(** AppPure satisfies the witness property *)

Lemma pureapp_concrete : forall A B (F:val) (V:A) (P:B->Prop),
  pureapp F V P <-> exists V', P V' /\ pureapp F V (= V').
Proof.
  iff H.
  destruct H as (V'&N). destruct (N heap_empty). exists V'. split~.
    exists V'. intros h. destruct (N h). split~.
  destruct H as (V'&?&N). destruct N as (V''&N).
    exists V'. intros h. destruct (N h). subst~.
Qed.

(** Corrolaries of the previous equivalence *)

Lemma pureapp_witness : forall A B (F:val) (V:A) (P:B->Prop),
  pureapp F V P -> exists V', P V' /\ pureapp F V (= V').
Proof. intros. apply* pureapp_concrete. Qed.

Lemma pureapp_abstract : forall A B (F:val) (V:A) (V':B) (P:B->Prop),
  pureapp F V (= V') -> P V' -> pureapp F V P.
Proof. intros. apply* pureapp_concrete. Qed.

(** AppPure satisfies the determinacy property *)

Lemma pureapp_deterministic : forall A B (F:val) (V:A) (V1' V2':B),
  pureapp F V (= V1') -> pureapp F V (= V2') -> V1' = V2'.
Proof.
  introv (V1&N1) (V2&N2).
  destruct (N1 heap_empty). destruct (N2 heap_empty).
  subst. apply* eval_deterministic.
Qed.          

(** Corroloary of the witness and determinacy properties *)

Lemma pureapp_join : forall A B (F:val) (V:A) (V':B) (P:B->Prop),
  pureapp F V (= V') -> pureapp F V P -> P V'.    
Proof.
  introv HE1 H. lets [V'' [HP HE2]]: (pureapp_witness H). subst.
  replace V' with V''. auto. apply* pureapp_deterministic.
Qed.

(** AppPure is compatible with weakening *)

Lemma pureapp_weaken : forall A B (F:val) (V:A) (P P':B->Prop),
  pureapp F V P -> P ==> P' -> pureapp F V P'.
Proof.
  introv M W. lets [x [Px Hx]]: (pureapp_witness M). 
  apply* pureapp_abstract.
Qed.


(********************************************************************)
(* ** Definition and properties of AppReturns *)

(** The predicate AppReturns *)

Definition app_1 A B (f:val) (x:A) (H:hprop) (Q:B->hprop) :=  
  forall h i, \# h i -> H h -> 
    exists v' h' g, \# h' g i /\ Q v' h' /\
      eval f x (h \+ i) v' (h' \+ g \+ i).

(** AppReturns is a local property *)

Lemma app_local_1 : forall B A1 (x1:A1) f,
  is_local (app_1 (B:=B) f x1).
Proof.
  asserts Hint1: (forall h1 h2, \# h1 h2 -> \# h2 h1).
    intros. auto. 
  asserts Hint2: (forall h1 h2 h3, \# h1 h2 -> \# h1 h3 -> \# h1 (heap_union h2 h3)).
    intros. rew_disjoint*.
  asserts Hint3: (forall h1 h2 h3, \# h1 h2 -> \# h2 h3 -> \# h1 h3 -> \# h1 h2 h3) .
    intros. rew_disjoint*.
  intros. extens. intros H Q. iff M. apply~ local_erase.
  introv Dhi Hh. destruct (M h Hh) as (H1&H2&Q'&H'&D12&N&HQ).
  destruct D12 as (h1&h2&?&?&?&?).
  destruct~ (N h1 (heap_union i h2)) as (v'&h1'&i'&?&HQ'&E).
  subst h. rew_disjoint*.
  sets h': (heap_union h1' h2).
  forwards Hh': (HQ v' h'). subst h'. exists h1' h2. rew_disjoint*.
  destruct Hh' as (h3'&h4'&?&?&?&?).
  (* todo: optimize the assertions *)
  asserts Hint4: (forall h : heap, \# h h1' -> \# h h2 -> \# h h3'). 
    intros h0 H01 H02. asserts: (\# h0 h'). unfold h'. rew_disjoint*. rewrite H10 in H11. rew_disjoint*.
  asserts Hint5: (forall h : heap, \# h h1' -> \# h h2 -> \# h h4'). 
    intros h0 H01 H02. asserts: (\# h0 h'). unfold h'. rew_disjoint*. rewrite H10 in H11. rew_disjoint*.
  exists v' h3' (heap_union h4' i'). splits.
    subst h h'. rew_disjoint*.
    auto.
    subst h h'. rew_disjoint. intuition. applys_eq E 1 3.
      rewrite* <- heap_union_assoc. rewrite~ (@heap_union_comm h2).
      do 2 rewrite* (@heap_union_assoc h3'). rewrite <- H10.
      do 2 rewrite <- heap_union_assoc. fequal.
      rewrite heap_union_comm. rewrite~ <- heap_union_assoc. rew_disjoint*.
Qed.

Hint Resolve app_local_1.

(** AppReturns with frame *)

Lemma app_frame_1 : forall B A1 (x1:A1) f H (Q:B->hprop) H',
  app_1 f x1 H Q -> app_1 f x1 (H \* H') (Q \*+ H').
Proof. intros. applys* local_wframe. Qed.


(********************************************************************)
(* ** Interaction between AppPure and AppReturns *)

(** From AppPure to AppReturns *)

Lemma pureapp_to_app : forall A B (F:val) (V:A) (P:B->Prop),
  pureapp F V P -> app_1 F V [] \[P].
Proof.
  introv (v'&N). introv Dhi Hh. exists v' heap_empty heap_empty. splits.
  rew_disjoint*.
  destruct (N heap_empty). split~.
  hnf in Hh. subst. do 2 rewrite heap_union_neutral_l. destruct~ (N i).
Qed.

(** Corrolary with the frame rule integrated *)

Lemma pureapp_app_1 : forall  A B (F:val) (V:A) (P:B->Prop) (H:hprop) (Q:B->hprop),
  pureapp F V P -> (\[P] \*+ H ===> Q) -> app_1 F V H Q.
Proof.
  intros. apply* local_wframe. apply~ pureapp_to_app. rew_heap~.
Qed. 

(** Overlapping of AppPure and AppReturns *)

Lemma pureapp_and_app_1 : forall A B (F:val) (V:A) (V':B) (H:hprop) (Q:B->hprop),
  pureapp F V (= V') -> app_1 F V H Q -> 
     forall h, H h -> 
       (exists H', (Q V' \* H') h).
Proof. 
  introv (v'&N). introv Dhi Hh. destruct (N h). subst.
  hnf in Dhi. specializes Dhi h heap_empty Hh.
  destruct Dhi as (v'&h'&g&?&?&?).
  repeat rewrite heap_union_neutral_r in *.
  forwards (?&?): (eval_deterministic H0 H3). 
    exists (= g). exists h' g. subst. splits~. rew_disjoint*.
Qed.


(********************************************************************)
(* ** Definition of [AppReturns_n] *)

Definition app_2 A1 A2 B f (x1:A1) (x2:A2) :=
  local (fun H (Q:B->hprop) =>
    exists Q', app_1 f x1 H Q' 
            /\ forall g, app_1 g x2 (Q' g) Q).

Definition app_3 A1 A2 A3 B f (x1:A1) (x2:A2) (x3:A3) := 
  local (fun H (Q:B->hprop) => 
    exists Q', app_1 f x1 H Q' 
            /\ forall g, app_2 g x2 x3 (Q' g) Q).

Definition app_4 A1 A2 A3 A4 B f (x1:A1) (x2:A2) (x3:A3) (x4:A4) := 
  local (fun H (Q:B->hprop) => 
    exists Q', app_1 f x1 H Q' 
            /\ forall g, app_3 g x2 x3 x4 (Q' g) Q).


(********************************************************************)
(* ** Locality of app_n *)

Lemma app_local_2 : forall B A1 A2 (x1:A1) (x2:A2) f,
  is_local (app_2 (B:=B) f x1 x2).
Proof. intros. apply local_is_local. Qed.

Lemma app_local_3 : forall B A1 A2 A3 (x1:A1) (x2:A2) (x3:A3) f,
  is_local (app_3 (B:=B) f x1 x2 x3).
Proof. intros. apply local_is_local. Qed.

Lemma app_local_4 : forall B A1 A2 A3 A4 (x1:A1) (x2:A2) (x3:A3) (x4:A4) f,
  is_local (app_4 (B:=B) f x1 x2 x3 x4).
Proof. intros. apply local_is_local. Qed.

Hint Resolve app_local_2 app_local_3 app_local_4.


(********************************************************************)
(* ** Valid specifications *)

Definition is_spec_0 B (S:~~B->Prop) :=
   forall (R R':~~B), S R -> R ===> R' -> S R'.

Definition is_spec_1 A1 B (K:A1->~~B->Prop) :=
  forall x, is_spec_0 (K x).

Definition is_spec_2 A1 A2 B (K:A1->A2->~~B->Prop) :=
  forall x, is_spec_1 (K x).

Definition is_spec_3 A1 A2 A3 B (K:A1->A2->A3->~~B->Prop) :=
  forall x, is_spec_2 (K x).

Definition is_spec_4 A1 A2 A3 A4 B (K:A1->A2->A3->A4->~~B->Prop) :=
  forall x, is_spec_3 (K x).


(********************************************************************)
(* ** Specification predicates *)

Definition spec_1 A1 B (K: A1 -> ~~B -> Prop) f :=
  is_spec_1 K /\ forall x1, K x1 (app_1 f x1).

Definition spec_2 A1 A2 B (K: A1 -> A2 -> ~~B -> Prop) f :=
  is_spec_2 K /\ forall x1, pureapp f x1 (spec_1 (K x1)).

Definition spec_3 A1 A2 A3 B (K: A1 -> A2 -> A3 -> ~~B -> Prop) f :=
  is_spec_3 K /\ forall x1, pureapp f x1 (spec_2 (K x1)).

Definition spec_4 A1 A2 A3 A4 B (K: A1 -> A2 -> A3 -> A4 -> ~~B -> Prop) f :=
  is_spec_4 K /\ forall x1, pureapp f x1 (spec_3 (K x1)).

(********************************************************************)
(* ** Curried functions *)

Definition curried_1 (A1 B:Type) (f:val) := 
  spec_1 (fun (x1:A1) (R:~~B) => True) f.

Definition curried_2 (A1 A2 B:Type) f := 
  spec_2 (fun (x1:A1) (x2:A2) (R:~~B) => True) f.

Definition curried_3 (A1 A2 A3 B:Type) f := 
  spec_3 (fun (x1:A1) (x2:A2) (x3:A3) (R:~~B) => True) f.

Definition curried_4 (A1 A2 A3 A4 B:Type) f := 
  spec_4 (fun (x1:A1) (x2:A2) (x3:A3) (x4:A4) (R:~~B) => True) f.


(********************************************************************)
(* ** From a given spec to curried *)

Lemma spec_curried_1 : forall A1 B f (K:A1->~~B->Prop),
  spec_1 K f -> curried_1 A1 B f.
Proof. intros. split. intros_all~. auto. Qed.

Lemma spec_curried_2 : forall A1 A2 B f (K:A1->A2->~~B->Prop),
  spec_2 K f -> curried_2 A1 A2 B f.
Proof.
  intros. split.
    intros_all~.
    intros x. eapply (pureapp_weaken (proj2 H x)).
     intros g G. apply* spec_curried_1.
Qed.

Lemma spec_curried_3 : forall A1 A2 A3 B f (K:A1->A2->A3->~~B->Prop),
  spec_3 K f -> curried_3 A1 A2 A3 B f.
Proof.
  intros. split.
    intros_all~.
    intros x. eapply (pureapp_weaken (proj2 H x)).
     intros g G. apply* spec_curried_2.
Qed.

Lemma spec_curried_4 : forall A1 A2 A3 A4 B f (K:A1->A2->A3->A4->~~B->Prop),
  spec_4 K f ->
  curried_4 A1 A2 A3 A4 B f.
Proof.
  intros. split.
    intros_all~.
    intros x. eapply (pureapp_weaken (proj2 H x)).
     intros g G. apply* spec_curried_3.
Qed.


(********************************************************************)
(* ** Change of arities in applications *)

Section AppIntro.
Variables (Q':val->hprop).
Variables (A1 A2 A3 A4 B : Type) (f : val).
Variables (x1:A1) (x2:A2) (x3:A3) (x4:A4).
Variables (H:hprop) (Q:B->hprop).

Lemma app_intro_1_2 : 
  app_1 f x1 H Q' ->
  (forall g, app_1 g x2 (Q' g) Q) ->
  app_2 f x1 x2 H Q.
Proof. intros. apply* local_erase. Qed.

Lemma app_intro_1_3 : 
  app_1 f x1 H Q' ->
  (forall g, app_2 g x2 x3 (Q' g) Q) ->
  app_3 f x1 x2 x3 H Q.
Proof. intros. apply* local_erase. Qed.

Lemma app_intro_1_4 : 
  app_1 f x1 H Q' ->
  (forall g, app_3 g x2 x3 x4 (Q' g) Q) ->
  app_4 f x1 x2 x3 x4 H Q.
Proof. intros. apply* local_erase. Qed.

Lemma app_intro_2_3 : 
  app_2 f x1 x2 H Q' ->
  (forall g, app_1 g x3 (Q' g) Q) ->
  app_3 f x1 x2 x3 H Q.
Proof. 
  introv M1 M2.
  introv Hh. specializes M1 Hh. destruct M1 as (H1&H2&Q1&H'&?&(Q''&Ap1&Ap2)&Po).
  exists (= h) [] Q []. splits; rew_heap~.
  exists (Q'' \*+ H2). split.
    applys* local_wframe. intros h'. intro_subst~.
    intros. apply local_erase. exists __. split.
       apply* local_wframe.
       intros g'. specializes Po g'. applys* local_wgframe.
Qed.

Lemma app_intro_2_4 : 
  app_2 f x1 x2 H Q' ->
  (forall g, app_2 g x3 x4 (Q' g) Q) ->
  app_4 f x1 x2 x3 x4 H Q.
Proof. 
  introv M1 M2.
  introv Hh. specializes M1 Hh. destruct M1 as (H1&H2&Q1&H'&?&(Q''&Ap1&Ap2)&Po).
  exists (= h) [] Q []. splits; rew_heap~.
  exists (Q'' \*+ H2). split.
    applys* local_wframe. intros h'. intro_subst~.
    intros. apply local_erase. exists __. split.
       apply* local_wframe.
       intros g'. specializes Po g'. applys* local_wgframe.
Qed.

Lemma app_intro_3_4 : 
  app_3 f x1 x2 x3 H Q' ->
  (forall g, app_1 g x4 (Q' g) Q) ->
  app_4 f x1 x2 x3 x4 H Q.
Proof. 
(* TODO
  introv M1 M2.
  introv Hh. specializes M1 Hh. destruct M1 as (H1&H2&Q1&H'&?&(Q''&Ap1&Ap2)&Po).
  exists (= h) [] Q []. splits; rew_heap~.
  exists (Q'' \*+ H2). split.
    applys* local_wframe. intros h'. intro_subst~.
    intros.
  renames Ap2 to M1. specializes M1 g. clears h H1.
  intros h0 (h&h'&Hh&Hh'&HD&HU). specializes M1 Hh.
   destruct M1 as (H1&H2'&Q1'&H''&(h1&h2&?&?&?&?)&(Q'''&Ap1&Ap2)&Po').
  exists (= h1) (= h2 \+ h') Q (= h2 \+ h'). splits; rew_heap~. 
  exists h1 (h2 \+ h'). subst h0 h. splits~.
    rew_disjoint*.
    rewrite~ heap_union_assoc.
  exists Q'''. split.
    (* applys* local_wframe. intro. intro_subst~. exists h1 heap_empty. splits*. apply heap_is_empty_prove. *) skip.
    intros. apply local_erase. exists __. split.
       apply* local_wframe. skip.
       intros g'. specializes Po g'. applys* local_wgframe.
 
    intros

  exists (Q'' \*+ H2). split.
    applys* local_wframe. intros h'. intro_subst~.
    intros. apply local_erase. exists __. split.
       apply* local_wframe.
       intros g'. specializes Po g'. applys* local_wgframe.

apply local_erase. exists __. split.
       apply* local_wframe.
       intros g'. specializes Po g'. applys* local_wgframe.
*)
skip.
Qed.


End AppIntro.


(********************************************************************)
(* ** Introduction lemmas *)

Lemma spec_intro_1 : forall A1 B f (K:A1->~~B->Prop),
  is_spec_1 K ->
  curried_1 A1 B f ->
  (forall x1, K x1 (app_1 f x1)) ->
  spec_1 K f.
Proof. introv S _ H. split~. Qed.

Lemma spec_intro_2 : forall A1 A2 B f (K:A1->A2->~~B->Prop),
  is_spec_2 K ->
  curried_2 A1 A2 B f ->
  (forall x1 x2, K x1 x2 (app_2 f x1 x2)) ->
  spec_2 K f.
Proof.
  introv I C HK. split~.
  intros x1. destruct (pureapp_witness (proj2 C x1)) as [g1 [_ Hg1]].
  apply* pureapp_abstract. split~. 
  intros x2. eapply I. apply HK.
  intros H Q M. rewrite app_local_1. introv Hh.
  destruct (M _ Hh) as (H1&H2&Q1&H'&(h1&h2&?&?&?&?)&(Q'&Ap1&Ap2)&Po). clear M.
  specializes Ap2 g1.
  forwards* (H''&Ro): (>>> (@pureapp_and_app_1 A1 val) f x1).
  exists (Q' g1 \* H'') H2 __ (H' \* H''). splits.
    subst. exists___*.
    apply* local_wframe.
    intros r. specializes Po r. hsimpl. auto.
Qed.

Lemma spec_intro_3 : forall A1 A2 A3 B f (K:A1->A2->A3->~~B->Prop),
  is_spec_3 K ->
  curried_3 A1 A2 A3 B f ->
  (forall x1 x2 x3, K x1 x2 x3 (app_3 f x1 x2 x3)) ->
  spec_3 K f.
Proof.
  introv I C HK. split~.
  intros x1. destruct (pureapp_witness (proj2 C x1)) as [g1 [S1 Hg1]].
  apply* pureapp_abstract. split~.
  intros x2. destruct (pureapp_witness (proj2 S1 x2)) as [g2 [_ Hg2]].
  apply* pureapp_abstract. split~. apply I. 
  intros x3. eapply I. apply HK.
  intros H Q M. rewrite app_local_1. introv Hh.
  destruct (M _ Hh) as (H1&H2&Q1&H'&(h1&h2&?&?&?&?)&(Q'&Ap1&Ap2)&Po). clear M.
  specializes Ap2 g1. 
  forwards* (H''&(h3&h4&PH3&PH4&?&?)): (>>> (@pureapp_and_app_1 A1 val) f x1).
  destruct (Ap2 _ PH3) as (H1'&H2'&Q1'&H'''&(h1'&h2'&?&?&?&?)&(Q''&Ap1'&Ap2')&Po'). 
  forwards* (Hf&(h3'&h4'&PH3'&PH4'&?&?)): (>>> (@pureapp_and_app_1 A2 val) g1 x2).
  specializes Ap2' g2.
  exists (Q'' g2 \* H'') (H2 \* H2' \* Hf) __ (H' \* H'' \* H''' \* Hf). splits.
    exists (h3' \+ h4) (h2 \+ h2' \+ h4'). splits.
      exists___. subst. splits*. rew_disjoint*.
      exists h2 (h2' \+ h4'). splits~.
        exists___. subst. splits*. rew_disjoint*. subst. rew_disjoint*. 
        subst. rew_disjoint*.    
      subst. do 2 rewrite heap_union_assoc. auto. skip. (* todo: equal up to commutativity *)
    apply* local_wframe.
    intros v. hsimpl. hchange (Po' v). hchange (Po v). hsimpl.
Qed.

Lemma spec_intro_4 : forall A1 A2 A3 A4 B f (K:A1->A2->A3->A4->~~B->Prop),
  is_spec_4 K ->
  curried_4 A1 A2 A3 A4 B f ->
  (forall x1 x2 x3 x4, K x1 x2 x3 x4 (app_4 f x1 x2 x3 x4)) ->
  spec_4 K f.
Proof.
  (* todo: follow the same idea as previous proof -- need a tactic! *)
Admitted.


(********************************************************************)
(* ** Elimination lemmas *)

Lemma spec_elim_1 : forall A1 B (K: A1 -> ~~B -> Prop) f,
  spec_1 K f -> forall x1, K x1 (app_1 f x1).
Proof. introv [S H]. auto. Qed.

Lemma spec_elim_2 : forall A1 A2 B (K: A1 -> A2 -> ~~B -> Prop) f,
  spec_2 K f -> forall x1 x2, K x1 x2 (app_2 f x1 x2).
Proof.
  introv S. intros. destruct (pureapp_witness ((proj22 S) x1)) as [g [Pg Hg]].
  lets M: ((proj2 Pg) x2). applys (proj1 S) M. clear M. intros H Q Ap1.
  applys app_intro_1_2 (fun g' => [g'=g] \* H). 
    apply* pureapp_app_1. 
    intros g'. apply~ local_intro_prop'. intro_subst~.
Qed.    

Lemma spec_elim_3 : forall A1 A2 A3 B (K: A1 -> A2 -> A3 -> ~~B -> Prop) f,
  spec_3 K f -> forall x1 x2 x3, K x1 x2 x3 (app_3 f x1 x2 x3).
Proof.
  introv S. intros. destruct (pureapp_witness ((proj22 S) x1)) as [g [Pg Hg]].
  forwards M: (spec_elim_2 Pg). applys (proj1 S) M. clear M. intros H Q Ap1.
  applys app_intro_1_3 (fun g' => [g'=g] \* H). 
    apply* pureapp_app_1. 
    intros g'. apply~ local_intro_prop'. intro_subst~.
Qed.

Lemma spec_elim_4 : forall A1 A2 A3 A4 B (K: A1 -> A2 -> A3 -> A4 -> ~~B -> Prop) f,
  spec_4 K f -> forall x1 x2 x3 x4, K x1 x2 x3 x4 (app_4 f x1 x2 x3 x4).
Proof.
  introv S. intros. destruct (pureapp_witness ((proj22 S) x1)) as [g [Pg Hg]].
  forwards M: (spec_elim_3 Pg). applys (proj1 S) M. clear M. intros H Q Ap1.
  applys app_intro_1_4 (fun g' => [g'=g] \* H). 
    apply* pureapp_app_1. 
    intros g'. apply~ local_intro_prop'. intro_subst~.
Qed.


(********************************************************************)
(* ** Elimination lemmas from spec to app *)

(*-- spec_elim_1 --*)

Lemma spec_elim_1_1 : forall A1 B (K: A1 -> ~~B -> Prop) f,
  spec_1 K f -> forall x1 (H : hprop) (Q : B->hprop),
  (forall R, is_local R -> K x1 R -> R H Q) ->
  app_1 f x1 H Q.
Proof. introv S W. apply (W _). auto. apply S. Qed.

Lemma spec_elim_1_2 : forall A1 A2 (K: A1 -> ~~val -> Prop) f,
  spec_1 K f -> forall x1 (x2:A2) (H : hprop) (Q Q' : val->hprop),
  (forall R, is_local R -> K x1 R -> R H Q') -> 
  (forall g, app_1 g x2 (Q' g) Q) ->
  app_2 f x1 x2 H Q.
Proof. intros. apply* app_intro_1_2. apply* spec_elim_1_1. Qed.

Lemma spec_elim_1_3 : forall A1 A2 A3 (K: A1 -> ~~val -> Prop) f,
  spec_1 K f -> forall x1 (x2:A2) (x3:A3) (H : hprop) (Q Q' : val->hprop),
  (forall R, is_local R -> K x1 R -> R H Q') -> 
  (forall g, app_2 g x2 x3 (Q' g) Q) ->
  app_3 f x1 x2 x3 H Q.
Proof. intros. apply* app_intro_1_3. apply* spec_elim_1_1. Qed.

Lemma spec_elim_1_4 : forall A1 A2 A3 A4 (K: A1 -> ~~val -> Prop) f,
  spec_1 K f -> forall x1 (x2:A2) (x3:A3) (x4:A4) (H : hprop) (Q Q' : val->hprop),
  (forall R, is_local R -> K x1 R -> R H Q') -> 
  (forall g, app_3 g x2 x3 x4 (Q' g) Q) ->
  app_4 f x1 x2 x3 x4 H Q.
Proof. intros. apply* app_intro_1_4. apply* spec_elim_1_1. Qed.

(*-- spec_elim_2 --*)

Lemma spec_elim_2_1 : forall A1 A2 B (K: A1 -> A2 -> ~~B -> Prop) f,
  spec_2 K f -> forall x1,
  app_1 f x1 [] \[spec_1 (K x1)].
Proof. intros. destruct H as [I Ap1]. apply~ pureapp_to_app. Qed.

Lemma spec_elim_2_2 : forall A1 A2 B (K: A1 -> A2 -> ~~B -> Prop) f,
  spec_2 K f -> forall x1 x2 (H : hprop) (Q : B->hprop),
  (forall R, is_local R -> K x1 x2 R -> R H Q) ->
  app_2 f x1 x2 H Q.
Proof. introv S W. apply (W _). auto. apply* spec_elim_2. Qed.

Lemma spec_elim_2_3 : forall A1 A2 A3 (K: A1 -> A2 -> ~~val -> Prop) f,
  spec_2 K f -> forall x1 x2 (x3:A3) (H : hprop) (Q Q' : val->hprop),
  (forall R, is_local R -> K x1 x2 R -> R H Q') ->
  (forall g, app_1 g x3 (Q' g) Q) ->
  app_3 f x1 x2 x3 H Q.
Proof. intros. apply* app_intro_2_3. apply* spec_elim_2_2. Qed.

Lemma spec_elim_2_4 : forall A1 A2 A3 A4 (K: A1 -> A2 -> ~~val -> Prop) f,
  spec_2 K f -> forall x1 x2 (x3:A3) (x4:A4) (H : hprop) (Q Q' : val->hprop),
  (forall R, is_local R -> K x1 x2 R -> R H Q') ->
  (forall g, app_2 g x3 x4 (Q' g) Q) ->
  app_4 f x1 x2 x3 x4 H Q.
Proof. intros. apply* app_intro_2_4. apply* spec_elim_2_2. Qed.

(*-- spec_elim_3 --*)

Lemma spec_elim_3_1 : forall A1 A2 A3 B (K: A1 -> A2 -> A3 -> ~~B -> Prop) f,
  spec_3 K f -> forall x1,
  app_1 f x1 [] \[spec_2 (K x1)].
Proof. intros. destruct H as [I Ap1]. apply~ pureapp_to_app. Qed.

(* todo:move *)
Lemma local_intro_prop' : forall B (F:~~B) (P:Prop) Q,
  is_local F -> (P -> F [] Q) -> F [P] Q.
Proof.
  introv L H. applys~ local_intro_prop P.
  introv Hh. destruct~ Hh.
  intros M. apply~ local_weaken_pre. 
  intros h Hh. destruct~ Hh.
Qed. 

Lemma spec_elim_3_2 : forall A1 A2 A3 B (K: A1 -> A2 -> A3 -> ~~B -> Prop) f,
  spec_3 K f -> forall x1 x2,
  app_2 f x1 x2 [] \[spec_1 (K x1 x2)].
Proof. 
  intros. destruct H as [I Ap1]. specializes Ap1 x1.
  eapply app_intro_1_2.
    apply* pureapp_app_1.
    intros g. rew_heap. apply~ local_intro_prop'.
      intros M. apply (spec_elim_2_1 M).
Qed.

Lemma spec_elim_3_3 : forall A1 A2 A3 B (K: A1 -> A2 -> A3 -> ~~B -> Prop) f,
  spec_3 K f -> forall x1 x2 x3 (H : hprop) (Q : B->hprop),
  (forall R, is_local R -> K x1 x2 x3 R -> R H Q) ->
  app_3 f x1 x2 x3 H Q.
Proof. introv S W. apply (W _). auto. apply* spec_elim_3. Qed.

Lemma spec_elim_3_4 : forall A1 A2 A3 A4 (K: A1 -> A2 -> A3 -> ~~val -> Prop) f,
  spec_3 K f -> forall x1 x2 x3 (x4:A4) (H : hprop) (Q Q' : val->hprop),
  (forall R, is_local R -> K x1 x2 x3 R -> R H Q') ->
  (forall g, app_1 g x4 (Q' g) Q) ->
  app_4 f x1 x2 x3 x4 H Q.
Proof. intros. apply* app_intro_3_4. apply* spec_elim_3_3. Qed.

(*-- spec_elim_4 --*)

Lemma spec_elim_4_1 : forall A1 A2 A3 A4 B (K: A1 -> A2 -> A3 -> A4 -> ~~B -> Prop) f,
  spec_4 K f -> forall x1 (P : val->Prop),
  app_1 f x1 [] \[spec_3 (K x1)].
Proof. intros. destruct H as [I Ap1]. apply~ pureapp_to_app. Qed.

Lemma spec_elim_4_2 : forall A1 A2 A3 A4 B (K: A1 -> A2 -> A3 -> A4 -> ~~B -> Prop) f,
  spec_4 K f -> forall x1 x2,
  app_2 f x1 x2 [] \[spec_2 (K x1 x2)].
Proof. 
  intros. destruct H as [I Ap1]. specializes Ap1 x1.
  eapply app_intro_1_2.
    apply* pureapp_app_1.
    intros g. rew_heap. apply~ local_intro_prop'.
      intros M. apply (spec_elim_3_1 M).
Qed.

Lemma spec_elim_4_3 : forall A1 A2 A3 A4 B (K: A1 -> A2 -> A3 -> A4 -> ~~B -> Prop) f,
  spec_4 K f -> forall x1 x2 x3 (P : val->Prop),
  app_3 f x1 x2 x3 [] \[spec_1 (K x1 x2 x3)].
Proof. 
  intros. destruct H as [I Ap1]. specializes Ap1 x1.
  eapply app_intro_1_3.
    apply* pureapp_app_1.
    intros g. rew_heap. apply~ local_intro_prop'.
      intros M. apply (spec_elim_3_2 M).
Qed.

Lemma spec_elim_4_4 : forall A1 A2 A3 A4 B (K: A1 -> A2 -> A3 -> A4 -> ~~B -> Prop) f,
  spec_4 K f -> forall x1 x2 x3 x4 (H : hprop) (Q : B->hprop),
  (forall R, is_local R -> K x1 x2 x3 x4 R -> R H Q) ->
  app_4 f x1 x2 x3 x4 H Q.
Proof. introv S W. apply (W _). auto. apply* spec_elim_4. Qed.



(********************************************************************)
(* ** App from spec *)

Lemma app_spec_1 : forall A1 B f (v1:A1) (H:hprop) (Q : B->hprop),
  spec_1 (fun x1 R => x1 = v1 -> R H Q) f ->
  app_1 f v1 H Q.
Proof. introv S. apply~ (spec_elim_1_1 S). Qed.

Lemma app_spec_2 : forall A1 A2 B f (v1:A1) (v2:A2) (H:hprop) (Q : B->hprop),
  spec_2 (fun x1 x2 R => x1 = v1 -> x2 = v2 -> R H Q) f ->
  app_2 f v1 v2 H Q.
Proof. introv S. apply~ (spec_elim_2_2 S). Qed.

Lemma app_spec_3 : forall A1 A2 A3 B f (v1:A1) (v2:A2) (v3:A3) (H:hprop) (Q : B->hprop),
  spec_3 (fun x1 x2 x3 R => x1 = v1 -> x2 = v2 -> x3 = v3 -> R H Q) f -> 
  app_3 f v1 v2 v3 H Q.
Proof. introv S. apply~ (spec_elim_3_3 S). Qed.

Lemma app_spec_4 : forall A1 A2 A3 A4 B f (v1:A1) (v2:A2) (v3:A3) (v4:A4) (H:hprop) (Q : B->hprop),
  spec_4 (fun x1 x2 x3 x4 R => x1 = v1 -> x2 = v2 -> x3 = v3 -> x4 = v4 -> R H Q) f -> 
  app_4 f v1 v2 v3 v4 H Q.
Proof. introv S. apply~ (spec_elim_4_4 S). Qed.


(********************************************************************)
(* ** Weakening for spec *)

Section SpecWeaken.

Hint Resolve spec_curried_1 spec_curried_2 spec_curried_3 spec_curried_4. 

Lemma spec_weaken_1 : forall A1 B (K K': A1 -> ~~B -> Prop) f,
   spec_1 K f -> is_spec_1 K' -> 
   (forall x1 R, is_local R -> K x1 R -> K' x1 R) ->
   spec_1 K' f.
Proof. 
  introv ? ? M. apply* spec_intro_1. intros. apply~ M. apply~ spec_elim_1.
Qed.

Lemma spec_weaken_2 : forall A1 A2 B (K K': A1 -> A2 -> ~~B -> Prop) f,
   spec_2 K f -> is_spec_2 K' ->
   (forall x1 x2 R, is_local R -> K x1 x2 R -> K' x1 x2 R) ->
   spec_2 K' f.
Proof. 
  introv ? ? M. apply* spec_intro_2. intros. apply~ M. apply~ spec_elim_2.
Qed.

Lemma spec_weaken_3 : forall A1 A2 A3 B (K K': A1 -> A2 -> A3 -> ~~B -> Prop) f,
   spec_3 K f -> is_spec_3 K' -> 
   (forall x1 x2 x3 R, is_local R -> K x1 x2 x3 R -> K' x1 x2 x3 R) ->
   spec_3 K' f.
Proof. 
  introv ? ? M. apply* spec_intro_3. intros. apply~ M. apply~ spec_elim_3.
Qed.

Lemma spec_weaken_4 : forall A1 A2 A3 A4 B (K K': A1 -> A2 -> A3 -> A4 -> ~~B -> Prop) f,
   spec_4 K f -> is_spec_4 K' -> 
   (forall x1 x2 x3 x4 R, is_local R -> K x1 x2 x3 x4 R -> K' x1 x2 x3 x4 R) ->
   spec_4 K' f.
Proof. 
  introv ? ? M. apply* spec_intro_4. intros. apply~ M. apply~ spec_elim_4.
Qed.

End SpecWeaken.


(********************************************************************)
(* ** Induction lemmas for spec *)

Lemma spec_induction_1 : 
  forall A1 B A0,
  forall (lt:binary (A0*A1)) (Wf: wf lt) f (L:A0->A1->~~B->Prop),
  (forall y, is_spec_1 (L y)) ->
  spec_1 (fun x R => forall y,
    spec_1 (fun x' R' => forall y', lt (y',x') (y,x) -> L y' x' R') f ->
    L y x R) f ->
  spec_1 (fun x R => forall y, L y x R) f.
Proof.
  introv W Is H. 
  cuts Hyp: (forall y x, is_spec_0 (L y x) /\ L y x (app_1 f x)).
    apply spec_intro_1.
      intros x. introv HK HP. hnf. intros y. applys~ (proj1 (Hyp y x)).
      apply* spec_curried_1.
      intros x y. destruct~ (Hyp y x).
  cuts Hyp': (forall p, let '(y,x) := p in is_spec_0 (L y x) /\ L y x (app_1 f x)).
    intros y x. apply (Hyp' (y,x)).
  intros p. induction_wf IH: W p. destruct p as [y x].
  lets C: (spec_curried_1 H). 
  lets I: (proj1 H x).
  lets S: (spec_elim_1 H x y). clear H.
  split.
    apply~ Is.
    apply S. split.
      intros x'. introv HK HP Lt. applys~ (proj1 (IH _ Lt)).
      intros x' y' Lt. apply (proj2 (IH _ Lt)).
Qed.

Lemma spec_induction_2 : 
  forall A1 A2 B A0 (lt:binary(A0*A1*A2)),
  forall (Wf: wf lt) f (L:A0->A1->A2->~~B->Prop),
  (forall y, is_spec_2 (L y)) ->
  spec_2 (fun x1 x2 R => forall x0,
    spec_2 (fun y1 y2 R' => forall y0, 
      lt (y0,y1,y2) (x0,x1,x2) -> L y0 y1 y2 R') f ->
    L x0 x1 x2 R) f ->
  spec_2 (fun x1 x2 R => forall x0, L x0 x1 x2 R) f.
Proof.
  introv W Is H. 
  cuts Hyp: (forall y x1 x2, is_spec_0 (L y x1 x2) /\ L y x1 x2 (app_2 f x1 x2)).
    apply spec_intro_2.
      intros x1 x2. introv HK HP. hnf. intros y. applys~ (proj1 (Hyp y x1 x2)).
      apply* spec_curried_2.
      intros x1 x2 y. destruct~ (Hyp y x1 x2).
  cuts Hyp': (forall p, let '(y,x1,x2) := p in is_spec_0 (L y x1 x2) /\ L y x1 x2 (app_2 f x1 x2)).
    intros y x1 x2. apply (Hyp' (y,x1,x2)).
  intros p. induction_wf IH: W p. destruct p as [[y x1] x2].
  lets C: (spec_curried_2 H). 
  lets I: (proj1 H x1 x2).
  lets S: (spec_elim_2 H x1 x2 y). clear H.
  split.
    apply~ Is.
    apply S. apply spec_intro_2.
      intros x'. introv HK HP Lt. applys~ (proj1 (IH _ Lt)).
      auto.
      intros x1' x2' y' Lt. apply (proj2 (IH _ Lt)).
Qed.

Lemma spec_induction_3 : 
  forall A1 A2 A3 B A0 (lt:binary(A0*A1*A2*A3)) (Wf: wf lt) f 
         (L:A0->A1->A2->A3->~~B->Prop),
  (forall y, is_spec_3 (L y)) ->
  spec_3 (fun x1 x2 x3 R => forall x0,
    spec_3 (fun y1 y2 y3 R' => forall y0,
      lt (y0,y1,y2,y3) (x0,x1,x2,x3) -> L y0 y1 y2 y3 R') f ->
    L x0 x1 x2 x3 R) f ->
  spec_3 (fun x1 x2 x3 R => forall x0, L x0 x1 x2 x3 R) f.
Proof.
  introv W Is H. 
  cuts Hyp: (forall y x1 x2 x3, is_spec_0 (L y x1 x2 x3) /\ L y x1 x2 x3 (app_3 f x1 x2 x3)).
    apply spec_intro_3.
      intros x1 x2 x3. introv HK HP. hnf. intros y. applys~ (proj1 (Hyp y x1 x2 x3)).
      apply* spec_curried_3.
      intros x1 x2 x3 y. destruct~ (Hyp y x1 x2 x3).
  cuts Hyp': (forall p, let '(y,x1,x2,x3) := p in is_spec_0 (L y x1 x2 x3) /\ L y x1 x2 x3 (app_3 f x1 x2 x3)).
    intros y x1 x2 x3. apply (Hyp' (y,x1,x2,x3)).
  intros p. induction_wf IH: W p. destruct p as [[[y x1] x2] x3].
  lets C: (spec_curried_3 H). 
  lets I: (proj1 H x1 x2 x3).
  lets S: (spec_elim_3 H x1 x2 x3 y). clear H.
  split.
    apply~ Is.
    apply S. apply spec_intro_3.
      intros x'. introv HK HP Lt. applys~ (proj1 (IH _ Lt)).
      auto.
      intros x1' x2' x3' y' Lt. apply (proj2 (IH _ Lt)).
Qed.

Lemma spec_induction_4 : 
  forall A1 A2 A3 A4 B A0 (lt:binary(A0*A1*A2*A3*A4)) (Wf: wf lt) f 
         (L:A0->A1->A2->A3->A4->~~B->Prop),
  (forall y, is_spec_4 (L y)) ->
  spec_4 (fun x1 x2 x3 x4 R => forall x0,
    spec_4 (fun y1 y2 y3 y4 R' => forall y0,
       lt (y0,y1,y2,y3,y4) (x0,x1,x2,x3,x4) -> L y0 y1 y2 y3 y4 R') f ->
    L x0 x1 x2 x3 x4 R) f ->
  spec_4 (fun x1 x2 x3 x4 R => forall x0, L x0 x1 x2 x3 x4 R) f.
Proof.
  introv W Is H. 
  cuts Hyp: (forall y x1 x2 x3 x4, is_spec_0 (L y x1 x2 x3 x4) /\ L y x1 x2 x3 x4 (app_4 f x1 x2 x3 x4)).
    apply spec_intro_4.
      intros x1 x2 x3 x4. introv HK HP. hnf. intros y. applys~ (proj1 (Hyp y x1 x2 x3 x4)).
      apply* spec_curried_4.
      intros x1 x2 x3 x4 y. destruct~ (Hyp y x1 x2 x3 x4).
  cuts Hyp': (forall p, let '(y,x1,x2,x3,x4) := p in is_spec_0 (L y x1 x2 x3 x4) /\ L y x1 x2 x3 x4 (app_4 f x1 x2 x3 x4)).
    intros y x1 x2 x3 x4. apply (Hyp' (y,x1,x2,x3,x4)).
  intros p. induction_wf IH: W p. destruct p as [[[[y x1] x2] x3] x4].
  lets C: (spec_curried_4 H). 
  lets I: (proj1 H x1 x2 x3 x4).
  lets S: (spec_elim_4 H x1 x2 x3 x4 y). clear H.
  split.
    apply~ Is.
    apply S. apply spec_intro_4.
      intros x'. introv HK HP Lt. applys~ (proj1 (IH _ Lt)).
      auto.
      intros x1' x2' x3' x4' y' Lt. apply (proj2 (IH _ Lt)).
Qed.

Lemma spec_induction_1_noarg : 
  forall A1 B A0,
  forall (lt:binary A0) (Wf: wf lt) f (L:A0->A1->~~B->Prop),
  (forall y, is_spec_1 (L y)) ->
  spec_1 (fun x R => forall y,
    spec_1 (fun x' R' => forall y', lt y' y -> L y' x' R') f ->
    L y x R) f ->
  spec_1 (fun x R => forall y, L y x R) f.
Proof.
  introv W Is H. applys* spec_induction_1 (unproj21_wf (A2:=A1) W).
Qed. 

Lemma spec_induction_1_noheap : 
  forall A1 B,
  forall (lt:binary A1) (Wf: wf lt) f (K:A1->~~B->Prop),
  spec_1 (fun x R => 
    spec_1 (fun x' R' => lt x' x -> K x' R') f ->
    K x R) f ->
  spec_1 K f.
Proof. (* Here is a direct proof. One could also reuse [spec_induction_1]. *)
  introv W H.
  cuts Hyp: (forall x, is_spec_0 (K x) /\ K x (app_1 f x)).
    apply spec_intro_1. 
      intros x. apply (proj1 (Hyp x)).
      apply* spec_curried_1.
      intros x. destruct~ (Hyp x). 
  intros x. pattern x. induction_wf IH: W x.
  lets C: (spec_curried_1 H). 
  lets I: (proj1 H x).
  lets S: (spec_elim_1 H x). clear H. 
  asserts M: (spec_1 (fun x' R' => lt x' x -> K x' R') f). split.
    intros x'. introv HK HP Lt. applys~ (proj1 (IH _ Lt)).
    intros x' Lt. apply (proj2 (IH _ Lt)).
  split.
    introv HK HP. applys~ (I R R').
    apply~ S.
Qed.

Hint Resolve tt.

Lemma spec_induction_2_noheap : 
  forall A1 A2 B (lt:(A1*A2)->(A1*A2)->Prop),
  forall (Wf: wf lt) f (K:A1->A2->~~B->Prop),
  is_spec_2 K ->
  spec_2 (fun x1 x2 R => 
    spec_2 (fun y1 y2 R' => lt (y1,y2) (x1,x2) -> K y1 y2 R') f ->
    K x1 x2 R) f ->
  spec_2 K f.
Proof.
  intros. 
  forwards: (@spec_induction_2 A1 A2 B unit) 
    (fun p q : unit*A1*A2 => let '(_,y1,y2) := p in let '(_,x1,x2) := q in lt (y1,y2) (x1,x2)) 
    (fun _:unit => K).
  intros [[y x1] x2]. gen_eq p: (x1,x2). gen y x1 x2.
   induction_wf IH: Wf p. constructor. intros [[y' x1'] x2'] Lt. subst p. auto*.
  auto.
  applys spec_weaken_2 H0.
    intros_all. applys~ H.
    introv LR M _ N. apply M. applys spec_weaken_2 N.
      intros_all. applys~ H.
      intros_all. applys~ H2.
  applys~ spec_weaken_2 H1.
Qed.

Lemma spec_induction_3_noheap : 
  forall A1 A2 A3 B (lt:(A1*A2*A3)->(A1*A2*A3)->Prop) (Wf: wf lt) f 
         (K:A1->A2->A3->~~B->Prop),
  is_spec_3 K ->
  spec_3 (fun x1 x2 x3 R => 
    spec_3 (fun y1 y2 y3 R' => lt (y1,y2,y3) (x1,x2,x3) -> K y1 y2 y3 R') f ->
    K x1 x2 x3 R) f ->
  spec_3 K f.
Proof.
  intros. 
  forwards: (@spec_induction_3 A1 A2 A3 B unit) 
    (fun p q : unit*A1*A2*A3 => let '(_,y1,y2,y3) := p in let '(_,x1,x2,x3) := q in lt (y1,y2,y3) (x1,x2,x3)) 
    (fun _:unit => K).
  intros [[[y x1] x2] x3]. gen_eq p: (x1,x2,x3). gen y x1 x2 x3.
   induction_wf IH: Wf p. constructor. intros [[[y' x1'] x2'] x3'] Lt. subst p. auto*.
  auto.
  applys spec_weaken_3 H0.
    intros_all. applys~ H.
    introv LR M _ N. apply M. applys spec_weaken_3 N.
      intros_all. applys~ H.
      intros_all. applys~ H2.
  applys~ spec_weaken_3 H1.
Qed.

Lemma spec_induction_4_noheap : 
  forall A1 A2 A3 A4 B (lt:(A1*A2*A3*A4)->(A1*A2*A3*A4)->Prop) (Wf: wf lt) f 
         (K:A1->A2->A3->A4->~~B->Prop),
  is_spec_4 K ->
  spec_4 (fun x1 x2 x3 x4 R => 
    spec_4 (fun y1 y2 y3 y4 R' => lt (y1,y2,y3,y4) (x1,x2,x3,x4) -> K y1 y2 y3 y4 R') f ->
    K x1 x2 x3 x4 R) f ->
  spec_4 K f.
Proof.
  intros. 
  forwards: (@spec_induction_4 A1 A2 A3 A4 B unit) 
    (fun p q : unit*A1*A2*A3*A4 => let '(_,y1,y2,y3,y4) := p in let '(_,x1,x2,x3,x4) := q in lt (y1,y2,y3,y4) (x1,x2,x3,x4)) 
    (fun _:unit => K).
  intros [[[[y x1] x2] x3] x4]. gen_eq p: (x1,x2,x3,x4). gen y x1 x2 x3 x4.
   induction_wf IH: Wf p. constructor. intros [[[[y' x1'] x2'] x3'] x4'] Lt. subst p. auto*.
  auto.
  applys spec_weaken_4 H0.
    intros_all. applys~ H.
    introv LR M _ N. apply M. applys spec_weaken_4 N.
      intros_all. applys~ H.
      intros_all. applys~ H2.
  applys~ spec_weaken_4 H1.
Qed.


(********************************************************************)
(* ** Proofs that SpecN can be eliminated (part of the soundness proof) *)

Section SpecIff.
Hint Extern 1 (is_spec_1 _) =>
  let P := fresh in intros ? ? ? ? P; applys* P.
Hint Resolve app_local_1.

Lemma spec_iff_app_1 : forall A1 B f (G:A1->~~B),
  (forall K, is_spec_1 K -> (forall x, K x (G x)) -> spec_1 K f) <->
  (forall x H Q, G x H Q -> app_1 f x H Q).
Proof.
  intros. iff M.
  introv S. forwards* [U V]: (>>> M (fun (x':A1) (R:~~B) => x' = x -> R H Q)).
    intros_all. subst. applys* H1.
    intros. subst~.
  introv Is S. split~. intros x. applys Is S. intros H Q N. apply~ M.
Qed.

Lemma spec_iff_app_2 : forall A1 A2 B f (G:A1->A2->~~B),
  (forall K, is_spec_2 K -> (forall x y, K x y (G x y)) -> spec_2 K f) <->
  (forall x (P:val->Prop), 
     (forall g, (forall y H' Q', G x y H' Q' -> app_1 g y H' Q') -> P g) ->
     pureapp f x P).
Proof.
  intros. iff M.
  introv S. 
    forwards N: M (fun (x:A1) (y:A2) (R:~~B) => True). intros_all~. auto.
    destruct (pureapp_witness (proj2 N x)) as (g&Sg&Ag). clear Sg N.
    apply* pureapp_weaken. intros g'. intro_subst.
    apply S. intros y H' Q' Ap.
    forwards N: M (fun (x':A1) (y':A2) (R:~~B) => x' = x -> y' = y -> R H' Q').
       intros_all. subst. applys* H0. 
       intros_all. subst~.
    lets Ag': (proj2 N x). lets Sg: (>>> (@pureapp_join A1 val) Ag Ag').
    apply~ (proj2 Sg y).
  introv Is S. split~. intros x. apply M. intros g N.
   split~. intros y. applys Is. apply S. intros H Q L. apply~ N.
Qed.
End SpecIff.


(********************************************************************)
(* ** Lemmas for other tactics *)

Lemma xframe_lemma : forall H1 H2 B Q1 (F:~~B) H Q,
  is_local F -> 
  H ==> H1 \* H2 -> 
  F H1 Q1 -> 
  Q1 \*+ H2 ===> Q ->
  F H Q.
Proof. intros. apply* local_wframe. Qed.

Lemma xchange_lemma : forall H1 H1' H2 B H Q (F:~~B),
  is_local F -> (H1 ==> H1') -> (H ==> H1 \* H2) -> F (H1' \* H2) Q -> F H Q.
Proof.
  introv W1 L W2 M. applys local_wframe __ []; eauto.
  hsimpl. hchange~ W2. hsimpl~. rew_heap~. 
Qed.

Lemma local_gc_pre_all : forall B Q (F:~~B) H,
  is_local F -> 
  F [] Q ->
  F H Q.
Proof. intros. apply* (@local_gc_pre H). hsimpl. Qed.

Lemma xret_gc_lemma : forall HG B (v:B) H (Q:B->hprop),
  H ==> Q v \* HG -> 
  local (fun H' Q' => H' ==> Q' v) H Q.
Proof.  
  introv W. eapply (@local_gc_pre HG).
  auto. rewrite star_comm. apply W.
  apply~ local_erase.
Qed.

Lemma xret_lemma : forall B (v:B) H (Q:B->hprop),
  H ==> Q v -> 
  local (fun H' Q' => H' ==> Q' v) H Q.
Proof.  
  introv W. apply~ local_erase.
Qed.

Lemma xret_lemma_unify : forall B (v:B) H,
  local (fun H' Q' => H' ==> Q' v) H (\= v \*+ H).
Proof.  
  intros. apply~ local_erase. hsimpl. auto. 
Qed.

(* todo: move *)
Lemma local_frame : forall H' B H Q (F:~~B),
  is_local F -> 
  F H Q -> 
  F (H \* H') (Q \*+ H').
Proof. intros. apply* local_wframe. Qed.

Lemma xpost_lemma : forall B Q' Q (F:~~B) H,
  is_local F -> 
  F H Q' -> 
  Q' ===> Q ->
  F H Q.
Proof. intros. applys* local_weaken. Qed.


(********************************************************************)
(* ** Loop invariants for while-loops *)

(* todo: move *)

Lemma local_weaken_body : forall (B:Type) (F F':~~B),
  (forall H Q, F H Q -> F' H Q) -> 
  local F ===> local F'.
Proof.
  introv M. intros H Q N. introv Hh.
  destruct (N _ Hh) as (H1&H2&Q1&H'&P1&P2&P3). exists___*.
Qed.

Lemma local_extract_exists : forall B (F:~~B) A (J:A->hprop) Q,
  is_local F ->
  (forall x, F (J x) Q) -> 
  F (heap_is_pack J) Q.
Proof.
  introv L M. rewrite L. introv (x&Hx).
  exists (J x) [] Q []. splits~. rew_heap~.
Qed. 
 (* todo: where is local_intro_prop' rebound ? *)



Definition while_loop_cf (F1:~~bool) (F2:~~unit) :=
  local (fun (H:hprop) (Q:unit->hprop) => forall R:~~unit, is_local R ->
    (forall H Q, (exists Q', F1 H Q' 
       /\ (local (fun H Q => exists Q', F2 H Q' /\ R (Q' tt) Q) (Q' true) Q)
       /\ Q' false ==> Q tt) -> R H Q) 
    -> R H Q).

Definition while_loop_inv (F1:~~bool) (F2:~~unit) :=
  local (fun (H:hprop) (Q:unit->hprop) => 
    exists A:Type, exists I:A->hprop, exists J:A->bool->hprop, exists lt:binary A,
      wf lt 
   /\ (exists X0, H ==> (I X0))
   /\ (forall X, F1 (I X) (J X)
              /\ F2 (J X true) (# Hexists Y, (I Y) \* [lt Y X])
              /\ J X false ==> Q tt)).

Lemma while_loop_cf_to_inv : forall (F1:~~bool) (F2:~~unit),
  while_loop_inv F1 F2 ===> while_loop_cf F1 F2.
Proof. 
  intros. apply local_weaken_body. intros H Q (A&I&J&lt&W&(X0&I0)&M).
  introv LR HR. applys* local_weaken I0. clear I0. gen X0. 
  intros X. induction_wf IH: W X.
  destruct (M X) as (M1&M2&M3).
  applys HR. exists (J X). splits~.
  apply local_erase. esplit. split. apply M2. 
  apply~ local_extract_exists. intros x.
   rewrite star_comm. apply~ CFHeaps.local_intro_prop'.
Qed. 


(********************************************************************)
(* ** Loop invariants for for-loops *)

(* todo: move *)
Definition is_local_1 A1 B (S:A1->~~B) :=
  forall x, is_local (S x).


Definition for_loop_cf (a:int) (b:int) (F:~~unit) :=
  local (fun (H:hprop) (Q:unit->hprop) => forall S:int->~~unit, is_local_1 S ->
     (forall i H Q,  
          ((i <= (b)%Z -> (local (fun H Q => exists Q', F H Q' /\ S (i+1) (Q' tt) Q) H Q))
       /\ (i > b%Z -> H ==> Q tt)) 
       -> S i H Q)
    -> S a H Q).

Definition for_loop_inv (a:int) (b:int) (F:~~unit) :=
  local (fun (H:hprop) (Q:unit->hprop) => 
      (a > (b)%Z -> H ==> (Q tt)) 
   /\ (a <= (b)%Z -> exists H', exists I,
          (H ==> I a \* H') 
       /\ (forall i, a <= i /\ i <= (b)%Z -> F (I i) (# I(i+1))) 
       /\ (I ((b)%Z+1) \* H' ==> Q tt))).

Lemma for_loop_cf_to_inv : forall (a:int) (b:int) (F:~~unit),
  for_loop_inv a b F ===> for_loop_cf a b F.
Proof. 
  intros. apply local_weaken_body. intros H Q (Mgt&Mle). introv LS HS.
  tests (a > b) as C. apply HS. split. math. auto.
  clear Mgt. specializes Mle. math. destruct Mle as (H'&I&M1&M2&M3).
  applys~ (@local_wframe unit) (# I (b+1)); [| intros u; destruct~ u ]. (*todo*)
  clear M1. asserts L: (a <= a <= b+1). math. generalize L.
  set (a' := a) at 1. generalize a as i. unfold a'.
  intros i. induction_wf IH: (int_upto_wf (b+1)) i. intros Bnd.
  applys HS. split; intros C'.
    apply local_erase. esplit. split.
      apply M2; auto with maths.
      forwards: IH (i+1); auto with maths.
    math_rewrite~ (i = b +1).
Qed. 




