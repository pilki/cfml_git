Set Implicit Arguments.
Require Export LibCore LibEpsilon Shared.
Require Export CFHeaps.


Notation "h1 \+ h2" := (heap_union h1 h2)
   (at level 51, right associativity).

Lemma heap_union_assoc : forall h1 h2 h3,
  \# h1 h2 h3 -> h1 \+ (h2 \+ h3) = (h1 \+ h2) \+ h3.
Proof. skip. Qed.


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


Lemma heap_disjoint_union_inv' : forall h1 h2 h3,
  \# (heap_union h2 h3) h1 = (\# h2 h1 /\ \# h3 h1).
Proof. skip. Qed.

Lemma heaps_disjoint_3 : forall h1 h2 h3,
  \# h1 h2 h3 = (\# h1 h2 /\ \# h2 h3 /\ \# h1 h3).
Proof. skip. Qed.

Hint Rewrite 
  heap_disjoint_union_inv 
  heap_disjoint_union_inv'
  heaps_disjoint_3 : rew_disjoint.

Tactic Notation "rew_disjoint" :=
  autorewrite with rew_disjoint in *.
Tactic Notation "rew_disjoint" "*" :=
  rew_disjoint; auto_star.

Lemma app_local_1 : forall B A1 (x1:A1) f,
  is_local (app_1 (B:=B) f x1).
Proof.
  asserts Hint1: (forall h1 h2, \# h1 h2 -> \# h2 h1).
    intros. rewrite~ heap_disjoint_comm.
  asserts Hint2: (forall h1 h2 h3, \# h1 h2 -> \# h1 h3 -> \# h1 (heap_union h2 h3)).
    intros. rewrite* heap_disjoint_union_inv.
  asserts Hint3: (forall h1 h2 h3, \# h1 h2 -> \# h2 h3 -> \# h1 h3 -> \# h1 h2 h3) .
    intros. rewrite~ heaps_disjoint_3.
  intros. extens. intros H Q. iff M. apply~ local_erase.
  introv Dhi Hh. destruct (M h Hh) as (H1&H2&Q'&H'&D12&N&HQ).
  destruct D12 as (h1&h2&?&?&?&?).
  destruct~ (N h1 (heap_union i h2)) as (v'&h1'&i'&?&HQ'&E).
  subst h. rew_disjoint*.
  sets h': (heap_union h1' h2).
  forwards Hh': (HQ v' h'). subst h'. exists___. splits~. rew_disjoint*.
  destruct Hh' as (h3'&h4'&?&?&?&?).
     asserts Hint4: (forall h : heap, \# h h1' -> \# h h2 -> \# h h3'). skip. 
     asserts Hint5: (forall h : heap, \# h h1' -> \# h h2 -> \# h h4'). skip.
  exists v' h3' (heap_union h4' i'). splits.
    subst h h'. rew_disjoint*.
    auto.
    subst h h'. rew_disjoint. intuition. applys_eq E 1 3.
      rewrite* <- heap_union_assoc. rewrite~ (heap_union_comm h2).
      rewrite* <- heap_union_assoc. rewrite heap_union_assoc; [ | apply* Hint3 ].
      rewrite <- H8. rewrite* <- heap_union_assoc. rewrite (heap_union_comm i).
      rewrite* (@heap_union_assoc i'). rewrite (heap_union_comm i' h2).
      rewrite* <- heap_union_assoc.
Qed.






(********************************************************************)
(* ** Interaction between AppPure and AppReturns *)

(** From AppPure to AppReturns *)

Lemma pureapp_to_app : forall A B (F:val) (V:A) (P:B->Prop),
  pureapp F V P -> app_1 F V [] \[P].
Proof.
  introv (v'&N). introv Dhi Hh. exists v' heap_empty heap_empty. splits.
  skip. (* heap_disjoint heap_empty *)
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

Lemma pureapp_and_app : forall A B (F:val) (V:A) (V':B) (H:hprop) (Q:B->hprop) h,
  pureapp F V (= V') -> app_1 F V H Q -> H h -> exists H', (Q V' \* H') h.  (* H ==> Q V' \* H' *)
Proof.
  introv (V''&N) M Hh. destruct (N h) as (HE&?). clear N.
  subst. hnf in M. destruct (M h heap_empty) as (V''&h1&h2&?&HQ&HE'). 
    skip. (* disjoint *)
    auto.
    do 2 rewrite heap_union_neutral_r in HE'.
    forwards [? R]: (eval_deterministic HE HE'). exists (=h2). subst.
    destructs H0. exists h1 h2. splits~. skip. (* disjoint *)
Qed.





(********************************************************************)
(* ** OLD Axioms *)

(** The type Func *)

Axiom val : Type. 

(** The type Func is inhabited *)

Axiom val_inhab : Inhab val. 
Existing Instance val_inhab.

(** The predicate AppReturns *)

Axiom app_1 : forall A B,  
  val -> A -> hprop -> (B -> hprop) -> Prop.

(** The predicate AppPure *)

Axiom pureapp : forall A B,  
  val -> A -> (B -> Prop) -> Prop.

(** AppReturns is a local property *)

Axiom app_local_1 : forall B A1 (x1:A1) f,
  is_local (app_1 (B:=B) f x1). 

(** AppPure satisfies the witness property *)

Axiom pureapp_concrete : forall A B (F:val) (V:A) (P:B->Prop),
  pureapp F V P <-> exists V', P V' /\ pureapp F V (= V').

(** AppPure satisfies the determinacy property *)

Axiom pureapp_deterministic : forall A B (F:val) (V:A) (V1' V2':B),
  pureapp F V (= V1') -> pureapp F V (= V2') -> V1' = V2'.          

(** From AppPure to AppReturns *)

Axiom pureapp_to_app : forall A B (F:val) (V:A) (P:B->Prop),
  pureapp F V P -> app_1 F V [] \[P].
  (* Could also be stated: [pureapp F V ==> pure (app_1 F V)] *)

(** Overlapping of AppPure and AppReturns *)

Axiom pureapp_and_app : forall A B (F:val) (V:A) (V':B) (H:hprop) (Q:B->hprop),
  pureapp F V (= V') -> app_1 F V H Q -> (H ==> Q V').


(********************************************************************)
(* ** Immediate corrolaries *)

Hint Resolve app_local_1.





(** TODO; move Extraction of premisses from [local] *)

Lemma local_intro_prop : forall B (F:~~B) (H:hprop) (P:Prop) Q,
  is_local F -> (forall h, H h -> P) -> (P -> F H Q) -> F H Q.
Proof.
  introv L W M. rewrite L. introv Hh. forwards~: (W h).
  exists H [] Q []. splits; rew_heap~.
Qed. 
(*
Lemma app_intro_prop_1 : forall (U:Prop) A B (F:val) (V:A) (H:hprop) (Q:B->hprop),
  (H ==> [U]) -> (U -> app_1 F V H Q) -> app_1 F V H Q.
Proof.
  introv W M. eapply local_intro_prop.
Qed.
*)

(********************************************************************)
(* ** Applications of higher arity *)


Definition app_2 A1 A2 B f (x1:A1) (x2:A2) :=
  local (fun H (Q:B->hprop) =>
    exists Q', app_1 f x1 H Q' 
            /\ forall g, app_1 g x2 (Q' g) Q).

(*  forall h, H h ->
  exists H1 H2 Q1, 
     (H1 \* H2) h 
  /\ app_1 f x1 H1 Q1 
  /\ forall g, app_1 g x2 (Q1 g \* H2) Q.
*)

(*
  forall h, H h ->
  exists Q', app_1 f x1 H Q' 
          /\ forall g, app_1 g x2 (Q' g) Q.
*)
Definition app_3 A1 A2 A3 B f (x1:A1) (x2:A2) (x3:A3) (H:hprop) (Q:B->hprop) := 
  exists Q', app_1 f x1 H Q' 
          /\ forall g, app_2 g x2 x3 (Q' g) Q.

Definition app_4 A1 A2 A3 A4 B f (x1:A1) (x2:A2) (x3:A3) (x4:A4) (H:hprop) (Q:B->hprop) := 
  exists Q', app_1 f x1 H Q' 
          /\ forall g, app_3 g x2 x3 x4 (Q' g) Q.


(********************************************************************)
(* ** Locality of app_n *)

Lemma app_local_2 : forall B A1 A2 (x1:A1) (x2:A2) f,
  is_local (app_2 (B:=B) f x1 x2).
Proof. intros. apply local_is_local. Qed.

(*
Proof.
  intros. extens. intros H Q. iff M.
  apply~ local_erase.
  introv Hh. destruct (M _ Hh) as (H1&H2&Q1&H'&R&N&?).
  lets (h1&h2&?&?&?&?): R. clear R.
  destruct~ (N h1) as (H1'&H2'&Q1'&?&?&?).
  exists H1' (H2 \* H2') Q1'.
  splits~. rewrite (star_comm H2). rewrite star_assoc. exists h1 h2. splits~.
  intros g. specializes H9 g.
  rewrite (star_comm H2). rewrite star_assoc.
  apply* local_wgframe.
Qed.
*)
(*
  introv Hh. destruct (M _ Hh) as (H1&H2&Q1&H'&R&N&?).
  destruct R as (h1&h2&?&?&?&?).
  destruct~ (N h1) as (Q'&?&?).
  exists (Q' \*+ H2). split.
  rewrite app_local_1. introv Hh'.
  apply* local_wframe.
*)

(*
  destruct M as (H1&H2&Q1&H'&?&(Qg&?&Hg)&?).
  exists (fun g => Qg g ** H2). splits.
    apply* local_frame.
    intros. specializes Hg g. apply* local_elim.
*)


Lemma app_local_3 : forall B A1 A2 A3 (x1:A1) (x2:A2) (x3:A3) f,
  is_local (app_3 (B:=B) f x1 x2 x3).
Admitted.

Lemma app_local_4 : forall B A1 A2 A3 A4 (x1:A1) (x2:A2) (x3:A3) (x4:A4) f,
  is_local (app_4 (B:=B) f x1 x2 x3 x4).
Admitted.

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
Proof. introv M1 M2 Hh. exists H [] Q []. splits; rew_heap*. Qed.

Lemma app_intro_1_3 : 
  app_1 f x1 H Q' ->
  (forall g, app_2 g x2 x3 (Q' g) Q) ->
  app_3 f x1 x2 x3 H Q.
Proof. Admitted.

Lemma app_intro_1_4 : 
  app_1 f x1 H Q' ->
  (forall g, app_3 g x2 x3 x4 (Q' g) Q) ->
  app_4 f x1 x2 x3 x4 H Q.
Proof. Admitted.

Lemma app_intro_2_3 : 
  app_2 f x1 x2 H Q' ->
  (forall g, app_1 g x3 (Q' g) Q) ->
  app_3 f x1 x2 x3 H Q.
Proof. Admitted.
(*
  introv M1 M2 Hh. exists H [] Q [].
  introv (Q1&M1&M2) M. exists Q1. split~.
  intros g. exists~ Q'. 
*)

Lemma app_intro_2_4 : 
  app_2 f x1 x2 H Q' ->
  (forall g, app_2 g x3 x4 (Q' g) Q) ->
  app_4 f x1 x2 x3 x4 H Q.
Proof. Admitted.
(*
Proof. 
  introv (Q1&M1&M2) M. exists Q1. split~.
  intros g. exists~ Q'. 
Qed.
*)

Lemma app_intro_3_4 : 
  app_3 f x1 x2 x3 H Q' ->
  (forall g, app_1 g x4 (Q' g) Q) ->
  app_4 f x1 x2 x3 x4 H Q.
Proof. Admitted.

(*
Proof. 
  introv (Q1&M1&M2) M. exists Q1. split~.
  intros g. destruct (M2 g) as (Q2&M3&M4).
  exists Q2. split~. intros g'. exists~ Q'.
Qed.
*)

End AppIntro.


(********************************************************************)
(* ** Introduction lemmas *)

(* todo move *)
Lemma local_weaken_pre : forall H' B (F:~~B) H Q,
  is_local F -> 
  F H' Q -> 
  H ==> H' -> 
  F H Q.
Proof. intros. apply* local_weaken. Qed.

Lemma spec_intro_1 : forall A1 B f (K:A1->~~B->Prop),
  is_spec_1 K ->
  curried_1 A1 B f ->
  (forall x1, K x1 (app_1 f x1)) ->
  spec_1 K f.
Proof. introv S _ H. split~. Qed.



Axiom pureapp_and_app' : forall A B (F:val) (V:A) (V':B) (H:hprop) (Q:B->hprop) h,
  pureapp F V (= V') -> app_1 F V H Q -> H h -> exists H', (Q V' \* H') h. 

Lemma spec_intro_2 : forall A1 A2 B f (K:A1->A2->~~B->Prop),
  is_spec_2 K ->
  curried_2 A1 A2 B f ->
  (forall x1 x2, K x1 x2 (app_2 f x1 x2)) ->
  spec_2 K f.
Proof.
  introv I C HK. split~.
  intros x1. destruct (pureapp_witness (proj2 C x1)) as [g [_ Hg]].
  apply* pureapp_abstract. split~. intros x2. eapply I.
  apply HK.
  intros H Q M.
  rewrite app_local_1. introv Hh.
  destruct (M _ Hh) as (H1&H2&Q1&H'&?&N&?).
  destruct N as (Q'&Ap1&Ap2).
  specializes Ap2 g. 
(*
  lets (h1&h2&?&?&?&?): H0.
  forwards~ (HG&WH): (pureapp_and_app' h1 Hg Ap1).
  exists H1 H2. exists Q1 (H' \* HG). splits~.
  apply* local_weaken_pre.
  skip.
  intros r. 
*)

  lets WH: (pureapp_and_app Hg Ap1). (* todo : bug forwards ? *)  
  exists H1 H2. exists Q1 H'. splits~.
  apply* local_weaken_pre.

Qed. 

(*
  intros H Q (Q'&Ap1&Ap2). 
  lets WH: (pureapp_and_app Hg Ap1). (* todo : bug forwards ? *)
  apply* local_weaken.
Qed.
*)

Lemma spec_intro_3 : forall A1 A2 A3 B f (K:A1->A2->A3->~~B->Prop),
  is_spec_3 K ->
  curried_3 A1 A2 A3 B f ->
  (forall x1 x2 x3, K x1 x2 x3 (app_3 f x1 x2 x3)) ->
  spec_3 K f.
Proof.
Admitted.
(*
  introv I C HK. split~. split. intros_all~. intros x1.
  destruct (app_1_witness (proj2 C x1)) as [g [Cg Hg]].
  apply* app_1_abstract. split~. split. intros_all~. intros x2.
  destruct (app_1_witness (proj2 Cg x2)) as [h [_ Hh]]. 
  apply* app_1_abstract. split. apply I. intros x3. eapply I.
  apply HK. intros P HP. pattern h. apply* app_1_join.
  pattern g. apply* app_1_join.
Qed.
*)

Lemma spec_intro_4 : forall A1 A2 A3 A4 B f (K:A1->A2->A3->A4->~~B->Prop),
  is_spec_4 K ->
  curried_4 A1 A2 A3 A4 B f ->
  (forall x1 x2 x3 x4, K x1 x2 x3 x4 (app_4 f x1 x2 x3 x4)) ->
  spec_4 K f.
Proof.
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
  lets: ((proj2 Pg) x2). apply* (proj1 S). intros H' Q Ap1.
  applys app_intro_1_2 (fun g' => [g'=g] \* H'). 
    apply* pureapp_app_1. 
    intros g'. apply~ CFHeaps.local_intro_prop. intro_subst~.
Qed.    

(*

  introv S. intros. destruct (pureapp_witness ((proj22 S) x1)) as [g [Pg Hg]].
  lets: ((proj2 Pg) x2). apply* (proj1 S). intros H' Q Ap1.
  exists (fun g' => [g'=g] \* H'). split. apply* pureapp_app_1. 
   intros g'.
   apply (@app_pre_1 (g'=g)).
   skip. (* tactic for heaps: [g' = g] ** H' ==> [g' = g] *)
   intro_subst.
   eapply local_weaken with (H':=H'); eauto. 
    skip. (* tactics for heaps: [g = g] ** H' ==> H' *)
*)

Lemma spec_elim_3 : forall A1 A2 A3 B (K: A1 -> A2 -> A3 -> ~~B -> Prop) f,
  spec_3 K f -> forall x1 x2 x3, K x1 x2 x3 (app_3 f x1 x2 x3).
Proof.
Admitted.

Lemma spec_elim_4 : forall A1 A2 A3 A4 B (K: A1 -> A2 -> A3 -> A4 -> ~~B -> Prop) f,
  spec_4 K f -> forall x1 x2 x3 x4, K x1 x2 x3 x4 (app_4 f x1 x2 x3 x4).
Proof.
Admitted.


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

(*
intros. destruct H as [I Ap1].
specializes Ap1 x1.
eapply app_intro_1_2.
apply~ pureapp_app_1. eauto.
intros g.
rew_heap.
apply~ app_pre_1.
intros M.
eapply local_weaken with (H':=[]). auto.
forwards: (spec_elim_2_1 M). eapply H.
skip. (* todo: heaps ==> *)
auto.
*)

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
Proof. skip. Qed. (*todo: cf spec_elim_3_2 *)

Lemma spec_elim_4_3 : forall A1 A2 A3 A4 B (K: A1 -> A2 -> A3 -> A4 -> ~~B -> Prop) f,
  spec_4 K f -> forall x1 x2 x3 (P : val->Prop),
  app_3 f x1 x2 x3 [] \[spec_1 (K x1 x2 x3)].
Proof. skip. Qed. (*todo: cf spec_elim_3_2 *)

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

Definition post_for (h:heap) B (R:~~B) :=
  fun (H:hprop) (Q:B->hprop) => H h -> R H Q.

Lemma spec_induction_1 : 
  forall A1 B (lt:binary (heap*A1)),
  forall (Wf: wf lt) f (K:A1->~~B->Prop),
  spec_1 (fun x R => forall h,
    spec_1 (fun x' R' => forall h', lt (h',x') (h,x) -> K x' (post_for h' R')) f ->
    K x (post_for h R)) f ->
  spec_1 K f.
Admitted.
(*
Proof.
  introv W H.
  cuts I: (forall x, weakenable (K x) /\ K x (app_1 f x)).
    apply spec_intro_1. 
      intros x. apply (proj1 (I x)).
      apply* spec_curried_1.
      intros x. destruct~ (I x).
  intros x. pattern x. induction_wf IH: W x.
  lets C: (spec_curried_1 H). 
  lets I: (spec_is_spec_1 H x).
  lets S: (spec_elim_1 H x). clear H. 
  asserts M: (spec_1 (fun x' R' => lt x' x -> K x' R') f). split.
    intros x'. introv HK HP Lt. applys~ (proj1 (IH _ Lt)).
    intros x' Lt. apply (proj2 (IH _ Lt)).
  split.
    introv HK HP. applys~ (I P P').
    apply~ S.
Qed.

Lemma spec_induction_2 : 
  forall A1 A2 B (lt:(A1*A2)->(A1*A2)->Prop),
  forall (Wf: wf lt) f (K:A1->A2->~~B->Prop),
  spec_2 (fun x1 x2 R => 
    spec_2 (fun y1 y2 R' => lt (y1,y2) (x1,x2) -> K y1 y2 R') f ->
    K x1 x2 R) f ->
  spec_2 K f.
Proof.
  introv W H.
  cuts I: (forall p : A1*A2, let (x,y) := p in
           weakenable (K x y) /\ K x y (app_2 f x y)).
    apply spec_intro_2. 
      intros x y. apply (proj1 (I (x,y))).
      apply* spec_curried_2.
      intros x y. destruct~ (I (x,y)).
  intros p. pattern p. induction_wf IH: W p. destruct p as [x y].
  lets C: (spec_curried_2 H). 
  lets I: (spec_is_spec_2 H x y).
  lets S: (spec_elim_2 H x y). clear H. 
  asserts M: (spec_2 (fun x' y' R' => lt (x',y') (x,y) -> K x' y' R') f). split.
    intros x' y'. introv HK HP Lt. applys~ (proj1 (IH _ Lt)).
    apply spec_intro_weak_2.
      intros x' y'. introv HK WR Lt. applys~ (proj1 (IH _ Lt)).
      auto.
      intros x' y' Lt. apply (proj2 (IH _ Lt)).
  split.
    introv HK HP. applys~ (I P P').
    apply~ S.
Qed.

Lemma spec_induction_3 : 
  forall A1 A2 A3 B (lt:(A1*A2*A3)->(A1*A2*A3)->Prop) (Wf: wf lt) f 
         (K:A1->A2->A3->~~B->Prop),
  spec_3 (fun x1 x2 x3 R => 
    spec_3 (fun y1 y2 y3 R' => lt (y1,y2,y3) (x1,x2,x3) -> K y1 y2 y3 R') f ->
    K x1 x2 x3 R) f ->
  spec_3 K f.
Proof.
  introv W H.
  cuts I: (forall p : A1*A2*A3, let '((x,y),z) := p in 
           weakenable (K x y z) /\ K x y z (app_3 f x y z)).
    apply spec_intro_3. 
      intros x y z. apply (proj1 (I (x,y,z))).
      apply* spec_curried_3.
      intros x y z. destruct~ (I (x,y,z)).
  intros p. pattern p. induction_wf IH: W p. destruct p as [[x y] z].
  lets C: (spec_curried_3 H). 
  lets I: (spec_is_spec_3 H x y z).
  lets S: (spec_elim_3 H x y z). clear H. 
  asserts M: (spec_3 (fun x' y' z' R' => lt (x',y',z') (x,y,z) -> K x' y' z' R') f). split.
    intros x' y' z'. introv HK HP Lt. applys~ (proj1 (IH _ Lt)).
    apply spec_intro_weak_3.
      intros x' y' z'. introv HK WR Lt. applys~ (proj1 (IH _ Lt)).
      auto.
      intros x' y' z' Lt. apply (proj2 (IH _ Lt)).
  split.
    introv HK HP. applys~ (I P P').
    apply~ S.
Qed.

Lemma spec_induction_4 : 
  forall A1 A2 A3 A4 B (lt:(A1*A2*A3*A4)->(A1*A2*A3*A4)->Prop) (Wf: wf lt) f 
         (K:A1->A2->A3->A4->~~B->Prop),
  spec_4 (fun x1 x2 x3 x4 R => 
    spec_4 (fun y1 y2 y3 y4 R' => lt (y1,y2,y3,y4) (x1,x2,x3,x4) -> K y1 y2 y3 y4 R') f ->
    K x1 x2 x3 x4 R) f ->
  spec_4 K f.
Proof.
  introv W H.
  cuts I: (forall p : A1*A2*A3*A4, let '(((x,y),z),t) := p in
           weakenable (K x y z t) /\ K x y z t (app_4 f x y z t)).
    apply spec_intro_4. 
      intros x y z t. apply (proj1 (I (x,y,z,t))).
      apply* spec_curried_4.
      intros x y z t. destruct~ (I (x,y,z,t)).
  intros p. pattern p. induction_wf IH: W p. destruct p as [[[x y] z] t].
  lets C: (spec_curried_4 H). 
  lets I: (spec_is_spec_4 H x y z t).
  lets S: (spec_elim_4 H x y z t). clear H. 
  asserts M: (spec_4 (fun x' y' z' t' R' => lt (x',y',z',t') (x,y,z,t) -> K x' y' z' t' R') f). split.
    intros x' y' z' t'. introv HK HP Lt. applys~ (proj1 (IH _ Lt)).
    apply spec_intro_weak_4.
      intros x' y' z' t'. introv HK WR Lt. applys~ (proj1 (IH _ Lt)).
      auto.
      intros x' y' z' t' Lt. apply (proj2 (IH _ Lt)).
  split.
    introv HK HP. applys~ (I P P').
    apply~ S.
Qed.

*)

(********************************************************************)
(* ** Lemmas for other tactics *)

Hint Resolve local_is_local.

Notation "\= V" := (fun X => [X = V])
  (at level 40) : heap_scope.

Lemma xret_lemma : forall B (v:B) H (Q:B->hprop),
  (\= v \*+ H) ===> Q -> 
  local (fun H Q => H heap_empty /\ Q v heap_empty) H Q.
Proof.  
  introv W. applys local_wframe B [] H (\= v). (* todo: instantiate *)
  simpls. auto.
  apply local_erase. split. reflexivity. hnfs~. hsimpl. auto.
Qed.

Lemma xframe_lemma : forall H1 H2 B Q1 (F:~~B) H Q,
  is_local F -> 
  H ==> H1 \* H2 -> 
  F H1 Q1 -> 
  Q1 \*+ H2 ===> Q ->
  F H Q.
Proof. intros. apply* local_wframe. Qed.


(*move*)

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

Lemma xchange_lemma : forall H1 H1' H2 B H Q (F:~~B),
  is_local F -> (H1 ==> H1') -> (H ==> H1 \* H2) -> F (H1' \* H2) Q -> F H Q.
Proof.
  introv W1 L W2 M. applys local_wframe __ []; eauto.
  hsimpl. hchange~ W2. rew_heap~. 
Qed.








