Set Implicit Arguments.
Require Export LibCore LibEpsilon Shared.


(********************************************************************)
(* ** Axioms *)

(* The type Func *)

Axiom val : Type. 

(* The type Func is inhabited *)

Axiom val_inhab : Inhab val. 
Existing Instance val_inhab.

(* The predicate AppReturns *)

Axiom app_1 : forall A1 B,  
  val -> A1 -> (B -> Prop) -> Prop.

(* AppReturns satisfies the witness property (see appendix) *)

Axiom app_1_concrete : forall A B (F:val) (V:A) (P:B->Prop),
  app_1 F V P <-> exists V', P V' /\ app_1 F V (= V').

(*AppReturns satisfies the determinacy property (see appendix)  *)

Axiom app_1_deterministic : forall A B (F:val) (V:A) (V1' V2':B),
  app_1 F V (= V1') -> app_1 F V (= V2') -> V1' = V2'.          


(********************************************************************)
(* ** Corrolaries *)

Lemma app_1_witness : forall A B (F:val) (V:A) (P:B->Prop),
  app_1 F V P -> exists V', P V' /\ app_1 F V (= V').
Proof. intros. apply* app_1_concrete. Qed.

Lemma app_1_abstract : forall A B (F:val) (V:A) (V':B) (P:B->Prop),
  app_1 F V (= V') -> P V' -> app_1 F V P.
Proof. intros. apply* app_1_concrete. Qed.

Lemma app_1_join : forall A B (F:val) (V:A) (V':B) (P:B->Prop),
  app_1 F V (= V') -> app_1 F V P -> P V'.    
Proof.
  introv HE1 H. lets [V'' [HP HE2]]: (app_1_witness H). subst.
  replace V' with V''. auto. apply* app_1_deterministic.
Qed.


(********************************************************************)
(* ** Weakenable predicates *)

Definition weakenable A (R:(A->Prop)->Prop) :=
  forall P P', R P -> P ==> P' -> R P'.


(********************************************************************)
(* ** Applications *)

Definition app_2 A1 A2 B f (x1:A1) (x2:A2) (P:B->Prop) := 
  app_1 f x1 (fun g => app_1 g x2 P).

Definition app_3 A1 A2 A3 B f (x1:A1) (x2:A2) (x3:A3) (P:B->Prop) := 
  app_1 f x1 (fun g => app_2 g x2 x3 P).

Definition app_4 A1 A2 A3 A4 B f (x1:A1) (x2:A2) (x3:A3) (x4:A4) (P:B->Prop) := 
  app_1 f x1 (fun g => app_3 g x2 x3 x4 P).

(********************************************************************)
(* ** Weakening *)

Lemma app_weaken_1 : forall B (P: B->Prop) A1 (x1:A1) f,
  app_1 f x1 P -> forall P', P ==> P' -> app_1 f x1 P'.
Proof.
  introv HA HP. destruct (app_1_witness HA) as [V [PV HV]].
  apply* app_1_abstract.
Qed.

Lemma app_weaken_2 :
  forall B (P: B->Prop) A1 A2 (x1:A1) (x2:A2) f,
  app_2 f x1 x2 P -> forall P', P ==> P' -> app_2 f x1 x2 P'.
Proof. 
  introv H W. unfolds app_2. apply (app_weaken_1 H).
  introv G. apply~ (app_weaken_1 G). 
Qed.

Lemma app_weaken_3 :
  forall B (P: B->Prop) A1 A2 A3 (x1:A1) (x2:A2) (x3:A3) f,
  app_3 f x1 x2 x3 P -> forall P', P ==> P' -> app_3 f x1 x2 x3 P'.
Proof. 
  introv H W. unfolds app_3. apply (app_weaken_1 H).
  introv G. apply~ (app_weaken_2 G). 
Qed.

Lemma app_weaken_4 :
  forall B (P: B->Prop) A1 A2 A3 A4 (x1:A1) (x2:A2) (x3:A3) (x4:A4) f,
  app_4 f x1 x2 x3 x4 P -> forall P', P ==> P' -> app_4 f x1 x2 x3 x4 P'.
Proof. 
  introv H W. unfolds app_4. apply (app_weaken_1 H).
  introv G. apply~ (app_weaken_3 G). 
Qed.

(********************************************************************)
(* ** Valid specifications *)

Notation "'~~' A" := ((A->Prop)->Prop) 
  (at level 8, only parsing) : type_scope.

Definition is_spec_1 A1 B (K:A1->~~B->Prop) :=
  forall x, weakenable (K x).

Definition is_spec_2 A1 A2 B (K:A1->A2->~~B->Prop) :=
  forall x, is_spec_1 (K x).

Definition is_spec_3 A1 A2 A3 B (K:A1->A2->A3->~~B->Prop) :=
  forall x, is_spec_2 (K x).

Definition is_spec_4 A1 A2 A3 A4 B (K:A1->A2->A3->A4->~~B->Prop) :=
  forall x, is_spec_3 (K x).

(********************************************************************)
(* ** Specification predicate *)

Definition spec_1 A1 B (K: A1 -> ~~B -> Prop) f :=
  is_spec_1 K /\ forall x1, K x1 (app_1 f x1).

Definition total_1 A1 B (Q: A1 -> B -> Prop) :=
  spec_1 (fun x1 R => R (Q x1)).

Definition spec_2 A1 A2 B (K: A1 -> A2 -> ~~B -> Prop) f :=
  is_spec_2 K /\ total_1 (fun x1 => spec_1 (K x1)) f.

Definition total_2 A1 A2 B (Q: A1 -> A2 -> B -> Prop) :=
  total_1 (fun x1 => total_1 (Q x1)).

Definition spec_3 A1 A2 A3 B (K: A1 -> A2 -> A3 -> ~~B -> Prop) f :=
  is_spec_3 K /\ total_1 (fun x1 => spec_2 (K x1)) f.

Definition total_3 A1 A2 A3 B (Q: A1 -> A2 -> A3 -> B -> Prop) :=
  total_1 (fun x1 => total_2 (Q x1)).

Definition spec_4 A1 A2 A3 A4 B (K: A1 -> A2 -> A3 -> A4 -> ~~B -> Prop) f :=
  is_spec_4 K /\ total_1 (fun x1 => spec_3 (K x1)) f.

Definition total_4 A1 A2 A3 A4 B (Q: A1 -> A2 -> A3 -> A4 -> B -> Prop) :=
  total_1 (fun x1 => total_3 (Q x1)).

(********************************************************************)
(* ** Curried functions *)

Definition curried_1 (f:val) := 
  True.

Definition curried_2 (A1:Type) f := 
  total_1 (fun (x1:A1) (y:val) => True) f.

Definition curried_3 (A1 A2:Type) f := 
  total_2 (fun (x1:A1) (x2:A2) (y:val) => True) f.

Definition curried_4 (A1 A2 A3:Type) f := 
  total_3 (fun (x1:A1) (x2:A2) (x3:A3) (y:val) => True) f.

(********************************************************************)
(* ** Introduction lemmas *)

Lemma spec_intro_1 : forall A1 B f (K:A1->~~B->Prop),
  is_spec_1 K ->
  curried_1 f ->
  (forall x1, K x1 (app_1 f x1)) ->
  spec_1 K f.
Proof. introv S _ H. split~. Qed.

Lemma spec_intro_2 : forall A1 A2 B f (K:A1->A2->~~B->Prop),
  is_spec_2 K ->
  curried_2 A1 f ->
  (forall x1 x2, K x1 x2 (app_2 f x1 x2)) ->
  spec_2 K f.
Proof.
  introv I C HK. split~. split. intros_all~. intros x1.
  destruct (app_1_witness (proj2 C x1)) as [g [_ Hg]].
  apply* app_1_abstract. split~. intros x2. eapply I.
  apply HK. intros P HP. pattern g. apply* app_1_join.
Qed.

Lemma spec_intro_3 : forall A1 A2 A3 B f (K:A1->A2->A3->~~B->Prop),
  is_spec_3 K ->
  curried_3 A1 A2 f ->
  (forall x1 x2 x3, K x1 x2 x3 (app_3 f x1 x2 x3)) ->
  spec_3 K f.
Proof.
  introv I C HK. split~. split. intros_all~. intros x1.
  destruct (app_1_witness (proj2 C x1)) as [g [Cg Hg]].
  apply* app_1_abstract. split~. split. intros_all~. intros x2.
  destruct (app_1_witness (proj2 Cg x2)) as [h [_ Hh]]. 
  apply* app_1_abstract. split. apply I. intros x3. eapply I.
  apply HK. intros P HP. pattern h. apply* app_1_join.
  pattern g. apply* app_1_join.
Qed.

Lemma spec_intro_4 : forall A1 A2 A3 A4 B f (K:A1->A2->A3->A4->~~B->Prop),
  is_spec_4 K ->
  curried_4 A1 A2 A3 f ->
  (forall x1 x2 x3 x4, K x1 x2 x3 x4 (app_4 f x1 x2 x3 x4)) ->
  spec_4 K f.
Proof.
  introv I C HK. split~. split. intros_all~. intros x1.
  destruct (app_1_witness (proj2 C x1)) as [g [Cg Hg]].
  apply* app_1_abstract. split~. split. intros_all~. intros x2.
  destruct (app_1_witness (proj2 Cg x2)) as [h [Ch Hh]]. 
  apply* app_1_abstract. split. apply (I x1 x2). 
   split. intros_all~. intros x3.
  destruct (app_1_witness (proj2 Ch x3)) as [i [_ Hi]]. 
  apply* app_1_abstract. split. apply I. intros x4. eapply I.
  apply HK. intros P HP. pattern i. apply* app_1_join.
  pattern h. apply* app_1_join. pattern g. apply* app_1_join.
Qed.

(********************************************************************)
(* ** Elimination lemmas *)

Lemma spec_elim_1 : forall A1 B (K: A1 -> ~~B -> Prop) f,
  spec_1 K f -> forall x1, K x1 (app_1 f x1).
Proof. introv [S H]. auto. Qed.

Lemma spec_elim_2 : forall A1 A2 B (K: A1 -> A2 -> ~~B -> Prop) f,
  spec_2 K f -> forall x1 x2, K x1 x2 (app_2 f x1 x2).
Proof.
  introv S. intros. destruct (app_1_witness ((proj33 S) x1)) as [g [Pg Hg]].
  lets: ((proj2 Pg) x2). apply* (proj1 S). intros P HP. apply* app_1_abstract.
Qed.

Lemma spec_elim_3 : forall A1 A2 A3 B (K: A1 -> A2 -> A3 -> ~~B -> Prop) f,
  spec_3 K f -> forall x1 x2 x3, K x1 x2 x3 (app_3 f x1 x2 x3).
Proof.
  introv S. intros. destruct (app_1_witness ((proj33 S) x1)) as [g [Pg Hg]].
  destruct (app_1_witness ((proj33 Pg) x2)) as [h [Ph Hh]].
  lets: ((proj2 Ph) x3). apply* (proj1 S). intros P HP.
  apply* app_1_abstract. apply* app_1_abstract.
Qed.

Lemma spec_elim_4 : forall A1 A2 A3 A4 B (K: A1 -> A2 -> A3 -> A4 -> ~~B -> Prop) f,
  spec_4 K f -> forall x1 x2 x3 x4, K x1 x2 x3 x4 (app_4 f x1 x2 x3 x4).
Proof.
  introv S. intros. destruct (app_1_witness ((proj33 S) x1)) as [g [Pg Hg]].
  destruct (app_1_witness ((proj33 Pg) x2)) as [h [Ph Hh]].
  destruct (app_1_witness ((proj33 Ph) x3)) as [i [Pi Hi]].
  lets: ((proj2 Pi) x4). apply* (proj1 S). intros P HP.
  apply* app_1_abstract. apply* app_1_abstract. apply* app_1_abstract. 
Qed.

(********************************************************************)
(* ** Weakenability of app *)

Lemma app_weakenable_1 : forall A1 B f x1,
  weakenable (@app_1 A1 B f x1).
Proof. intros_all. apply~ (app_weaken_1 H). Qed.

Lemma app_weakenable_2 : forall A1 A2 B f x1 x2,
  weakenable (@app_2 A1 A2 B f x1 x2).
Proof.
   intros_all. apply (app_weaken_1 H). 
   intros_all. applys* app_weakenable_1.
Qed.

Lemma app_weakenable_3 : forall A1 A2 A3 B f x1 x2 x3,
  weakenable (@app_3 A1 A2 A3 B f x1 x2 x3).
Proof.
   intros_all. apply (app_weaken_1 H). 
   intros_all. applys* app_weakenable_2.
Qed.

Lemma app_weakenable_4 : forall A1 A2 A3 A4 B f x1 x2 x3 x4,
  weakenable (@app_4 A1 A2 A3 A4 B f x1 x2 x3 x4).
Proof.
   intros_all. apply (app_weaken_1 H). 
   intros_all. applys* app_weakenable_3.
Qed.

Hint Resolve app_weakenable_1 app_weakenable_2 
  app_weakenable_3 app_weakenable_4.


(********************************************************************)
(* ** Change of arities in applications *)

Section AppIntro.
Variables (A1 A2 A3 A4 B : Type) (f : val).
Variables (x1:A1) (x2:A2) (x3:A3) (x4:A4).

Lemma app_intro_1_2 : forall (P:B->Prop),
  app_1 f x1 (fun g => app_1 g x2 P) ->
  app_2 f x1 x2 P.
Proof. auto. Qed.

Lemma app_intro_1_3 : forall (P:B->Prop),
  app_1 f x1 (fun g => app_2 g x2 x3 P) ->
  app_3 f x1 x2 x3 P.
Proof. auto. Qed.

Lemma app_intro_1_4 : forall (P:B->Prop),
  app_1 f x1 (fun g => app_3 g x2 x3 x4 P) ->
  app_4 f x1 x2 x3 x4 P.
Proof. auto. Qed.

Lemma app_intro_2_1 : forall (P:B->Prop),
  app_2 f x1 x2 P ->
  app_1 f x1 (fun g => app_1 g x2 P).
Proof. auto. Qed.

Lemma app_intro_2_3 : forall (P:B->Prop),
  app_2 f x1 x2 (fun g => app_1 g x3 P) ->
  app_3 f x1 x2 x3 P.
Proof. auto. Qed.

Lemma app_intro_2_4 : forall (P:B->Prop),
  app_2 f x1 x2 (fun g => app_2 g x3 x4 P) ->
  app_4 f x1 x2 x3 x4 P.
Proof. auto. Qed.

Lemma app_intro_3_1 : forall (P:B->Prop),
  app_3 f x1 x2 x3 P ->
  app_1 f x1 (fun g => app_2 g x2 x3 P).
Proof. auto. Qed.

Lemma app_intro_3_2 : forall (P:B->Prop),
  app_3 f x1 x2 x3 P ->
  app_2 f x1 x2 (fun g => app_1 g x3 P).
Proof. auto. Qed.

Lemma app_intro_3_4 : forall (P:B->Prop),
  app_3 f x1 x2 x3 (fun g => app_1 g x4 P) ->
  app_4 f x1 x2 x3 x4 P.
Proof. auto. Qed.

Lemma app_intro_4_1 : forall (P:B->Prop),
  app_4 f x1 x2 x3 x4 P ->
  app_1 f x1 (fun g => app_3 g x2 x3 x4 P).
Proof. auto. Qed.

Lemma app_intro_4_2 : forall (P:B->Prop),
  app_4 f x1 x2 x3 x4 P ->
  app_2 f x1 x2 (fun g => app_2 g x3 x4 P).
Proof. auto. Qed.

Lemma app_intro_4_3 : forall (P:B->Prop),
  app_4 f x1 x2 x3 x4 P ->
  app_3 f x1 x2 x3 (fun g => app_1 g x4 P).
Proof. auto. Qed.

End AppIntro.

(********************************************************************)
(* ** Elimination lemmas from spec to app *)
(*-- spec_elim_1 --*)

Lemma spec_elim_1_1' : forall A1 B (K: A1 -> ~~B -> Prop) f,
  spec_1 K f -> forall x1 (P Q : B->Prop),
  (forall R, K x1 R -> R Q) -> (Q ==> P) ->
  app_1 f x1 P.
Proof. 
  introv [S H] W M. apply* (app_weaken_1 (P:=Q)).
  rapply W; eauto.
Qed.

Lemma spec_elim_1_2' : forall A1 A2 B (K: A1 -> ~~val -> Prop) f,
  spec_1 K f -> forall x1 (x2:A2) (P : B->Prop) (Q:val->Prop),
  (forall R, K x1 R -> R Q) -> (Q ==> (fun g:val => app_1 g x2 P)) ->
  app_2 f x1 x2 P.
Proof.
  intros. apply app_intro_1_2. apply* spec_elim_1_1'.
Qed.

Lemma spec_elim_1_3' : forall A1 A2 A3 B (K: A1 -> ~~val -> Prop) f,
  spec_1 K f -> forall x1 (x2:A2) (x3:A3) (P : B->Prop) (Q:val->Prop),
  (forall R, K x1 R -> R Q) -> (Q ==> (fun g:val => app_2 g x2 x3 P)) ->
  app_3 f x1 x2 x3 P.
Proof.
  intros. apply app_intro_1_3. apply* spec_elim_1_1'.
Qed.

Lemma spec_elim_1_4' : forall A1 A2 A3 A4 B (K: A1 -> ~~val -> Prop) f,
  spec_1 K f -> forall x1 (x2:A2) (x3:A3) (x4:A4) (P : B->Prop) (Q:val->Prop),
  (forall R, K x1 R -> R Q) -> (Q ==> (fun g:val => app_3 g x2 x3 x4 P)) ->
  app_4 f x1 x2 x3 x4 P.
Proof.
  intros. apply app_intro_1_3. apply* spec_elim_1_1'.
Qed.

(*-- spec_elim_2 --*)

Lemma spec_elim_2_1' : forall A1 A2 B (K: A1 -> A2 -> ~~B -> Prop) f,
  spec_2 K f -> forall x1 (P : val->Prop),
  ((spec_1 (K x1)) ==> P) ->
  app_1 f x1 P.
Proof.
  introv [_ H] W. eapply app_weaken_1.
    apply (proj2 H).
    apply W.
Qed.

Lemma spec_elim_2_2' : forall A1 A2 B (K: A1 -> A2 -> ~~B -> Prop) f,
  spec_2 K f -> forall x1 x2 (P Q : B->Prop),
  (forall R, K x1 x2 R -> R Q) -> (Q ==> P) ->
  app_2 f x1 x2 P.
Proof. 
  introv [S H] W M. eapply app_weaken_1.
    apply (proj2 H).
    intros_all. applys* spec_elim_1_1'.
Qed.

Lemma spec_elim_2_3' : forall A1 A2 A3 B (K: A1 -> A2 -> ~~val -> Prop) f ,
  spec_2 K f -> forall x1 x2 (x3:A3) (P : B->Prop) (Q:val->Prop),
  (forall R, K x1 x2 R -> R Q) -> (Q ==> (fun g:val => app_1 g x3 P)) ->
  app_3 f x1 x2 x3 P.
Proof.
  intros. apply app_intro_2_3. apply* spec_elim_2_2'.
Qed.

Lemma spec_elim_2_4' : forall A1 A2 A3 A4 B (K: A1 -> A2 -> ~~val -> Prop) f ,
  spec_2 K f -> forall x1 x2 (x3:A3) (x4:A4) (P : B->Prop) (Q:val->Prop),
  (forall R, K x1 x2 R -> R Q) -> (Q ==> (fun g:val => app_2 g x3 x4 P)) ->
  app_4 f x1 x2 x3 x4 P.
Proof.
  intros. apply app_intro_2_3. apply* spec_elim_2_2'.
Qed.

(*-- spec_elim_3 --*)

Lemma spec_elim_3_1' : forall A1 A2 A3 B (K: A1 -> A2 -> A3 -> ~~B -> Prop) f,
  spec_3 K f -> forall x1 (P : val->Prop),
  ((spec_2 (K x1)) ==> P) ->
  app_1 f x1 P.
Proof.
  introv [_ H] W. eapply app_weaken_1.
    apply (proj2 H).
    apply W.
Qed.

Lemma spec_elim_3_2' : forall A1 A2 A3 B (K: A1 -> A2 -> A3 -> ~~B -> Prop) f,
  spec_3 K f -> forall x1 x2 (P : val->Prop),
  ((spec_1 (K x1 x2)) ==> P) ->
  app_2 f x1 x2 P.
Proof.
  introv [_ H] W. eapply app_weaken_1.
    apply (proj2 H).
    intros_all. apply* spec_elim_2_1'.
Qed.

Lemma spec_elim_3_3' : forall A1 A2 A3 B (K: A1 -> A2 -> A3 -> ~~B -> Prop) f,
  spec_3 K f -> forall x1 x2 x3 (P Q : B->Prop),
  (forall R, K x1 x2 x3 R -> R Q) -> (Q ==> P) ->
  app_3 f x1 x2 x3 P.
Proof. 
  introv [S H] W M. eapply app_weaken_1.
    apply (proj2 H).
    intros_all. applys* spec_elim_2_2'.
Qed.

Lemma spec_elim_3_4' : forall A1 A2 A3 A4 B (K: A1 -> A2 -> A3 -> ~~val -> Prop) f ,
  spec_3 K f -> forall x1 x2 x3 (x4:A4) (P : B->Prop) (Q:val->Prop),
  (forall R, K x1 x2 x3 R -> R Q) -> (Q ==> (fun g:val => app_1 g x4 P)) ->
  app_4 f x1 x2 x3 x4 P.
Proof.
  intros. apply app_intro_3_4. apply* spec_elim_3_3'.
Qed.

(*-- spec_elim_4 --*)

Lemma spec_elim_4_1' : forall A1 A2 A3 A4 B (K: A1 -> A2 -> A3 -> A4 -> ~~B -> Prop) f,
  spec_4 K f -> forall x1 (P : val->Prop),
  ((spec_3 (K x1)) ==> P) ->
  app_1 f x1 P.
Proof.
  introv [_ H] W. eapply app_weaken_1.
    apply (proj2 H).
    apply W.
Qed.

Lemma spec_elim_4_2' : forall A1 A2 A3 A4 B (K: A1 -> A2 -> A3 -> A4 -> ~~B -> Prop) f,
  spec_4 K f -> forall x1 x2 (P : val->Prop),
  ((spec_2 (K x1 x2)) ==> P) ->
  app_2 f x1 x2 P.
Proof.
  introv [_ H] W. eapply app_weaken_1.
    apply (proj2 H).
    intros_all. apply* spec_elim_3_1'.
Qed.

Lemma spec_elim_4_3' : forall A1 A2 A3 A4 B (K: A1 -> A2 -> A3 -> A4 -> ~~B -> Prop) f,
  spec_4 K f -> forall x1 x2 x3 (P : val->Prop),
  ((spec_1 (K x1 x2 x3)) ==> P) ->
  app_3 f x1 x2 x3 P.
Proof.
  introv [_ H] W. eapply app_weaken_1.
    apply (proj2 H).
    intros_all. apply* spec_elim_3_2'. 
Qed.

Lemma spec_elim_4_4' : forall A1 A2 A3 A4 B (K: A1 -> A2 -> A3 -> A4 -> ~~B -> Prop) f ,
  spec_4 K f -> forall x1 x2 x3 x4 (P Q : B->Prop),
  (forall R, K x1 x2 x3 x4 R -> R Q) -> (Q ==> P) ->
  app_4 f x1 x2 x3 x4 P.
Proof. 
  introv [S H] W M. eapply app_weaken_1.
    apply (proj2 H).
    intros_all. applys* spec_elim_3_3'.
Qed.


(********************************************************************)
(* ** Elimination lemmas from spec to app *)

(*-- spec_elim_1 --*)

Lemma spec_elim_1_1 : forall A1 B (K: A1 -> ~~B -> Prop) f,
  spec_1 K f -> forall x1 (P : B->Prop),
  (forall R, weakenable R -> K x1 R -> R P) ->
  app_1 f x1 P.
Proof.
  introv [S H] W. apply W.
    intros_all. apply* app_weaken_1.
    applys* S.
Qed.

Lemma spec_elim_1_2 : forall A1 A2 B (K: A1 -> ~~val -> Prop) f,
  spec_1 K f -> forall x1 (x2:A2) (P : B->Prop),
  (forall R, weakenable R -> K x1 R -> R (fun g:val => app_1 g x2 P)) ->
  app_2 f x1 x2 P.
Proof.
  intros. apply app_intro_1_2. apply* spec_elim_1_1.
Qed.

Lemma spec_elim_1_3 : forall A1 A2 A3 B (K: A1 -> ~~val -> Prop) f,
  spec_1 K f -> forall x1 (x2:A2) (x3:A3) (P : B->Prop),
  (forall R, weakenable R -> K x1 R -> R (fun g:val => app_2 g x2 x3 P)) ->
  app_3 f x1 x2 x3 P.
Proof.
  intros. apply app_intro_1_3. apply* spec_elim_1_1.
Qed.

Lemma spec_elim_1_4 : forall A1 A2 A3 A4 B (K: A1 -> ~~val -> Prop) f,
  spec_1 K f -> forall x1 (x2:A2) (x3:A3) (x4:A4) (P : B->Prop),
  (forall R, weakenable R -> K x1 R -> R (fun g:val => app_3 g x2 x3 x4 P)) ->
  app_4 f x1 x2 x3 x4 P.
Proof.
  intros. apply app_intro_1_3. apply* spec_elim_1_1.
Qed.

(*-- spec_elim_2 --*)

Lemma spec_elim_2_1 : forall A1 A2 B (K: A1 -> A2 -> ~~B -> Prop) f,
  spec_2 K f -> forall x1 (P : val->Prop),
  ((spec_1 (K x1)) ==> P) ->
  app_1 f x1 P.
Proof.
  introv [_ H] W. eapply app_weaken_1.
    apply (proj2 H).
    apply W.
Qed.

Lemma spec_elim_2_2 : forall A1 A2 B (K: A1 -> A2 -> ~~B -> Prop) f,
  spec_2 K f -> forall x1 x2 (P : B->Prop),
  (forall R, weakenable R -> K x1 x2 R -> R P) ->
  app_2 f x1 x2 P.
Proof.
  introv [_ H] W. eapply app_weaken_1.
    apply (proj2 H).
    intros_all. applys* spec_elim_1_1.
Qed. 

Lemma spec_elim_2_3 : forall A1 A2 A3 B (K: A1 -> A2 -> ~~val -> Prop) f ,
  spec_2 K f -> forall x1 x2 (x3:A3) (P : B->Prop),
  (forall R, weakenable R -> K x1 x2 R -> R (fun g:val => app_1 g x3 P)) ->
  app_3 f x1 x2 x3 P.
Proof.
  intros. apply app_intro_2_3. apply* spec_elim_2_2.
Qed.

Lemma spec_elim_2_4 : forall A1 A2 A3 A4 B (K: A1 -> A2 -> ~~val -> Prop) f ,
  spec_2 K f -> forall x1 x2 (x3:A3) (x4:A4) (P : B->Prop),
  (forall R, weakenable R -> K x1 x2 R -> R (fun g:val => app_2 g x3 x4 P)) ->
  app_4 f x1 x2 x3 x4 P.
Proof.
  intros. apply app_intro_2_3. apply* spec_elim_2_2.
Qed.

(*-- spec_elim_3 --*)

Lemma spec_elim_3_1 : forall A1 A2 A3 B (K: A1 -> A2 -> A3 -> ~~B -> Prop) f,
  spec_3 K f -> forall x1 (P : val->Prop),
  ((spec_2 (K x1)) ==> P) ->
  app_1 f x1 P.
Proof.
  introv [_ H] W. eapply app_weaken_1.
    apply (proj2 H).
    apply W.
Qed.

Lemma spec_elim_3_2 : forall A1 A2 A3 B (K: A1 -> A2 -> A3 -> ~~B -> Prop) f,
  spec_3 K f -> forall x1 x2 (P : val->Prop),
  ((spec_1 (K x1 x2)) ==> P) ->
  app_2 f x1 x2 P.
Proof.
  introv [_ H] W. eapply app_weaken_1.
    apply (proj2 H).
    intros_all. apply* spec_elim_2_1.
Qed.

Lemma spec_elim_3_3 : forall A1 A2 A3 B (K: A1 -> A2 -> A3 -> ~~B -> Prop) f,
  spec_3 K f -> forall x1 x2 x3 (P : B->Prop),
  (forall R, weakenable R -> K x1 x2 x3 R -> R P) ->
  app_3 f x1 x2 x3 P.
Proof.
  introv [_ H] W. eapply app_weaken_1.
    apply (proj2 H).
    intros_all. apply* spec_elim_2_2.
Qed.

Lemma spec_elim_3_4 : forall A1 A2 A3 A4 B (K: A1 -> A2 -> A3 -> ~~val -> Prop) f ,
  spec_3 K f -> forall x1 x2 x3 (x4:A4) (P : B->Prop),
  (forall R, weakenable R -> K x1 x2 x3 R -> R (fun g:val => app_1 g x4 P)) ->
  app_4 f x1 x2 x3 x4 P.
Proof.
  intros. apply app_intro_3_4. apply* spec_elim_3_3.
Qed.

(*-- spec_elim_4 --*)

Lemma spec_elim_4_1 : forall A1 A2 A3 A4 B (K: A1 -> A2 -> A3 -> A4 -> ~~B -> Prop) f,
  spec_4 K f -> forall x1 (P : val->Prop),
  ((spec_3 (K x1)) ==> P) ->
  app_1 f x1 P.
Proof.
  introv [_ H] W. eapply app_weaken_1.
    apply (proj2 H).
    apply W.
Qed.

Lemma spec_elim_4_2 : forall A1 A2 A3 A4 B (K: A1 -> A2 -> A3 -> A4 -> ~~B -> Prop) f,
  spec_4 K f -> forall x1 x2 (P : val->Prop),
  ((spec_2 (K x1 x2)) ==> P) ->
  app_2 f x1 x2 P.
Proof.
  introv [_ H] W. eapply app_weaken_1.
    apply (proj2 H).
    intros_all. apply* spec_elim_3_1.
Qed.

Lemma spec_elim_4_3 : forall A1 A2 A3 A4 B (K: A1 -> A2 -> A3 -> A4 -> ~~B -> Prop) f,
  spec_4 K f -> forall x1 x2 x3 (P : val->Prop),
  ((spec_1 (K x1 x2 x3)) ==> P) ->
  app_3 f x1 x2 x3 P.
Proof.
  introv [_ H] W. eapply app_weaken_1.
    apply (proj2 H).
    intros_all. apply* spec_elim_3_2. 
Qed.

Lemma spec_elim_4_4 : forall A1 A2 A3 A4 B (K: A1 -> A2 -> A3 -> A4 -> ~~B -> Prop) f ,
  spec_4 K f -> forall x1 x2 x3 x4 (P : B->Prop),
  (forall R, weakenable R -> K x1 x2 x3 x4 R -> R P) ->
  app_4 f x1 x2 x3 x4 P.
Proof.
  introv [_ H] W. eapply app_weaken_1.
    apply (proj2 H).
    intros_all. apply* spec_elim_3_3.
Qed.


(********************************************************************)
(* ** App from spec *)

Lemma app_spec_1 : forall A1 B f (v1:A1) (P : B->Prop),
  spec_1 (fun x1 R => x1 = v1 -> R P) f ->
  app_1 f v1 P.
Proof. introv S. apply~ (spec_elim_1_1 S). Qed.

Lemma app_spec_2 : forall A1 A2 B f (v1:A1) (v2:A2) (P : B->Prop),
  spec_2 (fun x1 x2 R => x1 = v1 -> x2 = v2 -> R P) f ->
  app_2 f v1 v2 P.
Proof. introv S. apply~ (spec_elim_2_2 S). Qed.

Lemma app_spec_3 : forall A1 A2 A3 B f (v1:A1) (v2:A2) (v3:A3) (P : B->Prop),
  spec_3 (fun x1 x2 x3 R => x1 = v1 -> x2 = v2 -> x3 = v3 -> R P) f -> 
  app_3 f v1 v2 v3 P.
Proof. introv S. apply~ (spec_elim_3_3 S). Qed.

Lemma app_spec_4 : forall A1 A2 A3 A4 B f (v1:A1) (v2:A2) (v3:A3) (v4:A4) (P : B->Prop),
  spec_4 (fun x1 x2 x3 x4 R => x1 = v1 -> x2 = v2 -> x3 = v3 -> x4 = v4 -> R P) f -> 
  app_4 f v1 v2 v3 v4 P.
Proof. introv S. apply~ (spec_elim_4_4 S). Qed.

(********************************************************************)
(* ** Weakening for spec *)

Lemma spec_weaken_1 : forall A1 B (K K': A1 -> ~~B -> Prop) f,
   spec_1 K f -> is_spec_1 K' -> 
   (forall x1 R, weakenable R -> K x1 R -> K' x1 R) ->
   spec_1 K' f.
Proof. unfold spec_1. introv [S H] I W. split~. Qed.

Lemma spec_weaken_2 : forall A1 A2 B (K K': A1 -> A2 -> ~~B -> Prop) f,
   spec_2 K f -> is_spec_2 K' ->
   (forall x1 x2 R, weakenable R -> K x1 x2 R -> K' x1 x2 R) ->
   spec_2 K' f.
Proof. 
  unfold spec_2. introv [S H] I W. split~.
  apply (spec_weaken_1 H). intros_all. apply* H1.
  introv WR HR. applys* WR. intros_all. apply* spec_weaken_1.
Qed.

Lemma spec_weaken_3 : forall A1 A2 A3 B (K K': A1 -> A2 -> A3 -> ~~B -> Prop) f,
   spec_3 K f -> is_spec_3 K' -> 
   (forall x1 x2 x3 R, weakenable R -> K x1 x2 x3 R -> K' x1 x2 x3 R) ->
   spec_3 K' f.
Proof. 
  unfold spec_3. introv [S H] I W. split~.
  apply (spec_weaken_1 H). intros_all. apply* H1.
  introv WR HR. applys* WR. intros_all. apply* spec_weaken_2.
Qed.

Lemma spec_weaken_4 : forall A1 A2 A3 A4 B (K K': A1 -> A2 -> A3 -> A4 -> ~~B -> Prop) f,
   spec_4 K f -> is_spec_4 K' -> 
   (forall x1 x2 x3 x4 R, weakenable R -> K x1 x2 x3 x4 R -> K' x1 x2 x3 x4 R) ->
   spec_4 K' f.
Proof. 
  unfold spec_3. introv [S H] I W. split~.
  apply (spec_weaken_1 H). intros_all. apply* H1.
  introv WR HR. applys* WR. intros_all. apply* spec_weaken_3.
Qed.

(********************************************************************)
(* ** Elimination combined with weakening *)

Lemma spec_weaken_elim_1 : forall A1 B,
  forall (K K': A1 -> ~~B -> Prop) f x1,
  spec_1 K f -> 
  (forall R, weakenable R -> K x1 R -> K' x1 R) ->
  K' x1 (app_1 f x1).
Proof. introv [S T] H. apply~ H. Qed.

Lemma spec_weaken_elim_2 : forall A1 A2 B,
   forall (K K': A1 -> A2 -> ~~B -> Prop) f x1 x2,
   spec_2 K f -> 
   (forall R, weakenable R -> K x1 x2 R -> K' x1 x2 R) ->
   K' x1 x2 (app_2 f x1 x2).
Proof. introv S H. apply~ H. apply~ spec_elim_2. Qed.

Lemma spec_weaken_elim_3 : forall A1 A2 A3 B, 
   forall (K K': A1 -> A2 -> A3 -> ~~B -> Prop) f x1 x2 x3,
   spec_3 K f -> 
   (forall R, weakenable R -> K x1 x2 x3 R -> K' x1 x2 x3 R) ->
   K' x1 x2 x3 (app_3 f x1 x2 x3).
Proof. introv S H. apply~ H. apply~ spec_elim_3. Qed.

Lemma spec_weaken_elim_4 : forall A1 A2 A3 A4 B, 
   forall (K K': A1 -> A2 -> A3 -> A4 -> ~~B -> Prop) f x1 x2 x3 x4,
   spec_4 K f -> 
   (forall R, weakenable R -> K x1 x2 x3 x4 R -> K' x1 x2 x3 x4 R) ->
   K' x1 x2 x3 x4 (app_4 f x1 x2 x3 x4).
Proof. introv S H. apply~ H. apply~ spec_elim_4. Qed.


(********************************************************************)
(* ** cf_app *)

Lemma cf_app_1 : forall A1 B f v1 P,
  forall (C : A1 -> ~~B),
  (forall (K: A1 -> ~~B -> Prop), 
     is_spec_1 K -> (forall x1, K x1 (C x1)) -> spec_1 K f) ->
  C v1 P ->
  app_1 f v1 P.
Proof.
  introv CF CP. apply app_spec_1. apply CF. intros_all~. intros. subst~.
Qed.

Lemma cf_app_2 : forall A1 A2 B f v1 v2 P,
  forall (C : A1 -> A2 -> ~~B),
  (forall (K: A1 -> A2 -> ~~B -> Prop), 
     is_spec_2 K -> (forall x1 x2, K x1 x2 (C x1 x2)) -> spec_2 K f) ->
  C v1 v2 P ->
  app_2 f v1 v2 P.
Proof.
  introv CF CP. apply app_spec_2. apply CF. intros_all~. intros. subst~.
Qed.

Lemma cf_app_3 : forall A1 A2 A3 B f v1 v2 v3 P,
  forall (C : A1 -> A2 -> A3 -> ~~B),
  (forall (K: A1 -> A2 -> A3 -> ~~B -> Prop), 
     is_spec_3 K -> (forall x1 x2 x3, K x1 x2 x3 (C x1 x2 x3)) -> spec_3 K f) ->
  C v1 v2 v3 P ->
  app_3 f v1 v2 v3 P.
Proof.
  introv CF CP. apply app_spec_3. apply CF. intros_all~. intros. subst~.
Qed.

Lemma cf_app_4 : forall A1 A2 A3 A4 B f v1 v2 v3 v4 P,
  forall (C : A1 -> A2 -> A3 -> A4 -> ~~B),
  (forall (K: A1 -> A2 -> A3 -> A4 -> ~~B -> Prop), 
     is_spec_4 K -> (forall x1 x2 x3 x4, K x1 x2 x3 x4 (C x1 x2 x3 x4)) -> spec_4 K f) ->
  C v1 v2 v3 v4 P ->
  app_4 f v1 v2 v3 v4 P.
Proof.
  introv CF CP. apply app_spec_4. apply CF. intros_all~. intros. subst~.
Qed.

(********************************************************************)
(* ** From a given spec to curried *)

Lemma curried_1_true : forall f, curried_1 f.
Proof. split. Qed. 

Lemma spec_curried_1 : forall A1 B f (K:A1->~~B->Prop),
  spec_1 K f -> curried_1 f.
Proof. intros. split. Qed.

Lemma spec_curried_2 : forall A1 A2 B f (K:A1->A2->~~B->Prop),
  spec_2 K f -> curried_2 A1 f.
Proof. 
  intros. split.
    intros_all~.
    intros x. applys app_weaken_1. apply (proj33 H). intros_all~.
Qed.

Lemma spec_curried_3 : forall A1 A2 A3 B f (K:A1->A2->A3->~~B->Prop),
  spec_3 K f ->
  curried_3 A1 A2 f.
Proof.
  intros. split.
    intros_all~.
    intros x. applys app_weaken_1. apply (proj33 H).
     introv H'. lets: (proj2 H). unfolds total_1. (* todo: total_weaken *)
     eapply spec_weaken_1. apply H'. intros_all~. simpl. introv WR HR.
     applys WR. apply HR. intros_all~.
Qed.

Lemma spec_curried_4 : forall A1 A2 A3 A4 B f (K:A1->A2->A3->A4->~~B->Prop),
  spec_4 K f ->
  curried_4 A1 A2 A3 f.
Proof.
  intros. split.
    intros_all~.
    intros x. applys app_weaken_1. apply (proj33 H).
     introv H'. lets: (proj2 H). unfolds total_1. (* todo: total_weaken *)
     eapply spec_weaken_1. apply H'. intros_all~. simpl. introv WR HR.
     applys WR. apply HR.
    intros g [IG [IG' SG]]. split. intros_all~. intros y.
     applys* app_weaken_1. 
Qed.

(********************************************************************)
(* ** A sufficient specification for proving curried *)

Lemma curried_prove_1 : forall A1 B f,
  spec_1 (fun (x1:A1) (R:~~B) => True) f ->
  curried_1 f.
Proof. intros. apply (spec_curried_1 H). Qed.

Lemma curried_prove_2 : forall A1 A2 B f,
  spec_2 (fun (x1:A1) (x2:A2) (R:~~B) => True) f ->
  curried_2 A1 f.
Proof. intros. apply (spec_curried_2 H). Qed.

Lemma curried_prove_3 : forall A1 A2 A3 B f,
  spec_3 (fun (x1:A1) (x2:A2) (x3:A3) (R:~~B) => True) f ->
  curried_3 A1 A2 f.
Proof. intros. apply (spec_curried_3 H). Qed.

Lemma curried_prove_4 : forall A1 A2 A3 A4 B f,
  spec_4 (fun (x1:A1) (x2:A2) (x3:A3) (x4:A4) (R:~~B) => True) f ->
  curried_4 A1 A2 A3 f.
Proof. intros. apply (spec_curried_4 H). Qed.


(********************************************************************)
(* ** Introduction lemmas' TODO *)

Lemma spec_intro_1' : forall A1 B f (K:A1->~~B->Prop),
  is_spec_1 K ->
  spec_1 (fun (x1:A1) (R:~~B) => True) f ->
  (forall x1, K x1 (app_1 f x1)) ->
  spec_1 K f.
Proof. intros. applys~ spec_intro_1. applys* curried_prove_1. Qed.

Lemma spec_intro_2' : forall A1 A2 B f (K:A1->A2->~~B->Prop),
  is_spec_2 K ->
  spec_2 (fun (x1:A1) (x2:A2) (R:~~B) => True) f ->
  (forall x1 x2, K x1 x2 (app_2 f x1 x2)) ->
  spec_2 K f.
Proof. intros. applys~ spec_intro_2. applys* curried_prove_2. Qed.

Lemma spec_intro_3' : forall A1 A2 A3 B f (K:A1->A2->A3->~~B->Prop),
  is_spec_3 K ->
  spec_3 (fun (x1:A1) (x2:A2) (x3:A3) (R:~~B) => True) f ->
  (forall x1 x2 x3, K x1 x2 x3 (app_3 f x1 x2 x3)) ->
  spec_3 K f.
Proof. intros. applys~ spec_intro_3. applys* curried_prove_3. Qed.

Lemma spec_intro_4' : forall A1 A2 A3 A4 B f (K:A1->A2->A3->A4->~~B->Prop),
  is_spec_4 K ->
  spec_4 (fun (x1:A1) (x2:A2) (x3:A3) (x4:A4) (R:~~B) => True) f ->
  (forall x1 x2 x3 x4, K x1 x2 x3 x4 (app_4 f x1 x2 x3 x4)) ->
  spec_4 K f.
Proof. intros. applys~ spec_intro_4. applys* curried_prove_4. Qed.


(********************************************************************)
(* ** Extraction of is_spec from spec *)

Lemma spec_is_spec_1 : forall A1 B, 
  forall (K: A1 -> ~~B -> Prop) f,
  spec_1 K f -> is_spec_1 K.
Proof.
  introv [H1 H2]. auto.
Qed.

Lemma spec_is_spec_2 : forall A1 A2 B,
  forall (K: A1 -> A2 -> ~~B -> Prop) f,
  spec_2 K f -> is_spec_2 K.
Proof.
  introv H. intros x. apply (proj1 H).
Qed.

Lemma spec_is_spec_3 : forall A1 A2 A3 B,
  forall (K: A1 -> A2 -> A3 -> ~~B -> Prop) f,
  spec_3 K f -> is_spec_3 K.
Proof.
  introv H. intros x. apply (proj1 H).
Qed.

Lemma spec_is_spec_4 : forall A1 A2 A3 A4 B,
  forall (K: A1 -> A2 -> A3 -> A4 -> ~~B -> Prop) f,
  spec_4 K f -> is_spec_4 K.
Proof.
  introv H. intros x. apply (proj1 H).
Qed.


(********************************************************************)
(* ** Corrolaries of the axioms [spec_intro] *)

Lemma spec_intro_weak_1 : forall A1 B f (K:A1->~~B->Prop),
  is_spec_1 K ->
  curried_1 f ->
  (forall x1, K x1 (app_1 f x1)) ->
  (forall x, K x (app_1 f x)).
Proof. introv I C S. destruct~ (spec_intro_1 I C S). Qed.

Lemma spec_intro_weak_2 : forall A1 A2 B f (K:A1->A2->~~B->Prop),
  is_spec_2 K -> 
  curried_2 A1 f -> 
  (forall x1 x2, K x1 x2 (app_2 f x1 x2)) ->
  total_1 (fun x => spec_1 (K x)) f.
Proof. introv I C S. destruct~ (spec_intro_2 I C S). Qed.

Lemma spec_intro_weak_3 : forall A1 A2 A3 B f (K:A1->A2->A3->~~B->Prop),
  is_spec_3 K ->
  curried_3 A1 A2 f ->
  (forall x1 x2 x3, K x1 x2 x3 (app_3 f x1 x2 x3)) ->
  total_1 (fun x => spec_2 (K x)) f.
Proof. introv I C S. destruct~ (spec_intro_3 I C S). Qed.

Lemma spec_intro_weak_4 : forall A1 A2 A3 A4 B f (K:A1->A2->A3->A4->~~B->Prop),
  is_spec_4 K ->
  curried_4 A1 A2 A3 f ->
  (forall x1 x2 x3 x4, K x1 x2 x3 x4 (app_4 f x1 x2 x3 x4)) ->
  total_1 (fun x => spec_3 (K x)) f.
Proof. introv I C S. destruct~ (spec_intro_4 I C S). Qed.


(********************************************************************)
(* ** Induction lemmas for spec *)

Lemma spec_induction_1 : 
  forall A1 B (lt:A1->A1->Prop), 
  forall (Wf: wf lt) f (K:A1->~~B->Prop),
  spec_1 (fun x R => 
    spec_1 (fun x' R' => lt x' x -> K x' R') f ->
    K x R) f ->
  spec_1 K f.
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


(********************************************************************)
(* ** Additional results, to generalize *)

Lemma spec_2_1 : forall A1 A2 B (K : A1 -> A2 -> ~~B -> Prop) f,
  spec_2 K f -> total_1 (fun x1 g => spec_1 (K x1) g) f.
Proof.
  introv [I S]. unfolds total_1. applys* spec_weaken_1. intros_all~. 
Qed.

Lemma total_2_spec_2 : forall A1 A2 B (Q : A1 -> A2 -> B -> Prop) f,
  total_2 Q f -> spec_2 (fun x1 x2 R => R (Q x1 x2)) f.
Proof.
  introv [I S]. split. intros_all*.
  split. intros_all*.
  intros. specializes S x1.
  applys* app_weaken_1.
Qed.

Lemma spec_3_2 : forall A1 A2 A3 B (K : A1 -> A2 -> A3 -> ~~B -> Prop) f,
  spec_3 K f -> total_2 (fun x1 x2 g => spec_1 (K x1 x2) g) f.
Proof.
  introv [I S]. split. intros_all*.
  intros_all. destruct S.
  specializes H0 x1.
  applys* (app_weaken_1). intros_all.
  split. intros_all*.
  intros. applys* spec_elim_2_1.
Qed.


(********************************************************************)
(* ** Representation predicate *)

Class Rep a A := 
  { rep : a -> A -> Prop;
    rep_unique : forall x X Y, rep x X -> rep x Y -> X = Y }.

