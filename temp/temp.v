
(*-- spec_elim_1 --*)

Lemma spec_elim_1_1' : forall A1 B (K: A1 -> ~~B -> Prop) f,
  spec_1 K f -> forall x1 (P Q : B->Prop),
  (forall R, K x1 R -> R Q) -> (Q ==> P) ->
  app_1 f x1 P.
Proof. 
  introv [S H] W. apply W. applys* S.
  intros_all. apply* app_weaken_1.
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
  introv [S H] W. apply W. applys* S.
  intros_all. apply* app_weaken_1.
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
    intros_all. apply* '.
Qed.

Lemma spec_elim_3_3' : forall A1 A2 A3 B (K: A1 -> A2 -> A3 -> ~~B -> Prop) f,
  spec_3 K f -> forall x1 x2 x3 (P Q : B->Prop),
  (forall R, K x1 x2 x3 R -> R Q) -> (Q ==> P) ->
  app_3 f x1 x2 x3 P.
Proof.
  introv [S H] W. apply W. applys* S.
  intros_all. apply* app_weaken_1.
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
  spec_4 K f -> forall x1 x2 x3 (P Q : val->Prop),
  ((spec_1 (K x1 x2 x3)) ==> P) ->
  app_3 f x1 x2 x3 P.
Proof.
  introv [_ H] W. eapply app_weaken_1.
    apply (proj2 H).
    intros_all. apply* spec_elim_3_2'. 
Qed.

Lemma spec_elim_4_4' : forall A1 A2 A3 A4 B (K: A1 -> A2 -> A3 -> A4 -> ~~B -> Prop) f ,
  spec_4 K f -> forall x1 x2 x3 x4 (P : B->Prop),
  (forall R, K x1 x2 x3 x4 R -> R Q) -> (Q ==> P) ->
  app_4 f x1 x2 x3 x4 P.
Proof.
  introv [S H] W. apply W. applys* S.
  intros_all. apply* app_weaken_1.
Qed.
