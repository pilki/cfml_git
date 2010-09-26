Set Implicit Arguments.
Require Import LibTactics.



(*****************************************************************************)
(** Maths *)


Require Export Arith.EqNat.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.


(*****************************************************************************)
(** Identifiers *)

Module Id.
Inductive id : Type := 
  Id : nat -> id.
Definition beq_id id1 id2 :=
  match (id1, id2) with
    (Id n1, Id n2) => beq_nat n1 n2
  end.
Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.
End Id.
Import Id.

(*****************************************************************************)
(** Syntax *)

Inductive aexp : Type := 
  | ANum : nat -> aexp
  | AId : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type := 
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Definition state := id -> nat.

Definition empty_state : state := fun _ => 0.

Definition update (st : state) (V:id) (n : nat) : state :=
  fun V' => if beq_id V V' then n else st V'.


(*****************************************************************************)
(** Notation *)

Notation "'SKIP'" := 
  CSkip.
Notation "l '::=' a" := 
  (CAss l a) (at level 60).
Notation "c1 ; c2" := 
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" := 
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" := 
  (CIf e1 e2 e3) (at level 80, right associativity).


(*****************************************************************************)
(** Semantics *)

Fixpoint aeval (st : state) (e : aexp) : nat :=
  match e with
  | ANum n => n
  | AId i => st i
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (e : bexp) : bool :=
  match e with 
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2 => ble_nat (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Reserved Notation "c1 '/' st '==>' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st ==> st
  | E_Ass : forall st a1 n l,
      aeval st a1 = n ->
      (l ::= a1) / st ==> (update st l n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st ==> st' ->
      c2 / st' ==> st'' ->
      (c1 ; c2) / st ==> st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      c1 / st ==> st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st ==> st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      c2 / st ==> st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st ==> st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      (WHILE b1 DO c1 END) / st ==> st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      c1 / st ==> st' ->
      (WHILE b1 DO c1 END) / st' ==> st'' ->
      (WHILE b1 DO c1 END) / st ==> st''

  where "c1 '/' st '==>' st'" := (ceval c1 st st').

(*****************************************************************************)
(** Reasoning *)

Definition Assertion := state -> Prop.

Definition assertion_impl (P Q:Assertion) :=
  forall st, P st -> Q st.

Notation "P '===>' Q" := (assertion_impl P Q) (at level 68).

Lemma assertion_impl_refl : forall P,
  P ===> P.
Proof. intros. unfolds~. Qed.

Hint Resolve assertion_impl_refl.

Definition bassn b : Assertion :=
  fun st => beval st b = true.


(*****************************************************************************)
(** Weakenable formulae *)

Definition Formula := Assertion -> Assertion -> Prop.

Definition weaken (R:Formula) :=
  fun H Q => forall st, H st -> exists H' Q', 
               H' st /\ R H' Q' /\ Q' ===> Q.

Lemma weaken_elim : forall (R:Formula) H Q,
  R H Q -> weaken R H Q.
Proof. intros_all*. Qed.

Notation "= x" := (fun y => y = x) (at level 69).

Lemma weaken_name : forall (R:Formula) H Q,
  (forall st, H st -> R (= st) Q) -> weaken R H Q.
Proof. introv M Pre. exists* (= st). Qed.


(*****************************************************************************)
(** Characteristic formula generation *)

Definition cf_skip : Formula :=
  weaken (fun H Q => H ===> Q).

Definition cf_ass (V : id) (a : aexp) : Formula :=
  fun H Q => H ===> (fun st => Q (update st V (aeval st a))).

Definition cf_seq (F1 F2 : Formula) : Formula :=
  fun H Q => exists H', F1 H H' /\ F2 H' Q.

Definition cf_if (b : bexp) (F1 F2 : Formula) : Formula :=
  fun H Q => F1 (fun st => H st /\ bassn b st) Q
          /\ F2 (fun st => H st /\ ~ bassn b st) Q.

Definition cf_while (b : bexp) (F1 : Formula) : Formula :=
  fun H Q => forall (R:Formula),
    (forall H' Q',
      (cf_if b (cf_seq F1 R) cf_skip) H' Q' -> R H' Q') ->
    R H Q.

Notation "'\SKIP'" := 
  cf_skip.
Notation "l '\::=' a" := 
  (cf_ass l a) (at level 60).
Notation "c1 \; c2" := 
  (cf_seq c1 c2) (at level 80, right associativity).
Notation "'\WHILE' b 'DO' c 'END'" := 
  (cf_while b c) (at level 80, right associativity).
Notation "'\IFB' e1 'THEN' e2 'ELSE' e3 'FI'" := 
  (cf_if e1 e2 e3) (at level 80, right associativity).


Fixpoint cf (c : com) : Formula :=
  match c with 
    | SKIP => \SKIP
    | l ::= a1 => l \::= a1
    | c1 ; c2 => cf c1 \; cf c2
    | IFB b THEN c1 ELSE c2 FI => \IFB b THEN cf c1 ELSE cf c2 FI
    | WHILE b1 DO c1 END => \WHILE b1 DO cf c1 END
  end.



(*****************************************************************************)
(** Soundness proof *)

Hint Constructors ceval.

Lemma E_Ass' : forall st a1 l,
      (l ::= a1) / st ==> (update st l (aeval st a1)).
Proof. intros. apply E_Ass. auto. Qed.
Hint Resolve E_Ass'.

Lemma beval_false : forall st b,
 beval st b = false -> ~ bassn b st.
Proof. intros. unfold bassn. rewrite~ H. Qed. 
Hint Resolve beval_false.


Lemma cf_sound : forall (c:com) (P Q:Assertion), 
  cf c P Q -> forall st, P st -> exists st', c / st ==> st' /\ Q st'.
Proof.
  induction c; intros P Q H st Hst.
  unfolds in H. unfolds in H.
  specializes H Hst. destruct H as (P'&Q'&Pre&Main&Post).

  
  eauto.
  eauto.
  destruct H as (H'&H1&H2).
   forwards* (st1&Red1&Post1): (>>> IHc1 H1).
   forwards* (st2&Red2&Post2): (>>> IHc2 H2).
  destruct H as (H1&H2). case_eq (beval st b); intro B.
   forwards* (st1&Red1&Post1): (>>> IHc1 H1).
   forwards* (st2&Red2&Post2): (>>> IHc2 H2).
  gen st. pattern P. pattern Q. apply H.
   clear H Q. intros H Q [M1 M2] st Hst.
   case_eq (beval st b); intro B.
     destruct M1 as (H'&M11&M12).
      forwards* (st1&Red1&Post1): (>>> IHc M11).
      forwards* (st2&Red2&Post2): M12.
     hnf in M2. eauto 7.
Qed.


Lemma cf_sound : forall (c:com) (P Q:Assertion), 
  cf c P Q -> forall st, P st -> exists st', c / st ==> st' /\ Q st'.

(*****************************************************************************)
(** Completeness proof *)

Lemma cf_complete : forall (c:com) (st st':state), 
  c / st ==> st'  ->  cf c (= st) (= st').
Proof.
  introv H. induction H.
  hnf. simple~.
  hnf. simpl. intros. subst~.
  hnf. exists~ (=st').
  hnf. split.
  
Qed.


(*****************************************************************************)
(** Hoare *)

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', 
       c / st ==> st' ->
       P st ->
       Q st'.

Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q) (at level 90) : hoare_spec_scope.
Open Scope hoare_spec_scope.

(* to get somewhere else *)
Axiom deterministic : forall c st st' st'',
  c / st ==> st' -> 
  c / st ==> st'' ->
  st' = st''.

Lemma cf_to_hoare : forall (c:com) (P Q:Assertion), 
  cf c P Q  ->  {{P}} c {{Q}}. 
Proof.
  introv Hcf Red Pre.
  forwards* [st'' [Red' Post]]: (>>> cf_sound Hcf).
  forwards* E: (>>> deterministic Red Red').
  rewrite~ E.
Qed.

