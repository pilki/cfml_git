Set Implicit Arguments.
Require Import LibTactics.

(*****************************************************************************)
(** Identifiers *)

Module Id.
Inductive id : Type := 
  Id : nat -> id.
Definition beq_id id1 id2 :=
  match (id1, id2) with
    (Id n1, Id n2) => beq_nat n1 n2
  end.
End Id.

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.


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
  | AId i => st i (* <----- NEW *)
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


(*****************************************************************************)
(** Characteristic formula generation *)

Definition Formula := Assertion -> Assertion -> Prop.

(* toadd after
Definition weaken (R:Formula) :=
  fun H Q => forall st, H st -> exists H' Q', 
               H' st /\ R H' Q' /\ Q' ===> Q.
*)


(*****************************************************************************)
(** Soundness proof *)

Lemma cf_sound : forall (c:com) (P Q:Assertion), 
  cf c P Q -> forall st, P st -> exists st', c / st ==> st' /\ Q st'.
Proof.
  skip.
Qed.


(*****************************************************************************)
(** Completeness proof *)

Lemma cf_complete : forall (c:com) (st st':state), 
  c / st ==> st'  ->  cf c (= st) (= st').
Proof.
  skip.
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

Lemma cf_to_hoare : forall (c:com) (P Q:Assertion), 
  cf c P Q  ->  {{P}} c {{Q}}. 
Proof.
  skip.
Qed.

