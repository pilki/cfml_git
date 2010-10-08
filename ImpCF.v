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
  weaken (fun H Q => H ===> (fun st => Q (update st V (aeval st a)))).

Definition cf_seq (F1 F2 : Formula) : Formula :=
  weaken (fun H Q => exists H', F1 H H' /\ F2 H' Q).

Definition cf_if (b : bexp) (F1 F2 : Formula) : Formula :=
  weaken (fun H Q => F1 (fun st => H st /\ beval st b = true) Q
                  /\ F2 (fun st => H st /\ beval st b = false) Q).

(*Definition cf_if (b : bexp) (F1 F2 : Formula) : Formula :=
  weaken (fun H Q => F1 (fun st => H st /\ bassn b st) Q
                  /\ F2 (fun st => H st /\ ~ bassn b st) Q).*)

Definition cf_while (b : bexp) (F1 : Formula) : Formula :=
  weaken (fun H Q => forall (R:Formula),
    (forall H' Q',
      (cf_if b (cf_seq F1 R) cf_skip) H' Q' -> R H' Q') ->
    R H Q).

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
(** Alternative semantics *)

Require Import List.

(** Auxiliary definitions *)

Inductive seq (A:Type) : A->A->list A->Prop :=
  | seq_init : forall x, 
      seq x x (x::nil)
  | seq_cons : forall y x z L,
      seq y z L -> 
      seq x z (x::L).

Inductive conseq (A:Type) : A->A->list A->Prop :=
  | conseq_here : forall x y L,
      conseq x y (x::y::L)
  | conseq_next : forall x y z L,
      conseq x y L ->
      conseq x y (z::L).

Hint Constructors seq conseq.

Lemma conseq_cons_seq : forall A (x y z : A) L,
  seq y z L -> conseq x y (x :: L).
Proof. introv H. inverts~ H. Qed.

Hint Resolve conseq_cons_seq.

(** Alternative semantics *)

Reserved Notation "c1 '//' st '==>' st'" (at level 40, st at level 39).

Inductive deval : com -> state -> state -> Prop :=
  | D_Skip : forall st,
      SKIP // st ==> st
  | D_Ass : forall st a1 n l,
      aeval st a1 = n ->
      (l ::= a1) // st ==> (update st l n)
  | D_Seq : forall c1 c2 st st' st'',
      c1 // st ==> st' ->
      c2 // st' ==> st'' ->
      (c1 ; c2) // st ==> st''
  | D_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      c1 // st ==> st' ->
      (IFB b1 THEN c1 ELSE c2 FI) // st ==> st'
  | D_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      c2 // st ==> st' ->
      (IFB b1 THEN c1 ELSE c2 FI) // st ==> st'
  | D_While : forall L b1 c1 s1 sn,
      seq s1 sn L ->
      (forall si sj, conseq si sj L -> beval si b1 = true) ->
      (forall si sj, conseq si sj L -> c1 // si ==> sj) ->
      beval sn b1 = false ->
      (WHILE b1 DO c1 END) // s1 ==> sn

(* Note: a conjunction in D_While looks better unfortunately
   Coq doesn't give us the induction hypothesis that we want. *)

  where "c1 '//' st '==>' st'" := (deval c1 st st').

(** Semantic equivalence *)

Hint Constructors ceval deval.

Lemma deval_to_ceval : forall c s s',
  (c // s ==> s') -> (c / s ==> s').
Proof.
  introv H. induction H; auto; eauto.
  induction H.
    apply~ E_WhileEnd.
    forwards: H0 x y. eauto.
     forwards: H2 x y. eauto.
     applys~ E_WhileLoop y. apply* IHseq.
Qed.

Lemma ceval_to_deval : forall c s s',
  (c / s ==> s') -> (c // s ==> s').
Proof.
  introv H. induction H; auto; eauto.
  applys~ (@D_While (st::nil)).
    introv M. inverts M as M. inverts M.
    introv M. inverts M as M. inverts M.
  inverts keep IHceval2 as Hseq Heach Hcond.
  applys~ (@D_While (st::L)). eauto.
    introv M. inverts M as M.
      inverts~ Hseq.
      forwards*: Heach.
    introv M. inverts M as M.
      inverts~ Hseq.
      forwards*: Heach.
Qed.


(*****************************************************************************)
(** Completeness proof *)

Ltac introeq := 
  let x := fresh in intros x; intro; subst x.

Lemma assertion_impl_trans : forall H2 H1 H3,
  H1 ===> H2 -> H2 ===> H3 -> H1 ===> H3.
Proof. intros_all~. Qed.

Lemma weaken_idem : forall (R:Formula) H Q,
  weaken (weaken R) H Q -> weaken R H Q.
Proof.
  introv M Pre. destruct~ (M st) as (H'&Q'&?&?&I1).
  destruct~ (H1 st) as (H''&Q''&?&?&I2).
  lets*: (>>> assertion_impl_trans I2 I1).
Qed.

Lemma weaken_cf : forall (c:com) (H Q : Assertion),
  weaken (cf c) H Q -> cf c H Q.
Proof. intros. destruct c; apply~ weaken_idem. Qed.
 
Lemma cf_name : forall (c:com) (H Q : Assertion),
  (forall st, H st -> cf c (= st) Q) -> cf c H Q. 
Proof. intros. apply weaken_cf. apply~ weaken_name. Qed.


Lemma cf_complete' : forall (c:com) (st st':state), 
  c // st ==> st'  ->  cf c (= st) (= st'). 
Proof.
  introv H. induction H; simpl.
  apply~ weaken_elim.
  apply~ weaken_elim. introeq. subst~.
  apply~ weaken_elim. exists~ (=st').
  apply~ weaken_elim. split.
    eapply cf_name. intros st2 [? ?]. subst~.
    eapply cf_name. intros st2 [? G]. subst. false*.
  apply~ weaken_elim. split.
    eapply cf_name. intros st2 [? G]. subst. false*.
    eapply cf_name. intros st2 [? ?]. subst~.
  apply~ weaken_elim. intros R M.
   renames H0 to Hcond, H2 to Hcfc. induction H as [|stj sti stn L].
   (* base case for loops *)
   apply M. clear M. apply weaken_elim. split.
     eapply weaken_name. intros st2 [? ?]. subst. false*.
     eapply weaken_name. intros st2 [? ?]. subst~.
   (* step case for loops *)
   apply M. clear M. apply weaken_elim. split.
     eapply weaken_name. intros st2 [? ?]. subst.
      exists (=stj). split. 
        apply* Hcfc.
        apply* IHseq.
     eapply weaken_name. intros st2 [? ?]. subst~. 
      forwards: Hcond sti stj. eauto. false.
Qed.

Lemma cf_complete : forall (c:com) (st st':state), 
  c / st ==> st'  ->  cf c (= st) (= st'). 
Proof.
  intros. apply cf_complete'. apply~ ceval_to_deval.
Qed.


(********************************************************************)
(* ** Lemmas for tactics *)

(* find elsewhre *)
Axiom beq_id_refl : forall x, beq_id x x = true.

Lemma assignement : forall st V X,
  update st V (aeval st (AId X)) V = st X.
Proof.
  intros. unfold aeval, update. rewrite~ beq_id_refl.
Qed.

Lemma ass_eq : forall st V a,
  update st V a V = a.
Proof.
  intros. unfold aeval, update. rewrite~ beq_id_refl.
Qed.

Lemma ass_neq : forall st V V' a,
  V <> V' ->
  update st V a V' = st V'.
Proof.
  intros. unfold aeval, update. skip. (* todo *)
Qed.


(********************************************************************)
(* ** Tactics *)

Tactic Notation "xseq" :=
  hnf; eapply weaken_elim; esplit; split.

Tactic Notation "xseq" constr(H) :=
  hnf; eapply weaken_elim; exists H; split.

Tactic Notation "xass" :=
  let st := fresh "st" in let Pst := fresh "Pst" in
  hnf; eapply weaken_elim; intros st Pst; 
  repeat rewrite ass_eq; repeat rewrite ass_neq;
  simpl aeval.

Tactic Notation "xif" :=
  hnf; eapply weaken_elim; split.

Tactic Notation "xskip" :=
  let st := fresh "st" in let Pst := fresh "Pst" in
  hnf; eapply weaken_elim; intros st Pst.

Tactic Notation "xwhile" :=
  let R := fresh "R" in let HR := fresh "H" R in
  hnf; eapply weaken_elim; intros R HR.


(********************************************************************)
(* ** Mathematics *)

Require Arith Omega.

Lemma mult_one : forall x, x = 1 * x.
Proof. intros. simpl. apply plus_n_O. Qed.

(* find elsewhere *)
Axiom peano_induction : forall P : nat -> Prop,
   (forall n : nat, (forall m : nat, lt m n -> P m) -> P n) ->
 forall n : nat, P n.

(* find elsewhere *)
Hint Extern 1 (Y <> Z) => skip.
Hint Extern 1 (Z <> Y) => skip.


(********************************************************************)
(* ** Facto *)

Module Factorial.

(** Mathematical factorial *)

Fixpoint real_fact (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (real_fact n')
  end.

Definition fact_body : com :=
  Y ::= AMult (AId Y) (AId Z);
  Z ::= AMinus (AId Z) (ANum 1).

Definition fact_loop : com :=
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    fact_body
  END.

Definition fact_com : com :=
  Z ::= (AId X);
  Y ::= ANum 1;
  fact_loop.

Lemma end_loop : forall Z st,
  ~ bassn (BNot (BEq (AId Z) (ANum 0))) st -> st Z = 0.
Proof.
  intros. simpls. unfolds bassn, beval. simpls.
  destruct (st Z0); simpls. auto. false. 
Qed.

Theorem fact_com_correct : forall x,
  cf fact_com (fun st => st X = x)
              (fun st => st Y = real_fact x).
Proof.
  intros x. 
  xseq (fun st => st Z = x). xass. auto.
  xseq (fun st => st Z = x /\ st Y = 1). xass; auto. 
  xwhile. cuts M: (forall n k, 
    R (fun st => st Z = n /\ st Y = k)
      (fun st => st Y = k * real_fact n)).
    rewrite (mult_one (real_fact x)). apply M.
   induction n using peano_induction; intros k.
   apply HR. xif.
     asserts: (n <> 0). skip. destruct n as [|n']. false.
     xseq (fun st => st Z = n' /\ st Y = k * (S n')).     
       xseq (fun st => st Z = S n' /\ st Y = k * (S n')).
         xass; auto*.
         xass; auto. destruct Pst. omega.
       unfold real_fact. fold (real_fact n').
        rewrite Mult.mult_assoc. apply~ H.
     xskip. destruct Pst as [[I J] K]. rewrite J.
      lets: (end_loop K). asserts_rewrite (n = 0). omega.
      simpl. omega.
Qed.

End Factorial.



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

Definition sound (c:com) (R:Formula) :=
  forall P Q, R P Q -> forall st, P st ->
    exists st', c / st ==> st' /\ Q st'.

Lemma sound_weaken : forall c R,
  sound c R -> sound c (weaken R).
Proof.
  introv M Wea Pre.
  destruct (Wea _ Pre) as (P'&Q'&Pre'&Main&Post').
  forwards* (st'&?&?): M. 
Qed.

Lemma cf_sound : forall (c:com), sound c (cf c).
Proof.
  induction c; simpl; apply sound_weaken; intros H Q F st Hst.
  eauto.
  eauto. 
  destruct F as (H'&H1&H2).
   forwards* (st1&Red1&Post1): (>>> IHc1 H1).
   forwards* (st2&Red2&Post2): (>>> IHc2 H2).
  destruct F as (H1&H2). case_eq (beval st b); intro B.
   forwards* (st1&Red1&Post1): (>>> IHc1 H1).
   forwards* (st2&Red2&Post2): (>>> IHc2 H2).
  gen st. apply F. clear F H Q. intros H Q M st Hst.
   destruct (M _ Hst) as (H'&Q'&Pre'&(M1&M2)&Post'). clear M.
   case_eq (beval st b); intro B.
     forwards~ (P''&Q''&?&(H''&M11&M12)&?): (M1 st). clear M1 M2.
      forwards* (st1&Red1&Post1): (>>> IHc M11).
      forwards* (st2&Red2&Post2): M12.
      esplit. split. apply* E_WhileLoop. eauto.
     forwards* (?&?&?&?&?): (M2 st). eauto 8.
Qed.


Lemma cf_sound' : forall (c:com) (P Q:Assertion) (st:state), 
  cf c P Q -> P st -> exists st', c / st ==> st' /\ Q st'.
Proof. intros. apply* cf_sound. Qed.




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
