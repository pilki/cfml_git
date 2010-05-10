Set Implicit Arguments.
Require Import LibCore.

(* todo: move*)
Global Opaque LibInt.eqb_inst.
Global Opaque LibNat.eqb_inst. (*etc..*)

Hint Unfold pred_le.

(* Another proof, based on the lemma [measure_induction]
  Proof.
  intros A mu x. apply (@measure_induction _ mu). clear x. 
  intros x H. apply Acc_intro. intros y Lt. apply H. auto.
  Defined.
*)

Ltac idtacs tt :=
  idtac.




(********************************************************************)


Lemma if_eq_1 : forall A (x:bool) (v1 v2 y : A), 
  ((if x then = v1 else = v2) y) -> (y = (if x then v1 else v2)).
Proof. tautob~. Qed.

Lemma if_eq_2 : forall A (x:bool) (v1 v2 y : A), 
  ((if x then eq v1 else = v2) y) -> (y = (if x then v1 else v2)).
Proof. tautob~. Qed.

Lemma if_eq_3 : forall A (x:bool) (v1 v2 y : A), 
  ((if x then = v1 else eq v2) y) -> (y = (if x then v1 else v2)).
Proof. tautob~. Qed.

Lemma if_eq_4 : forall A (x:bool) (v1 v2 y : A), 
  ((if x then eq v1 else eq v2) y) -> (y = (if x then v1 else v2)).
Proof. tautob~. Qed.

Tactic Notation "if_eq" "in" hyp(H) :=
  let go L := apply L in H in
  first [ go if_eq_1 | go if_eq_2 | go if_eq_3 | go if_eq_4 ].

Tactic Notation "if_eq" :=
  repeat match goal with H: ((if _ then _ else _) _) |- _ => if_eq in H end.



Ltac subst_hyp H :=
  match type of H with 
  | ?x = ?y => first [ subst x | subst y ] 
  | ?x == ?y => substb H
  | isTrue ?x => subst x
  | isTrue (! ?x) => apply eq_false_r_back in H; subst x
  end.  (*todo: ~b *)

Ltac calc_partial_eq tt :=
  repeat match goal with
  | H: (= _) _ |- _ => simpl in H 
  | H: ((if _ then _ else _) _) |- _ => if_eq in H
  end.


Ltac substs_core :=
  let go x y := first [ subst x | subst y ] in
  match goal with 
  | H: ?x = ?y |- _ => go x y
  | H: (= ?x) ?y |- _ => simpl in H; go x y
  end.

Ltac injects_core :=
  match goal with 
  | H: ?f _ = ?f _ |- _ => injects H
  | H: ?f _ _ = ?f _ _ |- _ => injects H
  | H: ?f _ _ _ = ?f _ _ _ |- _ => injects H
  | H: ?f _ _ _ _ = ?f _ _ _ _ |- _ => injects H 
  end.

Ltac substs_base :=
  try fold_bool; calc_partial_eq tt; repeat substs_core;
  try injects_core;
  try injects_core;
  try injects_core;
  try injects_core;
  try injects_core. (* temporary: to avoid loops *)

Tactic Notation "substs" := substs_base.
  

Tactic Notation "cases" := 
  case_if; try solve [ falseb ].
Tactic Notation "cases" "~" :=  
  cases; auto~.
Tactic Notation "cases" "*" :=  
  cases; auto*.


(************************************************************)
(* * General tactics *)

Ltac intro_hnf :=
  intro; match goal with H: _ |- _ => hnf in H end.


(*
Tactic Notation "intro_subst":=
  let x := fresh "TEMP" in let H := fresh "TEMP" in
  intros x H; subst x.
*)

Ltac invert_first_hyp :=
  let H := get_last_hyp tt in inverts H.

Ltac apply_last_hyp :=
  match goal with H: _ |- _ => apply H end.

(*
Tactic Notation "substs" := 
  hnfs; repeat (match goal with H: ?x = ?y |- _ => 
                first [ subst x | subst y] end).
*)

Tactic Notation "substs" constr(z) := 
  match goal with 
  | H: z = _ |- _ => subst z
  | H: (= _) z |- _ => hnf in H; subst z
  end.

Ltac substeq E :=
  try (hnf in E);
  match type of E with ?x = ?y => 
    first [ subst x | subst y | rewrite E in * ] end.



(************************************************************)
(* * Misc *)

Lemma conj_swap: forall (P Q: Prop), P -> Q -> Q /\ P.
Proof. auto*. Qed.


Definition bool_of (P:Prop) :=
   fun b => (isTrue b = P).

Require Import LibEpsilon.
Section BoolOf.
Variables (b:bool) (P:Prop).

Lemma bool_of_true : bool_of P b -> b -> P.
Proof. unfold bool_of. intros. subst~. Qed.

Lemma bool_of_false : bool_of P b -> !b -> ~ P.
Proof. unfold bool_of. intros. subst~. destruct~ b. Qed.

Lemma bool_of_true_back : b -> bool_of P b -> P.
Proof. unfold bool_of. intros. subst~. Qed.

Lemma bool_of_false_back : !b -> bool_of P b -> ~ P.
Proof. unfold bool_of. intros. subst~. destruct~ b. Qed.

Lemma bool_of_true_in : bool_of P true -> P.
Proof. unfold bool_of. intros. subst~. Qed.

Lemma bool_of_false_in : bool_of P false -> ~ P.
Proof. unfold bool_of. intros. subst~. Qed.

Lemma bool_of_true_in_forw : P -> bool_of P true.
Proof. intros. hnf. extens*. Qed.

Lemma bool_of_false_in_forw : ~ P -> bool_of P false.
Proof. intros. hnf. extens; auto_false*. Qed.

Lemma bool_of_True : bool_of P b -> P -> b.
Proof. unfold bool_of. intros. subst~. Qed.

Lemma bool_of_False : bool_of P b -> ~ P -> !b.
Proof. unfold bool_of. intros. subst~. Qed.

Lemma bool_of_prove : (b <-> P) -> bool_of P b.
Proof. intros. extens*. Qed.

(* todo: add  isTrue true = P to fold_prop *)
End BoolOf.

Lemma bool_of_eq : forall (P Q : Prop), 
  (P <-> Q) -> ((bool_of P) = (bool_of Q)).
Proof. 
  intros. apply prop_ext_1. intros_all. unfold bool_of;
  iff; rewrite H0; apply* prop_ext. 
Qed.

Lemma elim_isTrue_true : forall (b:bool) (P:Prop), 
  b -> (isTrue b = P) -> P.
Proof. intros. subst~. Qed.

Lemma elim_isTrue_false : forall (b:bool) (P:Prop), 
  !b -> (isTrue b = P) -> ~ P.
Proof. intros_all. subst~. destruct b; simpls; false. Qed.


Hint Rewrite isTrue_istrue istrue_isTrue : rew_istrue.
Ltac rew_istrue := autorewrite with rew_istrue.

Ltac fix_bool_of_known tt := 
  match goal with 
  | H: bool_of ?P true |- _ => 
     applys_to H bool_of_true_in
  | H: bool_of ?P false |- _ => 
     applys_to H bool_of_false_in
  | H: bool_of ?P ?b, Hb: isTrue ?b |- _ => 
     applys_to H (@bool_of_true_back b P Hb); clear Hb
  | H: bool_of ?P ?b, Hb: isTrue (! ?b) |- _ => 
     applys_to H (@bool_of_false_back b P Hb); clear Hb 
  | |- bool_of ?P true => 
     apply bool_of_true_in_forw
  | |- bool_of ?P false => 
     apply bool_of_false_in_forw
  | |- bool_of ?P ?b =>
     apply bool_of_prove; rew_istrue
  end.


Lemma pred_le_bool_of : forall (P Q : Prop), 
  (P <-> Q) -> (pred_le (bool_of P) (bool_of Q)).
Proof. unfold bool_of; intros_all. rewrite H0. apply~ prop_ext. Qed.


Ltac invert_first_hyp ::=
  let H := get_last_hyp tt in symmetry in H; inverts H.

(* todo move *)
Implicit Arguments lt_irrefl [A H Lt_irrefl]. 

Lemma true_eq_P : forall (P:Prop),
  (isTrue true = P) = P.
Proof. intros. apply prop_ext. iff. subst~. apply* prop_ext. Qed.
Hint Rewrite true_eq_P : rew_reflect.  




Tactic Notation "false" "~" constr(E) := (* coqfix *)
  false E; instantiate; auto_tilde. 

Tactic Notation "splits_all" "~" :=
  splits_all; auto_tilde.
Tactic Notation "splits_all" "*" :=
  splits_all; auto_star.


(********************************************************************)
(* ** Predicate weakening *)

Notation "P ==> Q" := (pred_le P Q) 
  (at level 55, right associativity) : func.

Open Scope func.

Hint Resolve pred_le_refl.

Lemma weaken_bool_of : forall (P Q : Prop), 
  (P <-> Q) -> ((bool_of P) ==> (bool_of Q)).
Proof. unfold bool_of. intros_all. rewrite H0. extens*. Qed.


