Set Implicit Arguments.

(********************************************************************)
(** Treatment of partially-applied equality *)

Require Import LibTactics LibCore LibEpsilon.

Global Opaque LibInt.eqb_inst.
Global Opaque LibNat.eqb_inst. 

Hint Unfold pred_le.

Tactic Notation "false" "~" constr(E) := 
  false E; instantiate; auto_tilde. 
  (* to work around a coq bug *)


(********************************************************************)
(** Treatment of partially-applied equality *)

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

Ltac calc_partial_eq tt :=
  repeat match goal with
  | H: (= _) _ |- _ => simpl in H 
  | H: ((if _ then _ else _) _) |- _ => if_eq in H
  end.


(************************************************************)
(* * Tactics for substitutions *)

(* todo: check not too slow *)

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

Tactic Notation "substs" constr(z) := 
  match goal with 
  | H: z = _ |- _ => subst z
  | H: (= _) z |- _ => hnf in H; subst z
  end.

Ltac subst_hyp H :=
  match type of H with 
  | ?x = ?y => first [ subst x | subst y ] 
  | ?x == ?y => substb H
  | isTrue ?x => subst x
  | isTrue (! ?x) => apply eq_false_r_back in H; subst x
  end.  (*todo: ~b *)


(************************************************************)
(* * Tactics for case analysis *)

Tactic Notation "old_cases" := 
  case_if; try solve [ falseb ].
Tactic Notation "old_cases" "~" :=  
  old_cases; auto~.
Tactic Notation "old_cases" "*" :=  
  old_cases; auto*.


(************************************************************)
(* * TODO: move *)

Axiom isTrue_andb : forall b1 b2 : bool,
  isTrue (b1 && b2) = (isTrue b1 /\ isTrue b2).
Axiom isTrue_orb : forall b1 b2 : bool,
  isTrue (b1 || b2) = (isTrue b1 \/ isTrue b2).
Axiom isTrue_negb : forall b : bool,
  isTrue (! b) = (~ isTrue b).

Lemma istrue_eq : forall (P Q : Prop),
  ((istrue P) = (istrue Q)) = (P <-> Q).
Proof.
  intros. extens. iff H.
  unfolds istrue. case_if; case_if; tryfalse; intuition.
  asserts_rewrite~ (P = Q). extens~.
Qed.

Hint Rewrite istrue_eq isTrue_istrue isTrue_andb isTrue_orb isTrue_negb : rew_logicb.

Hint Rewrite not_True not_False not_not not_and not_or : rew_logic.

Tactic Notation "rew_logic" := 
  autorewrite with rew_logic.
Tactic Notation "rew_logic" "in" hyp(H) := 
  autorewrite with rew_logic in H.
Tactic Notation "rew_logic" "in" "*" := 
  autorewrite with rew_logic in *.

Tactic Notation "rew_logicb" := 
  autorewrite with rew_logicb.
Tactic Notation "rew_logicb" "in" hyp(H) := 
  autorewrite with rew_logicb in H.
Tactic Notation "rew_logicb" "in" "*" := 
  autorewrite with rew_logicb in *.

Tactic Notation "rew_logics" := 
  rew_logicb; rew_logic.
Tactic Notation "rew_logic" "in" hyp(H) := 
  rew_logicb in H; rew_logic in H.
Tactic Notation "rew_logic" "in" "*" := 
  rew_logicb in *; rew_logic in *.


(************************************************************)
(* * Predicate for post-conditions on boolean values *)
(* --> todo: remove *)

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

Lemma bool_of_impl : forall (P Q : Prop) x, 
  bool_of P x -> (P <-> Q) -> bool_of Q x.
Proof. unfold bool_of. intros. subst. extens*. Qed.

Lemma bool_of_impl_neg : forall (P Q : Prop) x, 
  bool_of P x -> (~P <-> Q) -> bool_of Q (!x).
Proof. unfold bool_of. intros. subst. extens. rew_reflect*. Qed.

Lemma bool_of_neg_impl : forall (P Q : Prop) x, 
  bool_of P (!x) -> (~P <-> Q) -> bool_of Q x.
Proof.
  unfold bool_of. introv M K. subst. extens.
  rew_reflect in K. rew_classic in K. auto.
Qed.

Lemma pred_le_bool_of : forall (P Q : Prop), 
  (P <-> Q) -> (pred_le (bool_of P) (bool_of Q)).
Proof. unfold bool_of; intros_all. rewrite H0. apply~ prop_ext. Qed.


(********************************************************************)
(* ** Tactics for normalizing hypotheses *)

Lemma true_eq_P : forall (P:Prop),
  (isTrue true = P) = P.
Proof. intros. apply prop_ext. iff. subst~. apply* prop_ext. Qed.
Hint Rewrite true_eq_P : rew_reflect.  

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
     first [ apply refl_equal 
           | apply bool_of_prove; 
             try (check_noevar_goal; rew_istrue) ]
  end.


(********************************************************************)
(* ** Case analysis after pattern matching *)

(* todo: move to CFTactics *)

Ltac invert_first_hyp :=
  let H := get_last_hyp tt in inverts H.

Ltac invert_first_hyp ::=
  let H := get_last_hyp tt in symmetry in H; inverts H.


(********************************************************************)
(* ** Predicate weakening *)

Notation "P ==> Q" := (pred_le P Q) 
  (at level 55, right associativity) : func.

Open Scope func.

Hint Resolve pred_le_refl.

Lemma weaken_bool_of : forall (P Q : Prop), 
  (P <-> Q) -> ((bool_of P) ==> (bool_of Q)).
Proof. unfold bool_of. intros_all. rewrite H0. extens*. Qed.

Definition rel_le A B (P Q : A->B->Prop) := 
  forall x, P x ==> Q x.

Notation "P ===> Q" := (rel_le P Q) 
  (at level 55, right associativity) : func.

Open Scope func.


Lemma pred_le_extens : forall A (H1 H2 : A->Prop),
  H1 ==> H2 -> H2 ==> H1 -> H1 = H2.
Proof. intros. extens*. Qed.

Lemma pred_le_proj1 : forall A (H1 H2 : A->Prop),
  H1 = H2 -> H1 ==> H2.
Proof. intros. subst~. Qed.

Lemma pred_le_proj2 : forall A (H1 H2 : A->Prop),
  H1 = H2 -> H2 ==> H1.
Proof. intros. subst~. Qed.

Implicit Arguments pred_le_proj1 [H1 H2].
Implicit Arguments pred_le_proj2 [H1 H2].
Implicit Arguments pred_le_extens [H1 H2].

