

(********************************************************************)
(********************************************************************)
(********************************************************************)
(* * Technical Appendix

(************************************************************)
(** Appendix: a proof that characteristic formulae defined
    in terms of AppReturns are equivalent to those defined
    in terms of Spec. *)

(* for arity one *)

Lemma equiv_1 : forall A B (Pf : val -> Prop) (Q : A ->(B->Prop)->Prop),
  (forall f, (forall x P, Q x P -> app_1 f x P) -> Pf f) 
  <->
  (forall f, (forall K:A->~~B->Prop, is_spec_1 K ->
     (forall x, K x (Q x)) -> spec_1 K f) -> Pf f).
Proof.
  split.
  (* correctness *)
  introv H1 H2. apply H1.
  apply (H2 (fun x R => forall P, Q x P -> R P)). 
    intros_all~. 
    auto.
  (* completeness *)
  introv H1 H2. apply H1. introv SK HK. split~. intros x.
  applys* SK. applys* H2.
Qed.

(* for arity two *)

Lemma equiv_2 : forall A1 A2 B (Pf : val -> Prop) 
    (Q : A1 -> A2 ->(B->Prop)->Prop),
  (forall f, (forall K1:A1->~~val->Prop, is_spec_1 K1 ->
    (forall x, K1 x (fun P', forall g, 
      (forall K2:A2->~~B->Prop, is_spec_1 K2 ->
         (forall y, K2 y (Q x y)) -> spec_1 K2 g)
      -> P' g)) -> spec_1 K1 f) -> Pf f)
  <->
  (forall f, (forall K:A1->A2->~~B->Prop, is_spec_2 K ->
     (forall x y, K x y (Q x y)) -> spec_2 K f) -> Pf f).
Proof.
  split.
  (* correctness *)
  introv H1 H2. apply H1. clear H1. introv SK1 HK1.
  applys spec_weaken_1. 
  specializes H2 (fun x y R' =>
    forall K2:A2->~~B->Prop, is_spec_1 K2 -> K2 y (Q x y) -> K2 y R').
  sapply~ H2; clear H2.
    intros x y. intros_all. forwards* M: H. applys* H1. auto.
  simpl. intros x R WR HR. sapply SK1. sapply HK1.
  intros P' HP'. sapply WR. apply HR. clear HR.
  intros g Hg. apply HP'. clear HP'.
  introv SK2 HK2. applys spec_weaken_1. apply Hg. auto. clear Hg.
  simpl. intros y R' WR' HR'. intros. applys SK2. sapply HK2.
  intros z Hz. apply (HR' (fun (_:A2) (R':(B->Prop)->Prop) => R' z)).
    intros_all~. auto.
  (* completeness *)
  introv H1 H2. apply H1. clear H1. introv SK HK. split~.
  apply H2. intros_all~. clear H2. introv Hg.
  applys spec_weaken_1. apply~ (Hg (K x)). auto. auto.
Qed.
  

 *)
