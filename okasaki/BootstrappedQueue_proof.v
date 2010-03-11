Set Implicit Arguments.
Require Import FuncTactics LibCore.
Require Import QueueSig_ml QueueSig_proof.
Require Import BootstrappedQueue_ml.

(* todo: move, and try to prove implicit queues with it *)

Definition eq_gt_implies (P : (nat->Prop) -> Prop) :=
  forall n, (forall m, n > m -> P (eq m)) -> P (gt n).

Hint Unfold eq_gt_implies.

Lemma eq_gt_induction_2 : forall (P1 P2 : (nat->Prop) -> Prop),
  eq_gt_implies P1 -> eq_gt_implies P2 ->
  (forall n, P1 (gt n) -> P2 (gt n) -> P1 (eq n) /\ P2 (eq n)) ->
  (forall n, P1 (eq n)) /\ (forall n, P2 (eq n)).
Proof.
  introv H1 H2 R.
  cuts M: (forall n, P1 (eq n) /\ P2 (eq n)).
    split; intros n; specializes M n; auto*.
  induction n using peano_induction. apply R;
    match goal with K: eq_gt_implies ?Pi |- ?Pi _ =>
      apply K; intros; forwards*: H; try math end.
Qed.

Lemma conj_strengthen_2 : forall (Q1 Q2 P1 P2 : Prop),
  (Q1 -> P1) -> (Q2 -> P2) -> (Q1 /\ Q2) -> (P1 /\ P2).
Proof. auto*. Qed.

Lemma eq_gt_induction_5 : forall (P1 P2 P3 P4 P5 : (nat->Prop) -> Prop),
  eq_gt_implies P1 -> eq_gt_implies P2 -> eq_gt_implies P3 -> 
  eq_gt_implies P4 -> eq_gt_implies P5 ->
  (forall n, P1 (gt n) -> P2 (gt n) -> P3 (gt n) -> P4 (gt n) -> P5 (gt n) -> 
    P1 (eq n) /\ P2 (eq n) /\ P3 (eq n) /\ P4 (eq n) /\ P5 (eq n)) ->
  (forall n, P1 (eq n)) /\ (forall n, P2 (eq n)) /\ (forall n, P3 (eq n))
    /\ (forall n, P4 (eq n))  /\ (forall n, P5 (eq n)).
Proof. 
  introv H1 H2 H3 H4 H5 R.
  cuts M: (forall n, P1 (eq n) /\ P2 (eq n) /\ P3 (eq n) /\ P4 (eq n) /\ P5 (eq n)).
    splits; intros n; specializes M n; auto*.
  induction n using peano_induction. apply R;
    match goal with K: eq_gt_implies ?Pi |- ?Pi _ =>
      apply K; intros; forwards*: H; try math end.
Qed. 

Lemma conj_strengthen_5 : forall (Q1 Q2 Q3 Q4 Q5 P1 P2 P3 P4 P5 : Prop),
  (Q1 -> P1) -> (Q2 -> P2) -> (Q3 -> P3) -> (Q4 -> P4) -> (Q5 -> P5) ->
  (Q1 /\ Q2 /\ Q3 /\ Q4 /\ Q5) -> (P1 /\ P2 /\ P3 /\ P4 /\ P5).
Proof. auto*. Qed.


Module BootstrappedQueueSpec <: QueueSigSpec.

(** instantiations *)

Module Import Q <: MLQueue := MLBootstrappedQueue.
Import MLBootstrappedQueue.

(** invariant *)

Inductive doubling (A:Type) : bool -> int -> list (list A) -> Prop :=
  | doubling_nil : forall first n,
     doubling first n nil
  | doubling_cons : forall (first:bool) n l ls,
     doubling false (if first then n else 2*n) ls ->
     n <= length l ->
     doubling first n (l::ls).

Inductive inv : bool -> bool -> forall `{Rep a A}, queue a -> list A -> Prop :=
  | inv_empty : forall `{Rep a A} okb okf,
     inv okb okf _ Empty nil
  | inv_struct : forall `{Rep a A} (okb okf:bool) lenfm f m lenr r Qf Qr Qms Qm Q,
     Forall2 rep f Qf ->
     Forall2 rep r Qr ->
     inv true true _ m Qms ->
     Qm =' concat Qms ->
     lenr =' length r ->
     lenfm =' length Qf + length Qm ->
     Q =' Qf ++ Qm ++ rev Qr ->
     (if okf then f <> nil else True) ->
     (lenr:int) <= lenfm + (if okb then 0 else 1)->
     doubling true 1 Qms ->
     inv okb okf _ (Struct lenfm f m lenr r) Q.
     
Global Instance queue_rep `{Rep a A} : Rep (queue a) (list A) := 
  inv true true H.

(** automation *)
Hint Constructors doubling inv Forall2.
Hint Resolve Forall2_last.
Hint Extern 1 (@rep (queue _) _ _ _ _) => simpl.
Hint Extern 1 (@rep (queues _) _ _ _ _) => simpl.
Ltac auto_tilde ::= eauto with maths.

(** useful facts *)

Fixpoint depth a (q:queue a) : nat :=
  match q with
  | Empty => 0%nat
  | Struct lenfm f m lenr r => (1 + depth m)%nat
  end.

Lemma to_empty : forall `{Rep a A} Q,
  rep Empty Q -> Q = nil.
Proof. introv RQ. set_eq Q': Q. inverts~ RQ. Qed.
  (*todo: bug de inversion ! *)  

Lemma from_empty : forall `{Rep a A} q,
  rep q nil -> q = Empty.
Proof.
  introv RQ. set_eq q': q. inverts RQ as.
  auto.
  intros. destruct f. false. inverts H4. false.
Qed.

Lemma doubling_last_ind : forall A (l:list A) ls n,
  doubling false n ls -> 
  length (concat ls) + n <= length l ->
  doubling false n (ls&l).
Proof.
  induction ls; introv H L; inverts H; rew_list in *; auto~.
Qed.

Lemma doubling_last : forall A (l:list A) ls,
  doubling true 1 ls -> 
  length (concat ls) < length l ->
  doubling true 1 (ls&l).
Proof.
  introv H L. inverts H; rew_list in *.
  auto~.
  constructors~. apply~ doubling_last_ind.
Qed.

(** verification *)

Lemma empty_spec : forall `{Rep a A},
  rep (@empty a) (@nil A).
Proof. intros. gen A H. apply (empty_cf a). xgo~. Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma empty_inv : forall `{Rep a A},
  inv true true _ empty nil.
Proof. intros. apply empty_spec. Qed.

Hint Extern 1 (inv true true _ empty _) => apply empty_inv.

Lemma is_empty_spec : forall `{Rep a A},
  RepTotal is_empty (Q;queue a) >> bool_of (Q = nil).
Proof.
  xcf. intros q Q RQ. xgo.
  apply~ to_empty.
  intro_subst_hyp. applys C. apply~ from_empty.
Qed.

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Definition checkq_spec `{Rep a A} :=
  Spec checkq (q:queue a) |R>>
     forall Q, inv false false _ q Q -> R (Q ; queue a).

Definition checkf_spec `{Rep a A} :=
  RepSpec checkf (Q;queue a) |R>>
     Q <> nil -> R (is_head Q ;; a).

Definition head_spec `{Rep a A} :=
  RepSpec head (Q;queue a) |R>>
     Q <> nil -> R (is_head Q ;; a).

Definition tail_spec `{Rep a A} :=
  RepSpec tail (Q;queue a) |R>> 
     Q <> nil -> R (is_tail Q ;; queue a).

Definition snoc_spec `{Rep a A} :=
  RepTotal snoc (Q;queue a) (X;a) >> (Q & X) ; queue a.

Lemma all_specs : 
  checkq_spec /\ checkf_spec /\ head_spec /\ tail_spec /\ snoc_spec.
Proof.
  eapply conj_strengthen_5.
  apply eq_gt_induction_5.
Qed.

Definition head_spec := proj53 all_specs.
Definition tail_spec := proj54 all_specs.
Definition snoc_spec := proj55 all_specs.

Hint Extern 1 (RegisterSpec head) => Provide head_spec.
Hint Extern 1 (RegisterSpec tail) => Provide tail_spec.
Hint Extern 1 (RegisterSpec snoc) => Provide snoc_spec.

End BootstrappedQueueSpec.