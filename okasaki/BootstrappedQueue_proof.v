Set Bootstrapped Arguments.
Require Import FuncTactics LibCore.
Require Import QueueSig_ml QueueSig_proof.
Require Import BootstrappedQueue_ml.

(* todo: move, and try to prove implicit queues with it *)

Definition eg_gt_implies (P : (nat->Prop) -> Prop) :=
  (forall n, (forall m, n > m -> P (eq m)) -> P (gt n).

Hint Unfold eg_gt_implies.

Lemma eq_gt_induction_2 : forall (P1 P2 : (nat->Prop) -> Prop),
  eg_gt_implies P1 -> eg_gt_implies P2 ->
  (forall n, P1 (gt n) -> P2 (gt n) -> P1 (eq n) /\ P2 (eq n)) ->
  (forall n, P1 (eq n)) /\ (forall n, P2 (eq n)).
Proof. intros. induction n using peano_induction. auto. Qed. 

Lemma conj_strengthen_2 : forall (Q1 Q2 P1 P2 : Prop),
  (Q1 -> P1) -> (Q2 -> P2) -> (Q1 /\ Q2) -> (P1 /\ P2).
Proof. auto*. Qed.

Lemma eq_gt_induction_5 : forall (P1 P2 P3 P4 P5 : (nat->Prop) -> Prop),
  eg_gt_implies P1 -> eg_gt_implies P2 -> eg_gt_implies P3 -> 
  eg_gt_implies P4 -> eg_gt_implies P5 ->
  (forall n, P1 (gt n) -> P2 (gt n) -> P3 (gt n) -> P4 (gt n) -> P5 (gt n) -> 
    P1 (eq n) /\ P2 (eq n) /\ P3 (eq n) /\ P4 (eq n) /\ P5 (eq n)) ->
  (forall n, P1 (eq n)) /\ (forall n, P2 (eq n)) /\ (forall n, P3 (eq n))
    /\ (forall n, P4 (eq n))  /\ (forall n, P5 (eq n)).
Proof. intros. induction n using peano_induction. auto. Qed. 

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
  | doubling cons : forall first n l ls,
     doubling false (if first then n else 2*n) ls ->
     n <= length l ->
     doubling first n (l::ls).

Inductive inv : bool -> bool -> forall `{Rep a A}, queue a -> list A -> Prop :=
  | inv_empty : forall `{Rep a A} okb okf,
     inv okb okf _ Empty nil
  | inv_struct : forall `{Rep a A} okb okf lenfm f m lenr r Qf Qr Qms Qm Q,
     Forall2 rep f Qf ->
     Forall2 rep r Qr ->
     inv true true _ m Qms ->
     Qm =' concat Qms ->
     lenr =' length r ->
     lenfm =' length Qf + length Qm ->
     Q =' Qf ++ Qm ++ rev Qr ->
     (if okf then f <> nil else True) ->
     lenr <= lenfm + (if okb then 0 else 1) ->
     doubling true 1 Qms ->
     inv okb okf _ (Struct lenfm f m lenr r) Q
     
Global Instance queue_rep `{Rep a A} : Rep (queue a) (list A) := 
  inv true true H.

(** automation *)
Hint Constructors invd inv Forall2.
Hint Resolve Forall2_last.
Hint Extern 1 (@rep (queue _) _ _ _ _) => simpl.
Hint Extern 1 (@rep (queues _) _ _ _ _) => simpl.
Ltac auto_tilde ::= eauto.

(** useful facts *)

Fixpoint depth a (q:queue a) : nat :=
  match q with
  | Empty => 0%nat
  | Struct lenfm f m lenr r => (1 + depth m)%nat
  end.

Lemma to_empty : forall `{Rep a A} Q,
  rep Empty Q -> Q = nil.
Proof. introv RQ. inverts RQ as _ M. inverts~ M. Qed.

Lemma from_empty : forall `{Rep a A} q,
  rep q nil -> q = Empty.
Proof.
  introv RQ. inverts RQ as.
  introv _ ID. inverts~ ID.
  introv ? ? Df ? ? ?. inverts Df; false.
Qed.

Lemma doubling_last_ind : forall A l ls n,
  doubling false n ls -> 
  length ls + n <= length l ->
  doubling false n (ls&l).
Proof.
  induction ls.
Qed.

Lemma doubling_last : forall A l ls n,
  doubling true 1 ls -> 
  length ls < length l ->
  doubling true 1 (ls&l).
Proof.
  inversion H. apply doubling_last_ind.
Qed.

(** verification *)

Lemma empty_spec : forall `{Rep a A},
  rep (@empty a) (@nil A).
Proof. intros. gen A H. apply (empty_cf a). xgo~. Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma empty_inv : forall `{Rep a A},
  inv _ empty nil.
Proof. intros. apply empty_spec. Qed.

Hint Extern 1 (inv _ empty _) => apply empty_inv.

Lemma is_empty_spec : forall `{Rep a A},
  RepTotal is_empty (Q;queue a) >> bool_of (Q = nil).
Proof.
Qed.

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Definition checkq_spec := forall `{Rep a A},
  RepSpec head (Q;queue a) |R>>
     Q <> nil -> R (is_head Q ;; a).

Definition checkf_spec := forall `{Rep a A},
  RepSpec head (Q;queue a) |R>>
     Q <> nil -> R (is_head Q ;; a).

Definition head_spec := forall `{Rep a A},
  RepSpec head (Q;queue a) |R>>
     Q <> nil -> R (is_head Q ;; a).

Definition tail_spec := forall `{Rep a A},
  RepSpec tail (Q;queue a) |R>> 
     Q <> nil -> R (is_tail Q ;; queue a).

Definition snoc_spec := forall `{Rep a A},
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