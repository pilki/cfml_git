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
  | inv_struct : forall `{Rep a A} (okb okf:bool) (lenfm:int) f m (lenr:int) r Qf Qr Qms Qm Q,
     rep f Qf ->
     rep r Qr ->
     inv true true _ m Qms ->
     Qm =' concat Qms ->
     lenr =' length Qr ->
     lenfm =' length Qf + length Qm ->
     Q =' Qf ++ Qm ++ rev Qr ->
     (if okf then f <> nil else True) ->
     (lenr:int) <= lenfm + (if okb then 0 else 1)->
     doubling true 1 Qms ->
     inv okb okf _ (Struct lenfm f m lenr r) Q.
     
Implicit Arguments inv [[a] [A] [H]].

Global Instance queue_rep `{Rep a A} : Rep (queue a) (list A).
Proof.
  intros. apply (Build_Rep (inv true true)).
  introv H1 H2. gen Y. induction H1; introv M.
  set_eq Y': Y. inverts~ M.
  set_eq Y': Y. inverts~ M. lets: (IHinv _ H20). subst. prove_rep.
Defined.

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

Lemma doubling_weaken_n : forall A (ls:list (list A)) n m,
  doubling false n ls -> m <= n -> doubling false m ls.
Proof.
  introv H. gen_eq b: false; gen_eq n':n. gen m n.
  induction H; intros; subst.
  auto.
  constructors. subst. apply~ IHdoubling. math.
Qed.

Lemma doubling_weaken_f : forall A (ls:list (list A)),
  doubling false 1 ls -> doubling true 1 ls.
Proof.
  introv H. inverts H. auto. constructors~.
  apply~ doubling_weaken_n.
Qed.

(** verification *)

Lemma empty_spec : forall `{Rep a A},
  rep (@empty a) (@nil A).
Proof. intros. gen A H. apply (empty_cf a). xgo~. Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma empty_inv : forall `{Rep a A},
  inv true true empty nil.
Proof. intros. apply empty_spec. Qed.

Hint Extern 1 (inv true true empty _) => apply empty_inv.

Lemma is_empty_spec : forall `{Rep a A},
  RepTotal is_empty (Q;queue a) >> bool_of (Q = nil).
Proof.
  xcf. intros q Q RQ. xgo.
  apply~ to_empty.
  intro_subst_hyp. applys C. apply~ from_empty.
Qed.

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Coercion queue_of_body a (q:body a) : queue a :=
  let '(lenfm,f,m,lenr,r) := q in
  Struct lenfm f m lenr r.


Definition checkq_spec `{Rep a A} :=
  Spec checkq (q:body a) |R>>
     forall Q, inv false false q Q -> R (Q ; queue a).

Definition checkf_spec `{Rep a A} :=
  Spec checkf (q:body a) |R>>
     forall Q, inv true false q Q -> R (Q ; queue a).

Definition snoc_spec `{Rep a A} :=
  RepTotal snoc (Q;queue a) (X;a) >> (Q & X) ; queue a.
Definition head_spec `{Rep a A} :=
  RepSpec head (Q;queue a) |R>>
     Q <> nil -> R (is_head Q ;; a).

Definition tail_spec `{Rep a A} :=
  RepSpec tail (Q;queue a) |R>> 
     Q <> nil -> R (is_tail Q ;; queue a).

Ltac all_specs_go :=
  unfolds; first [ xintros; instantiate;  
    [ xcf; auto; 
      try match goal with H: Rep ?a _ |- _ => instantiate (1 := a) end;
      try xisspec | ]
  | xintros ].

Hint Extern 1 (@gt nat _ _ _) => simpl; math.

Lemma list_rep_cons : forall `{Rep a A} l L x X,
  rep l L -> rep x X -> rep (x::l) (X::L).
Proof. intros. constructors~. Qed.
Hint Resolve @list_rep_cons.

Lemma cons_neq_nil : forall A (x:A) l, x::l <> nil.
Proof. auto_false. Qed.
Hint Immediate cons_neq_nil.

Lemma Forall2_rev : forall A1 A2 (P:A1->A2->Prop) l1 l2,
  Forall2 P l1 l2 -> Forall2 P (rev l1) (rev l2).
Proof. induction l1; introv M; inverts M; rew_rev; auto. Qed.
Hint Resolve Forall2_rev.

Lemma concat_doubling_length : forall A (Qms:list (list A)),
  doubling true 1 Qms -> length Qms <= length (concat Qms).
Proof.
  introv D. sets_eq n:1. asserts~ M: (n >= 1). clear EQn.
  gen M. induction D; intros; subst.
  rew_length~. destruct first; rew_list in *.
   forwards~: IHD. maths (2*n>=1). lets~: (IHD H0).
Qed.

Lemma decrease_r : forall A (Q Qf Qm Qr : list A) Qms,
  Q = Qf ++ Qm ++ rev Qr ->
  0 < length Qr -> 
  Qm = concat Qms ->
  doubling true 1 Qms ->
  length Qms < length Q.
Proof.
  introv E L Em Dm. destruct Qr. gen L. rew_list~. 
  forwards: (concat_doubling_length Dm).
  subst Q Qm. rew_length~.
Qed.

Lemma decrease_f : forall `{Rep a A} f (Q Qf Qm Qr : list A) Qms,
  Q = Qf ++ Qm ++ rev Qr ->
  f <> nil -> rep f Qf ->
  Qm = concat Qms ->
  doubling true 1 Qms ->
  length Qms < length Q.
Proof.
  introv E L R Em Dm. destruct f. false. inverts R.
  forwards: (concat_doubling_length Dm).
  subst Q Qm. rew_length~.
Qed.

Lemma all_specs : 
  (forall `{Rep a A}, checkq_spec) /\ 
  (forall `{Rep a A}, checkf_spec) /\ 
  (forall `{Rep a A}, snoc_spec) /\
  (forall `{Rep a A}, head_spec) /\
  (forall `{Rep a A}, tail_spec).
Proof.
  eapply conj_strengthen_5; try intros M; intros; try all_specs_go.
  intros q. intros. gen_eq n:((3 * depth q + 1)%nat). gen n a A q Q H0. apply M.
  intros q. intros. gen_eq n:((3 * depth q)%nat). gen n a A q Q H0. apply M.
  intros q x. intros. gen_eq n:((3 * depth q + 2)%nat). gen n a A q x Q X H0 H1. apply M.
  intros q. intros. gen_eq n:((3 * depth q + 2)%nat). gen n a A q Q H0 H1. apply M.
  intros q. intros. gen_eq n:((3 * depth q + 2)%nat). gen n a A q Q H0 H1. apply M.
  forwards (H1&H2&H3&H4&H5): (eq_gt_induction_5);
    try match goal with |- _ /\ _ /\ _ /\ _ /\ _ =>
      splits; intros n; pattern (eq n);
      [ apply H1 | apply H2 | apply H3 | apply H4 | apply H5 ] end;
    auto~.
  introv IHcheckq IHcheckf IHsnoc IHhead IHtail. simpls. splits.
  (* verification of checkq *)
  clear IHcheckq IHhead IHtail.
  introv RQ N. subst n. xcf_app. xmatch. xif.
  inverts RQ. subst q. xapp. constructors~. auto~.
  inverts RQ. subst q. (* ? xapp (>>> (list a) Qms (rev Qr)). *)
  specializes IHsnoc (>>> (list a) Qms (rev Qr)). xapp~. simpls.
(*   subst Qm. forwards~: (>>> decrease_r H19). simpls.*)
  xapp. constructors~. subst Qm. rew_list~. subst Q Qm. rew_list~.
  apply~ doubling_last. subst Qm. rew_length~.
  simpl. math. skip. (* décroissance pas bonne *)
  (* verification of checkf *)
  clear IHcheckq IHcheckf IHsnoc.
  introv RQ N. subst n. xcf_app. xmatch. xmatch.
  xgo. inverts RQ as. introv EQm LR LFM _ Le D RF RM RR EQ.
   subst Qm. inverts RF. inverts RM. rew_list in LFM.
    forwards~ M: (@length_zero_inv _ Qr). subst Qr. 
    inverts RR. subst Q. rew_list. constructors~.
  inverts RQ. inverts H9. 
  specializes IHhead (>>> (list a) Qms). xapp~. clear IHhead.
   intro_subst_hyp. applys C. fequals. apply~ @from_empty.
  subst Qm. skip.
  destruct P_x2 as (Hm'&RHm'&[Tm' EQms']). 
  specializes IHtail (>>> (list a) Qms). xapp~. clear IHtail.
skip.
  destruct P_x3 as (Tm&RHm&[Hm EQms]). 
  subst Qms. injects EQms. subst Q Qm. xgo.
  rew_list in H18. inverts H22 as K P. constructors~. rew_list~.
   intro_subst_hyp. inverts RHm'. rew_list in P. math.
   apply~ doubling_weaken_f.
  xgo. inverts RQ. constructors~. intro_subst_hyp. inverts H10. false~ C0.
  (* verification of snoc *)
  clear IHcheckf IHsnoc IHhead IHtail.
  introv RQ RX N. subst n. xcf_app. xgo.
  inverts RQ. constructors~.
  inverts RQ. constructors~. rew_list~. subst. rew_list~.
  rew_length~.
  (* verification of head *)
  clear IHcheckf IHcheckq IHsnoc IHhead IHtail.
  introv RQ NE N. subst n. xcf_app. xgo.
  inverts RQ. false.
  inverts RQ. inverts~ H9.
  inverts RQ. false. destruct f; false.
  (* verification of tail *)
  clear IHcheckf IHsnoc IHhead IHtail.
  introv RQ RX N. subst n. xcf_app. xmatch.
  xgo. inverts RQ. false.
  inverts RQ. inverts H9. specializes IHcheckq a (l2 ++ Qm ++ rev Qr).
  xapp. clear IHcheckq.
   constructors~. subst. rew_list~.
  auto~.
  ximpl~.
  xgo. inverts RQ. false. destruct f; false.
Qed.

Definition head_spec := proj53 all_specs.
Definition tail_spec := proj54 all_specs.
Definition snoc_spec := proj55 all_specs.

Hint Extern 1 (RegisterSpec head) => Provide head_spec.
Hint Extern 1 (RegisterSpec tail) => Provide tail_spec.
Hint Extern 1 (RegisterSpec snoc) => Provide snoc_spec.

End BootstrappedQueueSpec.

(*


Axiom factorize : forall (P1 P2 P3 P4 P5 : nat -> Prop),
  (forall n, P1 n /\ P2 n /\ P3 n /\ P4 n /\ P5 n) ->
  (forall n, P1 (n)) /\ (forall n, P2 (n)) /\ (forall n, P3 (n))
    /\ (forall n, P4 (n))  /\ (forall n, P5 (n)).

Lemma eq_gt_induction_5' : forall (P1 P2 P3 P4 P5 : (nat->Prop) -> Prop),
  eq_gt_implies P1 -> eq_gt_implies P2 -> eq_gt_implies P3 -> 
  eq_gt_implies P4 -> eq_gt_implies P5 ->
  (forall n, P1 (gt n) -> P2 (gt n) -> P3 (gt n) -> P4 (gt n) -> P5 (gt n) -> 
    P1 (eq n) /\ P2 (eq n) /\ P3 (eq n) /\ P4 (eq n) /\ P5 (eq n)) ->
  (forall n, P1 (eq n) /\ P2 (eq n) /\ P3 (eq n) /\ P4 (eq n) /\ P5 (eq n)).
Proof. 
  introv H1 H2 H3 H4 H5 R.
  induction n using peano_induction. apply R;
    match goal with K: eq_gt_implies ?Pi |- ?Pi _ =>
      apply K; intros; forwards*: H; try math end.
Qed. 

Axiom go :forall (P1 P2 P3 P4 P5 : (nat->Prop) -> Prop),
 (forall n, P1 (eq n) /\ P2 (eq n) /\ P3 (eq n) /\ P4 (eq n) /\ P5 (eq n)).
(*
Lemma conj_strengthen_5' : forall (Q1 Q2 Q3 Q4 Q5 P1 P2 P3 P4 P5 : (nat -> Prop) -> Prop),
  (Q1 -> P1) -> (Q2 -> P2) -> (Q3 -> P3) -> (Q4 -> P4) -> (Q5 -> P5) ->
  (Q1 /\ Q2 /\ Q3 /\ Q4 /\ Q5) -> (P1 /\ P2 /\ P3 /\ P4 /\ P5).
Proof. auto*. Qed.
*)

(*
Axiom go' :forall (P1 : (nat->Prop) -> Prop),
 (forall n, P1 (eq n)).

Axiom go'' :forall f n  (P1 P2 : (nat->Prop) -> Prop),
 (f = eq n -> (P1 f /\ P2 f)).
*)
*)