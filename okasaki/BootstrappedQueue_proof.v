Set Implicit Arguments.
Require Import FuncTactics LibCore.
Require Import QueueSig_ml QueueSig_proof.
Require Import BootstrappedQueue_ml.

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
 
(** model *)
    
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
Hint Resolve Forall2_last Forall2_rev.
Hint Immediate cons_neq_nil.
Ltac auto_tilde ::= eauto with maths.
Hint Extern 1 (@gt nat _ _ _) => simpl; math.

(** useful facts *)

Coercion queue_of_body a (q:body a) : queue a :=
  let '(lenfm,f,m,lenr,r) := q in
  Struct lenfm f m lenr r.

Definition is_empty_front a (q:body a) : bool :=
  let '(lenfm,f,m,lenr,r) := q in
  match f with nil => true | _ => false end.

Lemma to_empty : forall `{Rep a A} Q,
  rep Empty Q -> Q = nil.
Proof. introv RQ. set_eq Q': Q. inverts~ RQ. Qed.

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

Lemma concat_doubling_length : forall A (Qms:list (list A)),
  doubling true 1 Qms -> length Qms <= length (concat Qms).
Proof.
  introv D. sets_eq n:1. asserts~ M: (n >= 1). clear EQn.
  gen M. induction D; intros; subst.
  rew_length~. destruct first; rew_list in *.
   forwards~: IHD. maths (2*n>=1). lets~: (IHD H0).
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

Definition checkq_specs `{Rep a A} :=
  Spec checkq (q:body a) |R>>
    forall Q, inv false false q Q -> R (Q ;- queue a).

Definition checkf_specs `{Rep a A} :=
  Spec checkf (q:body a) |R>>
    forall Q, inv true false q Q -> R (Q ;- queue a).

Definition snoc_specs `{Rep a A} :=
  RepTotal snoc (Q;queue a) (X;a) >> (Q & X) ;- queue a.

Definition head_specs `{Rep a A} :=
  RepSpec head (Q;queue a) |R>>
    Q <> nil -> R (is_head Q ;; a).

Definition tail_specs `{Rep a A} :=
  RepSpec tail (Q;queue a) |R>> 
    Q <> nil -> R (is_tail Q ;; queue a).

Lemma all_specs : 
  (forall `{Rep a A}, checkq_specs) /\ 
  (forall `{Rep a A}, checkf_specs) /\ 
  (forall `{Rep a A}, snoc_specs) /\
  (forall `{Rep a A}, head_specs) /\
  (forall `{Rep a A}, tail_specs).
Proof.
  eapply conj_strengthen_5; try intros M; intros; try (unfolds; xintros).
  intros q. intros. gen_eq n:((if is_empty_front q 
    then 3 * length Q + 3 else 3 * length Q - 2)%nat).
    gen n a A q Q H0. apply M.
  intros q. intros. gen_eq n:(if is_empty_front q 
    then (3 * length Q + 2)%nat else 0%nat).
    gen n a A q Q H0. apply M.
  intros q x. intros. gen_eq n:((3 * length Q + 2)%nat). gen n a A q x Q X H0 H1. apply M.
  intros q. intros. gen_eq n:(0%nat). gen n a A q Q H0 H1. apply M.
  intros q. intros. gen_eq n:((3 * length Q + 1)%nat). gen n a A q Q H0 H1. apply M.
  forwards (H1&H2&H3&H4&H5): (eq_gt_induction_5);
    try match goal with |- _ /\ _ /\ _ /\ _ /\ _ =>
      splits; intros n; pattern (eq n);
      [ apply H1 | apply H2 | apply H3 | apply H4 | apply H5 ] end;
    auto~.
  introv IHcheckq IHcheckf IHsnoc IHhead IHtail. simpls. splits.
  (* verification of checkq *)
  clear IHcheckq IHhead IHtail.
  introv RQ N. subst n. xcf_app. xmatch; inverts RQ.
  rename H9 into RQf. xif.
  subst q. xapp. constructors~. simpl. destruct f.
    math. 
    inverts RQf. subst Q. rew_list~.
  forwards~: (@concat_doubling_length _ Qms).
   specializes IHsnoc (>>> (list a) Qms (rev Qr)). xapp~; clear IHsnoc.
     destruct f; simpl.
       subst Q Qm. rew_list~.
       inverts RQf. subst Q Qm. rew_list~.
   simpls. xapp~.
     constructors~.
       subst. rew_list~.
       subst. rew_list~.
       apply~ doubling_last. subst Qm. rew_length~.
     destruct f; simpl. math. inverts RQf. subst Q. rew_length~. 
  (* verification of checkf *)
  clear IHcheckq IHcheckf IHsnoc.
  introv RQ N. subst n. xcf_app. xmatch. xmatch.
  xgo. inverts RQ as. introv EQm LR LFM _ Le D RF RM RR EQ.
   subst Qm. inverts RF. inverts RM. rew_list in LFM.
    forwards~ M: (@length_zero_inv _ Qr). subst Qr. 
    inverts RR. subst Q. rew_list. constructors~.
  inverts RQ. inverts H9. 
   specializes IHhead (>>> (list a) Qms). xapp~. 
    intro_subst_hyp. applys C. fequals. apply~ @from_empty.
   clear IHhead. destruct P_x2 as (Hm'&RHm'&[Tm' EQms']). 
   specializes IHtail (>>> (list a) Qms). xapp~.
    simpl. subst Q Qm. rew_length. 
    forwards~: (@concat_doubling_length _ Qms).
   clear IHtail. destruct P_x3 as (Tm&RHm&[Hm EQms]). 
   subst Qms. injects EQms. subst Q Qm. xgo.
   rew_list in H18. inverts H22 as K P. constructors~. rew_list~.
    intro_subst_hyp. inverts RHm'. rew_list in P. math.
    apply~ doubling_weaken_f.
  xgo. inverts RQ. constructors~. intro_subst_hyp. inverts H10. false~ C0.
  (* verification of snoc *)
  clear IHcheckf IHsnoc IHhead IHtail.
  introv RQ RX N. subst n. xcf_app. inverts RQ; xgo.
  constructors~.
  constructors~. rew_length~. subst Q. rew_list~.
  simpl. destruct f. false. rew_length~.
  (* verification of head *)
  clear IHcheckf IHcheckq IHsnoc IHhead IHtail.
  introv RQ NE N. subst n. xcf_app. inverts RQ. false. 
  xgo. inverts~ H4. destruct f; false.
  (* verification of tail *)
  clear IHcheckf IHsnoc IHhead IHtail.
  introv RQ RX N. subst n. xcf_app. inverts RQ. false. xmatch.
  inverts H4. specializes IHcheckq a (l2 ++ Qm ++ rev Qr).
   xapp; clear IHcheckq.
     constructors~. subst. rew_list~.
     simpl. subst Q. rew_length. destruct f'; math.
     ximpl~.
  xgo. destruct f; false.
Qed.

Lemma head_spec : forall `{Rep a A}, head_specs.
Proof. intros. apply~ (proj54 all_specs). Qed.

Lemma tail_spec : forall `{Rep a A}, tail_specs.
Proof. intros. apply~ (proj55 all_specs). Qed.

Lemma snoc_spec : forall `{Rep a A}, snoc_specs.
Proof. intros. apply~ (proj53 all_specs). Qed.

Hint Extern 1 (RegisterSpec head) => Provide head_spec.
Hint Extern 1 (RegisterSpec tail) => Provide tail_spec.
Hint Extern 1 (RegisterSpec snoc) => Provide snoc_spec.

End BootstrappedQueueSpec.
