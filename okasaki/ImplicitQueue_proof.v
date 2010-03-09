Set Implicit Arguments.
Require Import FuncTactics LibCore.
Require Import QueueSig_ml QueueSig_proof.
Require Import ImplicitQueue_ml.

Module ImplicitQueueSpec <: QueueSigSpec.

(** instantiations *)

Module Import Q <: MLQueue := MLImplicitQueue.
Import MLImplicitQueue.

(** invariant *)

Global Instance queue_rep `{Rep a_ A} : Rep (queue a_) (list A) :=
  fun (q:queue a_) (Q:list A) => Q = nil.
  (*let (f,r) := q in 
     Forall2 rep (f ++ rev r) Q
  /\ (f = nil -> r = nil).*)

  (*todo: xisspec loop is invariant is just true *)

(** automation *)

Hint Constructors Forall2.
Hint Resolve Forall2_last.
Hint Unfold is_head is_tail.
(*
Hint Extern 1 (@rep (queue _) _ _ _ _) => simpl; rew_list.
Hint Extern 1 (@rep (queues _) _ _ _ _) => simpl; rew_list.
*)

Ltac auto_star ::= try solve [ rew_list in *; intuition (eauto) ].


(** useful facts *)

(** verification *)

Definition spec_hyp_2 (A1 A2 B : Type)
  (P:A1->A2->Prop) (K:A1->A2->~~B->Prop) f :=
  spec_2 (fun x1 x2 R => P x1 x2 -> K x1 x2 R) f.

(*
Lemma spec_hyp_size : forall (A1 A2 : Type) (mu:A1->A2->nat) (B : Type)
  (P:A1->A2->Prop) (K:A1->A2->~~B->Prop) f,
  is_spec
  (forall n, spec_hyp_2 (fun x1 x2 => n = mu x1 x2) K f) ->
  spec_2 K f.
*)

Ltac xintros_core cont1 cont2 cont3 ::=
   let arity := spec_goal_arity tt in
   let lemma := get_spec_intro_x arity in
   apply lemma; [ instantiate; cont1 tt | instantiate; cont2 tt | instantiate; cont3 tt ]. 

Ltac xcurried_core ::=
  let arity := spec_goal_arity tt in
  let lemma := get_curried_prove_x arity in
  eapply lemma; try solve [ xcf; auto; instantiate; try xisspec ].

Lemma good_induct : forall (P : (nat->Prop) -> Prop),
  (forall n, (forall m, n > m -> P (eq m)) -> P (gt n)) ->
  (forall n, P (gt n) -> P (eq n)) ->
  (forall n, P (eq n)).
Proof. intros. induction n using peano_induction. auto. Qed. 

Ltac name_around e x :=
  pattern e; match goal with |- ?P _ => sets x: P end.

Ltac xcf_for_core f ::=
 ltac_database_get database_cf f;
  let H := fresh "TEMP" in intros H; 
  match type of H with
  | tag tag_topfun _ _ => sapply H; [ instantiate; try xisspec | ]
  | _ => sapply H
  end; clear H; xcf_post tt.

Lemma snoc_spec : forall `{Rep a A},
  RepTotal snoc (Q;queue a) (X;a) >> (Q & X) ; queue a.
Proof.
  intros. xintros. intros. sets_eq n: (length Q). gen x1 x2 Q X.
  gen H. gen a A. apply~ good_induct; clears n.
  introv IH RQ N RX. subst_hyp N.
  xcf_app; auto. xisspec. (* todo: automate xisspec *)
  xmatch.
  
Qed.

Hint Extern 1 (RegisterSpec snoc) => Provide snoc_spec.






Section Polymorphic.
Variables (a_ A : Type) (RA:Rep a_ A).

Lemma empty_spec : 
  rep (@empty a_) (@nil A).
Proof.
  generalizes RA A. apply (empty_cf a_). xgo.
  intros. simpl. rew_list*. (*todo: rew_list~*)
Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma is_empty_spec : 
  RepTotal is_empty (Q;queue a_) >> bool_of (Q = nil).
Proof.
  xcf. intros (f0,r0) l [H M]. xgo.
  rewrite~ M in H. inverts~ H.
  intro_subst_hyp. inverts H as K.
   destruct (nil_eq_app_rev_inv K). false.
Qed.

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Lemma checkf_spec : 
  Spec checkf (q:queue a_) |R>>
    forall Q, (let (f,r) := q in Forall2 rep (f ++ rev r) Q) ->
    R (Q ; queue a_).
Proof.
  xcf. intros (f,r) l K. xgo; rew_list in K.
  auto~. split; auto_false.
Qed.

Hint Extern 1 (RegisterSpec checkf) => Provide checkf_spec.

Lemma snoc_spec : 
  RepTotal snoc (Q;queue a_) (X;a_) >> (Q & X) ; queue a_.
Proof.
  xcf. intros [f r] x. introv [H M] RX. xgo~.
  rew_list. rewrite~ <- app_assoc.
Qed.

Hint Extern 1 (RegisterSpec snoc) => Provide snoc_spec.

Lemma head_spec : 
  RepSpec head (Q;queue a_) |R>>
     Q <> (@nil A) -> R (is_head Q ;; a_).
Proof.
  xcf. intros [f r] q. introv [H M] NE. xgo; rew_list in H.
  rewrite~ M in H. inverts~ H.
  inverts~ H.
Qed.

Hint Extern 1 (RegisterSpec head) => Provide head_spec.

Lemma tail_spec :
  RepSpec tail (Q;queue a_) |R>> 
     Q <> nil -> R (is_tail Q ;; queue a_).
Proof.
  xcf. intros [f r] q. introv [H M] NE. xmatch.
  xgo. rewrite~ M in H. inverts~ H.
  inverts H. xgo~.
  (*todo: use ximpl for ( ; ) ==> ( ;; ) *)
Qed.

Hint Extern 1 (RegisterSpec tail) => Provide tail_spec.

End Polymorphic.

End ImplicitQueueSpec.