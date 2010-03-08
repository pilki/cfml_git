Set Implicit Arguments.
Require Import FuncTactics LibCore.
Require Import DequeSig_ml DequeSig_proof.
Require Import BankersDeque_ml.

Definition C := 2.

Lemma c_val : c = C.
Proof. xgo~. Qed.


Module BankersQueueSpec <: QueueSigSpec.

(** instantiations *)

Module Import Q <: MLDeque := MLBankersDeque.
Import MLBankersDeque.

(** invariant *)

Definition inv (d:int) `{Rep a_ A} (q:deque a_) (Q:list A) :=
  let '(lenf,f,lenr,r) := q in 
     Forall2 rep (f ++ rev r) Q
  /\ lenf = length f
  /\ lenr = length r
  /\ lenf <= C*lenr + 1 + d
  /\ lenr <= C*lenf + 1 + d.

Global Instance deque_rep `{Rep a_ A} : Rep (deque a_) (list A) :=
  inv 0.

(** automation *)

Lemma C_val2 : C = 2.
Proof. auto. Qed.
Lemma c_val2 : c = 2.
Proof. rewrite~ c_val. Qed.
Hint Rewrite C_val2 c_val2 : rew_maths.

Hint Constructors Forall2.
Hint Resolve Forall2_last.
Hint Extern 1 (@rep (deque _) _ _ _ _) => simpl.
Hint Unfold inv.

Ltac auto_tilde ::= eauto with maths.

Section Polymorphic.
Variables (a_ A : Type) (RA:Rep a_ A).

(** useful facts *)

Lemma empty_from_len : forall f lenf lenr r Q,
  rep (lenf, f, lenr, r) Q -> lenf + lenr = 0 -> Q = nil.
Proof.
  introv (H&LF&LR&CF&CR) L.  
  rewrite~ (@length_zero_inv _ r) in H.
  rewrite~ (@length_zero_inv _ f) in H.
  inverts~ H.
Qed.

Lemma empty_from_list : forall lenf lenr Q,
  rep (lenf, nil, lenr, nil) Q -> Q = nil.
Proof.
  introv K. lets (H&LF&LR&CF&CR): K.
  rew_list in *. apply~ empty_from_len.
Qed.

Lemma singleton_right : forall lenf lenr x r Q,
  rep (lenf, nil, lenr, x::r) Q -> r = nil.
Proof.
  introv (H&LF&LR&CF&CR). rew_list in *.
  apply~ length_zero_inv.
Qed.

Lemma singleton_left : forall lenf lenr x f Q,
  rep (lenf, x::f, lenr, nil) Q -> f = nil.
Proof.
  introv (H&LF&LR&CF&CR). rew_list in *.
  apply~ length_zero_inv.
Qed.

(** verification *)

Lemma empty_spec : 
  rep (@empty a_) (@nil A).
Proof.
  generalizes RA A. apply (empty_cf a_). xgo.
  intros. simpl. rew_list~.
Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma is_empty_spec : 
  RepTotal is_empty (Q;deque a_) >> bool_of (Q = nil).
Proof.
  xcf. intros (((lenf,f),lenr),r) Q RQ. xgo.
  unfolds. extens. iff Z; fold_prop; subst.
  apply~ empty_from_len.
  intuit RQ. inverts H. destruct (nil_eq_app_rev_inv H5). subst~.
Qed. 

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Ltac xauto_tilde_default cont ::= 
  check_not_a_tag tt;  
  try solve [ cont tt | apply refl_equal | substs; if_eq; solve [ cont tt | apply refl_equal ] ].

Ltac xret_pre cont := 
  match ltac_get_tag tt with
  | tag_ret => cont tt
  | tag_let => xlet; [ cont tt | instantiate ]
  end.  

Tactic Notation "xret" :=  (* todo: fonctions ltac *)
  xret_pre ltac:(fun _ => xret_noclean; xclean).
Tactic Notation "xret" "~" :=  
  xret; xauto~.
Tactic Notation "xret" "*" :=  
  xret; xauto*.

Axiom div2_bounds : forall m n,
  m = n / 2 -> n <= 2 * m /\ 2 * m <= n + 1.
Implicit Arguments div2_bounds [m n].

Axiom abs_pos_le : forall (n:int) (m:nat),
  0 <= n -> n <= m -> abs n <= m.

Axiom rev_rev : forall A (l:list A), rev (rev l) = l.
Hint Rewrite rev_rev : rew_list.

Axiom nat_int_eq : forall (n:int) (m:nat),
  m = abs n -> m = n :> int.
Implicit Arguments nat_int_eq [n m].

Lemma check_spec : 
  Spec check (q:deque a_) |R>>
    forall Q, inv 2 q Q ->
    R (Q ; deque a_).
Proof.
  xcf. intros (((lenf,f),lenr),r) Q (H&LF&LR&CF&CR).
  xmatch. xcases.
  (* rebalance left *) 
  xret~. xret~.
  lets (B1&B2): (div2_bounds (eq_sym Pi)).
  asserts: (0 <= i /\ i <= length f). math. (*todo: math E *)
  xgo~. forwards~ (Ef&Lf'&Lx14): take_and_drop. apply~ abs_pos_le.
  lets: (nat_int_eq Lf'). hnf. splits.
    gen H. rewrite Ef. rewrite <- Pr'. rew_list~.
    auto~.
    subst r'. rew_length~.
    math.
    math.   
  (* rebalance right *)
  xret~. xret~.
  lets (B1&B2): (div2_bounds (eq_sym Pi)).
  asserts: (0 <= i /\ i <= length r). math. (*todo: math E *)
  xgo~. forwards~ (Er&Lr'&Lx10): take_and_drop. apply~ abs_pos_le.
  lets: (nat_int_eq Lr'). hnf. splits.
    gen H. rewrite Er. rewrite <- Pf'. rew_list~.
    subst f'. rew_length~.
    auto~.
    math.
    math.   
  (* no rebalance *)
  xgo. simpl. subst q. splits~.
Qed.

Hint Extern 1 (RegisterSpec check) => Provide check_spec.

Lemma cons_spec : 
  RepTotal cons (X;a_) (Q;deque a_) >> (X::Q) ; deque a_.
Proof.
  xcf. intros x (((lenf,f),lenr),r) X Q RX RQ. 
  xgo; ximpl_nointros. intuit RQ. splits~; rew_list~. 
Qed.

Hint Extern 1 (RegisterSpec cons) => Provide cons_spec.

Lemma head_spec : 
  RepSpec head (Q;deque a_) |R>>
     Q <> (@nil A) -> R (is_head Q ;; a_).
Proof.
  xcf. intros (((lenf,f),lenr),r) Q RQ NE. xgo; xcleanpat.
  apply NE. apply~ empty_from_list.
  rewrite (singleton_right RQ) in RQ. intuit RQ.
   rew_list in H. inverts~ H.
  intuit RQ. rew_list in H. inverts~ H.
Qed.

Hint Extern 1 (RegisterSpec head) => Provide head_spec.

Hint Resolve empty_spec.

Lemma tail_spec :
  RepSpec tail (Q;deque a_) |R>> 
     Q <> nil -> R (is_tail Q ;; deque a_).
Proof.
  xcf. intros (((lenf,f),lenr),r) Q RQ NE. xmatch; xcleanpat.
  xgo. apply NE. apply~ empty_from_list.
  xgo. rewrite (singleton_right RQ) in RQ. intuit RQ.
   rew_list in H. inverts H. inverts~ H6. 
  intuit RQ. rew_list in *. inverts H.
   xapp. fapplys HR. constructors~. ximpl~.
Qed.

Hint Extern 1 (RegisterSpec tail) => Provide tail_spec.

Lemma snoc_spec : 
  RepTotal snoc (Q;deque a_) (X;a_) >> (Q & X) ; deque a_.
Proof.
  xcf. intros (((lenf,f),lenr),r) x Q X RQ RX.
  xgo; ximpl_nointros. intuit RQ. splits~; rew_list~.
  rewrite~ <- app_assoc.
Qed.

Hint Extern 1 (RegisterSpec snoc) => Provide snoc_spec.

Lemma is_last_one : forall A (x:A),
  is_last (x::nil) x.
Proof. intros. unfolds. exists~ (@nil A0). Qed.
Hint Resolve is_last_one.

Lemma is_init_one : forall A (x:A),
  is_init (x::nil) nil.
Proof. intros. unfolds. exists~ x. Qed.
Hint Resolve is_init_one.

(*
*)


Section PropProperties2.
Variables A1 A2 : Type.
Implicit Types l : list A1.
Implicit Types r : list A2.
Hint Constructors Forall2.

Lemma Forall2_last_inv : forall P l1 r' x1, 
  Forall2 P (l1 & x1) r' ->
  exists r2 x2, r' = r2 & x2 /\ Forall2 P l1 r2 /\ P x1 x2.
Admitted. (* todo *)

End PropProperties2.

Implicit Arguments Forall2_last_inv [A1 A2 P l1 r' x1].



Lemma last_spec : 
  RepSpec last (Q;deque a_) |R>>
     Q <> (@nil A) -> R (is_last Q ;; a_).
Proof.
  xcf. intros (((lenf,f),lenr),r) Q RQ NE. xgo; xcleanpat.
  apply NE. apply~ empty_from_list.
  rewrite (singleton_left RQ) in RQ. intuit RQ.
   rew_list in H. inverts H. inverts~ H6.
  intuit RQ. rew_list in H. rewrite <- app_assoc in H.
   lets~ (Q'&X&EQ'&RQ'&RX): (Forall2_last_inv H).
Qed.

Hint Extern 1 (RegisterSpec last) => Provide last_spec.

Lemma init_spec :
  RepSpec init (Q;deque a_) |R>> 
     Q <> nil -> R (is_init Q ;; deque a_).
Proof.
  xcf. intros (((lenf,f),lenr),r) Q RQ NE. xmatch; xcleanpat.
  xgo. apply NE. apply~ empty_from_list.
  xgo. rewrite (singleton_left RQ) in RQ. intuit RQ.
   rew_list in H. inverts H. inverts~ H6.
  intuit RQ. rew_list in *. rewrite <- app_assoc in H.
   lets (Q'&X&EQ'&RQ'&RX): (Forall2_last_inv H).
   xapp. fapplys HR. constructors~. ximpl~.
Qed.

Hint Extern 1 (RegisterSpec init) => Provide init_spec.

End Polymorphic.

End BankersQueueSpec.

