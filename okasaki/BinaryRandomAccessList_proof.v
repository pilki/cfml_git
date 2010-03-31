Set Implicit Arguments. 
Require Import FuncTactics LibCore.
Require Import RandomAccessListSig_ml RandomAccessListSig_proof.
Require Import BinaryRandomAccessList_ml.

Module BinaryRandomAccessListSpec <: RandomAccessListSigSpec.

(** instantiations *)

Module Import R <: MLRandomAccessList := MLBinaryRandomAccessList. 
Import MLBinaryRandomAccessList.

(** invariant *)

Section Polymorphic.
Variables (a A : Type) (RA:Rep a A).

Inductive btree : int -> tree a -> list A -> Prop :=
  | btree_nil : forall x X,
      rep x X ->
      btree 0 (Leaf x) (X::nil)
  | btree_cons : forall p p' n t1 t2 L1 L2 L',
      btree p t1 L1 ->
      btree p t2 L2 ->
      p' =' p+1 ->
      n =' 2^p' ->
      L' =' L1 ++ L2 ->
      btree p' (Node n t1 t2) L'.

Inductive inv : int -> rlist a -> list A -> Prop :=
  | inv_nil : forall p,
      p >= 0 ->
      inv p nil nil
  | inv_zero : forall p ts L,
      inv (p+1) ts L -> 
      L <> nil ->
      p >= 0 ->
      inv p (Zero :: ts) L
  | inv_one : forall p t ts L L' T,
      btree p t T ->
      inv (p+1) ts L ->
      L' =' T ++ L ->
      L' <> nil ->
      p >= 0 ->
      inv p (One t :: ts) L'.

(** model *)

Lemma btree_unique : forall t n1 n2 E1 E2, 
  btree n1 t E1 -> btree n2 t E2 -> E1 = E2.
Proof. 
  introv H1. gen n2 E2.
  induction H1; introv H2; inverts H2; subst; prove_rep.
Qed.

Hint Resolve btree_unique : rep.

Global Instance rlist_rep : Rep (rlist a) (list A).
Proof.
  apply (Build_Rep (inv 0)).
  cuts*: (forall ts p1 p2 E1 E2, 
    inv p1 ts E1 -> inv p2 ts E2 -> E1 = E2).
  introv K1. gen p2 E2. 
  induction K1; introv K2; inverts K2; subst; prove_rep.
Defined.

End Polymorphic.

Implicit Arguments btree [[a] [A] [RA]].
Implicit Arguments inv [[a] [A] [RA]].

(** automation *)

Hint Constructors btree inv.
Hint Extern 1 (@lt nat _ _ _) => rew_list; math.
Hint Extern 1 (@rep Z _ _ _ _) => reflexivity.
Hint Resolve ZNth_zero ZUpdate_here ZUpdate_not_nil.
Hint Resolve app_not_empty_l app_not_empty_r.

Section Polymorphic'.
Variables (a A : Type) (RA:Rep a A).

Definition U := list A.

Ltac myauto cont :=
  match goal with 
  | |- _ = _ :> list A => try solve [ change (list A) with U; cont tt ]
  | |- _ => cont tt
  end. 

Ltac auto_tilde ::= myauto ltac:(fun _ => eauto with maths).

(** useful facts *)

Fixpoint tree_size (t:tree a) : nat :=
  match t with
  | Leaf _ => 0%nat
  | Node _ t1 t2 => (1 + tree_size t1 + tree_size t2)%nat
  end.

Definition Size (t:tree a) :=
  match t with
  | Leaf _ => 1
  | Node w _ _ => w
  end.

Lemma btree_size_correct : forall p t L,
  btree p t L -> Size t = 2^p.
Proof. introv Rt. inverts~ Rt. Qed.
Hint Resolve btree_size_correct.

Lemma length_correct : forall t p L,
  btree p t L -> length L = 2^p :> int.
Proof.
  introv Rt. induction Rt. auto. 
  unfolds eq'. subst. rew_length. rewrite~ pow2_succ.
Qed.

Lemma btree_size_pos : forall p t L,
  btree p t L -> p >= 0.
Proof. introv Rt. induction Rt; unfolds eq'; math. Qed.

Hint Resolve btree_size_pos.

Lemma to_empty : forall p L,
  inv p nil L -> L = nil.
Proof. introv RL. inverts~ RL. Qed.

Lemma from_empty : forall p ts,
  inv p ts nil -> ts = nil.
Proof. introv RL. inverts RL; auto_false. Qed.

Lemma btree_not_empty : forall p t L,
  btree p t L -> L <> nil.
Proof.
  introv Rt. lets: (length_correct Rt). intro_subst_hyp. 
  rew_length in H. forwards~: (@pow2_pos p). math.
Qed.

Hint Resolve btree_not_empty.

(** verification *)

Lemma empty_spec : 
  rep (@empty a) (@nil A).
Proof. generalizes RA A. apply (empty_cf a). xgo~. Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma is_empty_spec : 
  RepTotal is_empty (L;rlist a) >> bool_of (L = nil).
Proof.
  xcf. introv RL. simpl in RL. xgo.
  apply~ to_empty.
  intro_subst_hyp. applys C. apply~ from_empty. 
Qed.

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Lemma size_spec : 
  Total size (t:tree a) >> = Size t.
Proof. xgo~. Qed.

Hint Extern 1 (RegisterSpec size) => Provide size_spec.

Lemma link_spec : 
  Spec link (t1:tree a) (t2:tree a) |R>>
    forall p L1 L2, btree p t1 L1 -> btree p t2 L2 ->
    R (fun t' => btree (p+1) t' (L1++L2)).
Proof.
  xgo. subst. constructors~.
  do 2 (erewrite btree_size_correct;eauto).
  rewrite~ pow2_succ.
Qed.

Hint Extern 1 (RegisterSpec link) => Provide link_spec.

Lemma cons_tree_spec : 
  Spec cons_tree (t:tree a) (ts:rlist a) |R>> 
    forall p T L, btree p t T -> inv p ts L ->
    R (fun ts' => inv p ts' (T++L)).
Proof.
  xinduction (fun (t:tree a) (ts:rlist a) => length ts).
  xcf. introv IH Rt Rts. inverts Rts; xgo~.
  constructors~. 
  subst. rew_list in P_x1. auto~.
Qed.

Hint Extern 1 (RegisterSpec cons_tree) => Provide cons_tree_spec.

Lemma cons_spec : 
  RepTotal cons (X;a) (L;rlist a) >> (X::L) ;- rlist a.
Proof. xcf. introv RX RL. simpl in RL. xgo~. Qed.

Hint Extern 1 (RegisterSpec cons) => Provide cons_spec.

Lemma uncons_tree_spec : 
  Spec uncons_tree (ts:rlist a) |R>> 
    forall p L, inv p ts L -> ts <> nil ->
    R (fun r => let (t',ts') := r : tree a * rlist a in
       exists T' L', btree p t' T' /\ inv p ts' L' /\ L = T' ++ L').
Proof.
  xinduction (fun (ts:rlist a) => length ts).
  xcf. introv IH Rts Ne. xmatch.
  xgo. inverts Rts as RT RL. inverts RL. subst. exists___; auto~. 
  xgo. inverts Rts.
   asserts: (L0 <> nil). intro_subst_hyp. eapply C0. fequals. apply~ from_empty.
   subst. exists___; auto~. 
  inverts Rts.
   asserts: (ts <> nil). intro_subst_hyp. inverts H1. false.
   xapp~. intuit _x1. xmatch. 
   xgo. inverts H3. maths (p0 = p). subst. exists___. splits~. rew_list~.
   xgo. inverts H3. math. applys~ C2.
Qed.

Hint Extern 1 (RegisterSpec uncons_tree) => Provide uncons_tree_spec.

Lemma head_spec : 
  RepSpec head (L;rlist a) |R>>
    L <> nil -> R (is_head L ;; a).
Proof.
  xcf. introv Rts NE. simpl in Rts. xgo~.
  inverts Rts; auto_false.
  destruct P_x0 as (T'&L'&RT'&RL'&E). inverts RT'. rew_list in E. xrep~. 
  intuit _x0. inverts H0.
    applys~ C.
    forwards: (btree_size_pos H3). math.
Qed.

Hint Extern 1 (RegisterSpec head) => Provide head_spec.

Lemma tail_spec :
  RepSpec tail (L;rlist a) |R>> 
     L <> nil -> R (is_tail L ;; rlist a).
Proof.
  xcf. introv Rts NE. simpl in Rts. xgo~.
  inverts Rts; auto_false.
  intuit P_x0. inverts H0.
    eauto.
    false. forwards~: (btree_size_pos H3). math.
Qed.

Hint Extern 1 (RegisterSpec tail) => Provide tail_spec.

Lemma lookup_tree_spec : 
  Spec lookup_tree (i:int) (t:tree a) |R>>
    forall p L, btree p t L -> ZInbound i L -> R (ZNth i L ;; a).
Proof.
  xinduction (fun (i:int) t => tree_size t).
  xcf. intros i t. introv IH Rt Bi. inverts Rt; xmatch.
  xgo. auto~. apply~ ZInbound_one_pos_inv.
  xif. subst. rewrite pow2_succ in C0. rewrite div2_odd in C0. xapp~. 
    subst. apply~ ZInbound_app_l_inv. rewrite~ (length_correct H).
    ximpl as l. xrep in Hx. xrep. 
     apply~ ZNth_app_l.
  subst. rewrite pow2_succ in C0. rewrite div2_odd in C0.
   rewrite pow2_succ. rewrite div2_odd. xapp~. 
    apply~ ZInbound_app_r_inv. rewrite~ (length_correct H).
    ximpl as l. xrep in Hx. xrep. 
     apply~ ZNth_app_r. rewrite~ (length_correct H).
Qed.

Hint Extern 1 (RegisterSpec lookup_tree) => Provide lookup_tree_spec.

Lemma update_tree_spec : 
  Spec update_tree (i:int) (x:a) (t:tree a) |R>>
    forall p X L, rep x X -> btree p t L -> ZInbound i L -> 
    R (fun t' => exists L', btree p t' L' /\ ZUpdate i X L L').
Proof.
  xinduction (fun (i:int) (x:a) t => tree_size t).
  xcf. intros i x t. introv IH Rx Rt Bi. inverts Rt; xmatch.
  xgo. xrep~. apply~ ZInbound_one_pos_inv.
  xif. subst. rewrite pow2_succ in C0. rewrite div2_odd in C0. xapp~. 
    subst. apply~ ZInbound_app_l_inv. rewrite~ (length_correct H).
    xret. xrep in P_x7. xrep~. apply~ ZUpdate_app_l.
  subst. rewrite pow2_succ in C0. rewrite div2_odd in C0.
   rewrite pow2_succ. rewrite div2_odd. xapp~. 
    apply~ ZInbound_app_r_inv. rewrite~ (length_correct H).
    xret. xrep in P_x4. xrep~. 
      constructors~. rewrite~ pow2_succ.
      apply~ ZUpdate_app_r. rewrite~ (length_correct H). 
Qed.

Hint Extern 1 (RegisterSpec update_tree) => Provide update_tree_spec.

Lemma lookup_spec_ind : 
  Spec lookup (i:int) (ts:rlist a) |R>>
    forall p L, inv p ts L -> ZInbound i L -> R (ZNth i L ;; a).
Proof.
  xinduction (fun (i:int) (ts:rlist a) => length ts).
  xcf. intros i ts. introv IH Rts Bi. xmatch; inverts Rts.
  xgo. apply~ ZInbound_nil_inv.
  xgo~.
  forwards~: (@length_correct t).
   forwards~: (>>> btree_size_correct t). xgo~.
    subst. apply~ ZInbound_app_l_inv.
    ximpl. xrep in Hx. xrep. subst. apply~ ZNth_app_l.
    subst. apply~ ZInbound_app_r_inv.
    ximpl. xrep in Hx. xrep. subst. apply~ ZNth_app_r.
Qed.

Lemma lookup_spec : 
  RepSpec lookup (i;int) (L;rlist a) |R>>
     ZInbound i L -> R (ZNth i L ;; a).
Proof.
  xweaken lookup_spec_ind. introv W H Ri Rts Bi.
  inverts Ri. simpl in Rts. apply~ H.
Qed.

Lemma update_spec_ind : 
  Spec update (i:int) (x:a) (ts:rlist a) |R>>
    forall p X L, rep x X -> inv p ts L -> ZInbound i L -> 
    R (fun ts' => exists L', inv p ts' L' /\ ZUpdate i X L L').
Proof.
  xinduction (fun (i:int) (x:a) (ts:rlist a) => length ts).
  xcf. intros i x ts. introv IH Rx Rts Bi. xmatch; inverts Rts.
  xgo. apply~ ZInbound_nil_inv.
  xgo~. xrep in P_x1 as L'. xrep~. 
  forwards~: (@length_correct t).
   forwards~: (>>> btree_size_correct t). xgo~.
    subst. apply~ ZInbound_app_l_inv.
    xrep in P_x7. xrep~. subst. apply~ ZUpdate_app_l.
    subst. apply~ ZInbound_app_r_inv.
    xrep in P_x4. xrep~. subst. apply~ ZUpdate_app_r.
Qed.

Lemma update_spec : 
  RepSpec update (i;int) (X;a) (L;rlist a) |R>> 
    ZInbound i L -> R (ZUpdate i X L ;; rlist a).
Proof.
  xweaken update_spec_ind. introv W H Ri Rx Rts Bi.
  inverts Ri. simpl in Rts. applys~ H.
Qed.

End Polymorphic'.

End BinaryRandomAccessListSpec.

