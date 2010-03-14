Set Implicit Arguments. 
Require Import FuncTactics LibCore.
Require Import RandomAccessListSig_ml RandomAccessListSig_proof.
Require Import BinaryRandomAccessList_ml.

Module BinaryRandomAccessListSpec <: RandomAccessListSigSpec.

(** instantiations *)

Module Import C <: MLRandomAccessList := MLBinaryRandomAccessList. 
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

Inductive inv : bool -> int -> rlist a -> list A -> Prop :=
  | inv_nil : forall p,
      inv true p nil nil
  | inv_zero : forall z p ts L,
      inv false (p+1) ts L ->
      inv z p (Zero :: ts) L
  | inv_one : forall z p t ts L L' T,
      btree p t T ->
      inv true (p+1) ts L ->
      L' =' T ++ L ->
      inv z p (One t :: ts) L'.

(*
Fixpoint size (t:tree) : nat :=
  let '(Node r x ts) := t in 
  (1 + List.fold_right (fun t x => (x + size t)%nat) 0%nat ts)%nat.

Lemma size_pos : forall t, size t > 0%nat.
Proof. destruct t. simpl. math. Qed.

Lemma btree_unique : forall t n1 n2 E1 E2, 
  btree n1 t E1 -> btree n2 t E2 -> E1 = E2.
Proof. 
  intros t. gen_eq m: (size t). gen t.
  induction m using peano_induction.
  introv M HX HY. subst m.
  inverts HX; inverts HY. prove_rep.
  maths (r = r0). subst. fequals.
  applys* H. simpl; math.
  applys* H. simpl. forwards: (size_pos t0). math.
Qed.

Hint Resolve btree_unique : rep.
*)

Global Instance rlist_rep : Rep (rlist a) (list A).
Proof.
  apply (Build_Rep (inv true 0)). skip.
Defined.

End Polymorphic.

(** automation *)

Hint Extern 1 (@rep (rlist _) _ _ _ _) => simpl.
Ltac auto_tilde ::= eauto with maths.
Hint Constructors btree inv.

(** useful facts *)

Section Polymorphic'.
Variables (a A : Type) (RA:Rep a A).

Definition Size (t:tree a) :=
  match t with
  | Leaf _ => 1
  | Node w _ _ => w
  end.

(** verification *)

Lemma empty_spec : 
  rep (@empty a) (@nil A).
Proof. generalizes RA A. apply (empty_cf a). xgo~. Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma is_empty_spec : 
  RepTotal is_empty (L;rlist a) >> bool_of (L = nil).
Proof.
  xcf. introv RL. xgo.
  skip. (* see binominal *)
  skip.
Qed.

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Lemma size_spec : 
  Total size (t:tree a) >> = Size t.
Proof. xgo~. Qed.

Hint Extern 1 (RegisterSpec size) => Provide size_spec.

Implicit Arguments btree [[a] [A] [RA]].

Axiom pow2_succ : forall n, 2^(n+1) = 2*2^n.

Lemma size_correct : forall p t L,
  btree p t L -> Size t = 2^p.
Proof. introv Rt. inverts~ Rt. Qed.
Hint Resolve size_correct.

Lemma length_correct : forall p t L,
  btree p t L -> length L = 2^p :> int.
Proof.
  introv Rt. induction Rt. auto. 
  unfolds eq'. subst. rew_length. rewrite~ pow2_succ.
Qed.

Lemma btree_not_empty : forall p t L,
  btree p t L -> L <> nil.
Proof.
  introv Rt. lets: (length_correct Rt). intro_subst_hyp. 
  rew_length in H. skip. (* pow > 0 *)
Qed.

Lemma link_spec : 
  Spec link (t1:tree a) (t2:tree a) |R>>
    forall p L1 L2, btree p t1 L1 -> btree p t2 L2 ->
    R (fun t' => btree (p+1) t' (L1++L2)).
Proof.
  xgo. subst. constructors~.
  do 2 (erewrite size_correct;eauto).
  rewrite~ pow2_succ.
Qed.

Hint Extern 1 (RegisterSpec link) => Provide link_spec.

Implicit Arguments inv [[a] [A] [RA]].

Lemma inv_weaken : forall p ts L,
  inv false p ts L -> inv true p ts L.
Proof. introv M. inverts M; constructors~. Qed.

Hint Resolve @inv_weaken.

Lemma inv_strengthen : forall p ts L T,
  inv true p ts (T++L) -> T <> nil -> inv false p ts (T++L).
Proof.
  introv M. gen_eq L':(T++L). gen T L. induction M; intros; subst.
  false H0. destruct~ (nil_eq_app_inv H).
  constructors~.
  constructors~.
Qed.

Hint Resolve @btree_not_empty.
Hint Resolve @inv_strengthen.


Lemma cons_tree_spec : 
  Spec cons_tree (t:tree a) (ts:rlist a) |R>> 
    forall z p T L, btree p t T -> inv z p ts L ->
    R (fun ts' => inv z p ts' (T++L)).
Proof.
  skip_goal.
  xcf. introv Rt Rts. inverts Rts; xgo~.
  subst. constructors. rew_list in P_x1. applys~ inv_strengthen.
Qed.

Hint Extern 1 (RegisterSpec cons_tree) => Provide cons_tree_spec.

Lemma cons_spec : 
  RepTotal cons (X;a) (L;rlist a) >> (X::L) ; rlist a.
Proof. xcf. introv RX RL. simpl in RL. xgo~. Qed.

Hint Extern 1 (RegisterSpec cons) => Provide cons_spec.



Hint Extern 1 (RegisterSpec uncons) => Provide uncons_spec.
Hint Extern 1 (RegisterSpec head) => Provide head_spec.
Hint Extern 1 (RegisterSpec tail) => Provide tail_spec.


Lemma head_spec : 
  RepSpec head (L;rlist a) |R>>
     L <> nil -> R (is_head L ;; a).
Proof.
Qed.

Lemma tail_spec :
  RepSpec tail (L;rlist a) |R>> 
     L <> nil -> R (is_tail L ;; rlist a).
Proof.
Qed.

Lemma lookup_spec : 
  RepSpec lookup (i;int) (L;rlist a) |R>>
     0 <= i -> i < length L -> R (Nth (abs i) L ;; a).
Proof.
Qed.

Lemma update_spec :
  RepSpec update (i;int) (X;a) (L;rlist a) |R>> 
     0 <= i -> i < length L -> R (Update (abs i) X L ;; rlist a).
Proof.
Qed.

End Polymorphic'.

End BatchedQueueSpec.