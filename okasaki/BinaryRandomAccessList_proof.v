Set Implicit Arguments. 
Require Import FuncTactics LibCore.
Require Import RandomAccessListSig_ml RandomAccessListSig_proof.
Require Import BinaryRandomAccessList_ml.

Module BinaryRandomAccessListSpec <: RandomAccessListSigSpec.

(** instantiations *)

Module Import C <: MLRandomAccessList := MLBinaryRandomAccessList. 
Import MLAltBinaryRandomAccesList.

(** invariant *)

Inductive btree : int -> tree -> multiset T -> Prop :=
  | btree_nil : forall x X,
      rep x X ->
      btree 0 (Node 0 x nil) \{X}
  | btree_cons : forall r r' x X t ts E Es E',
      rep x X ->
      btree r t E ->
      btree r (Node r x ts) Es ->
      foreach (is_ge X) E' -> 
      r' =' r+1 ->
      E' =' E \u Es ->
      btree r' (Node r' x (t::ts)) E'.

Inductive inv : int -> heap -> multiset T -> Prop :=
  | inv_nil : forall r,
      0 <= r -> inv r nil \{} 
  | inv_node : forall rs r r' t ts E Es E',
      btree r t E ->
      inv rs ts Es ->
      0 <= r' ->
      r' <= r ->
      r < rs ->
      E' =' E \u Es ->
      inv r' (t::ts) E'.

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

Global Instance heap_rep : Rep heap (multiset T).
Proof.
  apply (Build_Rep (inv 0)). intros x.
  set (n:=0) at 1. generalize 0. subst n. generalize 0.
  induction x; introv HX HY; inverts HX; inverts HY; subst; prove_rep.
Defined.

Global Instance queue_rep `{Rep a A} : Rep (queue a) (list A).
Proof. intros. apply (Build_Rep (
  fun (q:queue a) (Q:list A) =>
  let (f,r) := q in 
     Forall2 rep (f ++ rev r) Q
  /\ (f = nil -> r = nil))).
  destruct x; introv [? ?] [? ?].
  asserts: (rep (l++rev l0) X). auto~.
  asserts: (rep (l++rev l0) Y). auto~.
  prove_rep. (* todo: improve *)
Defined.

(** automation *)

Hint Constructors Forall2.
Hint Resolve Forall2_last.
Hint Extern 1 (@rep (rlist _) _ _ _ _) => simpl.
Ltac auto_tilde ::= eauto.

(** useful facts *)

(** verification *)

Section Polymorphic.
Variables (a A : Type) (RA:Rep a A).

Lemma empty_spec : 
  rep (@empty a) (@nil A).
Proof.
  generalizes RA A. apply (empty_cf a). xgo.
  intros. simpl. rew_list~. 
Qed.

Lemma is_empty_spec : 
  RepTotal is_empty (L;rlist a) >> bool_of (L = nil).
Proof.
  xcf. intros (f0,r0) l [H M]. xgo.
  rewrite~ M in H. inverts~ H.
  intro_subst_hyp. inverts H as K.
   destruct (nil_eq_app_rev_inv K). false.
Qed.

Lemma cons_spec : 
  RepTotal cons (X;a) (L;rlist a) >> (X::L) ; rlist a.
Proof.
Qed.

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

End Polymorphic.

End BatchedQueueSpec.