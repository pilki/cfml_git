Set Implicit Arguments.
Require Import FuncTactics LibCore.
Require Import OrderedSig_ml HeapSig_ml OrderedSig_proof HeapSig_proof.
Require Import LeftistHeap_ml.

Module LeftistHeapSpec (O:MLOrdered) (OS:OrderedSigSpec with Module O:=O)
  <: HeapSigSpec with Definition H.MLElement.t := O.t.

(** instantiations *)

Module Import H <: MLHeap := MLLeftistHeap O.
Module Import OS := OS.
Existing Instance le_inst.
Existing Instance le_order.

(** invariant *)

Fixpoint Rank e : nat :=
  match e with
  | Empty => 0%nat
  | Node r x a b => (1 + Rank b)%nat
  end.

Definition is_ge (X Y:T) := X <= Y.

Inductive inv : heap -> multiset T -> Prop :=
  | inv_empty : 
      inv Empty \{} 
  | inv_node : forall r a y b A Y B E,
      inv a A -> inv b B -> rep y Y ->
      foreach (is_ge Y) A -> foreach (is_ge Y) B ->
      E = (\{Y} \u A \u B) ->
      (r =' 1 + Rank b) ->
      Rank a >= Rank b ->
      inv (Node r y a b) E.

(** model *)

Instance heap_rep : Rep heap (multiset T).
Proof.
  apply (Build_Rep inv).
  induction x; introv HX HY; inverts HX; inverts HY; prove_rep.
Defined.

(** automation *)

Definition U := multiset T.

Ltac myauto cont :=
  match goal with 
  | |- _ = _ :> multiset ?T => try solve [ change (multiset T) with U; cont tt ]
  | |- _ => cont tt
  end. 

Ltac auto_tilde ::= myauto ltac:(fun _ => eauto with maths).
Ltac auto_star ::= try solve [ intuition (eauto 7 with multiset) ].

Hint Extern 1 (_ = _ :> multiset _) => permut_simpl : multiset.
Hint Extern 1 (_ < _) => simpl; math.

Hint Constructors inv.

(** useful facts *)

Fixpoint tree_size h :=
  match h with
  | Empty => 1%nat
  | Node r x a b => (1 + tree_size a + tree_size b)%nat
  end.

Lemma tree_size_pos : forall h,
  (tree_size h > 0%nat).
Proof. destruct h; simpl; math. Qed.

Definition node_rank e :=
  match e with
  | Empty => 0%Z
  | Node r x a b => r
  end.

Lemma rank_correct : forall e E,
  rep e E -> node_rank e = Rank e.
Proof. introv H. inverts H; simpl; math. Qed.

Lemma foreach_ge_trans : forall (X Y : OS.T) (E : multiset OS.T),
  foreach (is_ge X) E -> Y <= X -> foreach (is_ge Y) E.
Proof. intros. apply~ foreach_weaken. intros_all. apply* le_trans. Qed.

Hint Resolve foreach_ge_trans.

Lemma min_of_prove : forall (X : OS.T) (E F : multiset OS.T),
  foreach (is_ge X) E -> foreach (is_ge X) F -> 
  min_of ('{X} \u E \u F) X.
Proof.
  introv H1 H2. split~. introv M. multiset_in M. 
  apply le_refl. applys~ H1. applys~ H2.
Qed.

Hint Resolve min_of_prove.

(** verification *)

Lemma empty_spec : rep empty \{}.
Proof. 
  apply empty_cf. xret~.
Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma is_empty_spec : RepTotal is_empty (E;heap) >> 
  bool_of (E = \{}).
Proof.
  xcf. intros e E RepE. inverts RepE; xgo. 
  auto. multiset_inv.
Qed. 

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Lemma rank_spec : Total rank h >> (= node_rank h).
Proof.  
  xgo~. 
Qed.

Hint Extern 1 (RegisterSpec rank) => Provide rank_spec.

Lemma make_node_spec : RepSpec make_node (X;O.t) (A;heap) (B;heap) |R>>
  foreach (is_ge X) A -> foreach (is_ge X) B ->
  R (\{X} \u A \u B ; heap).
Proof.
  xcf. introv RepX RepA RepB GeA GeB.
  forwards~: (@rank_correct a). forwards~: (@rank_correct b).
  xgo; subst.
    constructors~.
    constructors~. auto*.
Qed.

Hint Extern 1 (RegisterSpec make_node) => Provide make_node_spec.

Lemma merge_spec : RepTotal merge (E1;heap) (E2;heap) >>
  E1 \u E2 ; heap.
Proof.
  xinduction (fun e1 e2 => (tree_size e1 + tree_size e2)%nat).
  xcf. introv IH Rep1 Rep2. xmatch.
  xgo. inverts Rep2. equates* 1.
  xgo. inverts Rep1. equates* 1.
  xcleanpat. inverts Rep1. inverts Rep2. xgo~.
    eauto 8.
    intros_all. equates* 1.
    lets: (nle_to_sle P_x0). eauto 8.
    intros_all. equates* 1.
Qed.

Hint Extern 1 (RegisterSpec merge) => Provide merge_spec.

Lemma insert_spec : RepTotal insert (X;O.t) (E;heap) >>
  \{X} \u E ; heap.
Proof.
  xcf. introv RepX RepE. xapp* (>>> \{X} E).
   constructors~. auto*.
Qed.

Hint Extern 1 (RegisterSpec insert) => Provide insert_spec.

Lemma find_min_spec : RepSpec find_min (E;heap) |R>>
  E <> \{} -> R (min_of E ;; O.t).
Proof.
  xcf. intros e E RepE HasE. inverts RepE; xgo*.
Qed.

Hint Extern 1 (RegisterSpec find_min) => Provide find_min_spec.

Lemma delete_min_spec : RepSpec delete_min (E;heap) |R>>
  E <> \{} -> R (removed_min E ;; heap).
Proof. 
  xcf. intros e E RepE HasE. inverts RepE; xgo~. ximpl. xrep~.
Qed.

Hint Extern 1 (RegisterSpec delete_min) => Provide delete_min_spec.

End LeftistHeapSpec.

