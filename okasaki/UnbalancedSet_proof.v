Set Implicit Arguments.
Require Import FuncTactics LibCore LibOrder LibSet Shared. 
Require Import FsetSig_ml OrderedSig_ml FsetSig_proof OrderedSig_proof.
Require Import UnbalancedSet_ml.

Module UnbalancedSetSpec (O:MLOrdered) (OS:OrderedSigSpec with Module O:=O)
  <: FsetSigSpec with Definition F.elem := O.t.

(** instantiations *)

Module Import F <: MLFset := MLUnbalancedSet O.
Import OS.

Existing Instance le_inst.
Existing Instance le_order.

Definition T := OS.T.
Definition elem_rep := OS.rep_t.

(** invariant *)

Definition is_lt (X Y:T) := Y < X.
Definition is_gt (X Y:T) := X < Y.

Inductive inv : set -> LibSet.set T -> Prop :=
  | inv_empty : inv Empty \{}
  | inv_node : forall a y b A Y B C,
      inv a A -> inv b B -> rep y Y ->
      foreach (is_lt Y) A -> foreach (is_gt Y) B ->
      C =' (\{Y} \u A \u B) ->
      inv (Node a y b) C.

Global Instance set_rep : Rep set (LibSet.set T) := inv.

(** termination relation *)

Inductive subtree : set -> set -> Prop :=
  | subtree_left : forall a x b, subtree a (Node a x b)
  | subtree_right : forall a x b, subtree b (Node a x b).

Hint Constructors subtree.

Lemma subtree_wf : wf subtree.
Proof.
  intros e. induction e;
    constructor; introv H; inversions~ H.
Qed.

Hint Resolve subtree_wf : wf.

(** automation *)

Hint Extern 1 (_ = _ :> LibSet.set _) => permut_simpl : set.

Definition U := LibSet.set T.

Ltac myauto cont :=
  match goal with 
  | |- _ = _ :> LibSet.set ?T => try solve [ change (LibSet.set T) with U; cont tt ]
  | |- _ => cont tt
  end. (* todo: pour éviter un hint trop lent de hint-core avec eauto *)

Ltac auto_tilde ::= myauto ltac:(fun _ => eauto).
Ltac auto_star ::= try solve [ intuition (eauto with set) ].

Hint Extern 1 (rep _ _) => simpl. (* todo: specialize *)

Hint Constructors inv.

(** useful facts *)

  (* todo : inversion for fset *)

Lemma in_node_cases : forall (X Y : T) (A B : LibSet.set T),
  X \in \{Y} \u A \u B -> 
  X = Y \/ X \in A \/ X \in B.
Proof.
  introv H. destruct (in_union_inv H) as [H'|H'].
    left. rewrite~ (in_single H').
    right. destruct (in_union_inv H'); eauto.
Qed.

Lemma foreach_gt_notin : forall (A : LibSet.set T) (X Y : T),
  foreach (is_gt Y) A -> lt X Y -> X \notin A.
Proof. introv F L N. lets: (F _ N). apply* lt_slt_false. Qed.

Lemma foreach_lt_notin : forall (A : LibSet.set T) (X Y : T),
  foreach (is_lt Y) A -> lt Y X -> X \notin A.
Proof. introv F L N. lets: (F _ N). apply* lt_slt_false. Qed.

(** verification *)

Lemma empty_spec : rep empty \{}.
Proof. 
  apply empty_cf. xret. simple~.
Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma member_spec : RepTotal member (X;elem) (E;set) >> 
  bool_of (X \in E).
Proof.
  xinduction (unproj22 elem subtree).  
  xcf. intros x e IH X E RepX RepE. inverts RepE as. 
  xgo. rewrite in_empty_eq. auto.
  introv IA IB RepY LtA GtB EqE. subst E. xgo~.
  iff M. auto. destruct (in_node_cases M) as [N|[N|N]].
    subst. false~ (lt_irrefl Y).
    auto.
    false. applys* (@foreach_gt_notin B).
  iff M. auto. destruct (in_node_cases M) as [N|[N|N]].
    subst. false~ (lt_irrefl Y).
    false. applys* (@foreach_lt_notin A).
    auto.
  asserts_rewrite~ (X = Y). apply~ nlt_nslt_to_eq. 
Qed.

Hint Extern 1 (RegisterSpec member) => Provide member_spec.

Lemma insert_spec : RepTotal insert (X;elem) (E;set) >>
  \{X} \u E ; set.
Proof.
  xinduction (unproj22 elem subtree).  
  xcf. intros x e IH X E RepX RepE. 
  inverts RepE; [| subst E]; xgo~ '_m1 XsubstAlias.
  applys* inv_node.
  applys* inv_node.
  applys* inv_node. 
  asserts_rewrite (X = Y). applys~ nlt_nslt_to_eq. applys* inv_node. 
Qed.
 
Hint Extern 1 (RegisterSpec insert) => Provide insert_spec.

End UnbalancedSetSpec.
