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

(** model *)

Global Instance set_rep : Rep set (LibSet.set T).
Proof.
  apply (Build_Rep inv).
  induction x; introv HX HY; inverts HX; inverts HY; subst; prove_rep.
Defined.

(** automation *)

Hint Extern 1 (_ = _ :> LibSet.set _) => permut_simpl : set.

Definition U := LibSet.set T.

Ltac myauto cont :=
  match goal with 
  | |- _ = _ :> LibSet.set ?T => try solve [ change (LibSet.set T) with U; cont tt ]
  | |- _ => cont tt
  end. 

Ltac auto_tilde ::= myauto ltac:(fun _ => eauto).
Ltac auto_star ::= try solve [ intuition (eauto with set) ].
Hint Extern 1 (@lt nat _ _ _) => simpl; math.
Hint Constructors inv.

(** useful facts *)

Fixpoint size t :=
  match t with
  | Empty => 0%nat
  | Node a _ b => (1 + size a + size b)%nat
  end.

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
  xinduction (fun (x:elem) e => size e).  
  xcf. intros x e IH X E RepX RepE. inverts RepE as. 
  xgo. rewrite in_empty_eq. auto.
  introv IA IB RepY LtA GtB EqE. subst E. xgo~.
  iff M. auto. set_in M.
    false~ (lt_irrefl Y).
    auto.
    false. applys* (@foreach_gt_notin B).
  iff M. auto. set_in M.
    subst. false~ (lt_irrefl Y).
    false. applys* (@foreach_lt_notin A).
    auto.
  asserts_rewrite~ (X = Y). apply~ nlt_nslt_to_eq. 
Qed.

Hint Extern 1 (RegisterSpec member) => Provide member_spec.

Lemma insert_spec : RepTotal insert (X;elem) (E;set) >>
  \{X} \u E ;- set.
Proof.
  xinduction (fun (x:elem) e => size e).  
  xcf. intros x e IH X E RepX RepE.
  inverts RepE; [| subst E]; xgo~. 
  applys* inv_node.
  applys* inv_node.
  applys* inv_node. 
  asserts_rewrite (X = Y). applys~ nlt_nslt_to_eq. 
   subst. applys* inv_node. 
Qed.
 
Hint Extern 1 (RegisterSpec insert) => Provide insert_spec.

End UnbalancedSetSpec.
