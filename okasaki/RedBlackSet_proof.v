Set Implicit Arguments.
Require Import FuncTactics LibCore LibNat LibOrder LibSet Shared.
Require Import FsetSig_ml OrderedSig_ml FsetSig_proof OrderedSig_proof.
Require Import RedBlackSet_ml.

Module UnbalancedSetSpec (O:MLOrdered) (OS:OrderedSigSpec with Module O:=O)
  <: FsetSigSpec with Definition F.elem := O.t.

(** instantiations *)

Module Import F <: MLFset := MLRedBlackSet O.
Import OS.

Definition T := OS.T.
Definition elem_rep := OS.rep_t.

Implicit Types rr : bool.

(** invariant *)

Definition node_color e :=
  match e with
  | Empty => Black
  | Node col _ _ _ => col
  end.

Definition is_lt (X Y:T) := Y < X.
Definition is_gt (X Y:T) := X < Y.

Inductive inv : bool -> nat -> set -> LibSet.set T -> Prop :=
  | inv_empty : forall rr,
      inv rr 0 Empty \{} 
  | inv_node : forall rr n m col a y b A Y B E,
      inv true m a A -> inv true m b B -> rep y Y ->
      foreach (is_lt Y) A -> foreach (is_gt Y) B ->
      E = (\{Y} \u A \u B) ->
      (if rr then match col with 
         | Black => True 
         | Red => node_color a = Black /\ node_color b = Black
         end else True) ->
      (n =' match col with Black => S m | Red => m end) ->
      inv rr n (Node col a y b) E.

(** model *)

Global Instance set_rep : Rep set (LibSet.set T).
Proof.
  apply (Build_Rep (fun e E => 
    exists n, inv true n e E /\ node_color e = Black)). 
  introv (nx&HX&CX) (ny&HY&CY). clear CX CY. gen nx ny X Y.
  induction x; introv HX HY; inverts HX; inverts HY; prove_rep. 
Defined.

(** automation *)

Hint Constructors inv.
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

Ltac my_intuit := 
  rew_foreach in *; intuit; tryfalse.

(** useful facts *)

Fixpoint size t :=
  match t with
  | Empty => 0%nat
  | Node _ a _ b => (1 + size a + size b)%nat
  end.

Definition case_color col (A:Type) (vred vblack:A) :=
  match col with
  | Red => vred
  | Black => vblack
  end.  

Lemma inv_weaken : forall b n E e,
  inv b n e E -> inv false n e E.
Proof. introv RepE. inverts* RepE. Qed.

Lemma inv_weaken' : forall (b' b : bool) n E e,
  inv b n e E -> (b' -> b) -> inv b' n e E.
Proof.
  introv RepE N. destruct b; destruct b'; auto.
  inverts* RepE. false~ N.
Qed.

Lemma inv_strengthen : forall n E col a x b,
  inv false n (Node col a x b) E ->
  match col with 
  | Black => True 
  | Red => node_color a = Black /\ node_color b = Black
  end ->
  inv true n (Node col a x b) E.
Proof. introv RepE H. inverts* RepE. Qed.

Lemma my_lt_trans : forall Y X Z, 
  X < Y -> Y < Z -> X < Z.
Proof. intros Z HZ. eapply @lt_trans; typeclass. Qed.

Lemma foreach_gt_notin : forall (E : LibSet.set T) (X Y : T),
  foreach (is_gt Y) E -> lt X Y -> X \notin E.
Proof. introv F L N. lets: (F _ N). apply* lt_slt_false. Qed.

Lemma foreach_lt_notin : forall (E : LibSet.set T) (X Y : T),
  foreach (is_lt Y) E -> lt Y X -> X \notin E.
Proof. introv F L N. lets: (F _ N). apply* lt_slt_false. Qed.

Lemma foreach_lt_trans : forall (X Y : T) (E : LibSet.set OS.T),
  foreach (is_gt X) E -> Y < X -> foreach (is_gt Y) E.
Proof. intros. apply~ foreach_weaken. intros_all. apply* my_lt_trans. Qed.

Lemma foreach_gt_trans : forall (X Y : T) (E : LibSet.set OS.T),
  foreach (is_lt X) E -> X < Y -> foreach (is_lt Y) E.
Proof. intros. apply~ foreach_weaken. intros_all. apply* my_lt_trans. Qed.

Hint Resolve foreach_lt_trans foreach_gt_trans.

(** verification *)

Lemma empty_spec : rep empty \{}.
Proof. 
  apply empty_cf. xret. simple~. 
Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma member_spec : RepTotal member (X;elem) (E;set) >> 
  bool_of (X \in E).
Proof.
  cuts: (Spec member x e |R>>
    forall rr n X E, rep x X -> inv rr n e E -> R (bool_of (X \in E))).
    xweaken. simpl. intros_all. destruct H3 as (n&Inv&_). eauto.
  xinduction (fun (x:elem) e => size e).  
  xcf. intros x e IH rr n X E RepX InvE. inverts InvE; xgo~.
  iff M. auto. set_in M.
    subst. false~ (lt_irrefl Y).
    auto.
    false* (@foreach_gt_notin B).
  iff M. auto. set_in M. 
    subst. false~ (lt_irrefl Y). 
    false* (@foreach_lt_notin A).
    auto.
  asserts_rewrite~ (X = Y). apply~ nlt_nslt_to_eq. 
Qed.

Hint Extern 1 (RegisterSpec member) => Provide member_spec.

Lemma balance_spec : 
  Spec balance (p : color * set * O.t * set) |R>> 
  let '(col,e1,x,e2) := p  in
  forall i1 i2 n E1 E2 X,
  rep x X -> inv i1 n e1 E1 -> inv i2 n e2 E2 -> 
  foreach (is_lt X) E1 -> foreach (is_gt X) E2 ->
  match col with Black => xor i1 i2 | Red => i1 /\ i2 end ->
  R (fun e => inv (match col with Black => true | Red => false end)
                  (match col with Black => S n | Red => n end)
                  e (\{X} \u E1 \u E2)).
Proof. 
  xcf; intros [[[c e1] x] e2]. xisspec.
  introv RepX I1 I2 GtX LtX Ixor. xgo.
  (* balance 1 *)
  xcleanpat. inverts I1 as IA IB. inverts IA. subst.
  destruct (xor_cases Ixor) as [M|M]; destruct M; subst i1 i2; my_intuit.
  applys* (>>> inv_node (\{Y0} \u A0 \u B0) Y (\{X} \u B \u E2)). 
  (* balance 2 *) 
  xcleanpat. inverts I1 as IA IB. inverts IB. subst.
  destruct (xor_cases Ixor) as [M|M]; destruct M; subst i1 i2; my_intuit.
  applys* (>>> inv_node (\{Y} \u A \u A0) Y0 (\{X} \u B0 \u E2)). 
  (* balance 3 *) 
  xcleanpat. inverts I2 as IA IB. inverts IA. subst.
  destruct (xor_cases Ixor) as [M|M]; destruct M; subst i1 i2; my_intuit.
  applys* (>>> inv_node (\{X} \u E1 \u A0) Y0 (\{Y} \u B0 \u B)). 
  (* balance 4 *) 
  xcleanpat. inverts I2 as IA IB. inverts IB. subst.
  destruct (xor_cases Ixor) as [M|M]; destruct M; subst i1 i2; my_intuit.
  applys* (>>> inv_node (\{X} \u E1 \u A) Y (\{Y0} \u A0 \u B0)). 
  (* no balance *)
  destruct c.
    destruct Ixor. substb i1. substb i2. constructors~.
    destruct (xor_cases Ixor) as [M|M]; destruct M; subst i1 i2.
      inverts keep I2; auto~. constructors~. apply~ inv_strengthen.
        destruct~ col. split. 
          destruct~ a. destruct~ c. false~ C1.
          destruct~ b. destruct~ c. false~ C2.
      inverts keep I1; auto~. constructors~. apply~ inv_strengthen.
        destruct~ col. split. 
          destruct~ a. destruct~ c. false~ C.
          destruct~ b. destruct~ c. false~ C0.
Qed.

Hint Extern 1 (RegisterSpec balance) => Provide balance_spec.

Definition ins_spec X ins :=
  Spec ins e |R>>
    forall n E, inv true n e E -> 
    R (fun e' => inv (match node_color e with Black => true | Red => false end)
                     n e' (\{X} \u E)).

Lemma insert_spec : RepTotal insert (X;elem) (E;set) >>
  \{X} \u E ; set.
Proof. 
  xcf. introv RepX (n&InvE&HeB).
  xfun_induction_nointro (ins_spec X) size.
    clears s n E. intros e IH n E InvE. inverts InvE as. xgo*.
    simple*.
    introv InvA InvB RepY GtY LtY Col Num.
    xgo~ '_x4 XstopAfter, '_x3 XstopAfter.
    forwards~ M: (>>> inv_weaken' (match col with Black => false | Red => true end)).
      intro; destruct col; destruct (node_color a); destruct Col; tryfalse; auto.
     clear P_x4. xapp~. destruct~ col.
     ximpl as e. simpl. destruct col; subst; equates* 1.
    forwards~ M: (>>> inv_weaken' (match col with Black => false | Red => true end)).
      intro; destruct col; destruct (node_color b); destruct Col; tryfalse; auto.
     clear P_x3. xapp~. destruct~ col.
     ximpl as e. simpl. destruct col; subst; equates* 1.
    asserts_rewrite~ (X = Y). apply~ nlt_nslt_to_eq.
      subst s. simpl. destruct col; constructors*.
  xlet. xapp~. inverts P_x5; xgo.
    fset_inv.
    exists* __.
Qed.

Hint Extern 1 (RegisterSpec insert) => Provide insert_spec.

End UnbalancedSetSpec.

