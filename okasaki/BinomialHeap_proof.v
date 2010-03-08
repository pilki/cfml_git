Set Implicit Arguments.
Require Import FuncTactics LibCore.
Require Import OrderedSig_ml HeapSig_ml OrderedSig_proof HeapSig_proof.
Require Import BinomialHeap_ml.

(*
Inductive intbar :=
  | intbar_int : int -> intbar
  | intbar_inf : intbar.

Instance intbar_le : Le intbar := fun (x y : intbar) => 
  match x,y with
  | intbar_int n, intbar_int m => n <= m
  | intbar_inf, intbar_int n => False
  | _, intbar_inf => True
  end.

(* todo: generic min *)

Ltac simpl_intbar_le :=
  repeat match goal with H: (@le intbar _ _ _) |- _ =>
    simpl in H end.
   
Axiom min : int -> int -> int.

Definition min_intbar (x y : intbar) :=
  match x,y with
  | intbar_int n, intbar_int m => intbar_int (min n m)
  | intbar_int n, _ => intbar_int n
  | _, intbar_int n => intbar_int n
  | _,_ => intbar_inf
  end.

Axiom min_trans_elim : forall a b x y : int,
  min a b <= x -> y <= a -> y <= b -> y <= x.
  *)


Tactic Notation "fset_inv" := 
  match goal with
  | |- \{} <> _ => let H := fresh in intro H; fset_inv H
  | |- _ <> \{} => let H := fresh in intro H; fset_inv H
  | H: \{} = _ |- _ => fset_inv H
  | H: _ = \{} |- _ => fset_inv H
  end.

Module BinomialHeapSpec (O:MLOrdered) (OS:OrderedSigSpec with Module O:=O)
  <: HeapSigSpec with Definition H.MLElement.t := O.t.

(** instantiations *)

Module Import H <: MLHeap := MLBinomialHeap O.
Module Import OS := OS.
Existing Instance le_inst.
Existing Instance le_order.

Definition min_of (E:multiset T) (X:T) := 
  X \in E /\ forall_ Y \in E, X <= Y.

Definition removed_min (E E':multiset T) :=
  exists X, min_of E X /\ E = \{X} \u E'.

(** invariant *)

Definition is_ge (X Y:T) := X <= Y.

Inductive btree : int -> tree -> multiset T -> Prop :=
  | btree_nil : forall x X,
      rep x X ->
      btree 0 (Node 0 x nil) \{X}
  | btree_cons : forall r r' x X t ts E Es E',
      rep x X ->
      btree r t E ->
      btree r (Node r x ts) Es ->
      foreach (is_ge X) E' -> (* todo: E suffirait *)
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

Global Instance heap_rep : Rep heap (multiset T) := inv 0.

(** automation *)

Hint Extern 1 (_ < _) => simpl; math.

Hint Extern 1 (_ = _ :> multiset _) => permut_simpl : multiset.

Definition U := multiset T.

Ltac myauto cont :=
  match goal with 
  | |- _ = _ :> LibSet.set ?T => try solve [ change (multiset T) with U; cont tt ]
  | |- _ => cont tt
  end. (* todo: pour éviter un hint trop lent de hint-core avec eauto *)

Ltac auto_tilde ::= myauto ltac:(fun _ => eauto with maths).
Ltac auto_star ::= try solve [ intuition (eauto with multiset) ].
 (*myauto ltac:(fun _ => intuition (eauto with multiset)). todo bin *)

Ltac check_noevar :=
  match goal with |- ?G => match G with G => idtac end end.

Ltac math_0 ::= idtac.
Ltac math_1 ::= intros; generalize_arith.
Ltac math_2 ::= instantiate; check_noevar; intros.
Ltac math_3 ::= rew_maths; nat_comp_to_peano; int_comp_to_zarith.
Ltac math_4 ::= math_setup_goal.
Ltac math_5 ::= omega.

(** useful facts *)

Hint Constructors inv.
Hint Extern 1 (@rep heap _ _ _ _) => simpl.

Lemma foreach_ge_trans : forall (X Y : OS.T) (E : multiset OS.T),
  foreach (is_ge X) E -> Y <= X -> foreach (is_ge Y) E.
Proof. intros. apply~ foreach_weaken. intros_all. apply* le_trans. Qed.

Hint Resolve foreach_ge_trans.
Hint Unfold removed_min.


Lemma btree_rank_pos : forall r t E, 
  btree r t E -> 0 <= r.
Proof. introv H. induction~ H. unfolds~ eq'. Qed.

Lemma inv_rank_pos : forall rs ts Es, 
  inv rs ts Es -> 0 <= rs.
Proof. introv H. inverts~ H. Qed.

Hint Resolve btree_rank_pos inv_rank_pos.


Lemma inv_rev_children : forall x X ts,
  rep x X -> forall r E r' ts' E',
  btree r (Node r x ts) E ->
  inv r' ts' E' ->
  r <= r' ->
  exists E'' r'', 
    inv r'' (rev ts ++ ts') (E' \u E'') /\
    E = \{X} \u E''.
Proof.
  introv RX. induction ts; introv H I C; inversions H; unfolds eq'.
  exists (\{}:multiset T) r'.
    skip_rewrite (X = X0). (* todo *)
    splits*. rew_list. equates* 1.
  rename a into t.
  forwards (E''&r''&I''&EQ''): (>>> IHts __ r0 (t::ts') (E' \u E0)).
    auto~. constructors*. auto~. auto~.
  exists (E0 \u E'') r''. split.
   rewrite rev_cons. rewrite app_last_sym. equates* 1.
   subst. permut_simpl.
Qed.
      


Definition Rank (t:tree) :=
  let (r,x,c) := t in r.

Definition Root (t:tree) :=
  let (r,x,c) := t in x.

Lemma btree_not_empty : forall E r t,
  btree r t E -> E <> \{}.
Proof.
  introv H. induction H. fset_inv. rewrite H4. skip. (* fset *)
Qed.

Lemma foreach_ge_single : forall X,
  foreach (is_ge X) ('{X}:multiset T).
Proof. introv H. hnf. multiset_in H. apply le_refl. Qed.

Hint Resolve foreach_ge_single.

Lemma btree_inv : forall E r r' x ts,
  btree r (Node r' x ts) E -> 
  r = r' /\ exists X, rep x X /\ foreach (is_ge X) E.
Proof. (* todo: fix induction *)
  introv H. sets_eq M: (Node r' x ts). gen x ts.
  induction H; intros; inverts EQM; eauto.
Qed.

Lemma inv_nil_change : forall rs rs' Es, 
  inv rs nil Es -> 0 <= rs' -> inv rs' nil Es.
Proof. introv H P. inverts~ H. Qed.
(*todo: use below instead?*)

Lemma inv_smaller : forall rs rs' ts Es, 
  inv rs ts Es -> 0 <= rs' -> rs' <= rs -> inv rs' ts Es.
Proof. introv H P L. inverts~ H. Qed.
  (* todo: math should be in auto~ but not if evars are there *)

(**)
  (* todo: math should be in auto~ but not if evars are there *)

Lemma rank_correct : forall t r E,
  btree r t E -> Rank t = r.
Proof. introv H. inverts~ H. Qed.

(** verification *)

Lemma empty_spec : rep empty \{}.
Proof. apply empty_cf. xret~. Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma is_empty_spec : RepTotal is_empty (E;heap) >> 
  bool_of (E = \{}).
Proof.
  xcf. intros e E RepE. inverts RepE; xgo. 
  auto. intros K. false (btree_not_empty H). skip. (* fset *)
Qed. 

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Lemma rank_spec : Total rank (t:tree) >> = Rank t.
Proof. xgo*. Qed.

Hint Extern 1 (RegisterSpec rank) => Provide rank_spec.

Lemma root_spec : Total root (t:tree) >> = Root t.
Proof. xgo*. Qed.

Hint Extern 1 (RegisterSpec root) => Provide root_spec.

Lemma link_spec : Spec link (t1:tree) (t2:tree) |R>> 
  forall r E1 E2,
  btree r t1 E1 -> btree r t2 E2 ->
  R (fun t' => btree (r+1) t' (E1 \u E2)).
Proof. 
  xcf. intros (r1,x1,c1) (r2,x2,c2). introv R1 R2.
  destruct (btree_inv R1) as (Er1&X1&Rx1&S1).
  destruct (btree_inv R2) as (Er2&X2&Rx2&S2).
  subst r1 r2. xgo~; subst t1 t2. 
    constructors*.
    applys_to P_x2 nle_to_sle. constructors*.
Qed.

Hint Extern 1 (RegisterSpec link) => Provide link_spec.

Ltac auto_tilde ::= myauto ltac:(fun _ => eauto with maths).

Ltac math_1 ::= intros.

Hint Extern 1 (@lt nat _ _ _) => rew_length; math.

Lemma ins_tree_spec : Spec ins_tree (t:tree) (ts:list tree) |R>> 
  forall r rs E Es,
  btree r t E -> inv rs ts Es -> r <= rs ->
  R (fun ts' => exists rs', inv rs' ts' (E \u Es) /\ r <= rs').
Proof. 
  xinduction (fun (t:tree) (ts:list tree) => length ts).
  xcf. intros t ts. introv IH Rt Rts Ran. 
  forwards: (btree_rank_pos Rt). inverts keep Rts; xmatch. 
  xgo. exists~ r. split. applys~ (@inv_node (r+1)). auto~.
  xapp~. xapp~. (* todo: xapp~ on rank should fold partial eq in post condition *)
  forwards~ K1: (@rank_correct t). forwards~ K2: (@rank_correct t0). 
  rewrite K1,K2 in *. clear K1 K2. subst _x2 _x3. subst.
  xif. xret. exists r. split. applys~ (@inv_node (r+1)). auto~.
  asserts: (r = r0). math. subst r0.
  xapp~. cbv beta in P_x4. xapp~. ximpl as ts' (rs'&Inv&Len).
  exists rs'. split~. equates* 1.
Qed.

Hint Extern 1 (RegisterSpec ins_tree) => Provide ins_tree_spec.

Hint Constructors btree.

Lemma insert_spec : RepTotal insert (X;O.t) (E;heap) >>
  \{X} \u E ; heap.
Proof.
  xcf. introv RepX RepE. simpl in RepE. xapp~.
  ximpl as ts' (rs'&Inv&Pos). simpl. applys~ (inv_smaller). 
Qed.

Hint Extern 1 (RegisterSpec insert) => Provide insert_spec.

(*

Coercion intbar_int : Z >-> intbar.
Notation "'oo'" := intbar_inf.

Definition Rank_hd (ts:heap) :=
  match ts with
  | nil => oo
  | t::ts => Rank t
  end.
*)

Definition Rank_hd_or r (ts:heap) :=
  match ts with
  | nil => r
  | t::ts => Rank t
  end.

(* todo: use above *)
Definition Rank_hd (ts:heap) :=
  match ts with
  | nil => 0
  | t::ts => Rank t
  end.

Lemma inv_cons_inv : forall r' t ts E',
  inv r' (t::ts) E' -> 
  exists rs E Es,
  btree (Rank t) t E /\
  inv rs ts Es /\
  Rank t < rs /\
  r' <= Rank t /\
  E' = E \u Es.
Proof.
  introv H. inverts H. exists rs E Es.
  forwards~: (@rank_correct t). subst~.
Qed.


Lemma inv_rank_hd : forall r ts Es,
  inv r ts Es -> inv (Rank_hd ts) ts Es.
Proof.
  introv H. inverts H; simpl. auto~.
  forwards~: (@rank_correct t).
Qed.

Lemma Rank_hd_comp : forall r ts Es,
  inv r ts Es -> 0 <= Rank_hd ts.
Proof.
  introv H. inverts H; simpl. math. 
  forwards~: (@rank_correct t).
Qed.

Lemma Rank_hd_comp' : forall r ts Es,
  inv r ts Es -> 
  (ts = nil -> r = 0) ->
  r <= Rank_hd ts.
Proof.
  introv H P. inverts H; simpl.
  rewrite~ P. 
  forwards~: (@rank_correct t).
Qed.

Lemma Rank_hd_comp'' : forall r ts Es,
  inv r ts Es -> ts <> nil ->
  r <= Rank_hd ts.
Proof.
  introv H P. inverts H; simpl. false. 
  forwards~: (@rank_correct t).
Qed.

Lemma Rank_hd_comp''' : forall r t ts Es,
  inv r (t::ts) Es -> r <= Rank t.
Proof.
  introv H. inverts H; simpl. 
  forwards~: (@rank_correct t).
Qed.

Hint Resolve inv_rank_hd Rank_hd_comp Rank_hd_comp' Rank_hd_comp''.


Lemma inv_smallest : forall rs ts Es,
  inv rs ts Es -> 
  exists rs',
  inv rs' ts Es /\
  rs' <= rs /\
  (ts = nil -> rs' = 0).
Proof.
  introv H. inverts H. exists~ 0.
  exists rs. splits. auto~. auto~. auto_false.
Qed. (* todo: improve autofalse *)


(*
Lemma le_rank_hd_or_elim : forall r ts,
  r <= Rank_hd_or r ts ->
  r <= Rank_hd ts.
Proof. intros. destruct ts.
*)

Axiom min : int -> int -> int.

Axiom min_trans_elim : forall a b x y : int,
  min a b <= x -> y < a -> y < b -> y < x.

Lemma inv_rank_hd_cons : forall r t ts Es,
  inv r (t::ts) Es -> inv (Rank t) (t::ts) Es.
Proof.
  introv H. inverts H; simpl.
  forwards~: (@rank_correct t).
Qed.
Hint Resolve inv_rank_hd_cons.

Axiom min_self : forall x : int,
  min x x = x.

Axiom min_left : forall x y : int,
  x <= y -> min x y = x.
Axiom min_right : forall x y : int,
  y <= x -> min x y = y.

Lemma merge_spec : RepTotal merge (E1;heap) (E2;heap) >>
  E1 \u E2 ; heap.
(*
Proof.
  cuts H: (Spec merge (ts1:heap) (ts2:heap) |R>>
    forall r1 r2 Es1 Es2,
      inv r1 ts1 Es1 -> inv r2 ts2 Es2 -> 
      R (fun ts' => exists r', inv r' ts' (Es1 \u Es2) 
           /\ match ts1,ts2 with
              | nil,nil => ts' = nil /\ r' = 0
              | t1::_,nil => ts' = ts1 /\ r' = Rank t1 
              | nil,t2::_ => ts' = ts2 /\ r' = Rank t2 
              | t1::_,t2::_ => min (Rank t1) (Rank t2) <= r' end)).
    xweaken. clear H. simpl. introv WR H I1 I2. applys WR.
    forwards~: H. ximpl as ts' (r'&Inv&P2). applys~ inv_smaller.
  xinduction (fun ts1 ts2 : heap => (length ts1 + length ts2)%nat).
  xcf. introv IH Rep1 Rep2. xmatch.
  xgo. inverts Rep2. rew_permut_simpl.
   destruct ts1. eauto. exists~ (Rank t).
  xgo. inverts Rep1. rew_permut_simpl.
   destruct ts2. eauto. exists~ (Rank t).
  xcleanpat.
  lets (rs1&E1&Ez1&B1&I1&R1&S1&EQ1): (inv_cons_inv Rep1). clear Rep1. 
  lets (rs2&E2&Ez2&B2&I2&R2&S2&EQ2): (inv_cons_inv Rep2). clear Rep2.
  xapp~. xapp~. calc_partial_eq tt. subst _x1 _x2.

  xif. 
   asserts: (inv (Rank t2) (t2::ts2') Es2). subst Es2. constructors~.
   xapp. specializes HR __. unfold uncurry2. auto~. (*todo: un simpl en trop! *)
   fapplys HR; eauto. ximpl. 
   destruct P_x9 as (r'&I'&P).
   xret. subst Es1. 
   asserts: (Rank t1 < r').
     destruct ts1'. maths.
     lets: (Rank_hd_comp''' I1).
     forwards: (@min_trans_elim _ _ _ (Rank t1) P); math.
   exists (Rank t1). split.
     equates 1. constructors~. permut_simpl.
     rewrite~ min_left.

  xapp~. xapp~. calc_partial_eq tt. subst _x4 _x5.
 xif. 
   asserts: (inv (Rank t1) (t1::ts1') Es1). subst Es1. constructors~.
   xapp. specializes HR __. unfold uncurry2. auto~. (*todo: un simpl en trop! *)
   fapplys HR; eauto. ximpl. 
   destruct P_x8 as (r'&I'&P).
   xret. subst Es2. 
   asserts: (Rank t2 < r').
     destruct ts2'. maths.
     lets: (Rank_hd_comp''' I2).
     forwards: (@min_trans_elim _ _ _ (Rank t2) P); math.
   exists (Rank t2). split.
     equates 1. constructors~. permut_simpl.
     rewrite~ min_right.

  asserts: (Rank t1 = Rank t2). eapply nlt_nslt_to_eq; eauto. clear C C0.
  rewrite <- H in *. clear H.
  xapp~. xapp. specializes HR __. unfold uncurry2. auto~. (*todo: un simpl en trop! *)
   fapplys HR; eauto. ximpl.
  cbv beta in *. destruct P_x7 as (r'&I'&P). subst.
  destruct ts1'; destruct ts2'; try destruct P; subst.
    xapp. applys~ (>>> HR __ (Rank t1 + 1) ___). inverts I1. inverts I2.
     ximpl as ts' (rs'&Inv&Ri).
      exists rs'. split. equates* 1. rewrite min_self. math.
    xapp. applys~ (>>> HR __ rs2 ___). inverts I1.
     ximpl as ts' (rs'&Inv&Ri). 
     exists rs'. split. equates* 1. rewrite min_self. math.
   xapp. applys~ (>>> HR __ rs1 ___). inverts I2.
     ximpl as ts' (rs'&Inv&Ri). 
     exists rs'. split. equates* 1. rewrite min_self. math.
   xapp~. 
    lets: (Rank_hd_comp''' I1).
    lets: (Rank_hd_comp''' I2). 
     forwards: (@min_trans_elim _ _ _ (Rank t1) P); math.
     ximpl as ts' (rs'&Inv&Ri). 
      exists rs'. split. equates* 1. rewrite min_self. math.
Qed.
*)
Admitted.

Hint Extern 1 (RegisterSpec merge) => Provide merge_spec.

Lemma root_le_all : forall r t E,
  btree r t E -> exists X, 
    rep (Root t) X /\ 
    foreach (is_ge X) E.
Proof. introv H. inverts~ H. Qed.

Lemma remove_min_tree_spec : Spec remove_min_tree (ts:heap) |R>>
  forall rs Es, inv rs ts Es -> Es <> \{} -> 
  R (fun o => let (t',ts') := o : tree * heap in
     exists E' Es' X r' rs', 
       btree r' t' E' /\
       inv rs' ts' Es' /\
       Es = E' \u Es' /\
       rep (Root t') X /\
       foreach (is_ge X) Es /\ 
       rs <= rs').
Proof.
(*
  xinduction (@List.length tree). xcf. introv IH RH NE. xmatch.
  xgo. inverts RH. false.
  xgo. inverts RH as Rt R0. inverts R0. 
    lets (X&RX&MX): (root_le_all Rt). subst Es. exists~ ___.
  lets (rs0&E0&Ez&Rt&Rts&K1&K2&EQ): (inv_cons_inv RH). clear RH.
  asserts: (Ez <> \{}). intro_subst_hyp.
    destruct ts. inverts Rts. false. inverts Rts as BT. lets: (btree_not_empty BT).
    skip. (*fsetinv*)
  xapp~. destruct _x1 as [t' ts'].
   destruct P_x1 as (E'&Es'&X&r'&rs'&Rt'&Rts'&EQ'&RX&MX&D).
  xmatch. xapp~. xapp~. cbv beta in *. subst _x3 _x4. 
  lets (Y&RY&MY): (root_le_all Rt). xgo~.
  subst Es. exists~ ___.
  subst Es Ez. applys_to P_x2 nle_to_sle. 
    exists E' (E0 \u Es') __ __ __. splits~. permut_simpl.
*) skip.
Qed.

Hint Extern 1 (RegisterSpec remove_min_tree) => Provide remove_min_tree_spec.

Hint Unfold min_of.

Lemma find_min_spec : RepSpec find_min (E;heap) |R>>
  E <> \{} -> R (min_of E ;; O.t).
Proof.
  xcf. intros e E RepE HasE. simpl in RepE. xgo~.
  destruct P_x0 as (E'&Es'&X&r'&rs'&Rt'&Rts'&EQ'&RX&MX&D).
  ximpl as x Px. subst x. skip: (X \in E). eauto. (* todo: unique representation *)
Qed.

Hint Extern 1 (RegisterSpec find_min) => Provide find_min_spec.

Lemma inv_rank_smaller : forall r ts Es,
  inv r ts Es -> inv 0 ts Es.
Proof.
  introv H. inverts H; simpl. auto~.
  forwards~: (@rank_correct t).
Qed.

Lemma inv_rev_children_final : forall x X ts r E,
  rep x X ->
  btree r (Node r x ts) E ->
  exists E', rep (rev ts) E' /\ E = '{X} \u E'.
Proof.
  introv RX RT. forwards~ (E'&R'&I'&EQ'): 
    (>>> inv_rev_children x ts E r (nil:heap)).
  rew_list in I'. rewrite union_empty_l in I'.
  exists E'. split. simpl.
  apply~ inv_smaller. eauto.  
Qed.




Lemma delete_min_spec : RepSpec delete_min (E;heap) |R>>
  E <> \{} -> R (removed_min E ;; heap).
Proof. 
  xcf. introv Rts NE. simpl in Rts. xapp~. xmatch.
  destruct P_x0 as (E'&Es'&X&r'&rs'&Rt'&Rts'&EQ'&RX&MX&D).
  simpl in RX. clear H.
  asserts: (_p0 = r'). inverts~ Rt'. subst.
    forwards~ (Er&I'&EQ'): (>>> inv_rev_children_final x ts1).
  xapp~.  
    sapply~ inv_rank_smaller.
    ximpl as h Ph.
  exists (Er \u Es'). split~. subst E'. exists* X.
Qed.

Hint Extern 1 (RegisterSpec delete_min) => Provide delete_min_spec.

End BinomialHeapSpec.


