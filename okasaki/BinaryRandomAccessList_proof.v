Set Implicit Arguments. 
Require Import FuncTactics LibCore.
Require Import RandomAccessListSig_ml RandomAccessListSig_proof.
Require Import BinaryRandomAccessList_ml.

Ltac xrep_in_core H I1 I2 I3 :=
  destruct H as (I1&I2&I3).

Tactic Notation "xrep" "in" hyp(H) "as" 
  simple_intropattern(I1) simple_intropattern(I2) simple_intropattern(I3) :=
  xrep_in_core H I1 I2 I3. 
Tactic Notation "xrep" "in" hyp(H) "as" simple_intropattern(I1) :=
  let I2 := fresh "R" I1 in let I3 := fresh "P" I1 in
  xrep in H as I1 I2 I3.
Tactic Notation "xrep" "in" hyp(H) :=
  let X := fresh "X" in xrep in H as X.

Ltac xrep_core_using E cont1 cont2 := 
  exists E; split; [ cont1 tt | cont2 tt ].
Ltac xrep_core cont1 cont2 := 
  esplit; split; [ cont1 tt | cont2 tt ].
Ltac xrep_core_post tt :=
  try assumption.
Ltac idtacs tt :=
  idtac.
Ltac xrep_core_using_with E solver := 
  xrep_core_using E ltac:(fun _ => xrep_core_post tt; solver tt) ltac:(solver).
Ltac xrep_core_with solver := 
  xrep_core_using ltac:(fun _ => xrep_core_post tt; solver tt) ltac:(solver).

Tactic Notation "xrep" constr(E) :=
  xrep_core_using E ltac:(xrep_core_post) ltac:(idtacs).
Tactic Notation "xrep" :=
  xrep_core ltac:(xrep_core_post) ltac:(idtacs).
Tactic Notation "xrep" "~" constr(E) :=
  xrep_core_using_with E ltac:(fun _ => xauto_tilde).
Tactic Notation "xrep" "~" :=
  xrep_core_with ltac:(fun _ => xauto_tilde).
Tactic Notation "xrep" "*" constr(E) :=
  xrep_core_using_with E ltac:(fun _ => xauto_star).
Tactic Notation "xrep" "*" :=
  xrep_core_with ltac:(fun _ => xauto_star).



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

(* todo: use next one *)
Lemma inv_strengthen : forall p ts L T,
  inv true p ts (T++L) -> T <> nil -> inv false p ts (T++L).
Proof.
  introv M. gen_eq L':(T++L). gen T L. induction M; intros; subst.
  false H0. destruct~ (nil_eq_app_inv H).
  constructors~.
  constructors~.
Qed.

Lemma inv_strengthen' : forall p ts L,
  inv true p ts L -> L <> nil -> inv false p ts L.
Proof.
  introv M. induction M; intros; subst; tryfalse; auto~.
Qed.


Lemma inv_strengthen'' : forall p ts L,
  inv true p ts L -> ts <> nil -> inv false p ts L.
Proof.
  introv M. induction M; intros; subst; tryfalse; auto~.
Qed.



Hint Resolve @btree_not_empty.
(*Hint Resolve @inv_strengthen.*)

Hint Extern 1 (@lt nat _ _ _) => rew_list; math.

Lemma cons_tree_spec : 
  Spec cons_tree (t:tree a) (ts:rlist a) |R>> 
    forall z p T L, btree p t T -> inv z p ts L ->
    R (fun ts' => inv z p ts' (T++L)).
Proof.
  xinduction (fun (t:tree a) (ts:rlist a) => length ts).
  xcf. introv IH Rt Rts. inverts Rts; xgo~.
  subst. constructors. rew_list in P_x1. applys inv_strengthen'.
   auto. intros K. destruct (app_eq_nil_inv K).  
   asserts: (T<>nil). auto~. (* todo: "down" *) false.
Qed.

Hint Extern 1 (RegisterSpec cons_tree) => Provide cons_tree_spec.

Lemma cons_spec : 
  RepTotal cons (X;a) (L;rlist a) >> (X::L) ; rlist a.
Proof. xcf. introv RX RL. simpl in RL. xgo~. Qed.

Hint Extern 1 (RegisterSpec cons) => Provide cons_spec.

Lemma uncons_tree_spec : 
  Spec uncons_tree (ts:rlist a) |R>> 
    forall z p L, inv z p ts L -> ts <> nil ->
    R (fun r => let (t',ts') := r : tree a * rlist a in
       exists T' L', btree p t' T' /\ inv true p ts' L' /\ L = T' ++ L').
Proof.
  xinduction (fun (ts:rlist a) => length ts).
  xcf. introv IH Rts Ne. xmatch.
  xgo. inverts Rts. inverts H5. subst. exists___. splits~.
  xgo. inverts Rts. subst. exists___. splits~. 
    constructors. applys~ inv_strengthen''. intro_subst_hyp. apply~ C0.
  inverts Rts. xapp~. intro_subst_hyp. inverts H3. xgo.
  intuit P_x1. inverts H1. maths (p = p0). subst p0.
  exists___. splits; eauto. (* todo: eq on list à protéger *)
  subst. rew_list~.
 intuit _x1. (* todo : intuit H ne doit s'appeler que sur les sousbuts*)
  (* todo: récupérer ça *) skip:(p>=0). inverts H1. math.
   applys~ C2.
Qed.

Hint Extern 1 (RegisterSpec uncons_tree) => Provide uncons_tree_spec.

Ltac xrep_core_post tt ::= try eassumption.

Lemma head_spec : 
  RepSpec head (L;rlist a) |R>>
    L <> nil -> R (is_head L ;; a).
Proof.
  xcf. introv RL NE. simpl in RL. xgo~.
  inverts RL; auto_false.
  destruct P_x0 as (T'&L'&RT'&RL'&E). inverts RT'. rew_list in E. 
  (* bug xrep~. *) xrep. eauto.
  intuit _x0. inverts H0. applys~ C.
  skip: (p >= 0). math.
Qed.

Hint Extern 1 (RegisterSpec head) => Provide head_spec.

Lemma tail_spec :
  RepSpec tail (L;rlist a) |R>> 
     L <> nil -> R (is_tail L ;; rlist a).
Proof.
  xcf. introv RL NE. simpl in RL. xgo~.
  inverts RL; auto_false.
  (* todo: modify source to avoid snd destruct P_x0 as (T'&L'&RT'&RL'&E). *)
  skip.
Qed.

Hint Extern 1 (RegisterSpec tail) => Provide tail_spec.

(* modifier le code de lookupTree aussi pour utiliser un if *)

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