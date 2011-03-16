Set Implicit Arguments. 
Require Import FuncTactics LibCore.
Require Import QueueBisSig_ml QueueBisSig_proof.
Require Import CatenableListImpl_ml.
Require Import CatenableListSig_ml CatenableListSig_proof.

Module CatenableListImplSpec (Q:MLQueueBis) 
 (QS:QueueBisSigSpec with Module Q:=Q) <: CatenableListSigSpec.

(** instantiations *)

Import Q. 
Module Import C <: MLCatenableList := MLCatenableListImpl Q.

(** invariant *)

Inductive inv `{Rep a A} : cat a -> list A -> Prop :=
  | inv_empty : 
      inv Empty nil
  | inv_struct : forall (x:a) (q:queue (cat a)) X Ls L,
      rep x X ->
      Forall2 inv q Ls ->
      L =' X :: concat Ls ->
      Forall (<> nil) Ls ->
      inv (Struct x q) L.

(** model *)

Fixpoint size a (c:cat a) : nat :=
  match c with
  | Empty => 0%nat
  | Struct _ q => (1 + List.fold_right (fun c x => (x + size c)%nat) 0%nat q)%nat
  end.

Global Instance cat_rep `{Rep a A} : Rep (cat a) (list A).
Proof.
  intros. apply (Build_Rep inv).
  intros c. gen_eq n: (size c). gen a A H.
  induction n using peano_induction. introv N K1 K2. subst n.
  inverts K1; inverts K2. prove_rep.
  subst. fequals. prove_rep. clears X0 X1. clear H4 H11.
  simpl in H.
  gen Ls0. induction H2; introv M; inverts M.
   auto. rew_concat. simpl in H. fequals.
   apply* H. math.
   apply~ IHForall2. intros. apply* H. math.
Defined.

(** automation  *)

Hint Constructors Forall2.
Hint Resolve Forall_last Forall2_last.
Hint Constructors inv.

Ltac auto_tilde ::= eauto. 

Section Polymorphic.
Variables (a A : Type) (RA:Rep a A).

  (* todo: shound not need the following lines *)
Hint Extern 1 (RegisterSpec Q.is_empty) => Provide (@QS.is_empty_spec (cats a) _ _).
Hint Extern 1 (RegisterSpec Q.snoc) => Provide (@QS.snoc_spec (cats a) _ _).
Hint Extern 1 (RegisterSpec Q.head) => Provide (@QS.head_spec (cats a) _ _).
Hint Extern 1 (RegisterSpec Q.tail) => Provide (@QS.tail_spec (cats a) _ _).

(** useful facts *)

Lemma to_empty : forall L,
  rep Empty L -> L = nil.
Proof. introv RL. inverts~ RL. Qed.

Lemma to_not_empty : forall c L,
  rep c L -> L <> nil -> c <> Empty.
Proof.
  introv RL NE K. subst. apply NE. apply~ to_empty.
Qed.

Lemma from_empty : forall c,
  rep c nil -> c = Empty.
Proof. introv RC. inverts RC. auto. false. Qed.

Lemma from_not_empty : forall l L,
  rep l L -> l <> Empty -> L <> nil.
Proof. introv H NE K. subst. apply NE. apply~ from_empty. Qed.

Lemma concat_not_nil : forall A (ls: list (list A)), 
  ls <> nil -> Forall (<> nil) ls -> concat ls <> nil.
Proof.
  introv NE NsE. destruct ls. false. inverts NsE.
  rew_concat. destruct l. false. intros K. false.
Qed.

(** verification *)

Lemma empty_spec : 
  rep (@empty a) (@nil A).
Proof.
  generalizes RA A. apply (empty_cf a). xgo~.
Qed.

Hint Extern 1 (rep empty _) => apply empty_spec.

Lemma is_empty_spec : 
  RepTotal is_empty (L;cat a) >> bool_of (L = nil).
Proof.
  xcf. intros l L RL. xgo.
  apply~ to_empty.
  intro_subst_hyp. apply C. apply~ from_empty.
Qed. 

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Lemma link_spec : 
  RepSpec link (L1;cat a) (L2;cat a) |R>>
    L1 <> nil -> L2 <> nil -> R (L1 ++ L2 ;- cat a).
Proof.
  xcf. introv RL1 RL2 N1 N2. xmatch.
  xgo. apply N1. apply~ to_empty.
  inverts RL1. xapp~. xgo. simpls.
  constructors~. subst. rew_concat; auto.  
Qed.

Hint Extern 1 (RegisterSpec link) => Provide link_spec.

Lemma link_all_spec : 
  RepSpec link_all (Ls;queue (cat a)) |R>>
    Ls <> nil -> Forall (<> nil) Ls -> R (concat Ls ;- cat a).
Proof.
  xintros. 
  intros ls Ls RLs Ne Nn. gen_eq n: (length Ls). gen ls Ls RLs Ne Nn.
  apply~ eq_gt_induction; clears n. introv IH RQ Ne Nn N. subst n.
  xcf_app.  
  xlet. xapp~. xret. eexact P_x0. 
  xlet. xapp~.
  destruct Pt as (L&RL&(Q&EQLs)).
  destruct Pq' as (Ls'&RLs'&(Q'&EQLs')).
  rewrite EQLs' in EQLs. inverts EQLs.
  xapp~. xif. xgo. subst. rew_concat. auto.
  xlet. fapplys IH; auto~.
    subst. inverts~ Nn.
    subst. rew_length. math.
  subst Ls. simpls. inverts Nn. inverts RQ. 
  destruct P_x0 as (X&RX&(T'&EQLT')). inverts EQLT'.
  xapp~. apply~ concat_not_nil.
Qed.

Hint Extern 1 (RegisterSpec link_all) => Provide link_all_spec.

Lemma append_spec : 
  RepTotal append (L1;cat a) (L2;cat a) >> (L1++L2) ;- cat a.
Proof.
  xcf. introv RL1 RL2. xmatch.
  xgo. inverts RL1. rew_list~.
  xgo. inverts RL2. rew_list~.
  xapp~.
    applys~ from_not_empty. intro_subst_hyp. false~ C.
    applys~ from_not_empty. intro_subst_hyp. false~ C0.
Qed.

Hint Extern 1 (RegisterSpec append) => Provide append_spec.

Hint Constructors Forall.

Lemma Q_empty_spec : Forall2 inv Q.empty nil.
Proof. lets H: (@QS.empty_spec (cats a) _ _). apply H. Qed.

Hint Resolve Q_empty_spec.

Lemma cons_spec : 
  RepTotal cons (X;a) (L;cat a) >> (X::L) ;- cat a.
Proof. xgo~. Qed.

Hint Extern 1 (RegisterSpec cons) => Provide cons_spec.

Lemma snoc_spec : 
  RepTotal snoc (L;cat a) (X;a) >> (L&X) ;- cat a.
Proof. xgo~. Qed.

Hint Extern 1 (RegisterSpec snoc) => Provide snoc_spec.

Lemma head_spec : 
  RepSpec head (L;cat a) |R>>
     L <> nil -> R (is_head L ;; a).
Proof.
  xcf. introv RL NE. inverts RL. false. xgo~.
Qed.

Hint Extern 1 (RegisterSpec head) => Provide head_spec.

Lemma tail_spec :
  RepSpec tail (L;cat a) |R>> 
     L <> nil -> R (is_tail L ;; cat a).
Proof.
  xcf. introv RL NE. inverts RL. false. xgo~.
  subst. eauto 8. 
  subst. ximpl~.
Qed.

Hint Extern 1 (RegisterSpec tail) => Provide tail_spec.

End Polymorphic.

End CatenableListImplSpec.


