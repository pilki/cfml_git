Set Implicit Arguments. 
Require Import FuncTactics LibCore.
Require Import QueueSig_ml QueueSig_proof.
Require Import CatenableListImpl_ml.
Require Import CatenableListSig_ml CatenableListSig_proof.


(* todo: move *)
Lemma Forall2_unique : forall A1 A2 (P:A1->A2->Prop) l L1 L2,
  (forall x X Y, P x X -> P x Y -> X = Y) -> 
  Forall2 P l L1 -> Forall2 P l L2 -> L1 = L2.
Proof.
  induction l; introv H H1 H2; inverts H1; inverts H2; prove_rep.
Qed.

Hint Resolve Forall2_unique : rep.

(*todo:move
Definition rep_from_eq : forall A, Rep A A.
Proof. intros. apply (Build_Rep eq). congruence. Defined.
*)

Module CatenableListImplSpec (Q:MLQueueBis) (QS:QueueBisSigSpec with Module Q:=Q) <: CatenableListSigSpec.

(** instantiations *)

Import Q.
Module Import C <: MLCatenableList := MLCatenableListImpl Q.

(** invariant *)

Section Polymorphic.
Context `{Rep a A}.

Inductive inv : cat a -> list A -> Prop :=
  | inv_empty : 
      inv Empty nil
  | inv_struct : forall (x:a) (q:queue (cat a)) X Ls L,
      rep x X ->
      Forall2 inv q Ls ->
      L =' X :: concat Ls ->
      Forall (<> nil) Ls ->
      inv (Struct x q) L.
      
End Polymorphic.

Global Instance cat_rep `{Rep a A} : Rep (cat a) (list A).
Proof.
  intros. apply (Build_Rep inv).
  induction x; introv HX HY; inverts HX; inverts HY;
   unfolds eq'; subst; try solve [prove_rep].
  (*todo:inductino on size or depth ! *)
skip.
Defined.

(** automation  *)

Hint Constructors Forall2.
Hint Resolve Forall2_last.
Hint Extern 1 (@rep (cat _) _ _ _ _) => simpl.
Hint Constructors inv.

Ltac auto_tilde ::= eauto. (* with maths.*)

Section Polymorphic'.
Variables (a A : Type) (RA:Rep a A).

  (* todo: avoid the following lines *)
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

(** verification *)

Lemma empty_spec : 
  rep (@empty a) (@nil A).
Proof.
  generalizes RA A. apply (empty_cf a). xgo.
  intros. simple~.
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

Hint Extern 1 (rep _ _) => simpl.
Hint Resolve Forall_last.

Lemma link_spec : 
  RepSpec link (L1;cat a) (L2;cat a) |R>>
    L1 <> nil -> L2 <> nil -> R (L1 ++ L2 ; cat a).
Proof.
  xcf. introv RL1 RL2 N1 N2. xmatch.
  xgo. apply N1. apply~ to_empty.
  inverts RL1. xapp~. xgo. simpls.
  constructors~. subst. rew_concat; auto.  
Qed.

Hint Extern 1 (RegisterSpec link) => Provide link_spec.

Lemma link_all_spec : 
  RepSpec link_all (Ls;queue (cat a)) |R>>
    Ls <> nil -> R (concat Ls ; cat a).
Proof.
  
Qed.

Hint Extern 1 (RegisterSpec link_all) => Provide link_all_spec.

Lemma append_spec : 
  RepTotal append (L1;cat a) (L2;cat a) >> (L1++L2) ; cat a.
Proof.
Qed.

Hint Extern 1 (RegisterSpec append) => Provide append_spec.

Lemma cons_spec : 
  RepTotal cons (X;a) (L;cat a) >> (X::L) ; cat a.
Proof.
Qed.

Hint Extern 1 (RegisterSpec cons) => Provide cons_spec.

Lemma snoc_spec : 
  RepTotal snoc (L;cat a) (X;a) >> (L&X) ; cat a.
Proof.
Qed.

Hint Extern 1 (RegisterSpec snoc) => Provide snoc_spec.

Lemma head_spec : 
  RepSpec head (L;cat a) |R>>
     L <> nil -> R (is_head L ;; a).
Proof.
Qed.

Hint Extern 1 (RegisterSpec head) => Provide head_spec.

Lemma tail_spec :
  RepSpec tail (L;cat a) |R>> 
     L <> nil -> R (is_tail L ;; cat a).
Proof.
Qed.

Hint Extern 1 (RegisterSpec tail) => Provide tail_spec.

End Polymorphic.

End CatenableListImplSpec.

