test
Set Implicit Arguments. 
Require Import FuncTactics LibCore.
Require Import RandomAccessListSig_ml RandomAccessListSig_proof.
Require Import AltBinaryRandomAccessList_ml.

(* todo share *)
Fixpoint splitin A (Q:list (A*A)) : list A :=
  match Q with
  | nil => nil
  | (x,y)::Q' => x::y::(splitin Q')
  end.

Lemma splitin_last : forall A Q (x y:A),
  splitin (Q & (x,y)) = splitin Q ++ x::y::nil.
Proof.
  intros. induction Q as [|[a b]]. auto.
  rew_list. simpl. rew_list. fequals.
Qed.


Module AltBinaryRandomAccessListSpec <: RandomAccessListSigSpec.

(** instantiations *)

Module Import C <: MLRandomAccessList := MLAltBinaryRandomAccesList. (* todo: missing "s" *)
Import MLAltBinaryRandomAccesList.

(** invariant *)

Inductive inv : bool -> forall `{Rep a A}, rlist a -> list A -> Prop :=
  | inv_null : forall `{Rep a A},
      inv true _ Null nil
  | inv_zero : forall `{Rep a A} ls Ls L' canstop,
      inv false _ ls Ls ->
      L' = splitin Ls ->
      inv canstop _ (Zero ls) L'
  | inv_one : forall `{Rep a A} x ls X Ls L' canstop,
      rep x X ->
      inv true _ ls Ls ->
      L' = X :: splitin Ls ->
      inv canstop _ (One x ls) L'.

Implicit Arguments inv [[a] [A] [H]].

Global Instance rlist_rep `{Rep a A} : Rep (rlist a) (list A).
Proof.
  intros. apply (Build_Rep (fun l L => exists b, inv b l L)).
  introv [bx HX] [by HY]. gen by Y. 
  induction HX; introv HY; gen_eq Y':Y; 
   inverts HY; intros; subst; prove_rep.
Defined.

(** automation  *)

Hint Extern 1 (@rep (rlist _) _ _ _ _) => simpl.
Hint Constructors inv.

Ltac auto_tilde ::= eauto.

(** useful facts *)

Fixpoint size a (l:rlist a) : nat :=
  match l with
  | Null => 0%nat
  | Zero ls => (2 * (size ls))%nat
  | One x ls => (2 * (size ls) + 1)%nat
  end.

Lemma to_empty : forall `{Rep a A} L b,
  inv b Null L -> L = nil.
Proof. introv RL. set_eq L':L. inverts~ RL. Qed.

Lemma from_empty : forall `{Rep a A} l b,
  inv b l nil -> l = Null.
Proof.
  introv.
(* gen_eq L: (@nil A). induction RQ; intros; subst. TODO*)
Admitted.

Lemma inv_weaken : forall `{Rep a A} l L,
  inv false l L -> inv true l L.
Proof. introv M. inverts M; constructors~. Qed.

Hint Resolve @inv_weaken.

Lemma inv_strengthen : forall `{Rep a A} l X L b,
  inv b l (X::L) -> inv false l (X::L).
Proof. introv M. inverts~ M. Qed.

Hint Resolve @inv_strengthen.

Lemma inv_strengthen' : forall `{Rep a A} l L b,
  inv b l L -> L <> nil -> inv false l L.
Proof. introv M. inverts~ M. auto_false. Admitted. (*evars*)

Hint Resolve @inv_strengthen.


(* H int Resolve (@rep (rlist _) _ _ _) => exists true.*)


(** verification *)

Lemma empty_spec : forall `{Rep a A},
  rep (@empty a) (@nil A).
Proof.
  intros. gen A H. apply (empty_cf a). xgo.
  intros. exists~ true.
Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma is_empty_spec : forall `{Rep a A},
  RepTotal is_empty (L;rlist a) >> bool_of (L = nil).
Proof.
  xcf. introv [b RL]. xgo.
  apply~ to_empty.
  intro_subst_hyp. applys C. apply~ from_empty.
Qed.

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Lemma pair_rep : forall `{Rep a1 A1} `{Rep a2 A2} (x:a1) (y:a2) X Y,
  rep x X -> rep y Y -> rep (x, y) (X,Y).
Proof. auto. Qed.

Hint Resolve @pair_rep.

Hint Extern 1 (@gt nat _ _ _) => simpl; math.

Lemma cons_spec : forall `{Rep a A},
  RepTotal cons (X;a) (L;rlist a) >> (X::L) ; rlist a.
Proof.
  intros. xintros. (* todo: intros useless *)
  intros x l. intros. gen_eq n: (size l). gen a A H x l X L.
  apply~ eq_gt_induction; clears n.
  introv IH RX [b RL] N. subst n. xcf_app. xmatch.
  xgo. rewrite~ (to_empty RL).
  xgo. simpl. inverts~ RL.
  inverts RL.
   specializes IH ((a*a)%type) __ __. xlet. fapplys IH; auto~. (* todo *)
   destruct P_x1 as (b'&K). lets: (inv_strengthen K). xgo~.
Qed.

Hint Extern 1 (RegisterSpec cons) => Provide cons_spec.
(*
Lemma rep_null : forall `{Rep a A},
  rep Null (@nil A).
Proof. exists~ __. Qed.
Hint Resolve @rep_null.
*)

Lemma uncons_spec : forall `{Rep a A},
  RepSpec uncons (L;rlist a) |R>>
     L <> nil -> R ((fun P => let (X,T) := P : A*list A in L = X::T) ;; a * rlist a).
Proof.
  intros. xintros. instantiate (1 := (a * rlist a)%type).
   instantiate (1 := rlist a). xcf; auto.
  intros l. intros. gen_eq n: (size l). gen a A H l L.
  apply~ eq_gt_induction; clears n.
  introv IH [b RL] NE N. subst n. xcf_app. xmatch.
  xgo. applys NE. apply~ to_empty.
  xgo. inverts RL. inverts H10. exists~ (X,@nil A).
  xgo. inverts RL. exists~ (X,splitin Ls). splits~.
   eapply pair_rep. eauto. exists __. constructors.
  eapply @inv_strengthen'. eauto. intro_subst_hyp.
  applys C0. rewrite~ (from_empty H10). auto. (* todo cleanup *)

  inverts RL. specializes IH (a*a)%type __ __. xlet.
  fapplys IH; eauto. (* todo: copy *) skip.
  simpl. (* size pos when non empty *) skip.
  xgo. destruct P_x1 as (((X,Y),Ls')&((RX&RY)&RLs')&EQL').
  subst Ls. exists __. split~. apply~ @pair_rep. skip.
  simpl. eauto. 
Qed.

Hint Extern 1 (RegisterSpec uncons) => Provide uncons_spec.

Lemma head_spec : forall `{Rep a A},
  RepSpec head (L;rlist a) |R>>
     L <> nil -> R (is_head L ;; a).
Proof.
  xcf. introv RQ NE.
  xlet. lets M: (>>> (@uncons_spec) a __ __). xapp~. (* todo *)
  destruct _x0 as [x t]. destruct P_x0 as ([X T]&[? ?]&?). xgo~.
Qed.

Hint Extern 1 (RegisterSpec head) => Provide head_spec.

Lemma tail_spec : forall `{Rep a A},
  RepSpec tail (L;rlist a) |R>> 
     L <> nil -> R (is_tail L ;; rlist a).
Proof.
  xcf. introv RQ NE.
  xlet. lets M: (>>> (@uncons_spec) a __ __). xapp~. (* todo *)
  destruct _x0 as [x t]. destruct P_x0 as ([X T]&[? ?]&?). xgo~.
Qed.

Hint Extern 1 (RegisterSpec tail) => Provide tail_spec.

Lemma snoc_spec : forall `{Rep a A},
  RepTotal snoc (Q;queue a) (X;a) >> (Q & X) ; queue a.
Proof.
  intros. xintros. intros. sets_eq n: (length Q).
  gen a A H x1 x2 Q X. apply~ eq_gt_induction; clears n.
  introv IH. intros ? ? ? q y Q RQ N Y RY. subst n.
  xcf_app. xmatch. 
  xgo. inverts RQ as _ M. inverts M. rew_list~.
  xgo. inverts RQ as _ M. inverts M. rew_list~. eauto 7.
  xgo. inverts RQ as. introv Df Vf Rm _ Dr EQ.
   inverts Dr. subst Q. rew_list~. eauto 7.
  inverts RQ as. introv Df Vf Rm _ Dr EQ. 
   inverts Dr as RX. xlet.
    applys~ (>>> IH ((a*a)%type) (x,y) (X,Y)). skip.
   xgo. hnf in P_x0. subst Q. constructors~.
     rew_list. rewrite~ splitin_last.
  xgo. inverts RQ. 
    destruct d. applys~ C. applys~ C0. auto.
    destruct dr. applys~ C1. applys~ C2. auto.
Qed.

Hint Extern 1 (RegisterSpec snoc) => Provide snoc_spec.

End AltBinaryRandomAccessListSpec.

