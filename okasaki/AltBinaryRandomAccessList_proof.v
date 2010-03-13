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
Admitted.

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

Lemma Nth_split : forall A (l:list (A*A)) (k r : nat) x y,
  r < 2%nat ->
  Nth (2*k) (splitin l) (if r '= 0%nat then x else y) <-> 
  Nth k l (x,y).
Admitted.

Ltac auto_tilde ::= eauto with maths.

Lemma lookup_spec : forall `{Rep a A},
  RepSpec lookup (i;int) (L;rlist a) |R>>
     0 <= i -> i < length L -> R (Nth (abs i) L ;; a).
Proof.
  intros. xintros. skip. intros i. gen_eq n: (abs i). gen a A H i.
  apply~ eq_gt_induction; clears n.
  introv IH. introv. introv N RI [b RL] Pos Len. inverts RI. subst n. 
  xcf_app. xret~. destruct _x0 as (i,f). inverts P_x0. xmatch.
  xgo. inverts RL. rew_length in Len. math.
  xgo. inverts RL. esplit. split~. equates 3. constructors~. skip.
  inverts RL. rew_length in Len. asserts: (i <> 0). intro_subst_hyp. false~ C0.
  specializes IH (i-1) (splitin Ls). rewrite gt_is_flip_lt. apply~ Zabs_nat_lt. 
   xapp. simpl. eauto. exists __. constructors~. apply~ @inv_strengthen'.
    intro_subst_hyp. simpl in Len. rew_length in Len. math. math. math.
   intros y (Y&RY&NY). exists Y. split~. equates 3. constructors~. apply~ abs_spos.
  inverts RL. xlet. specializes IH (a*a)%type (i/2) ps (i/2) Ls. skip. 
    xapp. simple~. eauto. skip. skip.
  xmatch. destruct P_x2 as ([X Y]&[HX HY]&NXY).
  xif. xgo. exists X. split~. skip.
  xgo. exists Y. split~. skip.    
Admitted.

Definition FUpdate A (n:nat) (f:A->A) l l' :=
     (forall y m, Nth m l y -> m <> n -> Nth m l' y)
  /\ (forall y, Nth n l y -> Nth n l (f y)).

Instance val_rep : Rep val val.
Proof. apply (Build_Rep eq). congruence. Defined.

Lemma fupdate_spec : forall `{Rep a A},
  RepSpec fupdate (f;val) (i;int) (L;rlist a) |R>> 
     0 <= i -> i < length L -> 
     forall F, (RepTotal f (x;a) >> = F x) ->
     R (FUpdate (abs i) F L ;; rlist a).
Proof.
 skip.
Qed.

Lemma update_spec : forall `{Rep a A},
  RepSpec update (i;int) (X;a) (L;rlist a) |R>> 
     0 <= i -> i < length L -> R (Update (abs i) X L ;; rlist a).
Proof.
  xcf. introv RI RX [b RL] L1 L2.
  xfun_mg. simpls. xapp_spec fupdate_spec.
  specializes~ HR (fun _:A => X). reflexivity. 
  fapplys HR.
  skip. ximpl as l' [L' [RL' G]].
   exists L'. splits. apply RL'.
   subst.
  destruct G. split. eauto. applys H1. skip. (* used to be one *)
Admitted.

Hint Extern 1 (RegisterSpec snoc) => Provide snoc_spec.

End AltBinaryRandomAccessListSpec.

