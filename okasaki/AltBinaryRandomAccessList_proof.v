Set Implicit Arguments. 
Require Import FuncTactics LibCore.
Require Import RandomAccessListSig_ml RandomAccessListSig_proof.
Require Import AltBinaryRandomAccessList_ml.

(* todo: move *)

Lemma pair_rep : forall `{Rep a1 A1} `{Rep a2 A2} (x:a1) (y:a2) X Y,
  rep x X -> rep y Y -> rep (x, y) (X,Y).
Proof. auto. Qed.

Hint Resolve @pair_rep.

Lemma cons_not_nil : forall A (x:A) l, x::l <> nil.
Proof. auto_false. Qed.

Hint Resolve cons_not_nil.


Module AltBinaryRandomAccessListSpec <: RandomAccessListSigSpec.

(** instantiations *)

Module Import C <: MLRandomAccessList := MLAltBinaryRandomAccessList.
Import MLAltBinaryRandomAccessList.

(** invariant *)

Fixpoint splitin A (Q:list (A*A)) : list A :=
  match Q with
  | nil => nil
  | (x,y)::Q' => x::y::(splitin Q')
  end.

Inductive inv : forall `{Rep a A}, rlist a -> list A -> Prop :=
  | inv_null : forall `{Rep a A},
      inv _ Null nil
  | inv_zero : forall `{Rep a A} ls Ls L',
      inv _ ls Ls ->
      L' =' splitin Ls ->
      L' <> nil ->
      inv _ (Zero ls) L'
  | inv_one : forall `{Rep a A} x ls X Ls L',
      rep x X ->
      inv _ ls Ls ->
      L' =' X :: splitin Ls ->
      inv _ (One x ls) L'.

(** model *)

Implicit Arguments inv [[a] [A] [H]].

Global Instance rlist_rep `{Rep a A} : Rep (rlist a) (list A).
Proof.
  intros. apply (Build_Rep inv).
  introv HX HY. gen Y. 
  induction HX; introv HY; gen_eq Y':Y; 
   inverts HY; intros; subst; prove_rep.
Defined.

(** automation  *)

Hint Constructors inv.
Ltac auto_tilde ::= eauto.
Hint Extern 1 (@gt nat _ _ _) => simpl; math.

(** useful facts *)

Fixpoint size a (l:rlist a) : nat :=
  match l with
  | Null => 1%nat
  | Zero ls => (2 * (size ls))%nat
  | One x ls => (2 * (size ls) + 1)%nat
  end.

Lemma size_pos : forall a (l:rlist a), (size l:int) > 0.
Proof. induction l; simpl; math. Qed.

Lemma splitin_last : forall A Q (x y:A),
  splitin (Q & (x,y)) = splitin Q ++ x::y::nil.
Proof.
  intros. induction Q as [|[a b]]. auto.
  rew_list. simpl. rew_list. fequals.
Qed.

Lemma to_empty : forall `{Rep a A} L,
  inv Null L -> L = nil.
Proof. introv RL. set_eq L':L. inverts~ RL. Qed.

Lemma from_empty : forall `{Rep a A} l,
  inv l nil -> l = Null.
Proof. introv RL. inverts RL; auto_false. Qed.

(** verification *)

Lemma empty_spec : forall `{Rep a A},
  rep (@empty a) (@nil A).
Proof.
  intros. gen A H. apply (empty_cf a). xgo~.
Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma is_empty_spec : forall `{Rep a A},
  RepTotal is_empty (L;rlist a) >> bool_of (L = nil).
Proof.
  xcf. introv RL. xgo.
  apply~ to_empty.
  intro_subst_hyp. applys C. apply~ from_empty.
Qed.

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Lemma cons_spec : forall `{Rep a A},
  RepTotal cons (X;a) (L;rlist a) >> (X::L) ; rlist a.
Proof.
  intros. xintros.
  intros x l. intros. gen_eq n: (size l). gen a A H x l X L.
  apply~ eq_gt_induction; clears n.
  introv IH RX RL N. subst n. xcf_app. xmatch.
  xgo. rewrite~ (to_empty RL).
  xgo. inverts RL. subst~.
  inverts RL. 
   specializes IH ((a*a)%type) __ __.   
   xlet. fapplys IH; auto~. (* todo: cleanup *)
   subst. simpls. xgo~.
Qed.

Hint Extern 1 (RegisterSpec cons) => Provide cons_spec.

Lemma uncons_spec : forall `{Rep a A},
  RepSpec uncons (L;rlist a) |R>>
    L <> nil ->
    R ((fun P => let (X,T) := P : A*list A in L = X::T) ;; a * rlist a).
Proof.
  intros. xintros. intros l. intros. gen_eq n: (size l). gen a A H l L.
  apply~ eq_gt_induction; clears n.
  introv IH RL NE N. subst n. xcf_app. xmatch.
  xgo. applys NE. apply~ to_empty.
  xgo. inverts RL as RX RLs. inverts RLs. exists~ (X,@nil A).
  xgo. inverts RL as RX RLs. 
    asserts: (splitin Ls <> nil). destruct Ls.
     false C0. rewrite~ (from_empty RLs). destruct p; simple~.
    xrep~ (X,splitin Ls).
  inverts RL as RX RLs. asserts: (Ls <> nil). destruct~ Ls.
   specializes IH (a*a)%type __ __.
   xlet. fapplys IH; eauto. forwards~: (size_pos ps).
   xgo. destruct P_x1 as (((Y,Z),Ls')&((RY&RZ)&RLs')&EQL').
   subst Ls. xrep~.
Qed.

Hint Extern 1 (RegisterSpec uncons) => Provide uncons_spec.

Lemma head_spec : forall `{Rep a A},
  RepSpec head (L;rlist a) |R>>
     L <> nil -> R (is_head L ;; a).
Proof.
  xcf. introv RQ NE.
  xlet. lets M: (>>> (@uncons_spec) a __ __). xapp~. (* todo *)
  destruct _x0 as [x t]. destruct P_x0 as ([? ?]&[? ?]&?). xgo~.
Qed.

Hint Extern 1 (RegisterSpec head) => Provide head_spec.

Lemma tail_spec : forall `{Rep a A},
  RepSpec tail (L;rlist a) |R>> 
     L <> nil -> R (is_tail L ;; rlist a).
Proof.
  xcf. introv RQ NE.
  xlet. lets M: (>>> (@uncons_spec) a __ __). xapp~. (* todo *)
  destruct _x0 as [x t]. destruct P_x0 as ([? ?]&[? ?]&?). xgo~.
Qed.

Hint Extern 1 (RegisterSpec tail) => Provide tail_spec.

Lemma ZNth_split : forall A (l:list (A*A)) i x y,
  ZNth i (splitin l) (if i mod 2 '= 0%nat then x else y) <-> 
  ZNth (i/2) l (x,y).
Admitted.

Ltac auto_tilde ::= eauto with maths.

Lemma ZInbound_splitin : forall A i j (ls:list (A*A)),
  ZInbound j (splitin ls) -> i= j/2 -> ZInbound i ls.
Admitted.

Lemma ZNth_splitin : forall A i (ls:list (A*A)) x y,
  ZNth (i / 2) ls (x,y) ->
  ZNth i (splitin ls) (if i mod 2 '= 0 then x else y).
Admitted.

Lemma lookup_spec : forall `{Rep a A},
  RepSpec lookup (i;int) (L;rlist a) |R>>
     ZInbound i L -> R (ZNth i L ;; a).
Proof.
  intros. xintros. intros i. gen_eq n: (abs i). gen a A H i.
  apply~ eq_gt_induction; clears n.
  introv IH. introv. introv N RI [b RL] Bi. inverts RI. subst n. 
  xcf_app. xret~. destruct _x0 as (i,f). inverts P_x0. xmatch.
  xgo. inverts RL. apply~ ZInbound_nil_inv.
  xgo. inverts RL. esplit. split~. apply~ ZNth_here.
  inverts RL.
    asserts: (i <> 0). intro_subst_hyp. false~ C0.
    forwards~ Bi': (ZInbound_cons_pos_inv Bi).
  specializes IH (i-1) (splitin Ls). 
   destruct Bi'. rewrite gt_is_flip_lt. apply~ Zabs_nat_lt. 
   (* todo: induction on int *)
   xapp. simpl. eauto. exists __. constructors~. apply~ @inv_strengthen'.
    intro_subst_hyp. apply~ ZInbound_nil_inv. auto.
   intros y (Y&RY&NY). exists Y. split~. apply~ ZNth_next.
  inverts RL. xlet. specializes IH (a*a)%type (i/2) ps (i/2) Ls. skip. 
    xapp. simple~. eauto. apply~ ZInbound_splitin. 
  xmatch. destruct P_x2 as ([X Y]&[HX HY]&NXY).
  applys_to NXY ZNth_splitin.
  xif; case_if in NXY; tryfalse. xgo~. xgo~.
Admitted.

Definition FUpdate A (n:int) (f:A->A) l l' :=
     (length l = length l')
  /\ (forall y m, ZNth m l y -> m <> n -> ZNth m l' y)
  /\ (forall y, ZNth n l y -> ZNth n l (f y)).

Lemma FUpdate_here : forall A (x:A) f l,
  FUpdate 0 f (x::l) (f x :: l).
Admitted.

Lemma FUpdate_next : forall A i j (x:A) f l l',
   FUpdate j f l l' ->
   j = i-1 ->
   FUpdate i f (x::l) (x::l').
Admitted.

Lemma FUpdate_splitin : forall A i j f f' (l l':list (A*A)),
  FUpdate j f' l l' -> j = i/2 ->
  (forall x y, f' (x,y) = if i mod 2 '= 0 then (f x, y) else (x, f y)) ->
  FUpdate i f (splitin l) (splitin l').
Admitted.

Instance val_rep : Rep val val.
Proof. apply (Build_Rep eq). congruence. Defined.

Lemma fupdate_spec : forall `{Rep a A},
  RepSpec fupdate (f;val) (i;int) (L;rlist a) |R>> 
     ZInbound i L ->
     forall F, (RepTotal f (x;a) >> (= F x ;; a)) ->
     R (FUpdate i F L ;; rlist a).
Proof.
  intros. xintros. skip. intros f i. gen_eq n: (abs i). gen a A H i f.
  apply~ eq_gt_induction; clears n.
  introv IH. introv. introv N RF RI [b RL] Bi SF.
  inverts RI. inverts RF. subst n.
  xcf_app. xret~. destruct _x0 as (i,f). inverts P_x0. xmatch.
  xgo. inverts RL. apply~ ZInbound_nil_inv.
  inverts RL. xgo~. destruct P_x1 as (Y&RY&FY). subst.
  esplit. split~. apply FUpdate_here.
  inverts RL.
    asserts: (i <> 0). intro_subst_hyp. false~ C0.
    forwards~ Bi': (ZInbound_cons_pos_inv Bi). 
  xlet. specializes IH (i-1). fapplys IH; eauto.
   skip. (* induction int *)
   reflexivity. (* automate *)
   reflexivity.
   exists __. constructors~. eapply inv_strengthen'. eauto.
    skip. (* Ls<>nil si (ZInbound i (splitin ls) *)
   destruct P_x2 as (Ls'&RLs'&PLs').
   xapp_spec~ (@cons_spec a _ _). 
   ximpl as L. (* todo Hx -> HL *)
   esplit. split~. (*tactic*) applys~ FUpdate_next.

  (* last *)
  inverts RL. xfun_mg. simpl in Sf'. xlet.
  specializes IH (a*a)%type (i/2) f'
    (fun P:A*A => let (x,y) := P in
     if i mod 2 '= 0 then (F x, y) else (x, F y)); auto~.
   skip. reflexivity. reflexivity. apply~ ZInbound_splitin.
   eapply IH.
 
  apply Sf'. xisspec. clear IH Sf'. clear C C0 C1.
  intros [x y] [X Y] [RX RY]. xmatch.
  xif. xapp~. destruct P_x8 as (X'&RX'&PX').
  xgo. exists (X',Y). split~. case_if; tryfalse. subst~.
  xapp~. destruct P_x7 as (Y'&RY'&PY').
  xgo. exists (X,Y'). split~. case_if; tryfalse. subst~.

  destruct P_x9 as (L'&[b' RL']&PL').
  xgo. exists (splitin L'). split.
   exists __. constructors~. eapply inv_strengthen'. eauto. skip.
   apply~ (FUpdate_splitin). 
Admitted.


Lemma FUpdate_ZUpdate : forall i x l l',
  FUpdate i (fun _ => x) l l' -> ZUpdate i x l l'.
Admitted.


Lemma update_spec : forall `{Rep a A},
  RepSpec update (i;int) (X;a) (L;rlist a) |R>> 
    ZInbound i L -> R (ZUpdate i X L ;; rlist a).
Proof.
  xcf. introv RI RX [b RL] Bi.
  (*
  xfun (fun f => RepTotal f (y;a) >> (= X ; a)).*)
  xfun_mg. simpls. xapp_spec fupdate_spec.
  specializes~ HR (fun _:A => X). reflexivity.
  fapplys HR. apply S_f0. xisspec. (* todo: xbody_exploit *)
   introv RY. xgo~.
  ximpl as l' [L' [RL' G]].
   exists L'. splits. apply RL'. apply~ FUpdate_ZUpdate.
Admitted.

Hint Extern 1 (RegisterSpec snoc) => Provide snoc_spec.

End AltBinaryRandomAccessListSpec.

