Set Implicit Arguments.
Require Import FuncTactics LibCore.
Require Import OrderedSig_ml SortableSig_ml OrderedSig_proof SortableSig_proof.
Require Import BottomUpMergeSort_ml.

Module BottomUpMergeSortSpec (O:MLOrdered) (OS:OrderedSigSpec with Module O:=O)
  <: SortableSigSpec with Definition H.MLElement.t := O.t.

(** instantiations *)

Module Import H <: MLSortable := MLBottomUpMergeSort O.
Import O.
Module Import OS := OS.
Existing Instance le_inst.
Existing Instance le_order.

(** invariant *)

Notation "'is_ge'" := (@le T _).

Inductive seg : list O.t -> multiset T -> Prop :=
  | seg_nil : seg nil \{}
  | seg_cons : forall s x X E E',
      rep x X ->
      seg s E ->
      foreach (is_ge X) E ->
      E' =' \{X} \u E ->
      seg (x::s) E'.

(** model *)

Instance seg_rep : Rep (list O.t) (multiset T).
Proof.
  apply (Build_Rep seg).
  induction x; introv HX HY; inverts HX; inverts HY; subst; prove_rep.
Defined.

(** invariant *)

Inductive inv : int -> int -> list (list O.t) -> multiset T -> Prop :=
  | inv_empty : forall p,
      inv 0 p nil \{} 
  | inv_even : forall k n p ss Es,
      inv k (2*p) ss Es -> 
      n = 2 * k ->
      inv n p ss Es
  | inv_odd : forall k n p s ss E Es E',
      inv k (2*p) ss Es ->
      n = 2 * k + 1 ->
      rep s E ->
      length s = p :> int ->
      E' =' E \u Es ->
      inv n p (s::ss) E'.

(** model *)

Instance heap_rep : Rep sortable (multiset T).
Proof.
  apply (Build_Rep (fun p E => let (n,ss) := p:sortable in inv n 1 ss E)).
  cuts: (forall l n1 p1 E1, inv n1 p1 l E1 -> forall n2 p2 E2, inv n2 p2 l E2 -> E1 = E2).
    intros. destruct* x.
  introv HX. induction HX; introv HY; unfolds eq'.
  gen_eq m: (@nil (list t)). induction HY; unfolds eq'; intros; subst; tryfalse; auto.
  eauto.
  gen_eq m: (s::ss). induction HY; introv EQ; unfolds eq'; intros; inverts EQ; subst; prove_rep.
Defined.

(** automation *)

Hint Extern 1 (_ = _ :> multiset _) => permut_simpl : multiset.
Definition U := multiset T.

Ltac myauto cont :=
  match goal with 
  | |- _ = _ :> multiset ?T => try solve [ change (multiset T) with U; cont tt ]
  | |- _ => cont tt
  end. 

Ltac auto_tilde ::= myauto ltac:(fun _ => eauto with maths).
Ltac auto_star ::= try solve [ intuition (eauto with multiset) ].
Hint Extern 1 (@lt nat _ _ _) => simpl; math.
Hint Constructors inv sorted Forall2.

(** useful facts *)

Lemma inv_n_pos : forall n p ss E, 
  inv n p ss E -> n >= 0.
Proof. introv H. induction~ H. Qed.

Lemma inv_nil_inv : forall n p Es,
  inv n p nil Es -> Es = \{}.
Proof.
  introv H. sets_eq R: (@nil (list t)).
  gen EQR. induction H; intros; subst; tryfalse; auto~.
Qed.

Lemma inv_cons_inv : forall n' p' s ss E',
  inv n' p' (s::ss) E' -> 
  exists n p E Es,  
    inv n p ss Es /\
    seg s E /\
    E' = E \u Es.
Proof.
  introv H. sets_eq R: (s::ss). gen s ss.
  induction H; intros; subst; tryfalse.
  eauto. inverts EQR. eauto 8.
Qed. 

Lemma foreach_ge_trans : forall (X Y : OS.T) (E : multiset OS.T),
  foreach (is_ge X) E -> Y <= X -> foreach (is_ge Y) E.
Proof. intros. apply* foreach_weaken. intros_all. apply* le_trans. Qed.

Lemma seg_to_sorted : forall s E, 
  seg s E -> exists S, rep s S /\ sorted S E.
Proof.
  introv H. induction H; unfolds eq'.
  exists~ (@nil T).
  destruct IHseg as (S&?&?). subst. exists~ (X::S).
Qed.

Hint Resolve inv_n_pos foreach_ge_trans.

(** verification *)

Lemma mrg_spec : Spec mrg s1 s2 |R>>
  forall E1 E2, seg s1 E1 -> seg s2 E2 ->
  R (fun s' => seg s' (E1 \u E2) 
     /\ length s' = (length s1 + length s2)%nat).
Proof.
  xinduction (fun s1 s2 : list t => (length s1 + length s2)%nat).
  xcf. introv IH Rs1 Rs2. xmatch.
  xgo. inverts Rs1. split. equates* 1. rew_list~. 
  xgo. inverts Rs2. split. equates* 1. rew_list~. 
  xcleanpat. unfold uncurry2 in IH. rew_length in IH.
  inverts keep Rs1 as Rx Sxs' Lx. 
  inverts keep Rs2 as Ry Sys' Ly. xapp*. xif.  
  xgo~. rew_length~. 
    intuit. rew_list in *. split~. subst. constructors*.
  xapp. rew_list in HR. fapplys HR; eauto. math. ximpl_nointros.
   xgo. intuit P_x1. applys_to P_x0 nle_to_sle. rew_length.
     split~. subst. constructors*.
Qed.

Hint Extern 1 (RegisterSpec mrg) => Provide mrg_spec.

Lemma empty_spec : rep empty \{}.
Proof. apply empty_cf. xret~. Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma add_spec : RepTotal add (X;t) (E;sortable) >>
  \{X} \u E ;- sortable.
Proof.
  xcf. introv RepX RepE. xmatch.
  xfun_induction_nointro
    (fun f => Spec f s ss n |R>>
       forall p E Es, inv n p ss Es -> seg s E -> length s = p :> int -> 
       R (fun ss' => inv (n+1) p ss' (E \u Es)))
    (fun (_:list t) (segs:list (list t)) (_:int) => length segs).
   clear x X RepE RepX H E size segs.
   intros s ss n IH. introv Rss Rs Ls. inverts Rss; rew_parity; eauto; xif.
     xgo. apply* inv_odd.
     xgo. apply* inv_odd.
     xapp~. xapp*. xapp*. xclean. subst.
      destruct P_x3 as [S3 L3]. xapp*. rew_length~. math. 
     ximpl as ss' M. applys~ inv_even. equates* 1. math.
  simpl in RepE. xapp~.
  constructors*. constructors*. ximpl_nointros.
  simpls. xret. equates* 1 3.
Qed.

Hint Extern 1 (RegisterSpec add) => Provide add_spec.

Lemma sort_spec : RepTotal sort (E;sortable) >>
  ((fun L => sorted L E) ;; list t).
Proof.
  xcf. introv RepE. xmatch. unfold id in *.
  xfun_induction_nointro (fun f => Spec f s ss |R>>
     forall n p E Es, inv n p ss Es -> seg s E -> 
       R (fun l => seg l (E \u Es)))
    (fun (_:list t) (segs:list (list t)) => length segs).
   clear E size segs RepE H. intros s ss IH. introv Rss Rs.
   xmatch. xgo. rewrite (inv_nil_inv Rss). equates* 1.
   lets (n'&p'&ss'&E'&Es'&Rss'&RE): (inv_cons_inv Rss).
   subst Es. xgo*. rew_length~. ximpl as l Hl. equates* 1.
  simpl in RepE. xapp*. constructors*.
  ximpl. apply seg_to_sorted. equates* 1.
Qed.

Hint Extern 1 (RegisterSpec sort) => Provide sort_spec.

End BottomUpMergeSortSpec.

