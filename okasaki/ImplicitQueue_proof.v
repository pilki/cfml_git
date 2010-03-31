Set Implicit Arguments.
Require Import FuncTactics LibCore.
Require Import QueueSig_ml QueueSig_proof.
Require Import ImplicitQueue_ml.

Module ImplicitQueueSpec <: QueueSigSpec.

(** instantiations *)

Module Import Q <: MLQueue := MLImplicitQueue.
Import MLImplicitQueue.

(** invariant *)

Inductive invd `{Rep a A} : digit a -> list A -> Prop :=
  | invd_zero : 
     invd Zero nil
  | invd_one : forall x X,
     rep x X -> invd (One x) (X::nil)
  | invd_two : forall x X y Y,
     rep x X -> rep y Y -> invd (Two x y) (X::Y::nil).

(** model *)

Global Instance digit_rep `{Rep a A} : Rep (digit a) (list A).
Proof. 
  intros. apply (Build_Rep invd).
  destruct x; introv KX KY; inverts KX; inverts KY; prove_rep.
Defined.

(** invariant *)

Fixpoint splitin A (Q:list (A*A)) : list A :=
  match Q with
  | nil => nil
  | (x,y)::Q' => x::y::(splitin Q')
  end.

Inductive inv : forall `{Rep a A}, queue a -> list A -> Prop :=
  | inv_shallow : forall `{Rep a A} d Q,
     (match d with Two _ _ => False | _ => True end) ->
     rep d Q ->
     inv _ (Shallow d) Q
  | inv_deep : forall `{Rep a A} df qm dr Qf Qr Qm Q,
     rep df Qf ->
     rep dr Qr ->
     inv _ qm Qm ->
     (match df with Zero => False | _ => True end) ->
     (match dr with Two _ _ => False | _ => True end) ->
     Q =' Qf ++ splitin Qm ++ Qr ->
     inv _ (Deep df qm dr) Q.

(** model *)

Implicit Arguments inv [[a] [A] [H]].

Global Instance queue_rep `{Rep a A} : Rep (queue a) (list A).
Proof. 
  intros. apply (Build_Rep inv).
  introv KX. induction KX; introv KY; inverts KY; subst; prove_rep.
Defined.

(** automation *)

Hint Constructors invd inv Forall2.
Hint Resolve Forall2_last.
Ltac auto_tilde ::= eauto.
Hint Extern 1 (@gt nat _ _ _) => simpl; math.

(** useful facts *)

Fixpoint depth a (q:queue a) : nat :=
  match q with
  | Shallow _ => 0%nat
  | Deep _ m _ => (1 + depth m)%nat
  end.

Lemma to_empty : forall `{Rep a A} Q,
  rep (Shallow Zero) Q -> Q = nil.
Proof. introv RQ. inverts RQ as _ M. inverts~ M. Qed.

Lemma from_empty : forall `{Rep a A} q,
  rep q nil -> q = Shallow Zero.
Proof.
  introv RQ. inverts RQ as.
  introv _ ID. inverts~ ID.
  introv ? ? Df ? ? ?. inverts Df; false.
Qed.

Lemma splitin_last : forall A Q (x y:A),
  splitin (Q & (x,y)) = splitin Q ++ x::y::nil.
Proof.
  intros. induction Q as [|[a b]]. auto.
  rew_list. simpl. rew_list. fequals.
Qed.

(** verification *)

Lemma empty_spec : forall `{Rep a A},
  rep (@empty a) (@nil A).
Proof. 
  intros. gen A H. apply (empty_cf a). xgo~.
Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma empty_inv : forall `{Rep a A},
  inv empty nil.
Proof. intros. apply empty_spec. Qed.

Hint Extern 1 (inv empty _) => apply empty_inv.

Lemma is_empty_spec : forall `{Rep a A},
  RepTotal is_empty (Q;queue a) >> bool_of (Q = nil).
Proof.
  xcf. introv RQ. xgo.
  apply~ to_empty.
  intro_subst_hyp. applys C. apply~ from_empty.
Qed.

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Lemma snoc_spec : forall `{Rep a A},
  RepTotal snoc (Q;queue a) (X;a) >> (Q & X) ;- queue a.
Proof.
  intros. xintros. intros q y Q Y RQ RY.
  sets_eq n: (depth q). gen a A H y q Q Y EQn.
  apply~ eq_gt_induction; clears n.
  introv IH. intros. subst n. xcf_app. xmatch. 
  xgo. inverts RQ as _ M. inverts M. rew_list~.
  xgo. inverts RQ as _ M. inverts M. rew_list~. eauto 7.
  xgo. inverts RQ as. introv Df Vf Rm _ Dr EQ.
   inverts Dr. subst Q. rew_list~. eauto 7.
  inverts RQ as. introv Df Vf Rm _ Dr EQ. 
   inverts Dr as RX. xlet.
    applys~ (>>> IH ((a*a)%type) (x,y) (X,Y)). 
   xgo. hnf in P_x0. subst Q. constructors~.
     rew_list. rewrite~ splitin_last.
  xgo. inverts RQ. 
    destruct d. applys~ C. applys~ C0. auto.
    destruct dr. applys~ C1. applys~ C2. auto.
Qed.

Hint Extern 1 (RegisterSpec snoc) => Provide snoc_spec.

Lemma head_spec : forall `{Rep a A},
  RepSpec head (Q;queue a) |R>>
     Q <> nil -> R (is_head Q ;; a).
Proof.
  xcf. intros q Q RQ NE. xgo. 
  apply NE. apply~ to_empty.
  inverts RQ as _ M. inverts~ M.
  inverts RQ as M. inverts M. subst Q. rew_list~.
  inverts RQ as M. inverts M. subst Q. rew_list~.
  inverts RQ. 
    destruct d. applys~ C. applys~ C0. auto.
    destruct df. auto. applys~ C1. applys~ C2.
Qed.

Hint Extern 1 (RegisterSpec head) => Provide head_spec.

Lemma tail_spec : forall `{Rep a A},
  RepSpec tail (Q;queue a) |R>> 
     Q <> nil -> R (is_tail Q ;; queue a).
Proof.
  intros. xintros. intros q Q RQ NE.
  sets_eq n: (depth q). gen a A H q Q EQn.
  apply~ eq_gt_induction; clears n.
  introv IH. intros. subst n. xcf_app. xmatch. 
  xgo. apply NE. apply~ to_empty.
  xgo. inverts RQ as _ M. inverts M. exists~ (@nil A). 
  xgo. inverts RQ as M. inverts M. subst Q. rew_list. eauto 10.
  inverts RQ as Df ? ? ? ? EQ. inverts Df. 
   rew_list in EQ.
    xapp_spec~ (@is_empty_spec (a*a)%type _ _).
   xif. xgo. subst. simpl. rew_list. eauto 7.
   xapp_spec~ (@head_spec (a*a)%type _ _).
   xcleanpat. xmatch. clear H0.
   xlet. applys~ (>>> IH ((a*a)%type) Qm). 
     subst Q. clear IH.
   destruct P_x2 as ([Y Z]&[RY RZ]&[Zm EQm]).
   destruct P_x3 as (Qm'&RQm'&[Tm' EQm']).
   subst Qm. inverts EQm'. xgo. eauto 10.
   xgo. inverts RQ. 
     destruct d. applys~ C. applys~ C0. auto.
     destruct df. auto. applys~ C2. applys~ C1.
Qed.

Hint Extern 1 (RegisterSpec tail) => Provide tail_spec.

End ImplicitQueueSpec.