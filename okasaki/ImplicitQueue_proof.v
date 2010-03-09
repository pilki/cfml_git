Set Implicit Arguments.
Require Import FuncTactics LibCore.
Require Import QueueSig_ml QueueSig_proof.
Require Import ImplicitQueue_ml.


Instance prod_rep : forall `{Rep a1 A1} `{Rep a2 A2},
   Rep (a1 * a2) (A1 * A2) := 
  fun p P => match p,P with (x,y),(X,Y) => rep x X /\ rep y Y end.



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

Fixpoint splitin A (Q:list (A*A)) : list A :=
  match Q with
  | nil => nil
  | (x,y)::Q' => x::y::(splitin Q')
  end.

Inductive inv : forall `{Rep a A}, queue a -> list A -> Prop :=
  | inv_shallow : forall `{Rep a A} d Q,
     (match d with Two _ _ => False | _ => True end) ->
     invd d Q ->
     inv _ (Shallow d) Q
  | inv_deep : forall `{Rep a A} df qm dr Qf Qr Qm Q,
     invd df Qf ->
     invd dr Qr ->
     inv _ qm Qm ->
     (match df with Zero => False | _ => True end) ->
     (match dr with Two _ _ => False | _ => True end) ->
     Q =' Qf ++ splitin Qm ++ Qr ->
     inv _ (Deep df qm dr) Q.
     
Global Instance queue_rep `{Rep a A} : Rep (queue a) (list A) := 
  inv H.

(* todo: si on met queue a_, on n'a pas d'erreur de bound name *)
(*todo: xisspec loop if evars are in the goal *)

(** automation *)

Hint Constructors Forall2.
Hint Resolve Forall2_last.
Hint Unfold is_head is_tail.

Hint Extern 1 (@rep (queue _) _ _ _ _) => simpl.
Hint Extern 1 (@rep (queues _) _ _ _ _) => simpl.


Ltac auto_tilde ::= try solve [ eauto ].
Ltac auto_star ::= try solve [ rew_list in *; intuition (eauto) ].


(** useful facts *)

(** verification *)

Definition spec_hyp_2 (A1 A2 B : Type)
  (P:A1->A2->Prop) (K:A1->A2->~~B->Prop) f :=
  spec_2 (fun x1 x2 R => P x1 x2 -> K x1 x2 R) f.

(*
Lemma spec_hyp_size : forall (A1 A2 : Type) (mu:A1->A2->nat) (B : Type)
  (P:A1->A2->Prop) (K:A1->A2->~~B->Prop) f,
  is_spec
  (forall n, spec_hyp_2 (fun x1 x2 => n = mu x1 x2) K f) ->
  spec_2 K f.
*)

Ltac xintros_core cont1 cont2 cont3 ::=
   let arity := spec_goal_arity tt in
   let lemma := get_spec_intro_x arity in
   apply lemma; [ instantiate; cont1 tt | instantiate; cont2 tt | instantiate; cont3 tt ]. 

Ltac xcurried_core ::=
  let arity := spec_goal_arity tt in
  let lemma := get_curried_prove_x arity in
  eapply lemma; try solve [ xcf; auto; instantiate; try xisspec ].

Lemma good_induct : forall (P : (nat->Prop) -> Prop),
  (forall n, (forall m, n > m -> P (eq m)) -> P (gt n)) ->
  (forall n, P (gt n) -> P (eq n)) ->
  (forall n, P (eq n)).
Proof. intros. induction n using peano_induction. auto. Qed. 

Ltac name_around e x :=
  pattern e; match goal with |- ?P _ => sets x: P end.

Ltac xcf_for_core f ::=
 ltac_database_get database_cf f;
  let H := fresh "TEMP" in intros H; 
  match type of H with
  | tag tag_topfun _ _ => sapply H; [ instantiate; try xisspec | ]
  | _ => sapply H
  end; clear H; xcf_post tt.

Ltac inverts_tactic H i1 i2 i3 i4 i5 i6 ::=
  let rec go i1 i2 i3 i4 i5 i6 :=
    match goal with 
    | |- (ltac_Mark -> _) => intros _
    | |- (?x = ?y -> _) => let H := fresh in intro H; 
                           first [ subst x | subst y ]; 
                           go i1 i2 i3 i4 i5 i6
    | |- (existT ?P ?p ?x = existT ?P ?p ?y -> _) =>
         let H := fresh in intro H; 
         generalize (@inj_pair2 _ P p x y H);
         clear H; go i1 i2 i3 i4 i5 i6
    | |- (?P -> ?Q) => i1; go i2 i3 i4 i5 i6 ltac:(intro)
    | |- (forall _, _) => intro; go i1 i2 i3 i4 i5 i6
    end in
  generalize ltac_mark; invert keep H; go i1 i2 i3 i4 i5 i6;
  unfold eq' in *.

Hint Constructors invd inv.

Lemma empty_inv : forall `{Rep a A},
  inv _ empty nil.
Admitted.
Hint Extern 1 (inv _ empty _) => apply empty_inv.

Ltac inverts_as_tactic H ::=
  let rec go tt :=
    match goal with 
    | |- (ltac_Mark -> _) => intros _
    | |- (?x = ?y -> _) => let H := fresh "TEMP" in intro H; 
                           first [ subst x | subst y ]; 
                           go tt
    | |- (existT ?P ?p ?x = existT ?P ?p ?y -> _) =>
         let H := fresh in intro H; 
         generalize (@inj_pair2 _ P p x y H);
         clear H; go tt
    | |- (forall _, _) => 
       intro; let H := get_last_hyp tt in mark_to_generalize H; go tt
    end in
  pose ltac_mark; inversion H; 
  generalize ltac_mark; gen_until_mark; 
  go tt; gen_to_generalize; unfolds ltac_to_generalize;
  unfold eq' in *.

Hint Extern 1 (@rep (prod _ _) _ _ _ _) => simpl.

Lemma splitin_last : forall A Q (x y:A),
  splitin (Q & (x,y)) = splitin Q ++ x::y::nil.
Proof.
  intros. induction Q as [|[a b]]. auto.
  rew_list. simpl. rew_list. fequals.
Qed.


Lemma snoc_spec : forall `{Rep a A},
  RepTotal snoc (Q;queue a) (X;a) >> (Q & X) ; queue a.
Proof.
  intros. xintros. intros. sets_eq n: (length Q).
  gen x1 x2 Q X. gen H. gen a A. apply~ good_induct; clears n.
  introv IH. intros ? ? ? q y Q RQ N Y RY. subst_hyp N.
  xcf_app; auto. xisspec. (* todo: automate xisspec *)
  xmatch. 
  xgo. inverts RQ as _ M. inverts M. rew_list~.
  xgo. inverts RQ as _ M. inverts M. rew_list~.
  xgo. inverts RQ as. introv Df Vf Rm _ Dr EQ.
   inverts Dr. subst Q. rew_list~.
  inverts RQ as. introv Df Vf Rm _ Dr EQ. 
   inverts Dr as RX. xlet. (* todo; xapp_args *)
    applys~ (>>> IH ((a*a)%type) (x,y) (X,Y)). skip.
   xgo. hnf in P_x0. subst Q. constructors~.
     rew_list. rewrite~ splitin_last.
  xgo. inverts RQ. 
    destruct d. applys~ C. applys~ C0. auto.
    destruct dr. applys~ C1. applys~ C2. auto.
Qed.

Hint Extern 1 (RegisterSpec snoc) => Provide snoc_spec.






Section Polymorphic.
Variables (a_ A : Type) (RA:Rep a_ A).

Lemma empty_spec : 
  rep (@empty a_) (@nil A).
Proof.
  generalizes RA A. apply (empty_cf a_). xgo.
  intros. simpl. rew_list*. (*todo: rew_list~*)
Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma is_empty_spec : 
  RepTotal is_empty (Q;queue a_) >> bool_of (Q = nil).
Proof.
  xcf. intros (f0,r0) l [H M]. xgo.
  rewrite~ M in H. inverts~ H.
  intro_subst_hyp. inverts H as K.
   destruct (nil_eq_app_rev_inv K). false.
Qed.

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.

Lemma checkf_spec : 
  Spec checkf (q:queue a_) |R>>
    forall Q, (let (f,r) := q in Forall2 rep (f ++ rev r) Q) ->
    R (Q ; queue a_).
Proof.
  xcf. intros (f,r) l K. xgo; rew_list in K.
  auto~. split; auto_false.
Qed.

Hint Extern 1 (RegisterSpec checkf) => Provide checkf_spec.

Lemma snoc_spec : 
  RepTotal snoc (Q;queue a_) (X;a_) >> (Q & X) ; queue a_.
Proof.
  xcf. intros [f r] x. introv [H M] RX. xgo~.
  rew_list. rewrite~ <- app_assoc.
Qed.

Hint Extern 1 (RegisterSpec snoc) => Provide snoc_spec.

Lemma head_spec : 
  RepSpec head (Q;queue a_) |R>>
     Q <> (@nil A) -> R (is_head Q ;; a_).
Proof.
  xcf. intros [f r] q. introv [H M] NE. xgo; rew_list in H.
  rewrite~ M in H. inverts~ H.
  inverts~ H.
Qed.

Hint Extern 1 (RegisterSpec head) => Provide head_spec.

Lemma tail_spec :
  RepSpec tail (Q;queue a_) |R>> 
     Q <> nil -> R (is_tail Q ;; queue a_).
Proof.
  xcf. intros [f r] q. introv [H M] NE. xmatch.
  xgo. rewrite~ M in H. inverts~ H.
  inverts H. xgo~.
  (*todo: use ximpl for ( ; ) ==> ( ;; ) *)
Qed.

Hint Extern 1 (RegisterSpec tail) => Provide tail_spec.

End Polymorphic.

End ImplicitQueueSpec.