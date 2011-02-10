Set Implicit Arguments.
Require Import CFLib LibGraph Dijkstra_ml.

(*************************************************************)

(*-----------------------------------------------------------*)

Definition min A (f:A->int) (P:A->Prop) :=  
  epsilon (fun n => (exists x, P x /\ n = f x)
                 /\ (forall x, P x -> n <= f x)).

Lemma min_eq : forall A x (f:A->int) (P:A->Prop),
  P x -> (forall y, P y -> f x <= f y) -> min f P = f x.
Proof.
  intros. unfold min.
  spec_epsilon* as y [(?&?&?) Sy]. clearbody y. subst y.
  forwards*: Sy x. forwards*: H0 x0. apply* le_antisym.
Qed.

Lemma min_exists_nonneg : forall A (f:A->int) (P:A->Prop),
  (exists x, P x) -> 
  value_nonneg f P ->
  exists n, (exists x, P x /\ n = f x)
          /\ (forall x, P x -> n <= f x).
Proof.
(*
  introv [a Pa] Pos. 
  match goal with |- ?G' => set (G := G') end.
  cuts: (forall m:nat, G \/ (forall x, P x -> f x <= m -> False)).
    destruct (H (abs (f a))) as [?|M].
      auto.
      false~ (M a). rewrite~ abs_pos. apply le_refl.
  induction m.
  destruct (classic (exists x, P x /\ f x = 0)) as [(y&Py&Hy)|M].
    left. exists* 0.
    right. intros x Px Non. rew_classic in M. specializes M x.
     rew_classic in M. destruct M as [?|H]. false. apply H. 
      apply~ le_antisym. rewrite le_is_flip_ge. unfold flip. auto.
  destruct IHm as [?|N]. eauto. right. intros x Px Le.
    destruct (classic (exists x, P x /\ f x = m)) as [(y&Py&Hy)|M].
*)
Admitted.

Lemma min_inv : forall A (f:A->int) (P:A->Prop),
  (exists x, P x) -> value_nonneg f P -> 
  exists x, P x /\ min f P = f x /\ (forall y, P y -> f x <= f y).
Proof.
  intros. forwards* (n&(y&Py&Ey)&My): min_exists_nonneg.
  unfold min. spec_epsilon* as z' ((z&Pz&Ez)&Hz). rewrite* Ez in Hz.
Qed.

Lemma min_elim : forall A x (f:A->int) (P:A->Prop),
  value_nonneg f P ->
  P x -> 
  min f P <= f x.
Proof. intros. forwards* (y&Py&Ey&My): min_inv. rewrite~ Ey. Qed.


(*-----------------------------------------------------------*)

Definition mininf A (f:A->int) (P:A->Prop) :=  
  If (exists x, P x) then Finite(min f P) else Infinite.

Lemma mininf_infinite : forall A (f:A->int) (P:A->Prop),
  (forall x, ~ P x) -> mininf f P = Infinite.
Proof.
  intros. unfold mininf. case_if~. destruct e as [x ?]. false*.
Qed.

Lemma mininf_finite : forall A x (f:A->int) (P:A->Prop),
  P x -> (forall y, P y -> f x <= f y) -> mininf f P = Finite (f x).
Proof. 
  intros. unfold mininf. case_if. 
  fequal. apply~ min_eq. 
  rew_classic in n. false*.
Qed.

Lemma mininf_finite_inv : forall A n (f:A->int) (P:A->Prop),
  mininf f P = Finite n -> value_nonneg f P ->
   exists x, P x /\ f x = n /\ (forall y, P y -> n <= f y).
Proof.
  introv E N. unfold mininf in E. case_If. inverts E. 
  forwards* (x&Px&Ex&Mx): min_inv. rewrite* <- Ex in Mx.
Qed.

Lemma mininf_finite_elim : forall A n x (f:A->int) (P:A->Prop),
  mininf f P = Finite n -> value_nonneg f P -> P x -> n <= f x.
Proof.
  unfold mininf. introv H Pos Px. case_if.
  destruct e as [y ?]. invert H as M. apply~ min_elim.
  false.
Qed.

Lemma mininf_infinite_inv: forall A (f:A->int) (P:A->Prop),
  mininf f P = Infinite -> (forall x, ~ P x).
Proof. 
  unfold mininf. introv H Px. case_if.
  false.
  rew_classic in n. false*.
Qed.

Lemma mininf_infinite_elim : forall A x (f:A->int) (P:A->Prop),
  mininf f P = Infinite -> ~ P x.
Proof. intros. apply* mininf_infinite_inv. Qed.

(*-----------------------------------------------------------*)

Definition len_gt l d :=
  match l with Finite d' => d < d' | Infinite => True end.

Lemma mininf_len_gt : forall d A (f:A->int) (P:A->Prop),
  len_gt (mininf f P) d ->
  value_nonneg f P ->
  forall x, P x -> d < f x.
Proof.
  unfold len_gt. introv H NE. sets_eq l:(mininf f P).  (* todo: case_eq*)
  intros. destruct l.
    forwards*: (@mininf_finite_elim A). math.
    forwards*: (@mininf_infinite_elim A) x.
Qed.

Lemma mininf_len_gt_not : forall d A (f:A->int) (P:A->Prop),
  ~ (len_gt (mininf f P) d) ->
  value_nonneg f P ->
  exists d', mininf f P = Finite d' /\ d' <= d.
Proof. 
  unfold len_gt. introv H N. cases (mininf f P); tryfalse~.
  forwards* (x&Px&Ex&Mx): mininf_finite_inv. eauto with maths.
Qed.
Lemma mininf_len_gt_not_elim : forall d A (f:A->int) (P:A->Prop),
  ~ (len_gt (mininf f P) d) ->
  value_nonneg f P ->
  exists x, P x /\ f x <= d.
Proof.
  introv H N. forwards~ (d'&E&L): mininf_len_gt_not H.
  forwards~ (x&Px&Lx&_): mininf_finite_inv E. eauto with maths.
Qed.
