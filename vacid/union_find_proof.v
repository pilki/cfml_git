Set Implicit Arguments.
Require Import CFLib LibMap LibRelation union_find_ml.
Require Import LibSet.


(** LibRelation *)

Module Import Rel := LibRelation.

Record per A (R:binary A) :=
 { per_sym : sym R;
   per_trans : trans R }. 

Definition per_dom A (R:binary A) :=
  \set{ x | R x x}.

Lemma rel_eq_elim : forall A (R1 R2 : binary A), 
  R1 = R2 -> (forall x y, R1 x y <-> R2 x y).
Proof. intros. subst*. Qed.


(* todo: bug forwards: need to unfold if more arguments come *)


(*Lemma in_set : forall A (P:A->Prop) x,
  x \in set_st P = P x.*)

(** LibTactics *)

Tactic Notation "applys_to" hyp(H1) "," hyp(H2) constr(E) :=
  applys_to H1 E; applys_to H2 E.  
Tactic Notation "asserts" "*" ":" constr(E) :=
  let H := fresh "H" in asserts* H: E.

Tactic Notation "set_eq" :=
  let H := fresh "TEMP" in 
  apply set_ext; iff H; set_in H; in_union_get.
Tactic Notation "set_eq" "*" :=
  set_eq; auto*.


(** CFTactics *)


Instance content_inhab : Inhab content.
Proof. typeclass. Qed.
Hint Resolve content_inhab.


(** CFPrim *)

Notation "x \indom' E" := (@is_in _ (set _) _ x (@dom _ (set loc) _ E)) 
  (at level 39) : container_scope.
Notation "x \notindom' E" := (x \notin ((dom E) : set _)) 
  (at level 39) : container_scope.


Axiom ml_ref_spec_group : forall a,
  Spec ml_ref (v:a) |R>> forall (M:map loc a),
    R (Group (Ref Id) M) (fun l => Group (Ref Id) (M\(l:=v)) \* [l\notindom' M]).

Axiom ml_get_spec_group : forall a,
  Spec ml_get (l:loc) |R>> forall (M:map loc a),   
    Inhab a -> l \indom M ->
    keep R (Group (Ref Id) M) (\= M\(l)).

Axiom ml_set_spec_group : forall a, 
  Spec ml_set (l:loc) (v:a) |R>> forall (M:map loc a), 
    Inhab a -> l \indom M ->
    R (Group (Ref Id) M) (# Group (Ref Id) (M\(l:=v))).




(* todo: bug de congruence *)



(****************************************************)
(** Reflexive-symmetric-transitive closure *) 

(** Recall that [binary A] is the type of binary 
    relations over A, defined as [A->A->Prop]. *)

Inductive stclosure (A:Type) (R:binary A) : binary A :=
  | stclosure_step : forall x y,
      R x y -> stclosure R x y
  | stclosure_sym : forall x y, 
      stclosure R x y -> stclosure R y x
  | stclosure_trans : forall y x z,
      stclosure R x y -> stclosure R y z -> stclosure R x z.

Hint Resolve stclosure_step stclosure_sym stclosure_trans.

Lemma stclosure_le : forall A (R1 R2 : binary A),
  rel_le R1 R2 -> rel_le (stclosure R1) (stclosure R2).
Proof. unfolds rel_le, pred_le. introv Le H. induction* H. Qed.

Definition single A (a b:A) :=
  fun x y => x = a /\ y = b.

(** Extension of an per [B] with a node [z] *)

Definition add_node A (B:binary A) (z:A) :=
  Rel.union B (single z z).

(** Extension of an per [B] with an edge between [x] and [y] *)

Definition add_edge A (B:binary A) (x y:A) :=
  stclosure (Rel.union B (single x y)).

Lemma add_edge_le : forall A (B:binary A) a b,
  rel_le B (add_edge B a b).
Proof. introv. intros x y H. apply stclosure_step. left~. Qed.

Lemma add_edge_already : forall A (B:binary A) a b,
  per B -> B a b -> add_edge B a b = B.
Proof.
  introv P H. extens. intros x y. iff M.
  induction M.
    destruct H0. auto. destruct H0. subst~.
    apply* per_sym.
    apply* per_trans.
  hnf in M.
  apply~ add_edge_le.
Qed.

Lemma per_add_edge : forall A (R : binary A) a b,
  per R -> per (add_edge R a b).
Proof.
  introv [Rs Rt]. unfold add_edge. constructor.
  introv H. induction* H.
  introv H1. gen z. induction* H1. 
Qed.

Lemma per_dom_add_edge : forall A (B:binary A) x y,
   per_dom (add_edge B x y) = per_dom B \u \{x} \u \{y}.
Proof.
(*
  intros. unfold per_dom. apply set_ext. intros y.
  rewrite in_set. iff H.*) skip.
Qed.

Lemma per_dom_add_node : forall A (B:binary A) x,
   per_dom (add_edge B x x) = per_dom B \u \{x}.
Proof.
(*
  intros. unfold per_dom. apply set_ext. intros y.
  rewrite in_set. iff H.*) skip.
Qed.


(****************************************************)
(** Invariant of union-find *)

Implicit Type M : map loc content.
   
(** [is_repr M x r] asserts that [r] is the end of the
    path that starts from [x]. *)

Inductive is_repr M : binary loc := 
  | is_repr_root : forall x, 
      binds M x Root -> is_repr M x x
  | is_repr_step : forall x y r,
      binds M x (Node y) -> is_repr M y r -> is_repr M x r.
 
(** [is_forest M] captures the fact that every node 
    points to some root. *)

Definition is_forest M :=
  forall x, x \indom M -> exists r, is_repr M x r.

(** [is_equiv M x y] captures the fact that [x] and [y]
    point to a same root. *)

Definition is_equiv M x y :=
  exists r, is_repr M x r /\ is_repr M y r. 

(** [UF B] is a heap predicate that corresponds to a set of 
    cells describing the union-find structure associated with
    the PER [R], which is a binary relation over locations. *)

Definition UF (B:binary loc) : hprop :=
  Hexists (M:map loc content), Group (Ref Id) M \*
    [ per B /\
      is_forest M /\
      dom M = per_dom B /\
      is_equiv M = B ].


(****************************************************)
(** Automation *)

Hint Constructors is_repr.
Hint Unfold is_equiv.

Tactic Notation "rew_map" "~" := 
  rew_map; auto_tilde.

Hint Resolve binds_index.
Hint Resolve binds_update_neq'.

Hint Resolve binds_update_neq binds_update_eq.

Ltac auto_star ::= jauto.


(****************************************************)
(** Lemmas *)

(** Properties of [is_repr] *)

Lemma is_repr_inj : forall r1 r2 M x,
  is_repr M x r1 -> is_repr M x r2 -> r1 = r2.
Proof.
  introv H. gen r2. induction H; introv H'; inverts H'; auto_false.
  forwards~ E: binds_inj H1 H. inverts~ E.
Qed.

Implicit Arguments is_repr_inj [ ].

Lemma is_equiv_iff_same_repr : forall M x y rx ry,
  is_repr M x rx -> is_repr M y ry ->
  ((rx = ry) = is_equiv M x y).
Proof. 
  introv Rx Ry. iff H (r&Rx'&Ry'). subst*.
  applys (eq_trans r); applys is_repr_inj; eauto.
Qed.

Lemma is_equiv_refl : forall M x, 
  x \indom M -> is_forest M -> is_equiv M x x.
Proof. introv D H. forwards* [r R]: (H x). Qed. 

Lemma is_equiv_sym : forall M,
  sym (is_equiv M).
Proof. intros M x y (r&Hx&Hy). eauto. Qed.

Lemma is_equiv_trans : forall M,
  trans (is_equiv M).
Proof.
  intros M y x z (r1&Hx&Hy) (r2&Hy'&Hz).
  forwards: is_repr_inj r1 r2; eauto. subst*.
Qed.

Lemma is_repr_in_dom_l : forall M x r, 
  is_repr M x r -> x \indom M.
Proof. introv H. inverts H; apply* binds_dom. Qed. 

Lemma is_repr_in_dom_r : forall M x r, 
  is_repr M x r -> r \indom M.
Proof. introv H. induction H. apply* binds_dom. auto. Qed. 

Lemma is_repr_binds_root : forall M x r, 
  is_repr M x r -> binds M r Root.
Proof. introv H. induction~ H. Qed.

Lemma is_repr_equiv_root : forall M x r,
  is_repr M x r -> is_equiv M x r.
Proof. introv H. exists* r. Qed.

Hint Resolve is_repr_binds_root is_repr_equiv_root.
Hint Resolve is_repr_in_dom_l is_repr_in_dom_r.

(** General lemmas *)

Lemma is_repr_add_node : forall M r c x y,
  r \notin (dom M:set _) -> is_repr M x y -> is_repr (M\(r:=c)) x y.
Proof. introv N H. induction H; constructors*. Qed. 

Lemma binds_diff_false : forall x y M,
  binds M x Root -> binds M x (Node y) -> False.
Proof. introv H1 H2. forwards~: binds_inj H1 H2. false. Qed.


Lemma node_not_root : forall r x M y,
  binds M r Root -> binds M x (Node y) -> x <> r.
Proof. introv H1 H2. intro_subst. applys* binds_diff_false. Qed.

Lemma points_indom : forall x M y,
  is_forest M -> binds M x (Node y) -> y \indom M.
Proof.
  introv FM Bx. forwards  [r Hr]: FM x. applys* binds_dom. inverts Hr.
    false* binds_diff_false.
    forwards* E: binds_inj Bx H. inverts E. inverts* H0.
Qed.

Hint Resolve node_not_root points_indom.
 
(** Lemmas for 'create' function *)

Lemma is_forest_add_node : forall M r,
  is_forest M -> r \notindom' M -> is_forest (M\(r:=Root)).
Proof.
  introv FM Dr. intros x Dx. destruct (map_indom_update_inv Dx).
    subst*.
    forwards* [y Ry]: FM x. exists y. apply* is_repr_add_node.
Qed.

Hint Resolve binds_update_neq_inv.

Lemma inv_add_node : forall M B z,
  is_forest M ->
  dom M = per_dom B ->
  is_equiv M = B ->
  z \notindom' M -> 
  is_equiv (M\(z:=Root)) = add_node B z.
Proof.
  introv FM DM EM Mz. extens. intros x y. split.
  (* -- case [is_equiv M' -> B'] *)
  intros (r&Rx&Ry). tests (r = z).
  (* -- subcase [r = z] *)
  cuts St: (forall x, is_repr (M\(z:=Root)) x z -> x = z).
    rewrite~ (St x). rewrite~ (St y). right. unfolds~.
  clears x y. introv H. gen_eq r: z. gen_eq M': (M\(r:=Root)).
  induction~ H; intro_subst; intro_subst.
  forwards~: IHis_repr. subst y. false. tests (x = z).
    applys* (>> binds_diff_false H).
    forwards*: points_indom x.
  (* -- subcase [r <> z] *)
  cuts St: (forall x, is_repr (M\(z:=Root)) x r -> is_repr M x r).
    left. rewrite <- EM. exists* r.
  clears x y. introv H. induction H. applys* is_repr_root. eauto 7.
  (* -- case [B' -> is_equiv M'] *)
  intros [H|[Ex Ey]].
  (* -- subcase [B x y] *)
  rewrite <- EM in H. destruct H as (r&Rx&Ry).
  cuts St: (forall x, is_repr M x r -> is_repr (M\(z:=Root)) x r).
    exists* r.
  clears x y. introv H. induction H. eauto.
  cuts*: (x <> z). intro_subst. lets~: binds_dom H.
  (* -- subcase [x = y = z] *)
  subst x y. exists* z.
Admitted. (*faster*)

Axiom inv_add_node' : forall M B z,
  is_forest M ->
  dom M = per_dom B ->
  is_equiv M = B ->
  z \notindom' M -> 
  is_equiv (M\(z:=Root)) = add_edge B z z.


(** Lemmas for 'union' function *)

Lemma is_forest_add_edge : forall M rx ry,
  is_forest M -> binds M rx Root -> binds M ry Root -> rx <> ry ->
  is_forest (M\(rx:=Node ry)).
Proof.
  introv FM Bx By Neq. intros x D. rewrite* dom_update_in in D.
  forwards~ [r R]: FM x. tests (r = rx) as C.
  exists ry. induction R.
    eauto.
    cuts*: (x <> r). intro_subst. congruence.
  exists r. gen C. induction R; intros.
    eauto.
    cuts*: (x<>rx). congruence.
Qed.

Section InvAdd.
Hint Resolve per_trans per_sym.

Lemma inv_add_edge : forall M B a ra b rb,
  per B -> ra <> rb -> ra \indom M -> rb \indom M ->
  is_forest M -> dom M = per_dom B -> is_equiv M = B ->
  is_repr M a ra -> is_repr M b rb ->
  is_equiv (M\(ra:=Node rb)) = add_edge B a b.
Proof.
  introv PB Neq Da Db FM DM EM Ra Rb. extens. intros x y. split.
  (* -- case [is_equiv M' -> B'] *)
  intros (r&Rx&Ry). tests (r = rb) as C.
  (* -- subcase [r = rb] *)
  sets B': (add_edge B a b). asserts PB': (per B'). unfold B'. apply~ per_add_edge.
  cuts St: (forall x, is_repr (M\(ra:=Node rb)) x rb -> B' x rb). applys~ trans_sym_2.
  clears x y. introv H. gen_eq r:rb. gen Rb. induction H; intros.
    subst x. applys stclosure_step. left. cuts~: (rb \in per_dom B).
     rewrite <- DM. applys~ (map_indom_update_already_inv (binds_dom H)).
    subst r0 r1. tests (x = ra) as C'.
      applys~ trans_sym_1 a; [ | applys~ trans_elim b  ].
        applys add_edge_le. rewrite* <- EM.
        applys stclosure_step. right. unfolds~.
        applys add_edge_le. rewrite* <- EM.
      applys~ trans_elim y. applys add_edge_le. rewrite <- EM.
       forwards: binds_update_neq_inv x; eauto 3.
       forwards [ry Hry]: FM y __; eauto 3. exists* ry.
  (* -- case [r <> rb] *)
  cuts St: (forall x, is_repr (M\(ra:=Node rb)) x r -> is_repr M x r).
    applys add_edge_le. rewrite <- EM. exists* r.
  clears x y. introv H. induction H; cuts*: (x <> ra). 
    intro_subst. lets N: (binds_get H). rew_map in N. inverts N.
    intro_subst. lets N: (binds_get H). rew_map in N. inverts N.
     renames y to rb. applys C. applys* is_repr_inj. 
  (* -- case [B' -> is_equiv M'] *)
  asserts [Sa Sr]: 
     ((forall x, is_repr M x ra -> is_repr (M\(ra:=Node rb)) x rb) /\
      (forall x r, r <> ra -> is_repr M x r -> is_repr (M\(ra:=Node rb)) x r)).
    clears x y. split. 
      introv H. induction H; eauto 7. 
      introv Nq H. induction H; eauto 7. 
  intros H. induction H.
  destruct H as [?|[? ?]].
    rewrite <- EM in H. destruct H as (r&Rx&Ry). tests (r = ra); eauto 7.
    subst x y. exists* rb.
  applys* is_equiv_sym.
  applys* is_equiv_trans.
Admitted.

End InvAdd.

(****************************************************)
(** Verification *)

(*--------------------------------------------------*)
(** Function [repr] *)

Lemma repr_spec :
  Spec repr x |R>> forall M,
    is_forest M -> x \indom M ->
    keep R (Group (Ref Id) M) (\[is_repr M x]).
Proof.
  xintros. intros x M FM D. forwards~ [r Hr]: FM x. induction Hr.
  (* case root *)
  xcf_app. xlet. xapp_spec~ ml_get_spec_group. xextracts. (*todo:xapps_spec*)
  rewrite (binds_get H). xgos*. 
  (* case node *)
  xcf_app. xlet. xapp_spec~ ml_get_spec_group. xextracts. (*todo:xapps_spec*) 
  rewrite (binds_get H). xmatch. 
  forwards K: IHHr. apply* is_repr_in_dom_l. xapplys* K.
Admitted.

Hint Extern 1 (RegisterSpec repr) => Provide repr_spec.


(*--------------------------------------------------*)
(** Function [create] *)

Lemma create_spec :
  Spec create () |R>> forall B,
    R (UF B) (fun r => [r \notin (per_dom B)] \* UF (add_edge B r r)).
Proof.
  xcf. intros. unfold UF. xextract as M (PM&FM&DM&EM).
  xapp_spec ml_ref_spec_group.
  intros r. hextract as Neq. hsimpl. splits.
    apply~ per_add_edge.
    apply~ is_forest_add_node.
    rewrite~ dom_update_notin. rewrite per_dom_add_node. fequals.
    applys~ inv_add_node'.
    rewrite~ <- DM.
Admitted.

Hint Extern 1 (RegisterSpec create) => Provide create_spec.


(*--------------------------------------------------*)
(** Function [same] *)

Lemma same_spec :
  Spec same x y |R>> forall B, 
    x \in (per_dom B) -> y \in (per_dom B) ->
    keep R (UF B) (\= istrue (B x y)).
Proof.
  xcf. introv Dx Dy. unfold UF. xextract as M (PM&FM&DM&EM).
  rewrite <- DM in *. clear DM.
  xapp~ as rx. intros Rx. xapp~ as ry. intros Ry.
  xapp. intros b. xsimpl. subst~.
  subst b. rewrite <- EM. fequals. applys~ is_equiv_iff_same_repr.
Admitted.

Hint Extern 1 (RegisterSpec equiv) => Provide same_spec.


(*--------------------------------------------------*)
(** Function [union] *)

Lemma union_spec :
  Spec union_find_ml.union x y |R>> forall B,
    x \in (per_dom B) -> y \in (per_dom B) ->
    R (UF B) (# UF (add_edge B x y)). 
Proof.
  xcf. introv Dx Dy. unfold UF. xextract as M (PM&FM&DM&EM).
  rewrite <- DM in *. 
  xapp~ as rx. intros Rx. xapp~ as ry. intros Ry.
  xapps. xif.
  (* case [rx <> ry] *)
  xapp_spec~ ml_set_spec_group. apply* is_repr_in_dom_r.
  hsimpl. splits.
    applys~ per_add_edge.   
    apply* is_forest_add_edge; apply* is_repr_binds_root.  
    rewrite per_dom_add_edge. rewrite <- DM.
     rewrite~ dom_update_in. set_eq*. forwards*: is_repr_binds_root Rx.
    apply* inv_add_edge.
  (* case [rx = ry] *)
  xrets. splits~. 
    applys~ per_add_edge. 
    rewrite per_dom_add_edge. rewrite <- DM. set_eq*.
    rewrite~ add_edge_already. rewrite* <- EM. 
Admitted.

Hint Extern 1 (RegisterSpec union) => Provide union_spec.




---------------
---------------
---------------

(*
Lemma connected_eq : forall A (G' G:graph A),
  edges G = edges G' -> connected G = connected G'.
Proof. introv H. unfolds. rewrite~ H. Qed.

Implicit Arguments connected_eq [A].
*)

(*
Lemma is_equiv_add_node : forall M r,
  is_forest M -> r \notindom' M ->
  is_equiv (M\(r:=Root)) = is_equiv M.
Proof.
  introv FM D. extens. intros x y.
  tests (x = r); tests (y = r).

 (* todo: wlog *)
  iff H. apply~ is_equiv_refl.
  unfold is_equiv.
*)
Admitted.
(*
Lemma is_equiv_add_node : forall M r x y,
  is_equiv (M\(r:=Root)) x y = (is_equiv M x y \/ (x = r /\ y = r)).
Admitted.
*)

(****************************************************)
(** Graph structure *)

(** A graph has nodes and edges, which are pairs of nodes. *)

Record graph A := graph_of { 
  nodes : set A;
  edges : set (A*A) }.

(** The functions [add_node] and [add_edge] can be used to
    augment a given graph. *)

Definition add_node A (G:graph A) x :=
  graph_of (nodes G \u \{x}) (edges G).

Definition add_edge A (G:graph A) x y :=
  graph_of (nodes G) (edges G \u \{(x,y)}).

(** [connected G x y] indicates that the nodes [x] and [y]
    belong to the same connected component in [G]. 
    A connected component is defined as the reflexive-
    symmetric-transitive closure of the edges. *)

Definition connected A (G:graph A) x y :=
  closure (fun x y => (x,y) \in edges G) x y.

(*-----
Lemma is_repr_added_node : forall M x z,
  z \notindom' M -> is_repr (M\(z:=Root)) x z -> x = z.
Proof.
  introv D Rx. inverts~ Rx.
Qed.



(*
Lemma indom_from_innodes : forall x G M,
  dom M = nodes G -> x \in nodes G -> x \indom' M.
Proof. introv H D. rewrite H. auto. Qed.
Hint Resolve indom_from_innodes.
*)



(*

Inductive closure (A:Type) (R:binary A) : binary A :=
  | closure_step : forall x y,
      R x y -> closure R x y
  | closure_refl : forall x,
      closure R x x
  | closure_sym : forall x y, 
      closure R x y -> closure R y x
  | closure_trans : forall y x z,
      closure R x y -> closure R y z -> closure R x z.


Hint Constructors closure.
Lemma closure_le : forall A (R1 R2 : binary A),
  rel_le R1 R2 -> rel_le (closure R1) (closure R2).
Proof. unfolds rel_le, pred_le. introv Le H. induction* H. Qed.
*)
