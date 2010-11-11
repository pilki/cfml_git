Set Implicit Arguments.
Require Import CFLib LibMap LibRelation union_find_ml.
Require Import LibSet.

Notation "\set{ x | P }" := (@set_st _ (fun x => P))
  (at level 0, x ident, P at level 200).

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


(*Lemma in_set : forall A (P:A->Prop) x,
  x \in set_st P = P x.*)

(** LibTactics *)

Tactic Notation "applys_to" hyp(H1) "," hyp(H2) constr(E) :=
  applys_to H1 E; applys_to H2 E.  

(** CFTactics *)

Ltac xapp_as_base spec args solver x :=
  let cont tt := xapp_inst args solver in
  xlet as x; 
  [ xuntag tag_apply; xapp_core spec cont
  | instantiate; xextract ].

Tactic Notation "xapp" "as" ident(x) :=
  xapp_as_base ___ (>>) ltac:(fun _ => idtac) x.
Tactic Notation "xapp" "~" "as" ident(x) :=
  xapp_as_base ___ (>>) ltac:(fun _ => xauto~) x.
Tactic Notation "xapp" "*" "as" ident(x) :=
  xapp_as_base ___ (>>) ltac:(fun _ => xauto*) x.

Tactic Notation "hextracts" :=
  let E := fresh "TEMP" in hextract as E; subst_hyp E.

Tactic Notation "xgos" :=
  xgo; hsimpl.
Tactic Notation "xgos" "~" :=
  xgos; auto_tilde.
Tactic Notation "xgos" "*" :=
  xgos; auto_star.

Tactic Notation "xapply" constr(H) :=
  xapply_local H. 
Tactic Notation "xapplys" constr(H) :=
  xapply_local H; [ hcancel | hsimpl ].

Tactic Notation "xapplys" "~" constr(H) :=
  xapplys H; auto_tilde.
Tactic Notation "xapplys" "*" constr(H) :=
  xapplys H; auto_star.


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

(** Other *)

Lemma case_classic_l : forall P Q, P \/ Q -> (P \/ (~ P /\ Q)).
Proof. intros. tautoB P Q. Qed.

(** Maps *)



Axiom map_indom_update_inv : forall A `{Inhab B} (m:map A B) (i j:A) (v:B),
  j \indom (m\(i:=v)) -> (j = i \/ j \indom m).
Axiom map_indom_update_already : forall A `{Inhab B} (m:map A B) (i j:A) (v:B),
  j \indom m -> j \indom (m\(i:=v)).

Axiom binds_def : forall A `{Inhab B} (M:map A B) x v,
  binds M x v = (x \indom M /\ M\(x) = v).
Axiom binds_inv : forall A `{Inhab B} (M:map A B) x v,
  binds M x v -> (x \indom M /\ M\(x) = v).
Axiom binds_prove : forall A `{Inhab B} (M:map A B) x v,
  x \indom M -> M\(x) = v -> binds M x v.

Axiom binds_update_neq : forall A i j `{Inhab B} v w (M:map A B),
  j \notindom' M -> binds M i v -> binds (M\(j:=w)) i v.
Axiom binds_update_eq : forall A i `{Inhab B} v (M:map A B),
  binds (M\(i:=v)) i v.

Axiom binds_update_neq_inv : forall A i j `{Inhab B} v w (M:map A B),
  binds (M\(j:=w)) i v -> i <> j -> binds M i v.

Axiom binds_inj : forall A i `{Inhab B} v1 v2 (M:map A B),
  binds M i v1 -> binds M i v2 -> v1 = v2.

(*
Axiom binds_update_rem : forall A i j `{Inhab B} v w (M:map A B),
  j \notindom' M -> binds (M\(j:=w)) i v -> binds M i v.
Hint Resolve binds_update_rem.

Lemma is_repr_rem_node : forall M r c x y,
  r \notin (dom M:set _) -> is_repr (M\(r:=c)) x y -> is_repr M x y.
Proof. introv N H. induction H; constructors*. Qed. 
*)

Axiom binds_get : forall A `{Inhab B} (M:map A B) x v,
  binds M x v -> M\(x) = v.
Axiom binds_dom : forall A `{Inhab B} (M:map A B) x v,
  binds M x v -> x \indom M.

Axiom dom_update_notin : forall A i `{Inhab B} v (M:map A B),
  i \notindom' M -> dom (M\(i:=v)) = dom M \u \{i}.

Axiom binds_index : forall A i `{Inhab B} v (M:map A B),
  binds M i v -> index M i.

Axiom binds_update_neq' : forall A i j `{Inhab B} v w (M:map A B),
  i <> j -> binds M i v -> binds (M\(j:=w)) i v.


Global Opaque binds_inst. 

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
  ((rx = ry) <-> is_equiv M x y).
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

Hint Resolve is_repr_in_dom_l is_repr_in_dom_r is_repr_binds_root.

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
    forwards*: points_indom x. applys* binds_update_neq_inv.
  (* -- subcase [r <> z] *)
  cuts St: (forall x, is_repr (M\(z:=Root)) x r -> is_repr M x r).
    left. rewrite <- EM. exists* r.
  clears x y. introv H. induction H.
    applys is_repr_root. applys* binds_update_neq_inv.
     forwards*: (binds_update_neq_inv H). applys* node_not_root.
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

Lemma inv_add_edge : forall M B a ra b rb,
  per B ->
  is_equiv M = B ->
  is_repr M a ra ->
  is_repr M b rb ->
  is_equiv (M\(ra:=Node rb)) = add_edge B a b.
Proof.
  introv PB EM Ra Rb. extens. intros x y. split.
  (* -- case [is_equiv M' -> B'] *)
  (* -- subcase [r = z] *)
  (* -- case [r <> z] *)
skip.
  (* -- case [B' -> is_equiv M'] *)
  asserts Sa: (forall x, is_repr M x ra -> is_repr (M\(ra:=Node rb)) x rb).
    skip.
  asserts Sr: (forall x r, r <> ra -> is_repr M x r -> is_repr (M\(ra:=Node rb)) x r).
    skip.
  intros H. induction H.
  destruct H as [?|[? ?]].
    rewrite <- EM in H. destruct H as (r&Rx&Ry).
     tests* (r = ra). exists* rb. exists* r.
    subst x y. 
  applys* is_equiv_sym.
  applys* is_equiv_trans.
Qed.


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
  forwards K: IHHr. apply* is_repr_in_dom. xapplys* K.
Admitted.

Hint Extern 1 (RegisterSpec repr) => Provide repr_spec.


(*--------------------------------------------------*)
(** Function [create] *)

Lemma create_spec :
  Spec create () |R>> forall B,
    S (UF B) (fun r => [r \notin (rel_dom B)] \* UF (Rel.union B (single r r))).
Proof.
  xcf. intros. unfold UF. xextract as M (FM&DM&EM).
  xapp_spec ml_ref_spec_group.
  intros r. hextract as Neq. hsimpl. splits.
    apply~ is_forest_add_node.
    rewrite~ dom_update_notin. fequals.
    apply~ inv_add_node.
Admitted.

Hint Extern 1 (RegisterSpec create) => Provide create_spec.


(*--------------------------------------------------*)
(** Function [same] *)

Lemma same_spec :
  Spec same x y |R>> forall B, 
    x \in (rel_dom B) -> y \in (rel_dom B) ->
    keep R (UF B) (\= istrue (B x y)).
Proof.
  xcf. introv Dx Dy. unfold UF. xextract as M (FM&DM&EM).
  rewrite <- DM in *. clear DM.
  xapp~ as rx. intros Rx. xapp~ as ry. intros Ry.
  xapp. intros b. xsimpl; subst~.
  fequal. rewrite <- EM. extens. apply* is_equiv_iff_same_repr.
Admitted.

Hint Extern 1 (RegisterSpec equiv) => Provide equiv_spec.


(*--------------------------------------------------*)
(** Function [union] *)

Lemma union_spec :
  Spec union x y |R>> forall B,
    x \in (rel_dom B) -> y \in (rel_dom B) ->
    R (UF B) (# UF (stclosure (Rel.union B (single x y)))).
Proof.
  xcf. introv Dx Dy. unfold UF. xextract as M (FM&DM&EM).
  rewrite <- DM in *. clear DM.
  xapp~ as rx. intros Rx. xapp~ as ry. intros Ry.
  xapps. xif.
  (* case [rx <> ry] *)
  xapp_spec~ ml_set_spec_group. apply* is_repr_in_dom_r.
  hsimpl. splits.
    apply* is_forest_add_edge; apply* is_repr_binds_root.  
    rewrite~ dom_update_in. forwards*: is_repr_binds_root Rx.
    apply* inv_add_edge.
  (* case [rx = ry] *)
  xrets. splits~. rewrite~ inv_add_no_edge. rewrite* <- EM. 
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
