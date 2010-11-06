Set Implicit Arguments.
Require Import CFLib LibSet LibMap union_find_ml.


Instance content_inhab : Inhab content.
Proof. typeclass. Qed.
Hint Resolve content_inhab.

Notation "x \indom' E" := (@is_in _ (set _) _ x (@dom _ (set loc) _ E)) 
  (at level 39) : container_scope.
Notation "x \notindom' E" := (x \notin ((dom E) : set _)) 
  (at level 39) : container_scope.


(****************************************************)
(** Reflexive-symmetric-transitive closure *) 

(** Recall that [binary A] is the type of binary 
    relations over A, defined as [A->A->Prop]. *)

Inductive closure (A:Type) (R:binary A) : binary A :=
  | closure_step : forall x y,
      R x y -> closure R x y
  | closure_refl : forall x,
      closure R x x
  | closure_sym : forall x y, 
      closure R x y -> closure R y x
  | closure_trans : forall y x z,
      closure R x y -> closure R y z -> closure R x z.


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
  x \in (nodes G) /\ y \in (nodes G) /\
  closure (fun x y => (x,y) \in edges G) x y.


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

(** [UF G] is a heap predicate that corresponds to a set of 
    cells describing the union-find structure associated with
    the graph [G], where the nodes of [G] are of type [loc] *)
    
Definition UF (G:graph loc) : hprop :=
  Hexists (M:map loc content), Group (Ref Id) M \*
    [ is_forest M /\ dom M = nodes G /\ is_equiv M = connected G ].


(****************************************************)
(** Automation *)

Hint Constructors is_repr.
Hint Unfold is_equiv.



Tactic Notation "rew_map" "~" := 
  rew_map; auto_tilde.


Axiom map_indom_inv : forall A `{Inhab B} (m:map A B) (i j:A) (v:B),
  j \indom (m\(i:=v)) -> (j = i \/ j \indom m).

Lemma case_classic_l : forall P Q, P \/ Q -> (P \/ (~ P /\ Q)).
Proof. intros. tautoB P Q. Qed.


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

Axiom binds_inj : forall A i `{Inhab B} v1 v2 (M:map A B),
  binds M i v1 -> binds M i v2 -> v1 = v2.


Hint Resolve binds_update_neq binds_update_eq.

Axiom ml_ref_spec_group : forall a,
  Spec ml_ref (v:a) |R>> forall (M:map loc a),
    R (Group (Ref Id) M) (fun l => Group (Ref Id) (M\(l:=v)) \* [l\notindom' M]).


(****************************************************)
(** Lemmas *)

Global Opaque binds_inst. (* todo: bug de congruence *)

Lemma is_repr_inj : forall r1 r2 M x,
  is_repr M x r1 -> is_repr M x r2 -> r1 = r2.
Proof.
  introv H. gen r2. induction H; introv H'. (* todo : inductions. *)
  inverts H'.
    auto. 
    forwards~: binds_inj H H0. false.
  inverts H'. 
    forwards~: binds_inj H1 H. false.  
    forwards~ E: binds_inj H1 H. inverts E. apply~ IHis_repr.
Qed.

Lemma is_equiv_refl : forall M x, 
  x \indom M -> is_forest M -> is_equiv M x x.
Proof. introv D H. forwards* [r R]: (H x). Qed. 

Lemma is_equiv_sym : forall M,
  sym (is_equiv M).
Proof. intros M x y (r&Hx&Hy). eauto. Qed.

Implicit Arguments is_repr_inj [ ].

Lemma is_equiv_trans : forall M,
  trans (is_equiv M).
Proof.
  intros M y x z (r1&Hx&Hy) (r2&Hy'&Hz).
  forwards: is_repr_inj r1 r2; eauto. subst*.
Qed.

Lemma is_repr_add_node : forall M r c x y,
  r \notin (dom M:set _) -> is_repr M x y -> is_repr (M\(r:=c)) x y.
Proof. introv N H. induction H; constructors*. Qed. 

(*
Lemma connected_eq : forall A (G' G:graph A),
  edges G = edges G' -> connected G = connected G'.
Proof. introv H. unfolds. rewrite~ H. Qed.

Implicit Arguments connected_eq [A].
*)

Lemma is_equiv_add_node : forall M r,
  is_forest M -> r \notindom' M ->
  is_equiv (M\(r:=Root)) = is_equiv M.
Proof.
  introv FM D. extens. intros x y.
  tests (x = r); tests (y = r).
(*
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

Lemma inv_add_node : forall M G r,
  is_equiv M = connected G ->
  r \notindom' M -> 
  is_equiv (M\(r:=Root)) = connected (add_node G r).
Admitted.

Lemma is_forest_add_node : forall M r,
  is_forest M -> r \notindom' M -> is_forest (M\(r:=Root)).
Proof.
  introv FM Dr. intros x Dx. destruct (map_indom_inv Dx).
    subst*.
    forwards* [y Ry]: FM x. exists y. apply* is_repr_add_node.
Qed.


(****************************************************)
(** Verification *)

(*--------------------------------------------------*)
(** Function [repr] *)

Axiom ml_get_spec_group : forall a,
  Spec ml_get (l:loc) |R>> forall (M:map loc a),   
    Inhab a -> l \indom M ->
    keep R (Group (Ref Id) M) (\= M\(l)).

Axiom binds_get : forall A `{Inhab B} (M:map A B) x v,
  binds M x v -> M\(x) = v.
Axiom binds_dom : forall A `{Inhab B} (M:map A B) x v,
  binds M x v -> x \indom M.

Lemma is_repr_in_dom : forall M x r, 
  is_repr M x r -> x \indom M.
Proof. introv H. inverts H; apply* binds_dom. Qed. 

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

Axiom dom_update_notin : forall A i `{Inhab B} v (M:map A B),
  i \notindom' M -> dom (M\(i:=v)) = dom M \u \{i}.

Lemma create_spec :
  Spec create () |R>> forall G,
    R (UF G) (fun r => UF (add_node G r)).
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
(** Function [equiv] *)

(*
Lemma indom_from_innodes : forall x G M,
  dom M = nodes G -> x \in nodes G -> x \indom' M.
Proof. introv H D. rewrite H. auto. Qed.
Hint Resolve indom_from_innodes.
*)

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

Lemma is_equiv_iff_same_repr : forall M x y rx ry,
  is_repr M x rx -> is_repr M y ry ->
  ((rx = ry) <-> is_equiv M x y).
Proof. 
  introv Rx Ry. iff H (r&Rx'&Ry'). subst*.
  applys (eq_trans r); applys is_repr_inj; eauto.
Qed.

Lemma equiv_spec :
  Spec equiv x y |R>> forall G, 
    x \in (nodes G) -> y \in (nodes G) ->
    keep R (UF G) (\= istrue(connected G x y)).
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

Axiom ml_set_spec_group :  forall a, 
  Spec ml_set (l:loc) (v:a) |R>> forall (M:map loc a), 
    Inhab a -> l \indom M ->
    R (Group (Ref Id) M) (# Group (Ref Id) (M\(l:=v))).

Lemma is_repr_in_dom' : forall M x r, 
  is_repr M x r -> r \indom M.
Proof. introv H. induction H. apply* binds_dom. auto. Qed. 

Lemma is_repr_binds_root : forall M x r, 
  is_repr M x r -> binds M r Root.
Proof. introv H. induction~ H. Qed.

Lemma is_forest_update : forall M x y,
  is_forest M -> binds M x Root -> binds M y Root -> 
  is_forest (M\(x:=Node y)).
Admitted.

Lemma inv_add_edge : forall M G x rx y ry,
  is_equiv M = connected G ->
  is_repr M x rx ->
  is_repr M y ry ->
  is_equiv (M\(rx:=Node ry)) = connected (add_edge G x y).
Admitted.


Lemma union_spec :
  Spec union x y |R>> forall G,
    x \in (nodes G) -> y \in (nodes G) ->
    R (UF G) (# UF (add_edge G x y)).
Proof.
  xcf. introv Dx Dy. unfold UF. xextract as M (FM&DM&EM).
  rewrite <- DM in *. clear DM.
  xapp~ as rx. intros Rx. xapp~ as ry. intros Ry.
  xapp_spec~ ml_set_spec_group. apply* is_repr_in_dom'.
  hsimpl. splits.
    apply* is_forest_update; apply* is_repr_binds_root.  
    rewrite~ dom_update_in. forwards: is_repr_binds_root Rx. skip.
    apply* inv_add_edge.
Admitted.

Hint Extern 1 (RegisterSpec union) => Provide union_spec.


