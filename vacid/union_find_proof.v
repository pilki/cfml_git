Set Implicit Arguments.
Require Import CFLib LibSet LibMap union_find_ml.


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

(** A graph here is simply a set of edges, which are pairs
    of nodes. *)

Record graph A := { edges : set (A*A) }.


(** [connected G x y] indicates that the nodes [x] and [y]
    belong to the same connected component in [G]. 
    A connected component is defined as the reflexive-
    symmetric-transitive closure of the edges. *)

Definition connected A (G:graph A) : binary A :=
  closure (fun x y => (x,y) \in edges G).


(****************************************************)
(** Invariant of union-find *)

Implicit Type M : map loc content.
   

(** [is_repr M x y] asserts that [y] is the end of the
    path that starts from [x]. *)

Definition is_repr 

(** [is_forest M] captures the fact that every node has a
    path to a root. *)

(** [UF G] is a heap predicate that corresponds to a set of 
    cells describing the union-find structure associated with
    the graph [G], where the nodes of [G] are of type [loc] *)
    
Definition UF (G:graph loc) : hprop :=
  Hexists (M:map loc content), Group Id M \*
    [ is_forest M /\ is_equiv M = connected G ].


(****************************************************)
(** Verification *)

(*--------------------------------------------------*)
(** Function [valid] *)

Lemma valid_spec :
  Spec valid i s |R>> forall n Val Idx Back, 
    good_sizes n Val Idx Back -> index L i -> n <= L ->
    keep R (s ~> SarrayPacked n Val Idx Back)
           (\= istrue (Valid n Idx Back i)).
Proof.
  xcf. introv Siz Ii Le. unfold SarrayPacked.
  xchange (Sarray_focus s) as n' val idx back E. subst n'.
  xapps. xapps*. xapps. xif. 
  (* case inbound *)
  xapps. xapps. hnf in Siz. eapply array_index_prove. math.
  xchange (Sarray_unfocus s).
  xret. hsimpl. rew_logics. unfolds Valid. splits*.
  (* case outof bound *)
  xchange (Sarray_unfocus s). 
  xret. hsimpl. fold_bool. fold_prop. unfold Valid.
  cuts*: (~ index n (Idx\(i))). rewrite* int_index_def.
Qed.

Hint Extern 1 (RegisterSpec valid) => Provide valid_spec.


(*--------------------------------------------------*)
(** Function [get] *)

Lemma get_spec' :
  Spec get i s |R>> forall f, index L i -> 
    keep R (s ~> SparseArray f) (\= f i).
Proof.
  xcf. introv ILi.
  unfold SparseArray. hdata_simpl.
  xextract as n Val Idx Back (Siz&Bok&Iok).
  xapps*. hnf in Siz; math.
  lets M: Iok i. xif; case_if in M; tryfalse.
  (* case is an index *)
  xchange (Sarray_focus s) as n' val idx back E. subst n'. xapps. xapp*.
  intros r. hchanges (Sarray_unfocus s); subst~.
  (* case not an index *)
  xrets*.
Qed. 


(*--------------------------------------------------*)
(** Function [set] *)

(** Auxiliary definition for update of a function *)

Definition update_fun A B (f:A->B) i v :=
  fun j => If i '= j then v else f j.

(** Auxiliary lemma for back pointers *)

Lemma not_Valid_to_notin_Back : forall i n Idx Back,
  ~ (Valid n Idx Back i) -> index L i -> BackCorrect n Idx Back ->
  (forall k, index n k -> i <> Back\(k)).
Proof.
  introv NVi ILi Bok Ink Eq. forwards~ [_ E]: Bok k. 
  unfolds Valid. rewrite (prop_eq_True_back ILi) in NVi. 
  rew_logic in NVi. destruct NVi as [H|H]; apply H; clear H; congruence.
Qed.

(** Auxiliary lemma for validity of indices *)

Lemma Valid_extend : forall n Idx Back i j,
  length Idx = L -> length Back = L -> index L n -> i <> j ->
  (Valid n Idx Back j <-> Valid (n + 1) (Idx\(i:=n)) (Back\(n:=i)) j).
Proof.
  introv Le1 Le2 ILn Neq. unfold Valid. 
  lets M: ILn. rewrite int_index_def in M.
  test_prop (index L j); [|auto*].
  rewrite~ (array_update_read_neq (t:=Idx)).
  rewrite int_index_succ; [|math].
  test_prop (index n (Idx\(j))).
    rew_array*.                           (* easy for SMT *)
      apply* index_array_length_le. math. (* easy for SMT *)
      rewrite int_index_def in *. math.   (* easy for SMT *)
    split; auto_false. intros [In Eq].    (* easy for SMT *)
     rewrite In in Eq.                    (* easy for SMT *)
     rewrite array_update_read_eq in Eq; auto_false. (* easy for SMT *)
Qed.

(** Verification of the [set] function *)

Lemma set_spec :
  Spec set i v l |R>> forall f, index L i ->
    R (l ~> SparseArray f) (# l ~> SparseArray (update_fun f i v)).
Proof.
  xcf. introv Imi. hdata_simpl SparseArray.
  xextract as n Val Idx Back (Siz&Bok&Iok).
  xchange (Sarray_focus s) as n' val idx back. intro_subst.
  xapps. xapps*.
  xchange (Sarray_unfocus s n). fold SarrayPacked. clear val idx back.
  xapps*. hnf in Siz; math. xif.
  (* case create back-index *)
  xchange (Sarray_focus s) as n' val idx back. intro_subst.
  lets Nbk: not_Valid_to_notin_Back Bok; eauto.
  skip: (n < L). (* pigeon-holes, see task description *)
  asserts: (0 <= n < L). hnf in Siz; math.                 (* easy for SMT *)
  asserts: (index L n). rewrite~ int_index_def.            (* easy for SMT *)
  xapps. xapps. xapps*. xapps. xapps*. xapp.
  hchanges (Sarray_unfocus s). splits.
    hnf. rew_array. hnf in Siz. jauto_set; auto; math.     (* easy for SMT *)
    intros k Ik. tests (k = n).                            (* easy for SMT *)
      rew_array*.                                          (* easy for SMT *)
      rewrite @int_index_def in Ik.                        (* easy for SMT *)
       asserts [? ?]: (index n k /\ index L k). strong.    (* easy for SMT *)
       forwards~ [? ?]: Bok k. rew_array*.                 (* easy for SMT *)
    intros j. unfold update_fun. specializes Iok j. case_if.
      asserts: (index (n + 1) n).                          (* easy for SMT *)
        eapply int_index_prove; math.                      (* easy for SMT *)
       subst. unfold Valid. rew_map_array*.                (* easy for SMT *)
       case_if; tryfalse*; auto.                           (* easy for SMT *)
      rewrite Iok. apply~ If_eq.
        myunfold. apply~ Valid_extend.
        intros. rew_array~.                                (* easy for SMT *)
  (* case nothing to do *)
   xret. hsimpl. splits~. unfold update_fun.
   intros j. specializes Iok j.                            (* easy for SMT *)
   case_if; case_if; tryfalse; auto.                       (* easy for SMT *)
     subst. rew_map_array*.                                (* easy for SMT *)
     rew_map_array*.                                       (* easy for SMT *)
Qed.







(*
      forall_ x \in nodes G, forall_ y \in nodes
 G,        (connected G x y <-> is_equiv M x y) ].
*)