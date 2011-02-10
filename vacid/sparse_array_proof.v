Set Implicit Arguments.
Require Import CFLib LibSet LibMap LibArray sparse_array_ml.


(****************************************************)
(** Shorthand *)

Notation "'tab'" := (array int).
Notation "'L'" := maxlen.

Definition SarrayPacked :=
  @Sarray int (array int) (array int) (array int) Id Array Array Array.

Definition SarrayUnpacked :=
  @Sarray int loc loc loc Id Id Id Id.


(****************************************************)
(** Invariant *)

(** [good_sizes] asserts that the three arrays have size [L] *)

Definition good_sizes n (Val Idx Back : tab) :=
  length Val = L /\ length Idx = L /\ length Back = L /\ 0 <= n <= L.

(** [i] is a [Valid] index if [Back(k) = i] for some [k] *)

Definition Valid n (Idx Back : tab) i :=
  index L i /\ let k := Idx\(i) in 
  index n k /\ Back\(k) = i.

(** [BackCorrect] holds when [k < n -> Idx(Back(k)) = k]*)

Definition BackCorrect n (Idx Back:tab) :=
  forall k, index n k ->
  let i := Back\(k) in index L i /\ Idx\(i) = k.

(** [s ~> SparseArray f] indicates that [s] is a record 
    describing a sparse array whose model is the function [f] *)

Definition SparseArray (f:int->int) (s:loc) :=
  Hexists (n:int) (Val:tab) (Idx:tab) (Back:tab),
     s ~> SarrayPacked n Val Idx Back
  \* [ good_sizes n Val Idx Back
       /\ BackCorrect n Idx Back
       /\ (forall i, f i = If Valid n Idx Back i then Val\(i) else 0) ].


(****************************************************)
(** Automation *)

(** Automation of [index] goals *)

Ltac myunfold := 
  repeat match goal with 
  | H: Valid _ _ _ _ |- _ => hnf in H 
  | H: good_sizes _ _ _ _ |- _ => hnf in H 
  end; jauto_set.

Hint Extern 1 (@index _ _ (array_index _) ?t ?i) =>
  myunfold; eassumption.
Hint Extern 1 (@index _ _ int_index ?t ?i) =>
  myunfold; eassumption.
Hint Extern 1 (@index _ _ (array_index _) ?t ?i) =>
  myunfold; match goal with H: @index _ _ int_index ?n i |- _ => 
    eapply index_array_length end.

Lemma index_array_length_le : forall A (t : array A) n i,
  index n i -> n <= length t -> index t i.
Proof.
  intros. subst. rewrite array_index_def.
  rewrite @int_index_def in *. math.
Qed.

Ltac strong := 
  math_0; math_1; math_2; math_3; try split; 
  eapply int_index_prove; math_3; math_4; math_5.

(** Tactic for rewriting *)

Tactic Notation "inhabs" := (* workaround coq bug *)
  try match goal with |- Inhab _ => typeclass end.
Tactic Notation "rew_map_array" :=
  rew_map; rew_array; inhabs.
Tactic Notation "rew_map_array" "~" :=
  rew_map_array; auto~; inhabs.
Tactic Notation "rew_map_array" "*" :=
  rew_map_array; auto*; inhabs.


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
      rew_arr*.                                            (* easy for SMT *)
      rewrite @int_index_def in Ik.                        (* easy for SMT *)
       asserts [? ?]: (index n k /\ index L k). strong.    (* easy for SMT *)
       forwards~ [? ?]: Bok k. rew_array*.                 (* easy for SMT *)
    intros j. unfold update_fun. specializes Iok j. case_if.
      asserts: (index (n + 1) n).                          (* easy for SMT *)
        eapply int_index_prove; math.                      (* easy for SMT *)
       subst. unfold Valid. rew_arr*.                      (* easy for SMT *)
       case_if; tryfalse*; auto.                           (* easy for SMT *)
      rewrite Iok. apply~ If_eq.
        myunfold. apply~ Valid_extend.
        intros. rew_array~.                                (* easy for SMT *)
  (* case nothing to do *)
   xret. hsimpl. splits~. unfold update_fun.
   intros j. specializes Iok j.                            (* easy for SMT *)
   case_if; case_if; tryfalse; auto.                       (* easy for SMT *)
     subst. rew_arr*.                                      (* easy for SMT *)
     rew_map_array*.                                       (* easy for SMT *)
Qed.




