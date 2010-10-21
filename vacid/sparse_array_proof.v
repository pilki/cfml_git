Set Implicit Arguments.
Require Import LibSet LibMap.
Require Import CF sparse_array_ml.


(****************************************************)
(** Shorthand *)

Notation "'tab'" := (array int).
Notation "'L'" := maxlen.

Definition SarrayPacked :=
  @Sarray int (array int) (array int) (array int) Id (Array Id) (Array Id) (Array Id).

Definition SarrayUnpacked :=
  @Sarray int loc loc loc Id Id Id Id.


(****************************************************)
(** Invariant *)

(** [good_sizes] asserts that the three arrays have size [L] *)

Definition good_sizes (Val Idx Back : tab) :=
  length Val = L /\ length Idx = L /\ length Back = L.

(** [i] is a [Valid] index if [Back(k) = i] for some [k] *)

Definition Valid n (Idx Back : tab) i :=
  index L i /\ let k := Idx\(i) in 
  index n k /\ Back\(k) = i.

(** [BackCorrect] holds when [k < n -> Idx(Back(k)) = k]*)

Definition BackCorrect n (Idx Back:tab) :=
  forall k, index n k ->
  let i := Back\(k) in index L i /\ Idx\(i) = k.

(** [s ~> SparseArray m] indicates that [s] is a record 
    describing a sparse array whose model is the map [m] *)

Definition SparseArray (m:map int int) (s:loc) :=
  Hexists (n:int) (Val:tab) (Idx:tab) (Back:tab),
     s ~> SarrayPacked n Val Idx Back
  \* [ good_sizes Val Idx Back
       /\ BackCorrect n Idx Back
       /\ (forall i, index m i -> Valid n Idx Back i /\ Val\(i) = m\(i)) ].


(****************************************************)
(** Automation *)

(* todo: paufiner avec les hint extern *)
Ltac myunfolds := unfolds good_sizes, Valid.
Ltac auto_star ::= try solve [myunfolds; intuition eauto]. (* jauto => should splitt iff *)
Ltac auto_tilde ::= try solve [myunfolds; auto].
Ltac autom := myunfolds; auto with maths.

Hint Resolve int_index_le int_index_prove.
Hint Resolve array_index_prove index_array_length.
Hint Resolve length_update_prove.

Lemma le_succ : forall n, n <= n +1.
Proof. math. Qed.
Hint Resolve le_succ.

Tactic Notation "inhabs" := (* workaround coq bug *)
  match goal with |- Inhab _ => typeclass end.

Hint Rewrite @map_indom_update : rew_map.
Tactic Notation "rew_map_array" :=
  rew_map in *; rew_array in *.
Tactic Notation "rew_map_array" "~" :=
  rew_map_array; auto~; try inhabs.
Tactic Notation "rew_map_array" "*" :=
  rew_map_array; auto*; try inhabs.


(****************************************************)
(** Auxiliary lemmas *)

Lemma not_Valid_to_notin_Back : forall i n Idx Back,
  ~ (Valid n Idx Back i) -> index L i -> BackCorrect n Idx Back ->
  (forall k, index n k -> i <> Back\(k)).
Proof.
  introv NVi ILi Bok Ink Eq. forwards~ [_ E]: Bok k. 
  unfolds Valid. rewrite (prop_eq_True_back ILi) in NVi. 
  rew_logic in NVi. destruct NVi as [H|H]; apply H; clear H; congruence.
Qed.


(****************************************************)
(** Verification *)

(*--------------------------------------------------*)
(** Function [valid] *)

Lemma valid_spec :
  Spec valid i s |R>> forall n Val Idx Back, 
    good_sizes Val Idx Back -> index L i -> n <= L ->
    keep R (s ~> SarrayPacked n Val Idx Back)
           (\= istrue (Valid n Idx Back i)).
(*
Proof.
  xcf. introv Siz Ii Le.
  unfold SarrayPacked. xchange (Sarray_focus s) as n' val idx back.
    (* temp *) xchange (Id_focus n'). xextract. intro_subst.
  xapps. xapps. auto*. xapps. xif. 
  (* case inbound *)
  xapps. xapps. autom.
    (* temp: *) xchange (Id_unfocus n).
  xchange (Sarray_unfocus s n val idx back). xret. 
    hsimpl. rew_logics. unfolds* Valid.
  (* case outof bound *)
    (* temp *) xchange (Id_unfocus n).
  xchange (Sarray_unfocus s n val idx back). xret. 
   hsimpl. fold_bool. fold_prop. unfold Valid.
  cuts*: (~ index n (Idx\(i))). rewrite* int_index_def.
*)
Admitted.

Hint Extern 1 (RegisterSpec valid) => Provide valid_spec.


(*--------------------------------------------------*)
(** Function [get] *)

Lemma get_spec :
  Spec get i s |R>> forall m, index m i -> 
    keep R (s ~> SparseArray m) (\= m\(i)).
Proof.
(*
  xcf. introv Imi.
  unfold SparseArray. hdata_simpl.
  xextract as n Val Idx Back (Siz&Bok&Iok).
  forwards (Vi&Ei): Iok Imi. 
  xapps*. skip. (* n <= L *)
  xif.
  xchange (Sarray_focus s) as n' val idx back. (**-todo: focus only on values *)
  xapps. xapp*.
  intros v. hchange (Sarray_unfocus s n' val idx back).
  hextract. subst. hsimpl*.
Qed. 
*)
Admitted.


(*--------------------------------------------------*)
(** Function [set] *)

Lemma set_spec :
  Spec set i v l |R>> forall m, index L i ->
    R (l ~> SparseArray m) (# l ~> SparseArray (m\(i:=v))).
Proof.
  xcf. introv Imi.
  hdata_simpl SparseArray.
  xextract as n Val Idx Back (Siz&Bok&Iok).
  xchange (Sarray_focus s) as n' val idx back.
  xapps. xapps*.
  xchange (Sarray_unfocus s n' val idx back). fold SarrayPacked. clear n' val idx back.
  xapps*. (* skip. n <= L *) skip.
  xif; [|skip].
  (* case create back-index *)
  xchange (Sarray_focus s) as n' val idx back.
  (* temp *) xchange (Id_focus n'). xextract. intro_subst.
  lets Nbk: (>>> not_Valid_to_notin_Back Bok); eauto.
  skip: (0 <= n < L).
  xapps. xapps. xapps*. xapps. xapps*. xapp.
  intros _. hchange (Id_unfocus (n+1)).
  hchange (Sarray_unfocus s (n+1) val idx back). hsimpl. splits.
    splits*.
    intros k Ik. tests (k = n).
      rew_array; auto*.
      rewrite @int_index_def in Ik.
      asserts: (index n k). autom.
      forwards~ [? ?]: Bok k. rew_array; auto*. autom.
    intros j Imj. tests (j = i).
      asserts: (index (n + 1) n). autom. (* for efficiency *)

unfold Valid. rew_map_array*.
rew_map in Imj; try typeclass. destruct Imj; tryfalse.
forwards~ [? ?]: Iok j.
unfold Valid. rew_map_array; auto.
auto*.
auto*.
rewrite @array_index_def. myunfolds. eapply int_index_le. auto*. math.
myunfolds. do 2 rewrite @int_index_def in H1. math.
auto*.
  (* case nothing to do *)
   xret. hsimpl. splits~.
   intros j Imj. tests (j = i).
     rew_map_array*.
     forwards: Inv j; rew_map_array*. 
Qed.


  