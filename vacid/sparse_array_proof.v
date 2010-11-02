Set Implicit Arguments.
Require Import CFLib LibSet LibMap LibArray sparse_array_ml.

Lemma If_eq : forall (A:Type) (P P':Prop) (x x' y y' : A), 
  (P <-> P') -> (x = x') -> (y = y') ->
  (If P then x else y) = (If P' then x' else y').
Proof. intros. subst. asserts_rewrite (P = P'). extens~. auto. Qed.



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


Lemma Id_focus : forall A (x n : A),
  x ~> Id n ==> [x = n].
Proof. intros. unfold Id. hdata_simpl. hextract. hsimpl~. Qed.

Lemma Id_unfocus : forall A (x : A),
  [] ==> x ~> Id x.
Proof. intros. unfold Id. hdata_simpl. hextract. hsimpl~. Qed.

Implicit Arguments Id_focus [A].
Implicit Arguments Id_unfocus [A].

(*--------------------------------------------------*)
(** Function [valid] *)

Lemma hsimpl_id_unify : forall A (x : A) H' H1 H2,
  H' ==> H1 \* H2 -> H' ==> H1 \* (x ~> Id x \* H2).
Proof. intros. apply~ hsimpl_id. Qed.


Ltac hsimpl_step tt ::=
  match goal with |- ?HL ==> ?HA \* ?HN =>
  match HN with
  | ?H \* _ =>
    match H with
    | [] => apply hsimpl_empty
    | [_] => apply hsimpl_prop
    | heap_is_pack _ => hsimpl_extract_exists tt
    | _ \* _ => apply hsimpl_assoc
    | heap_is_single _ _ => hsimpl_try_same tt
    | ?H => hsimpl_find_same H HL 
    | hdata _ ?l => hsimpl_find_data l HL ltac:(hsimpl_find_data_post)
    | ?x ~> Id _ => check_noevar x; apply hsimpl_id
    | ?x ~> _ _ => check_noevar x; apply hsimpl_id_unify
    | ?H => apply hsimpl_keep
    end
  | [] => fail 1
  | _ => apply hsimpl_starify
  end end.


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

Ltac hsimpl_find_data_post tt ::=
  try solve 
   [ reflexivity
   | fequal; fequal; first [ eassumption | symmetry; eassumption ] ].


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

Definition update_fun A B (f:A->B) i v :=
  fun j => If i '= j then v else f j.

Lemma set_spec :
  Spec set i v l |R>> forall f, index L i ->
    R (l ~> SparseArray f) (# l ~> SparseArray (update_fun f i v)).
Proof.
  xcf. introv Imi. hdata_simpl SparseArray.
  xextract as n Val Idx Back (Siz&Bok&Iok).
  xchange (Sarray_focus s) as n' val idx back.
  xapps. xapps*.
  xchange (Sarray_unfocus s n' val idx back). 
   fold SarrayPacked. clear n' val idx back.
  xapps*. hnf in Siz; math.
  xif.
  (* case create back-index *)
  xchange (Sarray_focus s) as n' val idx back.
  xchange (Id_focus n'). xextract. intro_subst.
  lets Nbk: (>>> not_Valid_to_notin_Back Bok); eauto.
  skip: (n < L). (* pigeon-holes, see task description *)
  asserts: (0 <= n < L). hnf in Siz; math.
  asserts: (index L n). rewrite~ int_index_def. (* faster *)
  xapps. xapps. xapps*. xapps. xapps*. xapp.
  intros _. hchange (Id_unfocus (n+1)).
  hchange (Sarray_unfocus s (n+1) val idx back). hsimpl. splits.
    hnf. rew_array. hnf in Siz. jauto_set; auto; math. (* faster *)
    intros k Ik. tests (k = n).
      rew_array*. 
      rewrite @int_index_def in Ik.
       asserts [? ?]: (index n k /\ index L k). strong. (* faster *)
       forwards~ [? ?]: Bok k. rew_array*.
    intros j. unfold update_fun. specializes Iok j. case_if.
      subst. asserts: (index (n + 1) n). eapply int_index_prove; math. (* faster *)
       unfold Valid. rew_map_array*. case_if; tryfalse*; auto.
      rewrite Iok. case_if as N. (*todo: name*) renames v0 to N.
        rewrite If_l.
          rew_array~.
          unfold Valid in N|-*. destruct N as (N1&N2&N3). splits.
            auto.
            rew_array. rewrite int_index_def in N2 |- *. math.
            apply* index_array_length_le. myunfold. math.
            auto.
          rew_array~. rew_array~. apply* index_array_length_le. myunfold. math.
          rew_array. rewrite int_index_def in N2. math.
          apply* index_array_length_le. myunfold. math.
          auto.
        unfold Valid in n1|-*. case_if; auto. rew_logic in n1.
         false. destruct a as (N1&N2&N3). branches n1.
           false.
(*
           rew_array in N2; auto. rewrite int_index_def in N2,H2. math.

        
 rew_array.
      apply* index_array_length_le. myunfold. math. (* faster *) eauto. auto. unfold Valid. . fequals.
      unfold Valid. case_if.
   case_if; case_if; tryfalse; auto.
*)
skip.
rew_array in N3; auto. skip. skip.
(*
      rew_map in Imj; try typeclass. destruct Imj; tryfalse.
       forwards~ [(M1&M2&M3) E]: Iok j. unfold Valid. rew_map_array; auto.
         splits~. splits*. rewrite int_index_def in M2 |- *. math. (* faster *)
         apply* index_array_length_le. myunfold. math. (* faster *)
         rewrite @int_index_def in M2. math. (* faster *)
*)

  (* case nothing to do *)
   xret. hsimpl. splits~. 
   intros j. specializes Iok j. unfold update_fun. 
   case_if; case_if; tryfalse; auto.
     subst. rew_map_array*.
     rew_map_array*.
Qed.


  