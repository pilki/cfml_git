Set Implicit Arguments.
Require Import LibCore.
Require Import CFPrim CFTactics. (* todo: group as CF *)
Require Import sparse_array_ml.

(* Require Import FuncTactics.*)

Notation "'Hexists' x1 x2 x3 x4 , H" := 
  (Hexists x1, Hexists x2, Hexists x3, Hexists x4, H)
  (at level 39, x1 ident, x2 ident, x3 ident, x4 ident, H at level 50) : heap_scope.
Notation "'Hexists' x1 x2 x3 x4 x5 , H" := 
  (Hexists x1, Hexists x2, Hexists x3, Hexists x4, Hexists x5, H)
  (at level 39, x1 ident, x2 ident, x3 ident, x4 ident, x5 ident, H at level 50) : heap_scope.


Class BagIndex T A := { index : T -> A -> Prop }.

Instance int_index : BagIndex int int.
Proof. intros. constructor. exact (fun n i => 0 <= i < n). Defined.

Lemma int_index_def : forall (n i : int),
  index n i = (0 <= i < n).
Proof. auto. Qed. 

Instance array_index : forall A, BagIndex (array A) int.
Proof. intros. constructor. exact (fun t i => index (length t) i). Defined.

Lemma array_index_def : forall A (t:array A) i,
  index t i = index (length t) i.
Proof. auto. Qed. 

Lemma array_index_bounds : forall A (t:array A) i,
  index t i = (0 <= i < length t).
Proof. auto. Qed. 

Opaque int_index array_index.

Notation "m \( x )" := (LibBag.read m x)
  (at level 29, format "m \( x )") : container_scope.
Notation "m \( x := v )" := (update m x v)
  (at level 29, format "m \( x := v )") : container_scope.


Parameter ml_array_get_spec : forall a,
  Spec ml_array_get (l:loc) (i:int) |R>> 
    forall `{Inhab a} (t:array a), index t i ->
    keep R (l ~> Array Id t) (\= t\(i)).

Parameter ml_array_set_spec : forall a,
  Spec ml_array_set (l:loc) (i:int) (v:a) |R>> 
    forall (t:array a), index t i -> 
    R (l ~> Array Id t) (# l ~> Array Id (t\(i:=v))).
      (* (# Hexists t', l ~> Array Id t' \* [t' = t\(i:=v)]).*)

Hint Extern 1 (RegisterSpec ml_array_get) => Provide @ml_array_get_spec.
Hint Extern 1 (RegisterSpec ml_array_set) => Provide @ml_array_set_spec.


Ltac xchange_debug L :=
  let K := fresh "TEMP" in
  forwards_nounfold K: L; eapply xchange_lemma; 
    [ clear K; try xlocal
    | apply K
    | clear K; instantiate 
    | clear K ].

Axiom isTrue_andb : forall b1 b2 : bool,
  isTrue (b1 && b2) = (isTrue b1 /\ isTrue b2).
Axiom isTrue_orb : forall b1 b2 : bool,
  isTrue (b1 || b2) = (isTrue b1 \/ isTrue b2).
Axiom isTrue_negb : forall b : bool,
  isTrue (! b) = (~ isTrue b).

Hint Rewrite isTrue_istrue isTrue_andb isTrue_orb isTrue_negb : rew_logicb.

Hint Rewrite not_True not_False not_not not_and not_or : rew_logic.

Tactic Notation "rew_logic" := 
  autorewrite with rew_logic.
Tactic Notation "rew_logic" "in" hyp(H) := 
  autorewrite with rew_logic in H.
Tactic Notation "rew_logic" "in" "*" := 
  autorewrite with rew_logic in *.

Tactic Notation "rew_logicb" := 
  autorewrite with rew_logicb.
Tactic Notation "rew_logicb" "in" hyp(H) := 
  autorewrite with rew_logicb in H.
Tactic Notation "rew_logicb" "in" "*" := 
  autorewrite with rew_logicb in *.

Tactic Notation "rew_logics" := 
  rew_logicb; rew_logic.
Tactic Notation "rew_logic" "in" hyp(H) := 
  rew_logicb in H; rew_logic in H.
Tactic Notation "rew_logic" "in" "*" := 
  rew_logicb in *; rew_logic in *.

Ltac check_noevar_in H :=
  let T := type of H in
  match type of H with T => idtac | _ => fail 1 end.

Ltac xif_post H ::=
   calc_partial_eq tt;
   try fold_bool; fold_prop;
   try fix_bool_of_known tt;
   try solve [ discriminate | false; congruence ];
   first [ subst_hyp H; try fold_bool; try rewriteb H 
         | rewriteb H
         | idtac ];
   try fix_bool_of_known tt;
   try (check_noevar_in H; rew_logicb in H; rew_logic in H).

Lemma array_index_prove : forall A (t:array A) i,
  0 <= i < length t -> index t i.
Proof. intros. rewrite~ array_index_def. Qed.
Hint Resolve array_index_prove.

Tactic Notation "xapps" "~" := xapps; auto_tilde.
Tactic Notation "xapps" "*" := xapps; auto_star.


(****************************************************)
(* Specification of the invariant *)

Lemma test_omega : forall x,
  let y := x in
  2 + x = y + 2.
Proof. intros. try omega. unfold y. omega. Qed.

Definition y := 3.
Lemma test_omega' : y + 2 = 5.
Proof. intros. try omega. unfold y. omega. Qed.


(* todo: omega should match up to conversion *)
Notation "'tab'" := (array int).
Notation "'L'" := maxlen.

Definition SarrayPacked :=
  @Sarray int (array int) (array int) (array int) Id (Array Id) (Array Id) (Array Id).

Definition SarrayUnpacked :=
  @Sarray int loc loc loc Id Id Id Id.

(*
Definition map_read A `{Inhabited B} := @read _ _ _ (@read_inst A B _).
Coercion map_read : map >-> Funclass.
*)

Require Import LibSet LibMap.

Instance map_index : forall A B, BagIndex (map A B) A.
Proof. intros. constructor. exact (fun m k => k \in (dom m : set A)). Defined.

Lemma map_index_def : forall A B (m:map A B) k,
  index m k = (k \in (dom m : set A)).
Proof. auto. Qed. 

Opaque map_index_def.


Definition good_sizes (Val Idx Back : tab) :=
  length Val = L /\ length Idx = L /\ length Back = L.


Definition Valid n (Idx Back : tab) i :=
  index L i /\ let k := Idx\(i) in 
  index n k /\ Back\(k) = i.

Ltac myunfolds := unfolds good_sizes, Valid.

Ltac auto_star ::= try solve [myunfolds; intuition eauto]. (* jauto => should splitt iff *)
Ltac auto_tilde ::= try solve [myunfolds; auto].
Ltac autom := myunfolds; auto with maths.

Definition BackCorrect n (Idx Back:tab) :=
  forall k, index n k ->
  let i := Back\(k) in index L i /\ Idx\(i) = k.

Definition SparseArray (m:map int int) (s:loc) :=
  Hexists (n:int) (Val:tab) (Idx:tab) (Back:tab),
     s ~> SarrayPacked n Val Idx Back
  \* [ good_sizes Val Idx Back
       /\ BackCorrect n Idx Back
       /\ (forall i, index m i -> Valid n Idx Back i /\ Val\(i) = m\(i)) ].

Lemma classic_or_elim_l : forall P Q, P \/ Q -> P \/ (~ P /\ Q).
Proof. intros. destruct (classic P); auto_false*. Qed.
(*destruct (classic_or_elim_l NVi) as [H|[Ini H]]; apply H; clear H.*)

Lemma not_Valid_to_notin_Back : forall i n Idx Back,
  ~ (Valid n Idx Back i) -> index L i -> BackCorrect n Idx Back ->
  (forall k, index n k -> i <> Back\(k)).
Proof.
  introv NVi ILi Bok Ink Eq. forwards~ [_ E]: Bok k. 
  unfolds Valid. rewrite (prop_eq_True_back ILi) in NVi. 
  rew_logic in NVi. destruct NVi as [H|H]; apply H; clear H; congruence.
Qed.


(*
Lemma inbound_spec :
  Specs inbound i >> [] (\= istrue (index L i)).
Proof.
  xcf. intros. xret. hsimpl.
  extens. rew_logicb. rewrite* int_index_def.
Qed.

Hint Extern 1 (RegisterSpec inbound) => Provide inbound_spec.
*)

(* why not Axiom in middle of proofs ? --> coqbug *)


Lemma index_le : forall i n m : int,
  n <= m -> index n i -> index m i.
Proof. introv M. do 2 rewrite int_index_def. math. Qed.
Hint Resolve index_le.

Lemma index_array_length : forall A (t : array A) n i,
  index n i -> n = length t -> index t i.
Proof. intros. subst. rewrite~ array_index_def. Qed.
Hint Resolve index_array_length.

Lemma istrue_eq : forall (P Q : Prop),
  ((istrue P) = (istrue Q)) = (P <-> Q).
Proof.
  intros. extens. iff H.
  unfolds istrue. case_if; case_if; tryfalse; intuition.
  asserts_rewrite~ (P = Q). extens~.
Qed.

Hint Rewrite istrue_eq : rew_logicb.

Lemma Id_extract : forall A (x n : A),
  x ~> Id n ==> [x = n].
Proof. intros. unfold Id. hdata_simpl. xsimpl~. Qed.
Implicit Arguments Id_extract [A].

Lemma Id_import : forall A (x : A),
  [] ==> x ~> Id x.
Proof. intros. unfold Id. hdata_simpl. xsimpl~. Qed.
Implicit Arguments Id_import [A].

Lemma int_index_prove : forall (n i : int),
  0 <= i -> i < n -> index n i.
Proof. intros. rewrite~ int_index_def. Qed.
Hint Resolve int_index_prove. 


Lemma valid_spec :
  Spec valid i s |R>> forall n Val Idx Back, 
    good_sizes Val Idx Back -> index L i -> n <= L ->
    keep R (s ~> SarrayPacked n Val Idx Back)
           (\= istrue (Valid n Idx Back i)).
(*
Proof.
  xcf. introv Siz Ii Le.
  unfold SarrayPacked. xchange (Sarray_focus s) as n' val idx back.
    (* temp *) xchange (Id_extract n'). xextract. intro_subst.
  xapps. xapps. auto*. xapps. xif. 
  (* case inbound *)
  xapps. xapps. autom.
    (* temp: *) xchange (Id_import n).
  xchange (Sarray_unfocus s n val idx back). xret. 
    hsimpl. rew_logics. unfolds* Valid.
  (* case outof bound *)
    (* temp *) xchange (Id_import n).
  xchange (Sarray_unfocus s n val idx back). xret. 
   hsimpl. fold_bool. fold_prop. unfold Valid.
  cuts*: (~ index n (Idx\(i))). rewrite* int_index_def.
*)
Admitted.

Hint Extern 1 (RegisterSpec valid) => Provide valid_spec.

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

Import sparse_array_ml.

Tactic Notation "hdata_simpl" := 
  hdata_simpl.
Tactic Notation "hdata_simpl" constr(E) := 
  unfold E; hdata_simpl.

Axiom length_update_prove : forall A (t:array A) i v n,
  length t = n -> length (t\(i:=v)) = n.
Hint Resolve length_update_prove.

Opaque LibMap.dom_inst.


   Lemma array_update_read_eq : forall `{Inhab A} (t:array A) (i:int) (v:A),
     index t i -> (t\(i:=v))\(i) = v.
  Admitted.
   Lemma array_update_read_neq : forall `{Inhab A} (t:array A) (i j:int) (v:A),
     index t j -> i<>j -> (t\(i:=v))\(j) = t\(j).
  Admitted.
  Hint Rewrite @array_update_read_neq @array_update_read_eq : rew_array.
Tactic Notation "rew_array" := 
  autorewrite with rew_array.
Tactic Notation "rew_array" "in" hyp(H) := 
  autorewrite with rew_array in H.
Tactic Notation "rew_array" "in" "*" := 
  autorewrite with rew_array in *.

   Lemma map_update_read_eq : forall A `{Inhab B} (m:map A B) (i:A) (v:B),
     (m\(i:=v))\(i) = v.
  Admitted.
   Lemma map_update_read_neq : forall A `{Inhab B} (m:map A B) (i j:A) (v:B),
     i<>j -> (m\(i:=v))\(j) = m\(j).
  Admitted.
  Hint Rewrite @map_update_read_neq @map_update_read_eq : rew_map.
Tactic Notation "rew_map" := 
  autorewrite with rew_map.
Tactic Notation "rew_map" "in" hyp(H) := 
  autorewrite with rew_map in H.
Tactic Notation "rew_map" "in" "*" := 
  autorewrite with rew_map in *.

Lemma map_indom_update : forall A `{Inhab B} (m:map A B) (i j:A) (v:B),
  j \in (dom (m\(i:=v)) : LibSet.set _) = (j = i \/ j \in (dom m : LibSet.set _)).
Admitted.

Hint Rewrite @map_indom_update : rew_map.
Tactic Notation "inhabs" :=
  match goal with |- Inhab _ => typeclass end.
Tactic Notation "rew_map_array" :=
  rew_map in *; rew_array in *.
Tactic Notation "rew_map_array" "~" :=
  rew_map_array; auto~; inhabs.
Tactic Notation "rew_map_array" "*" :=
  rew_map_array; auto*; inhabs.


Lemma int_index_le : forall i n m : int,
  index n i -> n <= m -> index m i.
Admitted.

Lemma le_succ : forall n, n <= n +1.
Proof. math. Qed.
Hint Resolve le_succ.

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
  (* temp *) xchange (Id_extract n'). xextract. intro_subst.
  lets Nbk: (>>> not_Valid_to_notin_Back Bok); eauto.
  skip: (0 <= n < L).
  xapps. xapps. xapps*. xapps. xapps*. xapp.
  intros _. hchange (Id_import (n+1)).
  hchange (Sarray_unfocus s (n+1) val idx back). hsimpl. splits.
    splits*.
    intros k Ik. tests (k = n).
      rew_array; auto*.
      rewrite @int_index_def in Ik.
      asserts: (index n k). autom.
      forwards~ [? ?]: Bok k. rew_array; auto*. autom.
    intros j Imj. tests (j = i).
      asserts: (index (n + 1) n). autom. (* for efficiency *)
Tactic Notation "rew_map_array" "*" :=
  rew_map_array; auto*; try inhabs.
unfold Valid. rew_map_array*.
rew_map in Imj; try typeclass. destruct Imj; tryfalse.
forwards~ [? ?]: Iok j.
unfold Valid. rew_map_array; auto.
auto*.
auto*.
rewrite @array_index_def. myunfolds. eapply int_index_le. auto*. math.

skip.
auto*.
  (* case nothing to do *)
   xret. hsimpl. splits~.
   intros j Imj. tests (j = i).
     rew_map_array*.
     forwards: Inv j; rew_map_array*. 
Qed.


  
   Lemma array_update_length : forall `{Inhab A} (t:array A) (i:int) (v:A),
     index t i -> (t\(i:=v))\(i) = v.
  Admitted.


