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
  index t i = (0 <= i < length t).
Proof. auto. Qed. 

Opaque int_index array_index.

Notation "m \( x )" := (LibBag.read m x)
  (at level 29, format "m \( x )") : container_scope.
Notation "m \( x := v )" := (update m x v)
  (at level 29, format "m \( x := v )") : container_scope.


Parameter ml_array_get_spec : forall `{Inhabited a},
  Spec ml_array_get (l:loc) (i:int) |R>> 
    forall (t:array a), index t i ->
    keep R (l ~> Array Id t) (\= t\(i)).

Parameter ml_array_set_spec : forall a,
  Spec ml_array_set (l:loc) (i:int) (v:a) |R>> 
    forall (t:array a), index t i -> 
    R (l ~> Array Id t) (# l ~> Array Id (t\(i:=v))).
      (* (# Hexists t', l ~> Array Id t' \* [t' = t\(i:=v)]).*)

Hint Extern 1 (RegisterSpec ml_array_get) => Provide ml_array_get_spec.
Hint Extern 1 (RegisterSpec ml_array_set) => Provide ml_array_set_spec.


Ltac xchange_debug L :=
  let K := fresh "TEMP" in
  forwards_nounfold K: L; eapply xchange_lemma; 
    [ clear K; try xlocal
    | apply K
    | clear K; instantiate 
    | clear K ].


Hint Rewrite
 isTrue_istrue 
 istrue_isTrue 
 isTrue_neg_istrue 
 istrue_not_isTrue : rew_prop.

Tactic Notation "rew_prop" := 
  autorewrite with rew_prop.
Tactic Notation "rew_prop" "in" hyp(H) := 
  autorewrite with rew_prop in H.
Tactic Notation "rew_prop" "in" "*" := 
  autorewrite with rew_prop in *.

Lemma array_index_prove : forall A (t:array A) i,
  0 <= i < length t -> index t i.
Proof. intros. rewrite~ array_index_def. Qed.
Hint Resolve array_index_prove.

Ltac auto_star ::= try solve [intuition eauto]. (* jauto => should splitt iff *)
Ltac auto_tilde := auto with maths.



(****************************************************)
(* Specification of the invariant *)

Definition tab := array int.

Notation "'L'" := maxlen.

Definition SarrayPacked :=
  @Sarray int (array int) (array int) (array int) Id (Array Id) (Array Id) (Array Id).
Definition SarrayUnpacked :=
  @Sarray int loc loc loc Id Id Id Id.

Definition good_sizes (Val Idx Back : tab) :=
  length Val = L /\ length Idx = L /\ length Back = L.

Definition SparseArray (T:tab) (s:loc) :=
  Hexists (n:int) (Val:tab) (Idx:tab) (Back:tab),
     s ~> SarrayPacked n Val Idx Back
  \* [ good_sizes Val Idx Back
       /\ forall k, index n k -> let i := Back\(k) in
          index L i  /\  Idx\(i) = k  /\  T\(k) = Val\(k) ].

Lemma inbound_spec :
  Specs inbound i >> [] (\[ bool_of (index L i) ]).
Proof.
  xcf. intros. xret. hsimpl. apply bool_of_prove.
  rew_reflect. rew_prop. rewrite* int_index_def. 
Qed.

Lemma valid_spec :
  Spec valid i s |R>> forall n Val Idx Back, 
    good_sizes Val Idx Back ->
    keep R (s ~> SarrayPacked n Val Idx Back)
           (\[ bool_of (index L i /\ Back\(Idx\(i)) = i) ]).
Proof.
  xcf. introv (SVal&SIdx&SBack).
  unfold SarrayPacked.
  xchange (Sarray_focus s). xextract as n' val idx back.
(*  xpost.*)
  xif.
  (* case in bound *)
  rew_reflect in C. rew_prop in C. 
  xapps. xapps. xapps. apply array_index_prove. rewrite~ SIdx.
  xapps. apply array_index_prove. 


  (* case not in bound *)
  xchange (Sarray_unfocus s n' val idx back).
  xret. hsimpl. xclean. rew_reflect in *.
    intros [H _]. apply C. rewrite int_index_def in H. 
    split; fold_prop; unfolds L; try math.

 (*--todo :sortir le n' ~> Id n *)
Qed.

let valid i s =
   0 <= i && i < maxlen && s.back.(s.idx.(i)) = i


Lemma get_spec :
  Spec get i s |R>> forall T, index T i -> 
    keep R (s ~> SparseArray T) (\= T\(i)).
Proof.
  xcf. introv Ii.
  xlet. 

Qed.

    






---------

Definition L := maxlen.

Definition idx_back_coherent n Back Idx :=
   forall k, index n k -> index L (Back\[k]) /\ Idx\[Back\[k]] = k.

Definition back_pointed n Back i :=
  exists k, index n k /\ i = Back\[k].

Definition repr_valid n Back Val T :=
  forall i, index L i -> 
    If (back_pointed n Back i) 
      then T\[i] = Val\[i] 
      else T\[i] = 0.

(* Definition of "l ~> Sarray T" *)

Definition Sarray (T:array int) (l:loc) : heap -> Prop :=
  hexists n (val idx back : loc) (Val Idx Back : array int),
    l ~> sparse_array_of n val idx back 
  * val ~> Array Pure Val
  * idx ~> Array Pure Idx
  * back ~> Array Pure Back
  * [ size Val = L /\ 
      size Idx = L /\
      size Back = L /\
      idx_back_coherent n Back Idx /\
      repr_valid n Back Val T ].


Lemma used_cell_test_correct : forall n Back Idx i, 
  index L i -> idx_back_coherent n Back Idx ->
  (back_pointed n Back i) <-> (index n (Idx\[i]) /\ Back\[Idx\[i]] = i).

Lemma create_spec :
  Spec create size |R>> (0 <= size <= L) -> 
    R [] (fun l => l ~> Sarray (CoqArray.make size default)).
  
  spec_1 create (fun size R => ...).

Lemma get_spec :
  Spec get i l |R>> forall T, index T i -> 
    R (l ~> Sarray T) (fun v => l ~> Sarray T * [v = T\[i]]).
    
    keep R (l ~> Sarray T) (= T\[i]).

Lemma set_spec :
  Spec set i v l |R>> forall T, index T i ->
    R (l ~> Sarray T) (# l ~> Sarray (T\[i:=v])



(* ---------
invariant:
   0 <= n < size <= maxlen
   forall i, 0 <= i < n -> 0 <= back[i] < sz /\ idx[back[i]] = i
*)

  (*back_pointed: index n (Idx\[i]) /\ Back\[Idx\[i]] = i *)