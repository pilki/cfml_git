Set Implicit Arguments.
Require Import ZArith.
Open Scope Z_scope.

Definition int : Type := Z.


(**************************************************************************)
(** Formalization of arrays *)

(* type of arrays *)
Axiom array : Type -> Type.

(* length of an array *)
Axiom length : forall A, array A -> int.

(* reading in an array.
   The result is unspecfied outside of the bounds.
   The type [A] is assumed to be inhabited
     (a typeclass can be used to formally capture 
      this property in a generic manner). *)
Axiom array_read : forall A, array A -> int -> A.

Notation "m \( x )" := (array_read m x)
  (at level 33, format "m \( x )").

(* updating an array *)
Axiom array_update : forall A, array A -> int -> A -> array A.
Notation "m \( x := v )" := (array_update m x v)
  (at level 33, format "m \( x := v )").

(* a shorthand for arrays of int *)
Definition tab := array int. 

(* a shorthand for capturing bounds *)
Definition index (n : int) (i : int) :=
  (0 <= i /\ i < n).

(* a shorthand for capturing bounds in arrays *)
Definition array_index A (t:array A) (i : int) :=
  index (length t) i.



(**************************************************************************)
(** Manipulation of arrays *)

Example sparse_array_1 : forall
(L : int)
(n : int)
(Idx : tab)
(Back : tab)
(i : int)
(j : int)
(Le1 : length Idx = L)
(Le2 : length Back = L)
(ILn : index L n)
(Neq : i <> j)
(M : 0 <= n < L)
(C : index L j),
    (index n (Idx\(j)) /\ Back\(Idx\(j)) = j)
<-> ((index n (Idx\(j)) \/ Idx\(j) = n) /\ (Back\(n:=i))\(Idx\(j)) = j).
Admitted. 
  (* Note: the first step is a case analysis on [index n (Idx\(j)) = True].
     This first step can be provided by the user if needed. *)

(**************************************************************************)
(** Universally-quantified hypothesis *)

Definition good_sizes (L : int) (n:int) (Back:tab) (Idx:tab) (Val:tab) :=
  length Val = L /\ length Idx = L /\ length Back = L /\ 0 <= n <= L.

Definition BackCorrect (L n : int) (Back Idx : tab) :=
  forall k, index n k ->
  let i := Back\(k) in index L i /\ Idx\(i) = k.

Example sparse_array_2 : forall
(L : int)
(i : int)
(v : int)
(Imi : index L i)
(Back : tab)
(Idx : tab)
(n : int)
(Val : tab)
(Siz : good_sizes L n Back Idx Val)
(Bok : BackCorrect L n Back Idx)
(Nbk : forall k : int, index n k -> i <> Back\(k))
(H : n < L)
(H0 : 0 <= n < L)
(H1 : index L n)
(k : int)
(Ik : index (n + 1) k),
   index L ((Back\(n:=i))\(k)) 
/\ (Idx\(i:=n))\((Back\(n:=i))\(k)) = k.
Admitted. 
  (* Note: the first step is a case analysis on [k = n].
     This first step can be provided by the user if needed. *)

(**************************************************************************)
(** Abstract functions and classical logic *)

Axiom classicT : forall (P : Prop), {P} + {~ P}.

Notation "'IF' c1 'then' c2 'else' c3" := 
  (if (classicT c1) then c2 else c3)
  (at level 200, right associativity) : type_scope.

Definition Valid (L n : int) (Back Idx : tab) i :=
  index L i /\ let k := Idx\(i) in 
  index n k /\ Back\(k) = i.

Example sparse_array_3 : forall
(L : int)
(i : int)
(v : int)
(f : int -> int)
(Imi : index L i)
(Back : tab)
(Idx : tab)
(n : int)
(Val : tab)
(Siz : good_sizes L n Back Idx Val)
(Bok : BackCorrect L n Back Idx)
(Iok : forall k : int, f k = (IF (Valid L n Back Idx k) then Val\(k) else 0))
(C : Valid L n Back Idx i)
(j : int),
  (IF (i = j) then v else f j)
= (IF (Valid L n Back Idx j) then (Val\(i:=v))\(j) else 0).
Admitted.



(**************************************************************************)
(** Manipulation of sets *)

(* type of sets *)
Axiom set : Type -> Type.

(* empty set *)
Axiom set_empty : forall A, set A.
Notation "\{}" := (@set_empty _).

(* singleton set *)
Axiom set_single : forall A, A -> set A.
Notation "\{ x }" := (set_single x).

(* set union *)
Axiom set_union : forall A, set A -> set A -> set A.
Notation "m1 '\u' m2" := (set_union m1 m2)
  (at level 37, right associativity).

(* set inclusion *)
Axiom set_inclusion : forall A, set A -> set A -> Prop.
Notation "m1 '\c' m2" := (set_inclusion m1 m2) (at level 38).

(* cardinal of a set *)
Axiom card : forall A, set A -> nat.

(* set membership *)
Axiom set_in : forall A, A -> set A -> Prop.
Notation "x '\in' m" := (set_in x m) (at level 39).

(* set non-membership *)
Definition set_notin A x (E:set A) := ~ (set_in x E).
Notation "x '\notin' E" := (set_notin x E) (at level 39).


(**************************************************************************)
(** Permutation on sets *)

Example set_1 : forall A (x:A) l1 l2 l3,
    (l1 \u \{x} \u (l3 \u \{}) \u l2)
  = (l1 \u \{} \u l2 \u (\{x} \u l3)).
Admitted.

Example set_2 : forall A (x y:A) l1 l1' l1'' l2 l3,
  l1 = l1' \u l1'' ->
    (l1 \u (\{x} \u l2) \u (\{y} \u l3)) 
  = (\{y} \u (l1' \u l3) \u (l1'' \u \{x} \u l2)).
Admitted.


(**************************************************************************)
(** Non-membership reasoning on sets *)

Example set_notin_1 : forall A (x:A) E F G,
  x \notin (E \u F) -> 
  x \notin G -> 
  x \notin (E \u G).
Admitted.

Lemma set_notin_2 : forall A (x y : A) E,
  x <> y -> 
  x \notin E ->
  x \notin (E \u \{y}).
Admitted.

Lemma set_notin_3 : forall A (x:A) y E F,
  x \notin (E \u \{y} \u F) ->
     x \notin \{y} 
  /\ y \notin \{x} 
  /\ x <> y.
Admitted.

Lemma set_notin_4 : forall A (x y : A) E F G,
  x \notin (E \u \{y}) ->  
  (F \u G) \c E ->
  x \notin F.
Admitted.


(**************************************************************************)
(** Sets and arithmetics (bonus) *)

Lemma set_arithmetic : forall n m E F,
  n + 2 = 5 + m -> 
  E \c (F \u \{n}) ->
  (m + 3) \in F ->
  E \c F.

