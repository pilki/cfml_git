Set Implicit Arguments.
Require Export LibCore LibEpsilon Shared.


(********************************************************************)
(* ** Representation of Heaps *)

(** Representation of locations *)

Definition loc := nat.

(** Representation of heap items *)

Record dyn := { 
  dyn_type : Type; 
  dyn_value : dyn_type }.

(** Representation of heaps *)

Definition heap := option (map loc dyn).


(********************************************************************)
(* ** Construction of Heaps *)

(** Empty heap *)

Definition heap_empty : heap := 
  Some empty.

(** Singleton heap *)

Definition heap_single (l:loc) A (v:A) : heap := 
  Some (single l (Build_dyn v)).

(** Heap union *)

Definition heap_union (h1 h2 : heap) : heap := 
  match h1,h2 with
  | Some m1, Some m2 => 
      If disjoint (dom m1) (dom m2)
         then Some (m1 \u m2)
         else None
  | _,_ => None
  end.


(********************************************************************)
(* ** Predicate on Heaps *)

(** [hprop] is the type of predicates on heaps *)

Definition hprop := heap -> Prop.

(** Empty heap *)

Definition heap_is_empty : hprop := 
  = heap_empty.

(** Singleton heap *)

Definition heap_is_single (l:loc) A (P:A->Prop) : hprop := 
  fun h => exists v, h = heap_single l v /\ P v.

(** Heap union *)

Definition heap_is_star (H1 H2 : hprop) : hprop := 
  fun h => exists h1 h2, h = heap_union h1 h2 /\ H1 h1 /\ H2 h2.

(** Pack in heaps *)

Definition heap_is_pack A (Hof : A -> hprop) : hprop := 
  fun h => exists x, Hof x h.

(** Lifting of predicates *)

Definition heap_is_empty_st (H:Prop) : hprop :=
  fun h => h = heap_empty /\ H.


(********************************************************************)
(* ** Notation for predicates *)

Notation "[]" := (heap_is_empty) 
  (at level 0) : heap_scope.

Notation "[ L ]" := (heap_is_empty_st L) 
  (at level 0, L at level 99) : heap_scope.

Notation "[[ P ]]" := (fun v => heap_is_empty_st (P v)) 
  (at level 0, P at level 99) : heap_scope.

Notation "H1 * H2" := (heap_is_star H)
  (at level 40, left associativity) : heap_scope.

Notation "l '~>|' P" := (heap_is_single l P)
  (at level 35, no associativity) : heap_scope.

Notation "l '~>' v" := (heap_is_single l (=v))
  (at level 35, no associativity) : heap_scope.

Notation "'Hexists' x , H" := (heap_is_pack (fun x => H))
  (at level 35, x ident, H at level 200) : heap_scope.

Open Scope heap_scope.


(********************************************************************)
(* ** Facts *)

(*------------------------------------------------------------------*)
(* ** Properties of Star *)

Lemma star_neutral_l : neutral_l [] heap_is_star.
Proof. skip. Qed.

Lemma star_neutral_r : neutral_l [] heap_is_star.
Proof. skip. Qed.

Lemma star_comm : comm heap_is_star. 
Proof. skip. Qed.

Lemma star_assoc : assoc heap_is_star. 
Proof. skip. Qed.

