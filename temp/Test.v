

Parameter t : Type.
Definition t' := t.
Inductive u : Type := | u_intro : t -> u.
Definition u_intro' : t' -> u := u_intro.
Coercion u_intro : t >-> u.
Coercion u_intro' : t' >-> u.





Set Implicit Arguments.

Class Label := lab { label : nat }.

Instance Label_default : Label.
Proof. constructor. exact 0. Defined.

Definition tag `{x:Label} (P:Prop) := P.
Notation "n #> P" := (@tag (lab n) P) (at level 30, only parsing).
Notation "# P" := (@tag _ P) (at level 30).
Lemma test : 3 #> True.
Lemma test : # True.
Lemma test : tag True.
Lemma test : @tag (lab 3) True.


Implicit Argument 

Inductive Lab : nat->Type :=
  | lab : forall n, Lab n.

Class Label (n:nat) := { label : Lab n }

Definition tag (n:nat) (l:Lab n) (P:Prop) := P.

Notation "n #> P" := (@tag _ (lab n) P) (at level 30, only parsing).
Notation "# P" := (@tag _ (lab _) P) (at level 30).

Lemma test : #> True.
Lemma test : 3 #> True.




Inductive Lab : nat->Type :=
  | lab : forall n, Lab n.

Definition tag (n:nat) (l:Lab n) (P:Prop) := P.

Notation "n #> P" := (@tag _ (lab n) P) (at level 30, only parsing).
Notation "# P" := (@tag _ (lab _) P) (at level 30).

Lemma test : #> True.
Lemma test : 3 #> True.




Require Import Omega.
Lemma test : (1 > 0)%nat.
omega.

Lemma test : 1 > 0.
omega.

Definition false := True.
Lemma test_omega : forall n m,
  ~ ( (~ (n < m)) -> false) -> m <= n.
intros. info omega.


Module Type Dummy. 
End Dummy.

Module Type DummyWrap.
  Declare Module M : Dummy.
End DummyWrap.

Module A (B : Dummy) : Dummy. End A.


Module C (B : Dummy) <: DummyWrap with Module M := A B.
(* I get the error: "incompatble module types". 
   Why? I cannot see any good reason *)


(* And if I replace "<:" with ":", the error message
   is delayed until the end of the module *)

Module C (B : Dummy) : DummyWrap with Module M := A B.
  Module M := A B.
End C.


By the way, is it possible to make "Print Module X"
show not only the definition of X but also its signature?


Arthur.



*)


(*
*)







Set Implicit Arguments.



Module Type Dummy. Parameter Z : Type. End Dummy.
Module Type Truc. Parameter Y : Type. End Truc.
Module Type Super. Parameter X : Type. End Super.
Module B (A:Dummy) <: Truc. Definition Y := A.Z. End B.
Module C (D:Truc) <: Super. Definition X := D.Y. End C.

Module Test : Super with X := A..
Declare Module A : Dummy.
Module BA := B A.
Include (C BA).
Lemma test : A.Z = X.
reflexivity.
Qed.
End Test.


Module Test (A:Dummy) := 
  C (B A).




Require Import List.

(** Module types *)

Module Type OrderedType.
Parameter T : Type.
Parameter compare : T -> T -> bool.
End OrderedType.

Module Type FSet.
Parameter Elt : Type.
Parameter T : Type.
Parameter empty : T.
Parameter add : Elt -> T -> T.
End FSet.

(** Module implementation *)

Module OrderedNat <: OrderedType.
Definition T := nat.
Definition compare (x y : nat) := true.
End OrderedNat.

Module FSetList (O:OrderedType) <: FSet.
Definition Elt := O.T.
Definition T := list Elt.
Definition empty : T := nil.
Definition add (x:Elt) (e:T) : T := 
  if O.compare x x then x::e else e.
End FSetList.

Module FsetNat := FSetList OrderedNat.


(** Module specification *)

Module Type OrderedTypeSpec.
Declare Module O : OrderedType.
Import O.
Parameter R : T -> T -> Prop.
Parameter R_spec : forall x y, R x y.
Parameter compare_spec : forall x y,
  compare x y = true <-> R x y.  
End OrderedTypeSpec.

Module Type FSetSpec.
Declare Module F : FSet.
Import F.
Parameter empty_not_add : forall x e,
  add x e <> empty.
End FSetSpec.


(** Module verification *)

Module OrderedNatSpec 
  <: OrderedTypeSpec with Module O := OrderedNat.
Module Import O := OrderedNat.
Definition R (x y : T) := True.
Lemma R_spec : forall x y, R x y.
Proof. unfold R. auto. Qed.
Lemma compare_spec : forall x y,
  compare x y = true <-> R x y.
Proof. intros. unfold R, compare. tauto. Qed.
End OrderedNatSpec.

(*
Declare Module O : OrderedType.
Print Module Type FSet.
Module X := FSetList O.
Print X.
*)

Module FSetListSpec (O:OrderedType) (OS:OrderedTypeSpec with Module O:=O) 
   : FSetSpec  with Module F := FSetList O with Definition F.Elt := O.T.
(* .  -- why fails?  
   <: FSetSpec with Definition F.Elt := O.T.  *)

Module Import F <: FSet := FSetList O.
Lemma empty_not_add : forall x e,
  add x e <> empty.
Proof. 
  unfold empty, add. intros.
  rewrite (proj2 (OS.compare_spec x x) (OS.R_spec x x)).
  intros K. inversion K.
Qed.
End FSetListSpec.

Module FSetNatSpec : FSetSpec with Module F := FsetNat 
  := FSetListSpec OrderedNat OrderedNatSpec.

Check FSetNatSpec.empty_not_add.







(*-----------------------------*)

Module Type OrderedType.
Parameter T : Type.
Parameter compare : T -> T -> bool.
End OrderedType.

Module OrderedNat <: OrderedType.
Definition T := nat.
Definition compare (x y : nat) := true.
End OrderedNat.


Module Type Map (O:OrderedType).
Parameter v : O.T.
End Map.

Module MyMap (O:OrderedType) : Map O.
Parameter v : O.T.
End MyMap.


Module MyMap2.
Declare Module O:OrderedType.
Parameter v : O.T.
End MyMap2.

Module Test (O:OrderedType) := MyMap2.

Module Test := (MyMap2 with Module O := OrderedNat).
Print Module Test.


(*-----------------------------*)




Module Type Stream.
Inductive stream := Nil | Cons : stream.
End Stream.

Module MyStream : Stream.
Inductive stream := Nil | Cons : stream.
End MyStream.

(*-----------------------------*)




Module Type T.
Parameter V : Type.
End T.

Module X <: T.
Definition V := nat.
End X.

Module Y <: T.
Definition V := bool.
End Y.


Module H (X:T) <: T.
Include X.
End H.

Module HX := H X.


Module Type R (Z:T).
Declare Module F : T.
Declare Module G : T.
Module H := Z.
Parameter U : G.V.
End R.


Module S : R X with Module F := HX with Module G := Y.
Module F := X.
Module G := Y.
Module H := X.
Definition U := true.
End S. 


Module Type Y.
Parameter T : Type.
End Y.
