Set Implicit Arguments.
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

Module FSetListSpec (O:OrderedType) (OS:OrderedTypeSpec with Module O:=O) 
  (*: FSetSpec with Module F := FSetList O. -- why fails? *)
   <: FSetSpec.  
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






