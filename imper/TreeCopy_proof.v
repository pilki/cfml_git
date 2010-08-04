Set Implicit Arguments.
Require Import LibCore CFPrim TreeCopy_ml.


(*****************)

(** Tup3 *)

Definition Tup3 A1 A2 A3 a1 a2 a3 (T1:A1->a1->hprop) (T2:A2->a2->hprop) (T3:A3->a3->hprop) P p :=
  let '(X1,X2,X3) := P in let '(x1,x2,x3) := p in x1 ~> T1 X1 \* x2 ~> T2 X2 \* x3 ~> T3 X3.

Lemma focus_tup3 : forall a1 a2 a3 (p:a1*a2*a3) A1 A2 A3 (T1:htype A1 a1) (T2:htype A2 a2) (T3:A3->a3->hprop) V1 V2 V3,
  p ~> Tup3 T1 T2 T3 (V1,V2,V3) ==> let '(x1,x2,x3) := p in x1 ~> T1 V1 \* x2 ~> T2 V2 \* x3 ~> T3 V3.
Proof. auto. Qed.

Lemma unfocus_tup3 : forall a1 (x1:a1) a2 (x2:a2) a3 (x3:a3) A1 A2 A3 (T1:htype A1 a1) (T2:htype A2 a2) (T3:A3->a3->hprop) V1 V2 V3,
  x1 ~> T1 V1 \* x2 ~> T2 V2 \* x3 ~> T3 V3 ==> (x1,x2,x3) ~> Tup3 T1 T2 T3 (V1,V2,V3).
Proof. intros. unfold Tup3. hdata_simpl. auto. Qed.

Opaque Tup3.

(** Rec3 *)

Definition Rec3 A1 A2 A3 a1 a2 a3 (T1:A1->a1->hprop) (T2:A2->a2->hprop) (T3:A3->a3->hprop) P l :=
  l ~> Ref (Tup3 T1 T2 T3) P.

Lemma focus_rec3 : forall (l:loc) a1 a2 a3 A1 A2 A3 (T1:htype A1 a1) (T2:htype A2 a2) (T3:A3->a3->hprop) V1 V2 V3,
  l ~> Rec3 T1 T2 T3 (V1,V2,V3) ==> Hexists (x1:a1) (x2:a2) (x3:a3),
  l ~> Ref Id (x1,x2,x3) \* x1 ~> T1 V1 \* x2 ~> T2 V2 \* x3 ~> T3 V3.
Proof.
  intros. unfold Rec3. hdata_simpl. hchange (@focus_ref l). hextract as. 
  intros p [[x1 x2] x3] H. hchange (focus_tup3 p). destruct p as [[y1 y2] y3].
  inversions H. hsimpl~. 
Qed.

Lemma unfocus_rec3 : forall (l:loc) a1 (x1:a1) a2 (x2:a2) a3 (x3:a3) A1 A2 A3 (T1:htype A1 a1) (T2:htype A2 a2) (T3:A3->a3->hprop) V1 V2 V3,
  l ~> Ref Id (x1,x2,x3) \* x1 ~> T1 V1 \* x2 ~> T2 V2 \* x3 ~> T3 V3 ==>
  l ~> Rec3 T1 T2 T3 (V1,V2,V3).
Proof.
  intros. unfold Rec3. hdata_simpl. hchange (unfocus_tup3 x1 x2 x3). 
  hchange (@unfocus_ref l _ (x1,x2,x3)). hsimpl.
Qed.

Opaque Rec3.


(** Rec3 *)

Definition Ref3 A1 A2 A3 a1 a2 a3 (T1:A1->a1->hprop) (T2:A2->a2->hprop) (T3:A3->a3->hprop) (V1:A1) (V2:A2) (V3:A3) l :=
  l ~> Ref (Tup3 T1 T2 T3) (V1,V2,V3).

Lemma focus_ref3 : forall (l:loc) a1 a2 a3 A1 A2 A3 (T1:htype A1 a1) (T2:htype A2 a2) (T3:A3->a3->hprop) V1 V2 V3,
  l ~> Ref3 T1 T2 T3 V1 V2 V3 ==> Hexists (x1:a1) (x2:a2) (x3:a3),
  l ~> Ref Id (x1,x2,x3) \* x1 ~> T1 V1 \* x2 ~> T2 V2 \* x3 ~> T3 V3.
Proof.
  intros. unfold Ref3. hdata_simpl. hchange (@focus_ref l). hextract as. 
  intros p [[x1 x2] x3] H. hchange (focus_tup3 p). destruct p as [[y1 y2] y3].
  inversions H. hsimpl~. 
Qed.

Lemma unfocus_ref3 : forall (l:loc) a1 (x1:a1) a2 (x2:a2) a3 (x3:a3) A1 A2 A3 (T1:htype A1 a1) (T2:htype A2 a2) (T3:A3->a3->hprop) V1 V2 V3,
  l ~> Ref Id (x1,x2,x3) \* x1 ~> T1 V1 \* x2 ~> T2 V2 \* x3 ~> T3 V3 ==>
  l ~> Ref3 T1 T2 T3 V1 V2 V3.
Proof.
  intros. unfold Ref3. hdata_simpl. hchange (unfocus_tup3 x1 x2 x3). 
  hchange (@unfocus_ref l _ (x1,x2,x3)). hsimpl.
Qed.

Opaque Ref3.


(*
Definition Hor (H1 H2 : hprop) := fun h => H1 h \/ H2 h.
*)

Inductive tree A :=
  | Leaf : tree A
  | Node : A -> tree A -> tree A -> tree A.

Fixpoint Tree A a (T:htype A a) (t:tree A) (l:loc) : hprop :=
  match t with
  | Leaf => [l == null]
  | Node x t1 t2 => l ~> Ref3 T (Tree T) (Tree T) x t1 t2
  end.

Fixpoint tree_set A (t:tree A) : set A :=
  match t with
  | Leaf => \{}
  | Node x t1 t2 => \{x} \u (tree_set t1) \u (tree_set t2)
  end.

Definition TreeSet A a (T:htype A a) (E:set A) (l:loc) :=
  Hexists (t:tree A), l ~> Tree T t \* [E = tree_set t].
  

Lemma copy_tree_spec : forall a,
  Spec ListRev_ml.rev (l:mlist a) |R>> forall A (T:A->a->hprop) (L:list A),
     R (l ~> List T L) (~> List T (LibList.rev L)).
Proof.