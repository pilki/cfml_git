Set Implicit Arguments.
Require Import LibCore CFPrim TreeCopy_ml.


(*****************)

Lemma rev_spec : forall a,
  Spec ListRev_ml.rev (l:mlist a) |R>> forall A (T:A->a->hprop) (L:list A),
     R (l ~> List T L) (~> List T (LibList.rev L)).
Proof.