Set Implicit Arguments.
Require Import CFPrim StrongUpdate_ml.


(********************************************************************)
(* ** test_strong *)

Lemma test_strong_spec : 
  Spec test_strong () |R>> R [] (\=12).
Proof.
  xcf.
  xapp.
  xapp.
  xapp. intro_subst.
  xlet. xret. xextract. intro_subst.
  xapp.
  xapp. intro_subst.
  xapp. 
  xapp. intro_subst. (* by default! --todo *)
  xlet. xif. xret.
  xret_gc. hextract. hsimpl. math.
Qed.
