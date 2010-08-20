Set Implicit Arguments.
Require Import CFPrim StrongUpdate_ml.

Opaque Zplus Ref.

(*todo:remove*)
Ltac xapps_core spec args solver ::=
  let cont1 tt :=
    xapp_with spec args solver in
  let cont2 tt :=
    instantiate; xextract; try intro_subst in    
  match ltac_get_tag tt with
  | tag_let_trm => xlet; [ cont1 tt | cont2 tt ]
  | tag_seq =>     xseq; [ cont1 tt | cont2 tt ]
  end.


(********************************************************************)
(* ** test_strong *)

Lemma test_strong_spec : 
  Spec test_strong () |R>> R [] (\=12).
Proof.
  xcf.
  xapp.
  xapp.
  xapps.
  xlet. xret.
  xextract. intro_subst.
  xapp.
  xapps.
  xapp. 
  xapps.
  xlet. xif. xret.
  xret_gc. xsimpl. math.
Qed.
