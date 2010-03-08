Set Implicit Arguments.
Require Import FuncTactics demo_ml.

Lemma f_spec : forall A,
   Total f (x:A) >> = x.
Proof. xgo~. Qed.
