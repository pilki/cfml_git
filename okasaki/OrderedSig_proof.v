Set Implicit Arguments.
Require Import FuncTactics OrderedSig_ml LibCore.

Module Type OrderedSigSpec.

Declare Module O : MLOrdered.
Import O.
Parameter T : Type.
Global Instance rep_t : Rep t T.

Global Instance le_inst : Le T.
Global Instance le_order : Le_total_order.

Parameter eq_spec : RepTotal eq (X;t) (Y;t) >> bool_of (X = Y).
Parameter lt_spec : RepTotal lt (X;t) (Y;t) >> bool_of (LibOrder.lt X Y).
Parameter leq_spec : RepTotal leq (X;t) (Y;t) >> bool_of (LibOrder.le X Y).

Hint Extern 1 (RegisterSpec eq) => Provide eq_spec.
Hint Extern 1 (RegisterSpec lt) => Provide lt_spec.
Hint Extern 1 (RegisterSpec leq) => Provide leq_spec.

End OrderedSigSpec.
