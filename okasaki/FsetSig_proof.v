Set Implicit Arguments.
Require Import FuncTactics FsetSig_ml LibCore.

Module Type FsetSigSpec.

Declare Module F : MLFset.
Import F.

Parameter T : Type.
Global Instance elem_rep : Rep elem T.
Global Instance set_rep : Rep set (LibSet.set T).

Parameter empty_spec : rep empty \{}.

Parameter insert_spec : 
  RepTotal insert (X;elem) (E;set) >>
    \{X} \u E ;- set.

Parameter member_spec : 
  RepTotal member (X;elem) (E;set) >> 
    bool_of (X \in E).

End FsetSigSpec.

