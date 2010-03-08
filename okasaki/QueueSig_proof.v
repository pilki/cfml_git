Set Implicit Arguments.
Require Import FuncTactics QueueSig_ml LibCore.

Module Type QueueSigSpec.

Declare Module Q : MLQueue.
Import Q.

Global Instance queue_rep : forall `{Rep a_ A},  
  Rep (queue a_) (list A).

Section Polymorphic.
Variables (a_ A : Type) (RA:Rep a_ A).

Parameter empty_spec : 
  rep (@empty a_) (@nil A).

Parameter is_empty_spec : 
  RepTotal is_empty (Q;queue a_) >> bool_of (Q = nil).

Parameter snoc_spec : 
  RepTotal snoc (Q;queue a_) (X;a_) >> (Q&X) ; queue a_.

Parameter head_spec : 
  RepSpec head (Q;queue a_) |R>>
     Q <> (@nil A) -> R (is_head Q ;; a_).

Parameter tail_spec :
  RepSpec tail (Q;queue a_) |R>> 
     Q <> nil -> R (is_tail Q ;; queue a_).

End Polymorphic.

End QueueSigSpec.





