Set Implicit Arguments.
Require Import FuncTactics QueueSig_ml LibCore.

Module Type QueueSigSpec.

Declare Module Q : MLQueue.
Import Q.

Global Instance queue_rep : forall `{Rep a A},  
  Rep (queue a) (list A).

Section Polymorphic.
Variables (a A : Type) (RA:Rep a A).

Parameter empty_spec : 
  rep (@empty a) (@nil A).

Parameter is_empty_spec : 
  RepTotal is_empty (Q;queue a) >> bool_of (Q = nil).

Parameter snoc_spec : 
  RepTotal snoc (Q;queue a) (X;a) >> (Q&X) ;- queue a.

Parameter head_spec : 
  RepSpec head (Q;queue a) |R>>
     Q <> nil -> R (is_head Q ;; a).

Parameter tail_spec :
  RepSpec tail (Q;queue a) |R>> 
     Q <> nil -> R (is_tail Q ;; queue a).

End Polymorphic.

End QueueSigSpec.




