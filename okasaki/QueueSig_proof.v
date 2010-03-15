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
  RepTotal snoc (Q;queue a) (X;a) >> (Q&X) ; queue a.

Parameter head_spec : 
  RepSpec head (Q;queue a) |R>>
     Q <> nil -> R (is_head Q ;; a).

Parameter tail_spec :
  RepSpec tail (Q;queue a) |R>> 
     Q <> nil -> R (is_tail Q ;; queue a).

End Polymorphic.

End QueueSigSpec.


(** The same signature, but with an explicit type for
    the implementation of Queue, to work around the fact
    that Coq does not carry "positivity" information 
    about type constructors in signatures. *)

Module Type QueueBisSigSpec.

Declare Module Q : MLQueueBis.
Import Q.

Definition queue_rep : forall `{Rep a A},  
  Rep (queue a) (list A) 
  := fun a A H => list_rep (H:=H).

Existing Instance queue_rep. 

Section Polymorphic.
Variables (a A : Type) (RA:Rep a A).

Parameter empty_spec : 
  rep (@empty a) (@nil A).

Parameter is_empty_spec : 
  RepTotal is_empty (Q;queue a) >> bool_of (Q = nil).

Parameter snoc_spec : 
  RepTotal snoc (Q;queue a) (X;a) >> (Q&X) ; queue a.

Parameter head_spec : 
  RepSpec head (Q;queue a) |R>>
     Q <> nil -> R (is_head Q ;; a).

Parameter tail_spec :
  RepSpec tail (Q;queue a) |R>> 
     Q <> nil -> R (is_tail Q ;; queue a).

End Polymorphic.

End QueueBisSigSpec.



