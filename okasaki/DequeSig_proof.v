Set Implicit Arguments.
Require Import FuncTactics DequeSig_ml LibCore.

Module Type QueueSigSpec.

Declare Module Q : MLDeque.
Import Q.

Global Instance deque_rep : forall `{Rep a_ A},  
  Rep (deque a_) (list A).

Section Polymorphic.
Variables (a_ A : Type) (RA:Rep a_ A).

Parameter empty_spec : 
  rep (@empty a_) (@nil A).

Parameter is_empty_spec : 
  RepTotal is_empty (Q;deque a_) >> bool_of (Q = nil).

Parameter cons_spec : 
  RepTotal cons (X;a_) (Q;deque a_) >> (X::Q) ; deque a_.

Parameter head_spec : 
  RepSpec head (Q;deque a_) |R>>
     Q <> (@nil A) -> R (is_head Q ;; a_).

Parameter tail_spec :
  RepSpec tail (Q;deque a_) |R>> 
     Q <> nil -> R (is_tail Q ;; deque a_).

Parameter snoc_spec : 
  RepTotal snoc (Q;deque a_) (X;a_) >> (Q&X) ; deque a_.

Parameter last_spec : 
  RepSpec last (Q;deque a_) |R>>
     Q <> (@nil A) -> R (is_last Q ;; a_).

Parameter init_spec :
  RepSpec init (Q;deque a_) |R>> 
     Q <> nil -> R (is_init Q ;; deque a_).

End Polymorphic.

End QueueSigSpec.





