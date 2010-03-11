Set Implicit Arguments.
Require Import FuncTactics DequeSig_ml LibCore.

Module Type DequeSigSpec.

Declare Module Q : MLDeque.
Import Q.

Global Instance deque_rep : forall `{Rep a A},  
  Rep (deque a) (list A).

Section Polymorphic.
Variables (a A : Type) (RA:Rep a A).

Parameter empty_spec : 
  rep (@empty a) (@nil A).

Parameter is_empty_spec : 
  RepTotal is_empty (Q;deque a) >> bool_of (Q = nil).

Parameter cons_spec : 
  RepTotal cons (X;a) (Q;deque a) >> (X::Q) ; deque a.

Parameter head_spec : 
  RepSpec head (Q;deque a) |R>>
     Q <> nil -> R (is_head Q ;; a).

Parameter tail_spec :
  RepSpec tail (Q;deque a) |R>> 
     Q <> nil -> R (is_tail Q ;; deque a).

Parameter snoc_spec : 
  RepTotal snoc (Q;deque a) (X;a) >> (Q&X) ; deque a.

Parameter last_spec : 
  RepSpec last (Q;deque a) |R>>
     Q <> nil -> R (is_last Q ;; a).

Parameter init_spec :
  RepSpec init (Q;deque a) |R>> 
     Q <> nil -> R (is_init Q ;; deque a).

End Polymorphic.

End DequeSigSpec.





