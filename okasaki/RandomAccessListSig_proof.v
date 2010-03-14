Set Implicit Arguments.
Require Import FuncTactics RandomAccessListSig_ml LibCore.

Module Type RandomAccessListSigSpec.

Declare Module R : MLRandomAccessList.
Import R.

Global Instance rlist_rep : forall `{Rep a A},  
  Rep (rlist a) (list A).

Section Polymorphic.
Variables (a A : Type) (RA:Rep a A).

Parameter empty_spec : 
  rep (@empty a) (@nil A).

Parameter is_empty_spec : 
  RepTotal is_empty (L;rlist a) >> bool_of (L = nil).

Parameter cons_spec : 
  RepTotal cons (X;a) (L;rlist a) >> (X::L) ; rlist a.

Parameter head_spec : 
  RepSpec head (L;rlist a) |R>>
     L <> nil -> R (is_head L ;; a).

Parameter tail_spec :
  RepSpec tail (L;rlist a) |R>> 
     L <> nil -> R (is_tail L ;; rlist a).

Parameter lookup_spec : 
  RepSpec lookup (i;int) (L;rlist a) |R>>
     0 <= i -> i < length L -> R (Nth (abs i) L ;; a).

Parameter update_spec :
  RepSpec update (i;int) (X;a) (L;rlist a) |R>> 
     0 <= i -> i < length L -> R (Update (abs i) X L ;; rlist a).

End Polymorphic.

End RandomAccessListSigSpec.
