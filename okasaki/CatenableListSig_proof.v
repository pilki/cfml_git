Set Implicit Arguments.
Require Import FuncTactics CatenableListSig_ml LibCore.

Module Type CatenableListSigSpec.

Declare Module C : MLCatenableList.
Import C. 

Global Instance cat_rep : forall `{Rep a A},  
  Rep (cat a) (list A).

Section Polymorphic.
Variables (a A : Type) (RA:Rep a A).

Parameter empty_spec : 
  rep (@empty a) (@nil A).

Parameter is_empty_spec : 
  RepTotal is_empty (L;cat a) >> bool_of (L = nil).

Parameter cons_spec : 
  RepTotal cons (X;a) (L;cat a) >> (X::L) ; cat a.

Parameter snoc_spec : 
  RepTotal snoc (L;cat a) (X;a) >> (L&X) ; cat a.

Parameter append_spec : 
  RepTotal append (L1;cat a) (L2;cat a) >> (L1++L2) ; cat a.

Parameter head_spec : 
  RepSpec head (L;cat a) |R>>
     L <> nil -> R (is_head L ;; a).

Parameter tail_spec :
  RepSpec tail (L;cat a) |R>> 
     L <> nil -> R (is_tail L ;; cat a).

End Polymorphic.

End CatenableListSigSpec.





