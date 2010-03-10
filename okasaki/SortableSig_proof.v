Set Implicit Arguments.
Require Import FuncTactics SortableSig_ml OrderedSig_ml OrderedSig_proof.

Module Type SortableSigSpec.

Declare Module H : MLSortable.
Declare Module OS : OrderedSigSpec with Module O := H.MLElement.
Import H MLElement OS. 

Definition is_ge (X Y:T) := X <= Y.

Inductive sorted : list T -> multiset T -> Prop :=
  | sorted_nil : sorted nil \{}
  | sorted_cons : forall S X E,
      sorted S E ->
      foreach (is_ge X) E ->
      sorted (X::S) (\{X} \u E).

Global Instance heap_rep : Rep sortable (multiset T).

Parameter empty_spec : rep empty \{}.

Parameter add_spec : RepTotal add (X;t) (E;sortable) >>
  \{X} \u E ; sortable.

Parameter sort_spec : RepTotal sort (E;sortable) >>
  ((fun L => sorted L E) ;; list t).

End SortableSigSpec.
