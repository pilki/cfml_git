
(* G is a graph where nodes are indexed by location and contain integers, 
   and where edges are not indexed and not weighted *)

Definition weight_accessibles G x :=
  big_sum (accessible G x) (weight G).

Definition node_inv G (x:loc) (c:cell) :=
     weight G x = value c
  /\ outgoing G x = children c
  /\ incoming G x = set_of_option (parent c)
  /\ total c = weight_accessibles G x.

Definition Composite (G : nw_s_graph loc int) :=
  hexists M : map loc cell, Group M *
    [ nodes G = dom M 
    /\ forest G
    /\ foreach (nodes G) (fun x => node_inv G x (M\[x])) ].


(* termination: length of (the unique) path in "transpose G" from x *)

Lemma create_spec :
  Spec create v |R>> forall G,
    R (Composite G) (fun l => Composite (add_node G l v)).

Lemma add_child_spec :
  Spec add_child p c |R>> forall G,
    p \in nodes G -> c \in nodes G ->
    R (Composite G) (# Composite (add_edge G p c)).

Lemma update_spec :
  Spec update n v |R>> forall G,
    n \in nodes G ->
    R (Composite G) (# Composite (update_weight G n v)).

Lemma disloge_spec :
  Spec disloge c |R>> forall G,
    c \in nodes G ->
    R (Composite G) (# Composite (rem_incoming_edges G c)).


