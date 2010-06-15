

Definition partition A := set (set A).



Definition union_find_graph (Parent : int array) (G : sgraph int) :=
     nodes G = range 0 (size Parent - 1)
  /\ forest (transpose G)
  /\ forall_ x \in nodes G, Parent\[x] \in nodes G
                         /\ outgoing G x = Parent\[x].

     (* edges G = \{ (x,Parent\[x]) | x \in nodes G } *)


Definition Struct (P:partition int) (l:loc) :=
  hexists nb_compo parent Parent G,
    l ~> state_of nb_compo parent
  * parent ~> Array Pure Parent
  * [ union_find_graph Parent G ]
  * [ P = equiv_classes (unweighed_of G) ]
  * [ nb_compo = card P ].


Definition full_partition (E:set A) :=
  (* returns {{x1},{x2},..,{xn}} when
     E is {x1,x2,..xn} *) .

Definition partition_item (P:set (set A)) (x:A) :=
  exists_ E \in P, x \in E.

Definition partition_merge P x y :=
  (* returns a new partition where the set containing x
     has been merged with the set containing y *) 

Definition partition_same P x y :=
  exists_ E \in P /\ x \in E /\ y \in E.

Lemma create_spec :
  Spec create n |R>> n >= 0 ->
    R [] (_~> Struct (full_partition (range 0 (n-1)))).

Lemma union_spec : 
  Spec union s a b |R>> forall P,
    partition_item P a -> partition_item P b ->
    R (s ~> Struct P) (s ~> Struct (partition_merge P a b)).
    
Lemma same_compo_spec :
  Spec same_compo s a b |R>> forall P,
    partition_item P a -> partition_item P b ->
    keep R (s ~> Struct P) (bool_of (partition_same P a b)). 


(* variante:
Lemma union_spec : 
  Spec union s a b |R>> forall E P,
    a \in E -> b \in E -> partition_of E P ->
    R (s ~> Struct P) (s ~> Struct (partition_merge P a b)).
*)