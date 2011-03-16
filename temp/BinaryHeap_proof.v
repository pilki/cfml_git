Spec empty () |R>> 
  R [] (_~> Heap \{})

Spec insert l v |R>> forall E, 
  R (l ~> Heap E) (# l ~> Heap (E \u v))

Spec extract l |R>> forall E, 
  R (l ~> Heap E) (fun v => 
    hexists E', l ~> Heap E' * [removed_min E E' V])

Definition removed_min E E' V :=
  E = E' \u V /\ (forall_ V' \in E, V <= V').

-----

Spec empty () |R>> 
  forall T, R [] (_~> Heap T \{})


Spec insert l v |R>> forall T E V, 
  R (l ~> Heap T E * T V v) (# l ~> Heap T (E \u V))

Spec extract l |R>> forall T E, 
  R (l ~> Heap T E) (fun v => 
    hexists E' V, l ~> Heap T E' * T V v * [removed_min E E' V])

-------
