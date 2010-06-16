
Spec empty () |R>> 
  R [] (_~> Tree \{})

Spec get l k |R>> forall M, 
  R (l ~> Tree M) (fun o => l ~> Tree M * [o = map_get_option M k])

  keep R (l ~> Tree M) (= map_get_option M k)

Spec set l k v |R>> forall M,
  R (l ~> Tree M) (# l ~> Tree (M \u \[k := v]))

Spec rem l k |R>> forall M,
  R (l ~> Tree M) (l ~> Tree (M \rem l))


l ~> Tree M  
Tree M l
exists n, TreeRec n Black M l

TreeRec n c M l : hprop = hexists o,
  l ~> o *
  match o with
  | None => [n = 1 /\ c = Black]
  | Some (k,v,l1,l2,c') =>
     hexists c1 c2 M1 M2 n',
       l1 ~> TreeRec n' c1 M1 
     * l2 ~> TreeRec n' c2 M2
     * [ c' = c
      /\ n' = (if c = Black then n-1 else n)
      /\ (c = Red -> c1 = Black /\ c2 = Black)
      /\ foreach M1 (fun k' v' => k' < k)
      /\ foreach M2 (fun k' v' => k' > k)
      /\ M = M1 \u M2 \u \[k:=v]
      ]

