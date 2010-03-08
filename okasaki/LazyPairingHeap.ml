open Okasaki
open OrderedSig
open HeapSig

module LazyPairingHeap (Element : Ordered) : Heap =
  (* (Heap with module Element = Element)*)
struct

   module Element = Element

   type heap = Empty | Node of Element.t * heap * heap Lazy.t

   let empty = Empty

   let is_empty = function
      | Empty -> true
      | _ -> false

   let rec merge a b = 
      match a, b with
      | _, Empty -> a
      | Empty, _ -> b
      | Node (x, _, _), Node (y, _, _) -> 
         if Element.leq x y 
            then link a b 
            else link b a

   and link h a = 
      match h with
      | Node (x, Empty, m) -> Node (x, a, m)
      | Node (x, b, m) -> Node (x, Empty, lazy (merge (merge a b) !$m))
      | _ -> raise BrokenInvariant

   let insert x a = 
      merge (Node (x, Empty, lazy Empty)) a

   let find_min = function 
      | Empty -> raise EmptyStructure
      | Node (x, _, _) -> x

   let delete_min = function 
      | Empty -> raise EmptyStructure
      | Node (_, a, lazy b) -> merge a b

end
