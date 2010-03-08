open Okasaki
open OrderedSig
open HeapSig

module LeftistHeap (Element : Ordered) : Heap =
  (* (Heap with module Element = Element) *)
struct
  module Element = Element

  (*todo*)
  type heaps = Empty | Node of int * Element.t * heaps * heaps
  type heap = heaps

  let rank = function 
     | Empty -> 0 
     | Node (r,_,_,_) -> r

  let make_node x a b =
    if rank a >= rank b 
       then Node (rank b + 1, x, a, b)
       else Node (rank a + 1, x, b, a)

  let empty = Empty

  let is_empty = function
     | Empty -> true
     | _ -> false

  let rec merge h1 h2 = 
    match h1, h2 with
    | _, Empty -> h1
    | Empty, _ -> h2
    | Node (_, x, a1, b1), Node (_, y, a2, b2) ->
        if Element.leq x y 
           then make_node x a1 (merge b1 h2)
           else make_node y a2 (merge h1 b2)

  let insert x h = 
     merge (Node (1, x, Empty, Empty)) h

  let find_min = function 
     | Empty -> raise EmptyStructure 
     | Node (_, x, _, _) -> x
  
  let delete_min = function 
     | Empty -> raise EmptyStructure 
     | Node (_, x, a, b) -> merge a b
end