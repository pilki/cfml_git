open Okasaki
open OrderedSig
open HeapSig

module PairingHeap (Element : Ordered) : Heap =
  (* (Heap with module Element = Element)*)
struct
  module Element = Element

  (*todo*)
  type heaps = Empty | Node of Element.t * heaps list
  type heap = heaps

  let empty = Empty

  let is_empty = function
     | Empty -> true
     | _ -> false

  let merge h1 h2 = 
     match h1, h2 with
     | _, Empty -> h1
     | Empty, _ -> h2
     | Node (x, hs1), Node (y, hs2) ->
         if Element.leq x y 
            then Node (x, h2 :: hs1)
            else Node (y, h1 :: hs2)

  let insert x h = 
     merge (Node (x, [])) h

  let rec merge_pairs = function
     | [] -> Empty
     | [h] -> h
     | h1::h2::hs -> merge (merge h1 h2) (merge_pairs hs)

  let find_min = function 
     | Empty -> raise EmptyStructure 
     | Node (x, _) -> x
  
  let delete_min = function 
     | Empty -> raise EmptyStructure 
     | Node (x, hs) -> merge_pairs hs

end