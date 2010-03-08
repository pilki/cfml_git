open Okasaki
open OrderedSig
open HeapSig

module SplayHeap (Element : Ordered) : Heap =
  (* (Heap with module Element = Element)*)
struct
   module Element = Element

   type heaps = Empty | Node of heaps * Element.t * heaps
   type heap = heaps (* todo *)

   let empty = Empty

   let is_empty = function
     | Empty -> true
     | _ -> false

   let rec partition pivot = function
      | Empty -> Empty, Empty
      | Node (a, x, b) as t ->
      if Element.leq x pivot then
         match b with
         | Empty -> t, Empty
         | Node (b1, y, b2) ->
            if Element.leq y pivot then
               let small, big = partition pivot b2 in
               Node (Node (a, x, b1), y, small), big
            else
               let small, big = partition pivot b1 in
               Node (a, x, small), Node (big, y, b2)
      else
         match a with
         | Empty -> Empty, t
         | Node (a1, y, a2) ->
            if Element.leq y pivot then
               let small, big = partition pivot a2 in
               Node (a1, y, small), Node (big, x, b)
            else
               let small, big = partition pivot a1 in
               small, Node (big, y, Node (a2, x, b))

   let insert x t = 
      let a, b = partition x t in 
      Node (a, x, b)

   let rec merge h1 h2 = 
      match h1, h2 with
      | Empty, _ -> h2
      | Node (a, x, b), _ ->
         let ta, tb = partition x h2 in
         Node (merge ta a, x, merge tb b)

   let rec find_min = function
      | Empty -> raise EmptyStructure
      | Node (Empty, x, b) -> x
      | Node (a, x, b) -> find_min a

   let rec delete_min = function
      | Empty -> raise EmptyStructure
      | Node (Empty, x, b) -> b
      | Node (Node (Empty, x, b), y, c) -> Node (b, y, c)
      | Node (Node (a, x, b), y, c) -> Node (delete_min a, x, Node (b, y, c))
  
end
