open OrderedSig
open FsetSig

module UnbalancedSet (Element : Ordered) : Fset =
struct
   type elem = Element.t
   type tree = Empty | Node of tree * elem * tree
   type set = tree

   let empty = Empty

   let rec member x = function
      | Empty -> false
      | Node (a,y,b) -> 
         if Element.lt x y then member x a
         else if Element.lt y x then member x b
         else true

   let rec insert x = function
      | Empty -> Node (Empty,x,Empty)
      | Node (a,y,b) as s ->
         if Element.lt x y then Node (insert x a, y, b)
         else if Element.lt y x then Node (a, y, insert x b)
         else s
end

