open Okasaki
open OrderedSig
open FsetSig

module RedBlackSet (Element : Ordered) : Fset =
struct
   type elem = Element.t
   type color = Red | Black
   type tree = Empty | Node of color * tree * elem * tree
   type set = tree

   let empty = Empty

   let rec member x = function
      | Empty -> false
      | Node (_,a,y,b) -> 
         if Element.lt x y then member x a
         else if Element.lt y x then member x b
         else true

   let balance = function
     | (Black, Node (Red, Node (Red, a, x, b), y, c), z, d)
     | (Black, Node (Red, a, x, Node (Red, b, y, c)), z, d) 
     | (Black, a, x, Node (Red, Node (Red, b, y, c), z, d))
     | (Black, a, x, Node (Red, b, y, Node (Red, c, z, d))) ->
       Node (Red, Node (Black, a, x, b), y, Node (Black, c, z, d))
     | (c,a,x,y) -> Node (c,a,x,y)

   let rec insert x s =
      let rec ins = function
         | Empty -> Node (Red, Empty, x, Empty)
         | Node (col, a, y, b) as s ->
            if Element.lt x y then balance (col, ins a, y, b)
            else if Element.lt y x then balance (col, a, y, ins b)
            else s
         in
      match ins s with
      | Empty -> raise BrokenInvariant
      | Node (_, a, y, b) -> Node (Black, a, y, b)
end

