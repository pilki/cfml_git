open Okasaki
open RandomAccessListSig

module SkewBinaryRandomAccesList : RandomAccesList =
struct

   type 'a tree = Leaf of 'a | Node of 'a * 'a tree * 'a tree
   type 'a rlist = (int * 'a tree) list 

   let empty : 'a rlist = []

   let is_empty = function 
      | [] -> true
      | _ -> false

   let cons x = function
      | ((w1,t1)::(w2,t2)::ts') as ts -> 
         if w1 = w2 
            then (1+w1+w2, Node(x,t1,t2)) :: ts'
            else (1, Leaf x) :: ts
      | ts -> (1, Leaf x) :: ts

   let head = function
      | [] -> raise EmptyStructure
      | (1, Leaf x)::ts -> x
      | (w, Node(x,t1,t2))::ts -> x
      | _ -> raise BrokenInvariant

   let tail = function
      | [] -> raise EmptyStructure
      | (1, Leaf x)::ts -> ts
      | (w, Node(x,t1,t2))::ts -> (w/2,t1)::(w/2,t2)::ts
      | _ -> raise BrokenInvariant

   let rec lookupTree w i t = 
      match (w,t) with
      | (1, Leaf x) -> 
         if i = 0 then x else raise OutOfBound
      | (w, Node (x,t1,t2)) ->
         let w' = w/2 in
         if i = 0 then x 
         else if i <= w' then lookupTree w' (i-1) t1
         else lookupTree w' (i-1-w') t2
      | _ -> raise BrokenInvariant

   let rec updateTree w i y t = 
      match (w,t) with
      | (1, Leaf x) -> 
         if i = 0 then Leaf y else raise OutOfBound
      | (w, Node (x,t1,t2)) ->
         let w' = w/2 in
         if i = 0 then Node(y,t1,t2)
         else if i <= w' then Node (x, updateTree w' (i-1) y t1, t2)
         else Node (x, t1, updateTree w' (i-1-w') y t2)
      | _ -> raise BrokenInvariant

   let rec lookup i = function
      | [] -> raise OutOfBound
      | (w,t)::ts -> 
          if i < w 
             then lookupTree w i t
             else lookup (i-w) ts

   let rec update i y = function
      | [] -> raise OutOfBound
      | (w,t)::ts -> 
          if i < w 
             then (w, updateTree w i y t)::ts
             else (w,t) :: (update (i-w) y ts)

end

