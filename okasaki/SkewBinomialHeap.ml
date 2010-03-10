open Okasaki
open OrderedSig
open HeapSig

module BinomialHeap (Element : Ordered) : Heap =
  (* (Heap with module Element = Element)*)
struct
   module Element = Element

   type tree = Node of int * Element.t * Element.t list * tree list
   type heap = tree list

   let empty : heap = []

   let is_empty : heap -> bool = function 
      | [] -> true
      | _ -> false

   let rank (Node (r, _, _, _)) = r

   let root (Node (_, x, _, _)) = x

   let link (Node (r, x1, xs1, c1) as t1) (Node (_, x2, xs2, c2) as t2) =
      if Element.leq x1 x2 
         then Node (r+1, x1, xs1, t2::c1)
         else Node (r+1, x2, xs2, t1::c2)

   let skew_link x t1 t2 =
      let Node (r, y, ys, c) = link t1 t2 in
      if Element.leq x y
         then Node (r, x, y::ys, c)
         else Node (r, y, x::ys, c)

   let rec ins_tree t1 = function
      | [] -> [t1]
      | t2 :: ts ->
         if rank t1 < rank t2
            then t1 :: t2 :: ts
            else ins_tree (link t1 t2) ts

   let rec merge_trees ts1 ts2 = 
      match ts1, ts2 with
      | _, [] -> ts1
      | [], _ -> ts2
      | t1 :: ts1', t2 :: ts2' ->
         if rank t1 < rank t2 then t1 :: merge_trees ts1' ts2
         else if rank t2 < rank t1 then t2 :: merge_trees ts1 ts2'
         else ins_tree (link t1 t2) (merge_trees ts1' ts2')

   let normalize = function
      | [] -> []
      | t :: ts -> ins_tree t ts

   let insert x = function
   | t1 :: t2 :: rest as ts ->
      if rank t1 = rank t2 
         then skew_link x t1 t2 :: rest
         else Node (0, x, [], []) :: ts
   | ts -> Node (0, x, [], []) :: ts

   let merge ts1 ts2 = 
      merge_trees (normalize ts1) (normalize ts2)

   let rec remove_min_tree = function
      | [] -> raise EmptyStructure
      | [t] -> t, []
      | t :: ts ->
         let t', ts' = remove_min_tree ts in
         if Element.leq (root t) (root t') 
            then t, ts 
            else t', t :: ts'

   let find_min ts = 
      let (t,_) = remove_min_tree ts in root t

   let delete_min ts =
      let Node (_, x, xs, ts1), ts2 = remove_min_tree ts in
      let rec insert_all ts = function
         | [] -> ts
         | x :: xs' -> insert_all (insert x ts) xs' in
      insert_all (merge (List.rev ts1) ts2) xs
end