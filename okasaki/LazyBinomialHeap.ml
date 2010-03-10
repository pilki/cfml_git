open Okasaki
open OrderedSig
open HeapSig

module LazyBinomialHeap (Element : Ordered) : Heap =
  (* (Heap with module Element = Element)*)
struct
   module Element = Element

   type tree = Node of int * Element.t * tree list
   type heap = tree list Lazy.t

   let empty : heap = lazy []

   let is_empty : heap -> bool = function
     | lazy [] -> true
     | _ -> false

   let rank (Node(r,x,c)) = r

   let root (Node(r,x,c)) = x

   let link (Node (r,x1,c1) as t1) (Node (_,x2,c2) as t2) =
      if Element.leq x1 x2 
         then Node (r+1, x1, t2::c1)
         else Node (r+1, x2, t1::c2)

   let rec ins_tree t = function
      | [] -> [t]
      | t'::ts' as ts ->
         if rank t < rank t' 
            then t::ts
            else ins_tree (link t t') ts'

   let insert x ts = 
      lazy (ins_tree (Node (0, x, [])) (!$ ts))

   let rec mrg ts1 ts2 =
      match ts1, ts2 with
      | _, [] -> ts1
      | [], _ -> ts2
      | t1::ts1', t2::ts2' ->
         if rank t1 < rank t2 then t1 :: mrg ts1' ts2
         else if rank t2 < rank t1 then t2 :: mrg ts1 ts2'
         else ins_tree (link t1 t2) (mrg ts1' ts2')
   
   let merge ts1 ts2 =
      lazy (mrg (!$ ts1) (!$ ts2))

   let rec remove_min_tree = function
      | [] -> raise EmptyStructure
      | [t] -> t, []
      | t::ts ->
         let t',ts' = remove_min_tree ts in
         if Element.leq (root t) (root t')
            then (t, ts)
            else (t', t::ts')

   let find_min ts =
      let t,_ = remove_min_tree (!$ ts) in root t

   let delete_min ts =
      let Node(_,x,ts1),ts2 = remove_min_tree (!$ ts) in
      merge (List.rev ts1) ts2

end

