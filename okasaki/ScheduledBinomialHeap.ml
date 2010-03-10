open Okasaki
open Stream
open OrderedSig
open HeapSig

module ScheduledBinomialHeap (Element : Ordered) : Heap =
  (* (Heap with module Element = Element)*)
struct
   module Element = Element

   type tree = Node of Element.t * tree list
   type digit = Zero | One of tree
   type schedule = digit stream list
   type heap = digit stream * schedule

   let empty = (lazy Nil, [])
   let is_empty = function
      | (lazy Nil, _) -> true
      | _ -> false

   let link (Node (x1, c1) as t1) (Node (x2, c2) as t2) =
      if Element.leq x1 x2 
         then Node (x1, t2::c1)
         else Node (x2, t1::c2)

   let rec ins_tree t = function
      | lazy Nil -> lazy (Cons (One t, lazy Nil))
      | lazy (Cons (Zero, ds)) -> lazy (Cons (One t, ds))
      | lazy (Cons (One t', ds)) -> lazy (Cons (Zero, ins_tree (link t t') ds))

   let rec mrg a b =
      match a,b with
      | lazy Nil, ds2 -> ds2
      | ds1, lazy Nil -> ds1
      | lazy (Cons (Zero, ds1)), lazy (Cons (d, ds2)) -> 
          lazy (Cons (d, (mrg ds1 ds2)))
      | lazy (Cons (d, ds1)), lazy (Cons (Zero, ds2)) -> 
          lazy (Cons (d, mrg ds1 ds2))
      | lazy (Cons (One t1, ds1)), lazy (Cons (One t2, ds2)) ->
          lazy (Cons (Zero, ins_tree (link t1 t2) (mrg ds1 ds2)))

   let rec normalize ds = 
      match ds with
      | lazy Nil -> ds
      | lazy (Cons (_, ds')) -> let _ = normalize ds' in ds

   let exec = function
      | [] -> []
      | lazy (Cons (Zero, job)) :: sched -> job :: sched
      | _ :: sched -> sched

   let insert x (ds, sched) =
      let ds' = ins_tree (Node (x, [])) ds in
      (ds', exec (exec (ds' :: sched)))

   let merge (ds1, _) (ds2, _) = 
      let ds = normalize (mrg ds1 ds2) in (ds, [])

   let rec remove_min_tree = function
      | lazy Nil -> raise EmptyStructure
      | lazy (Cons (One t, lazy Nil)) -> (t, lazy Nil)
      | lazy (Cons (Zero, ds)) ->
          let (t',ds') = remove_min_tree ds in
          (t', lazy (Cons (Zero, ds')))
      | lazy (Cons (One (Node (x,_) as t), ds)) ->
          match remove_min_tree ds with
          | (Node (x',_) as t', ds') ->
             if Element.leq x x'       
                then (t, lazy (Cons (Zero, ds)))
                else (t', lazy (Cons (One t, ds)))

   let find_min (ds, _) = 
      let Node (x, _), _ = remove_min_tree ds in x

   let delete_min (ds, _) =
      let Node (_, c), ds' = remove_min_tree ds in
      let ds'' = mrg (Stream.of_list (List.map (fun e -> One e) (List.rev c))) ds' in
      (normalize ds'', [])
end
