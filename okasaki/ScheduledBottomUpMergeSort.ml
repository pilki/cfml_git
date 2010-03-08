open Okasaki
open Stream
open OrderedSig
open SortableSig

module ScheduledBottomUpMergeSort (Element : Ordered) : Sortable =
 (* todo: with ... *)
struct

   module Element = Element

   type schedule = Element.t stream list
   type sortable = int * (Element.t stream * schedule) list

   let rec mrg xs ys = 
      match xs, ys with
      | lazy Nil, _ -> ys
      | _, lazy Nil -> xs
      | lazy (Cons(x,xs')), lazy (Cons(y,ys')) ->
         if Element.leq x y 
            then lazy (Cons (x, mrg xs' ys))
            else lazy (Cons (y, mrg xs ys'))

   let rec exec1 = function
      | [] -> []
      | lazy Nil :: sched -> exec1 sched
      | lazy (Cons(x,xs)) :: sched -> xs :: sched

   let exec2 (xs, sched) =    
      xs, exec1 (exec1 sched)

   let empty : sortable = (0, [])

   let add x (size, segs) =
      let rec add_seg xs segs size rsched =
         if size mod 2 = 0 
            then (xs, List.rev rsched) :: segs 
            else match segs with
                 | (xs',[])::segs' ->
                   let xs'' = mrg xs xs' in
                   add_seg xs'' segs' (size / 2) (xs''::rsched)
                 | _ -> raise BrokenInvariant
         in
      let segs' = add_seg (lazy (Cons (x, lazy Nil))) segs size [] in
      (size + 1, List.map exec2 segs')

   let sort (size, segs) =
      let rec mrg_all xs = function
         | [] -> xs
         | (xs',_)::segs -> mrg_all (mrg xs xs') segs
         in
      Stream.to_list (mrg_all (lazy Nil) segs)

end


