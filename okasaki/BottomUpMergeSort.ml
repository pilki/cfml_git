open Okasaki
open OrderedSig
open SortableSig

module BottomUpMergeSort (Element : Ordered) : Sortable =
 (* todo: with ... *)
struct

   module Element = Element

   type sortable = int * Element.t list list Lazy.t

   let rec mrg xs ys = 
      match xs, ys with
      | [], _ -> ys
      | _, [] -> xs
      | x::xs', y::ys' ->
         if Element.leq x y 
            then x :: mrg xs' ys
            else y :: mrg xs ys'

   let empty : sortable = (0, lazy [])

   let add x (size, segs) =
      let rec add_seg seg segs size =
         if size mod 2 = 0 
            then seg::segs
            else add_seg (mrg seg (List.hd segs)) (List.tl segs) (size / 2) in
      (size+1, lazy (add_seg [x] (!$segs) size))

   let sort (size, segs) =
      let rec mrg_all xs = function
         | [] -> xs
         | seg::segs -> mrg_all (mrg xs seg) segs 
         in
      mrg_all [] !$segs

end


