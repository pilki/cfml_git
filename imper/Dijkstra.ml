module type Ordered =
sig 
   type t
   val eq : t -> t -> bool
   val lt : t -> t -> bool
   val leq : t -> t -> bool
end 

module type Heap =
sig
  module Element : Ordered
  type heap
  val create : unit -> heap
  val is_empty : heap -> bool
  val push : Element.t -> heap -> unit
  val top : heap -> Element.t 
  val pop : heap -> Element.t 
end

type weight = Finite of int | Infinite

module Dist : Ordered with type t = weight =
struct
  type t = weight
  let eq d1 d2 = match d1,d2 with
     | Finite x, Finite y -> x = y
     | Infinite, Infinite -> _
  let lt d1 d2 = match d1,d2 with
     | Finite x, Finite y -> x < y
     | Finite x, Infinite -> true
     | Infinite, _ -> false
  let leq d1 d2 = eq d1 d2 || lt d1 d2
end

module Dijkstra (Heap:HeapSig) = 
struct
   type edge = (int * int)
   type graph = (edge list) array
   
   let shortest_path (g:graph) source dest = 
      let nb_nodes = Array.length g in
      let dist = Array.make nb_nodes Infinite in
      let treated = Array.make nb_nodes false in
      let next = Heap.create() in
      Heap.push next (source,0);
      let finished = ref false in
      while not finished do
         let (node,node_dist) = Heap.pop next in
         if not treated.(node) then begin
            treated.(node) <- true;
            List.iter (fun (edge_dest,edge_dist) ->
               let new_dist = node_dist + edge_dist in
               if Dist.lt (Finite new_dist) dist.(edge_dest)
                  then (dist.(edge_dest) <- Finite new_dist;
                        Heap.push next (edge_dest,new_dist))
               ) (g.(node));
         end;
         if Heap.is_empty next || treated.(dest) 
            then finished := true
      done;
      dist.(dest)
end
