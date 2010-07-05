module type Ordered =
sig 
   type t
   val le : t -> t -> bool
end 

module type HeapSig =
sig
  module Element : Ordered
  type heap
  val create : unit -> heap
  val is_empty : heap -> bool
  val push : Element.t -> heap -> unit
  val pop : heap -> Element.t 
end

(* todo: gérer un context pour savoir si on est dans un module ou pas *)





module Item = (* : Ordered with type t = (int*int) *)
struct
  type t = int*int
  let le : t -> t -> bool =
     fun (_,x1) (_,x2) -> (x1 <= x2)
end

module type HeapItems = (* HeapSig with module Element = Item *)
sig
  type heap
  val create : unit -> heap
  val is_empty : heap -> bool
  val push : Item.t -> heap -> unit
  val pop : heap -> Item.t 
end



module Dijkstra (Heap:HeapItems) = 
struct

   type weight = Finite of int | Infinite

   let weight_lt d1 d2 =
      match d1,d2 with
        | Finite x, Finite y -> x < y
        | Finite x, Infinite -> true
        | Infinite, _ -> false

   type edge = (int * int)
   type graph = (edge list) array
   
   let shortest_path (g:graph) source dest = 
      let nb_nodes = Array.length g in
      let dist = Array.make nb_nodes Infinite in
      let treated = Array.make nb_nodes false in
      let next = Heap.create() in
      Heap.push (source,0) next;
      let finished = ref false in
      while not !finished do
         let (node,node_dist) = Heap.pop next in
         if not treated.(node) then begin
            treated.(node) <- true;
            List.iter (fun (edge_dest,edge_dist) ->
               let new_dist = node_dist + edge_dist in
               if weight_lt (Finite new_dist) dist.(edge_dest)
                  then (dist.(edge_dest) <- Finite new_dist;
                        Heap.push (edge_dest,new_dist) next)
               ) (g.(node));
         end;
         if Heap.is_empty next || treated.(dest) 
            then finished := true
      done;
      dist.(dest)
end


   (*
   let weight_le d1 d2 =
      match d1,d2 with
        | Finite x, Finite y -> x <= y
        | Finite x, Infinite -> true
        | Infinite, Finite _ -> false
        | Infinite, Infinite -> true
  *)

