module type Ordered =
sig 
   type t
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

type len = Finite of int | Infinite

module NextNode : Ordered with type t = int * int
struct
   type t = int * int
   let le (_,d1) (_,d2) -> (d1 <= d2)
end

module Dijkstra (Heap:HeapSig with module Element = NextNode) = 
struct 
   let shortest_path g a b = 
      let n = Array.length g in
      let b = Array.make n Inf in
      let t = Array.make n false in
      let h = Heap.create() in
      b.(a) <- Finite 0;
      Heap.push (a,0) h;
      while not (Heap.is_empty h) do
         let (x,dx) = Heap.pop h in
         if not t.(x) then begin
            t.(x) <- true;
            let udpate (y,w) =
              let dy = dx + w in
                 if (match b.(y) with | Finite d -> dy < d
                                      | _ -> True) then 
                    (b.(y) <- Finite dy; 
                     Heap.push h (y,dy))
               in
            List.iter update g.(x);
         end;
      done;
      dist.(b)
end
