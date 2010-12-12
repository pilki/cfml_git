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

type len = Finite of int | Infinite

module NextNode = (* Ordered with type t = int * int *)
struct
   type t = int * int
   let le : t -> t -> bool =
     fun (_,d1) (_,d2) -> (d1 <= d2)
end

module type HeapNextNodeSig =
sig
  type heap
  val create : unit -> heap
  val is_empty : heap -> bool
  val push : NextNode.t -> heap -> unit
  val pop : heap -> NextNode.t
end

module Dijkstra (Pqueue:HeapNextNodeSig) = (* Heap : HeapSig with module Element = NextNode *)
struct 
   let shortest_path g s e = 
      let n = Array.length g in
      let b = Array.make n Infinite in
      let v = Array.make n false in
      let q = Pqueue.create() in
      b.(s) <- Finite 0;
      Pqueue.push (s,0) q;
      while not (Pqueue.is_empty q) do
         let (x,dx) = Pqueue.pop q in
         if not v.(x) then begin
            v.(x) <- true;
            let update (y,w) =
               let dy = dx + w in
               if (match b.(y) with | Finite d -> dy < d
                                    | Infinite -> true)  
                  then (b.(y) <- Finite dy; 
                        Pqueue.push (y,dy) q)
               in
            List.iter update g.(x);
         end;
      done;
      b.(e)
end

