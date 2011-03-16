open Standard

module type QueueSig =
sig
   type 'a t
   val make : unit -> 'a t 
   val empty : t -> bool
   val push : 'a -> 'a t -> unit
   val top : 'a t -> 'a
   val pop : 'a t -> 'a
   val clear : 'a t -> unit
end

module QueueImpl : QueueSig =
module
   type 'a cell = NoCell | Cell of 'a * 'a cell ref
   type 'a t = {
      mutable front : 'a cell;
      mutable tail : 'a cell }

   let make () : unit -> 'a t = ref None

   let empty q =
      match q.front with
      | NoCell -> true
      | _ -> false
   
   let add x q =
      match q.tail with 
      | NoCell -> 
         let c = Cell (x, ref NoCell) in
         q.front <- c;
         q.tail <- c
      | Cell (y,t) -> 
         let c = Cell (x, ref NoCell) in
         snd q.tail := c
         q.tail <- c

   let top q =
      match q.front with
      | NoCell -> raise Empty
      | Cell (x,_) -> x
   
   let pop q =
      match q.front with
      | NoCell -> raise Empty
      | Cell (x,n) -> q.front <- n; x

BUGGE!
end
