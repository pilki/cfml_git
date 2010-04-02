module type QueueBis =
sig
   type 'a queue = 'a list

   val empty : 'a queue
   val is_empty : 'a queue -> bool
   
   val snoc : 'a queue -> 'a -> 'a queue
   val head : 'a queue -> 'a 
   val tail : 'a queue -> 'a queue
end
