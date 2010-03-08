module type Deque =
sig
   type 'a deque

   val empty : 'a deque
   val is_empty : 'a deque -> bool
 
   val cons : 'a -> 'a deque -> 'a deque
   val head : 'a deque -> 'a 
   val tail : 'a deque -> 'a deque

   val snoc : 'a deque -> 'a -> 'a deque
   val last : 'a deque -> 'a 
   val init : 'a deque -> 'a deque
end


