module type RandomAccessList =
sig 

   type 'a rlist

   val empty : 'a rlist
   val is_empty : 'a rlist -> bool

   val cons : 'a -> 'a rlist -> 'a rlist
   val head : 'a rlist -> 'a
   val tail : 'a rlist -> 'a rlist

   val lookup : int -> 'a rlist -> 'a 
   val update : int -> 'a -> 'a rlist -> 'a rlist

end 
