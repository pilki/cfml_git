module type CatenableList =
sig
   type 'a cat

   val empty : 'a cat
   val is_empty : 'a cat -> bool
 
   val cons : 'a -> 'a cat -> 'a cat
   val snoc : 'a cat -> 'a -> 'a cat
   val append : 'a cat -> 'a cat -> 'a cat

   val head : 'a cat -> 'a 
   val tail : 'a cat -> 'a cat
end


