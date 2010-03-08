module type FiniteMap =
sig 

   type key
   type 'a map

   val empty : 'a map
   val bind : key -> 'a -> 'a map -> 'a map
   val lookup : key -> 'a map -> 'a option
   
   (* note: lookup uses an option to avoid catching exceptions *)

end 
