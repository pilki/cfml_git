open Okasaki
open QueueSig

module BatchedQueue : Queue =
struct

   type 'a queue = 'a list * 'a list 

   let empty : 'a queue = ([],[])

   let is_empty = function  
     | [],_  -> true
     | _ -> false

   let checkf = function
     | [],r -> (List.rev r, [])
     | q -> q

   let snoc (f,r) x = checkf (f, x::r)

   let head = function
     | [], _ -> raise EmptyStructure
     | x::f, r -> x

   let tail = function 
     | [], _ -> raise EmptyStructure
     | x::f, r -> checkf (f,r)

end
