open Okasaki
open QueueSig


module BootstrappedQueue (* : Queue *) =
struct

   type 'a queues = Empty | Struct of int * 'a list * 'a list Lazy.t queues * int * 'a list 
   type 'a queue = 'a queues
   type 'a body = int * 'a list * 'a list Lazy.t queues * int * 'a list 

   let empty = Empty

   let is_empty = function  
     | Empty -> true
     | _ -> false

   let rec checkq : 'a. 'a body -> 'a queue = 
      fun ((lenfm, f, m, lenr, r) as q) ->
      if lenr <= lenfm 
         then checkf q
         else checkf (lenfm+lenr, f, snoc m (lazy (List.rev r)), 0, [])

   and checkf : 'a. 'a body -> 'a queue =
      fun (lenfm, f, m, lenr, r) -> 
      match f, m with
      | [], Empty -> Empty
      | [], _ -> Struct (lenfm, !$(head m), tail m, lenr, r)
      | _ -> Struct (lenfm, f, m, lenr, r)

   and snoc : 'a. 'a queue -> 'a -> 'a queue =
     fun q x ->
      match q with
      | Empty -> Struct (1, [x], Empty, 0, [])
      | Struct (lenfm, f, m, lenr, r) ->
         checkq (lenfm, f, m, lenr+1, x::r)

   and head : 'a. 'a queue -> 'a = function
      | Empty -> raise EmptyStructure
      | Struct (lenfm, x::f', m, lenr, r) -> x
      | _ -> raise BrokenInvariant

   and tail : 'a. 'a queue -> 'a queue = function 
      | Empty -> raise EmptyStructure
      | Struct (lenfm, x::f', m, lenr, r) -> 
         checkq (lenfm-1, f', m, lenr, r)
      | _ -> raise BrokenInvariant

end

