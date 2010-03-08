open Okasaki
open QueueSig

(*

module BootstrappedQueue : Queue =
struct

   type 'a queue = Empty | Struct of int * 'a list * 'a list Lazy.t queue * int * 'a list 

   let empty = Empty

   let is_empty = function  
     | Empty -> true
     | _ -> false

   let rec checkq ((lenfm, f, m, lenr, r) as q) = 
      if lenr <= lenfm 
         then checkf q
         else checkf (lenfm+lenr, f, snoc (m, lazy (List.rev r)), 0, [])

   and checkf (lenfm, f, m, lenr, r) =
      match f, m with
      | [], Empty -> Empty
      | [], _ -> Struct (lenfm, !$(head m), tail m, lenr, r)
      | _ -> Struct (lenfm, f, m, lenr, r)

   and snoc (q:'a queue) (x:'a) = 
      match q with
      | Empty -> Struct (1, [x], Empty, 0, [])
      | Struct (lenfm, f, m, lenr, r) ->
         checkq (lenfm, f, m, lenr+1, x::r)

   and head = function
      | Empty -> raise EmptyStructure
      | Struct (lenfm, x::f', m, lenr, r) -> x
      | _ -> raise BrokenInvariant

   and tail = function 
      | Empty -> raise EmptyStructure
      | Struct (lenfm, x::f', m, lenr, r) -> 
         checkq (lenfm-1, f', m, lenr, r)
      | _ -> raise BrokenInvariant

end
*)