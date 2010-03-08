open Okasaki
open Stream
open QueueSig

module PhysicistsQueue : Queue =
struct

   type 'a queue = 'a list * int * 'a list Lazy.t * int * 'a list

   let empty : 'a queue = 
      ([], 0, lazy [], 0, [])

   let is_empty : 'a queue -> bool = fun (_, lenf, _, _, _) ->
      (lenf = 0)

   let checkw = function
      | [], lenf, f, lenr, r -> !$f, lenf, f, lenr, r
      | q -> q

   let check (w, lenf, f, lenr, r as q) =
      if lenr <= lenf 
         then checkw q
         else let f' = !$f in
              checkw (f', lenf+lenr, lazy (f' @ List.rev r), 0, [])

   let snoc (w, lenf, f, lenr, r) x = 
      check (w, lenf, f, lenr+1, x::r)

   let head = function
      | [], lenf, f, lenr, r -> raise EmptyStructure
      | x::w, lenf, f, lenr, r -> x

   let tail = function
      | [], lenf, f, lenr, r -> raise EmptyStructure
      | x::w, lenf, f, lenr, r ->
         check (w, lenf-1, lazy (List.tl !$f), lenr, r)

end
