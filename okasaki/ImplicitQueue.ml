open Okasaki
open QueueSig

module ImplicitQueue : Queue =
struct

   type 'a digit = Zero | One of 'a | Two of 'a * 'a
   type 'a queues = Shallow of 'a digit | Deep of 'a digit * ('a * 'a) queues Lazy.t * 'a digit
   type 'a queue = 'a queues

   let empty : 'a queue = Shallow Zero

   let is_empty : 'a. 'a queue -> bool = function  
     | Shallow Zero -> true
     | _ -> false

   let rec snoc : 'a. 'a queue -> 'a -> 'a queue = fun q y ->
      match q with
      | Shallow Zero -> Shallow (One y)
      | Shallow (One x) -> Deep (Two (x,y), lazy empty, Zero)
      | Deep (f, m, Zero) -> Deep (f, m, One y)
      | Deep (f, m, One x) -> Deep (f, lazy (snoc (!$m) (x,y)), Zero)
      | _ -> raise BrokenInvariant

   and head : 'a. 'a queue -> 'a = function
      | Shallow Zero -> raise EmptyStructure
      | Shallow (One x) -> x
      | Deep (One x, m, r) -> x
      | Deep (Two (x,y), m, r) -> x
      | _ -> raise BrokenInvariant

   and tail : 'a. 'a queue -> 'a queue = function 
      | Shallow Zero -> raise EmptyStructure
      | Shallow (One x) -> empty
      | Deep (Two (x,y), m, r) -> Deep (One y, m, r)
      | Deep (One x, lazy q, r) -> 
          if is_empty q 
            then Shallow r
            else let (y,z) = head q in
                 Deep (Two (y,z), lazy (tail q), r)
      | _ -> raise BrokenInvariant

end
