open Okasaki
open QueueSig

(* 
module ImplicitQueue : Queue =
struct

   type 'a digit = Zero | One of 'a | Two of 'a * 'a
   type 'a queue = Shallow of 'a digit | Deep of 'a digit * ('a * 'a) queue Lazy.t * 'a digit

   let empty = Shallow Zero

   let is_empty = function  
     | Shallow Zero -> true
     | _ -> false

   let rec snoc : 'a queue -> 'a -> 'a queue = fun q y =>
      match q with
      | Shallow Zero -> Shallow (One y)
      | Shallow (One x) -> Deep (Two (x,y), lazy empty, Zero)
      | Deep (f, m, Zero) -> Deep (f, m, One y)
      | Deep (f, m, One x) -> Deep (f, lazy (snoc (!$m) (x,y)), Zero)

   and head : 'a queue -> 'a = function
      | Shallow Zero -> raise EmptyStructure
      | Shallow (One x) -> x
      | Deep (One x, m, r) -> x
      | Deep (Two (x,y), m, r) -> x

   and tail 'a queue -> 'a queue = function 
      | Shallow Zero -> raise EmptyStructure
      | Shallow (One x) -> empty
      | Deep (Two (x,y), m, r) -> Deep (One y, m, r)
      | Deep (One x, lazy q, r) -> 
          if is_empty q 
            then Shallow r
            else let (y,z) = head q in
                 Deep (Two (y,z), lazy (tail q), r)

end
*)
