open Okasaki
open Stream
open QueueSig

module BankersQueue : Queue =
struct

   type 'a queue = int * 'a stream * int * 'a stream

   let empty : 'a queue  = (0, lazy Nil, 0, lazy Nil)

   let is_empty : 'a queue -> bool = fun (lenf, _, _, _) -> (lenf = 0)

   let check ((lenf,f,lenr,r) as q) =
     if lenr <= lenf then q else (lenf + lenr, f ++ reverse r, 0, lazy Nil)

   let snoc (lenf,f,lenr,r) x =
      check (lenf, f, lenr+1, lazy (Cons (x,r)))
      
   let head = function
     | (lenf,lazy Nil,lenr,r) -> raise EmptyStructure
     | (lenf,lazy (Cons(x,_)),lenr,r) -> x

   let tail = function 
     | (lenf,lazy Nil,lenr,r) -> raise EmptyStructure
     | (lenf,lazy (Cons(x,f')),lenr,r) -> check (lenf-1,f',lenr,r)

end

