open Okasaki
open Stream
open QueueSig

module RealTimeQueue : Queue =
struct

   type 'a queue = 'a stream * 'a list * 'a stream

   let empty : 'a queue = (lazy Nil ,[], lazy Nil)

   let is_empty : 'a queue -> bool = function
     | lazy Nil, _, _  -> true
     | _ -> false

   let rec rotate : 'a queue -> 'a stream = function 
     | lazy Nil, y::_, a -> lazy (Cons (y,a))
     | lazy (Cons(x,xs)), y::ys, a -> lazy (Cons (x, rotate (xs, ys, lazy (Cons (y,a)))))
     | _ -> raise BrokenInvariant

   let exec : 'a queue -> 'a queue = function
     | f, r, lazy (Cons (x,s)) -> (f,r,s)
     | f, r, lazy Nil -> let f' = rotate (f,r,lazy Nil) in (f',[],f')

   let snoc : 'a queue -> 'a -> 'a queue = fun (f,r,s) x ->
     exec (f, x::r, s)

   let head : 'a queue -> 'a = function
     | lazy Nil, r, s -> raise EmptyStructure
     | lazy (Cons (x,f)), r, s -> x

   let tail : 'a queue -> 'a queue = function 
     | lazy Nil, r, s -> raise EmptyStructure
     | lazy (Cons (x,f)), r, s -> exec (f,r,s)

end
