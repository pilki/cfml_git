open Okasaki
open Stream
open DequeSig

let c = 2  (* c > 1 *)

module RealTimeDeque : Deque =
struct

   type 'a deque = int * 'a stream * 'a stream * int * 'a stream * 'a stream

   let empty : 'a deque  = (0, lazy Nil, lazy Nil, 0, lazy Nil, lazy Nil)

   let is_empty : 'a deque -> bool = 
      fun (lenf, f, sf, lenr, r, sr) -> (lenf + lenr = 0)

   let exec1 = function
      | lazy (Cons(x,s)) -> s
      | s -> s
   
   let exec2 s = exec1 (exec1 s)

   let rec rotate_rev s r a =  
      match s with
      | lazy Nil -> reverse r ++ a
      | lazy (Cons(x,f)) ->
          lazy (Cons (x, rotate_rev f (drop c r) (reverse (take c r) ++ a)))

   let rec rotate_drop f j r =
      if j < c 
         then rotate_rev f (drop j r) (lazy Nil)
         else match f with
              | lazy (Cons(x,f')) -> 
                  lazy (Cons(x, rotate_drop f' (j-c) (drop c r)))
              | _ -> raise BrokenInvariant

   let check ((lenf, f, sf, lenr, r, sr) as q) =
      if lenf > c * lenr + 1 then
         let i = (lenf + lenr) / 2 in
         let j = lenf + lenr - i in
         let f' = take i f in
         let r' = rotate_drop r i f in
         (i, f', f', j, r', r')
      else if lenr > c * lenf + 1 then
         let i = (lenf + lenr) / 2 in
         let j = lenf + lenr - i in
         let r' = take j r in
         let f' = rotate_drop f j r in
         (i, f', f', j, r', r')
      else q

   let cons x (lenf, f, sf, lenr, r, sr) = 
      check (lenf+1, lazy (Cons(x,f)), exec1 sf, lenr, r, exec1 sr)

   let head = function
      | _, lazy Nil, sf, _, lazy Nil, sr -> raise EmptyStructure
      | _, lazy Nil, sf, _, lazy (Cons(x, _)), sr -> x
      | _, lazy (Cons(x, _)), sf, _, _, sr -> x

   let tail = function
      | _, lazy Nil, sf, _, lazy Nil, sr -> raise EmptyStructure
      | _, lazy Nil, sf, _, lazy (Cons(_, _)), sr -> empty
      | lenf, lazy (Cons(x, f')), sf, lenr, r, sr -> 
         check (lenf-1, f', exec2 sf, lenr, r, exec2 sr)

   let snoc (lenf, f, sf, lenr, r, sr) x =
      check (lenf, f, exec1 sf, lenr+1, lazy (Cons(x,r)), exec1 sr)

   let last = function
      | _, lazy Nil, sf, _, lazy Nil, sr -> raise EmptyStructure
      | _, lazy (Cons(x, _)), sf, _, lazy Nil, sr -> x
      | _, _, sf, _, lazy (Cons(x, _)), sr -> x

   let init = function
      | _, lazy Nil, sf, _, lazy Nil, sr -> raise EmptyStructure
      | _, lazy (Cons(_, _)), sf, _, lazy Nil, sr -> empty
      | lenf, f, sf, lenr, lazy (Cons(_, r')), sr -> 
         check (lenf, f, exec2 sf, lenr-1, r', exec2 sr)

end
