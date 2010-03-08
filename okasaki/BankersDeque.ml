open Okasaki
open Stream
open DequeSig

let c = 2  (* c > 1 *)

module BankersDeque : Deque =
struct

   type 'a deque = int * 'a stream * int * 'a stream

   let empty : 'a deque  = (0, lazy Nil, 0, lazy Nil)

   let is_empty : 'a deque -> bool = 
      fun (lenf, _, lenr, _) -> (lenf + lenr = 0)

   let check ((lenf, f, lenr, r) as q) =
      if lenf > c * lenr + 1 then
         let i = (lenf + lenr) / 2 in
         let j = lenf + lenr - i in
         let f' = take i f in
         let r' = r ++ reverse (drop i f) in
         (i, f', j, r')
      else if lenr > c * lenf + 1 then
         let i = (lenf + lenr) / 2 in
         let j = lenf + lenr - i in
         let r' = take j r in
         let f' = f ++ reverse (drop j r) in
         (i, f', j, r')
      else q

   let cons x (lenf, f, lenr, r) = 
      check (lenf+1, lazy (Cons(x,f)), lenr, r)

   let head = function
      | _, lazy Nil, _, lazy Nil -> raise EmptyStructure
      | _, lazy Nil, _, lazy (Cons(x, _)) -> x
      | _, lazy (Cons(x, _)), _, _ -> x

   let tail = function
      | _, lazy Nil, _, lazy Nil -> raise EmptyStructure
      | _, lazy Nil, _, lazy (Cons(_, _)) -> empty
      | lenf, lazy (Cons(x, f')), lenr, r -> 
         check (lenf-1, f', lenr, r)

   let snoc (lenf, f, lenr, r) x =
      check (lenf, f, lenr+1, lazy (Cons(x,r)))

   let last = function
      | _, lazy Nil, _, lazy Nil -> raise EmptyStructure
      | _, lazy (Cons(x, _)), _, lazy Nil -> x
      | _, _, _, lazy (Cons(x, _)) -> x

   let init = function
      | _, lazy Nil, _, lazy Nil -> raise EmptyStructure
      | _, lazy (Cons(_, _)), _, lazy Nil -> empty
      | lenf, f, lenr, lazy (Cons(_, r')) -> 
         check (lenf, f, lenr-1, r')

end
