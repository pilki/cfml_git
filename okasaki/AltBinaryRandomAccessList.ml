open Okasaki
open RandomAccessListSig

(*
module AltBinaryRandomAccesList : RandomAccessList =
struct

   type 'a rlist = Nil | Zero of ('a * 'a) rlist | One of 'a * ('a * 'a) rlist

   let empty : 'a rlist = Nil

   let is_empty = function  
      | Nil -> true
      | _ -> false

   let rec cons : 'a -> 'a rlist -> 'a rlist = fun x -> function
      | Nil -> One (x, Nil)
      | Zero ps -> One (x, ps)
      | One (y, ps) -> Zero (cons (x,y) ps)

   let rec uncons : 'a rlist -> 'a * 'a rlist = function
      | Nil -> raise EmptyStructure
      | One (x, Nil) -> (x, Nil)
      | One (x, ps) -> (x, Zero ps)
      | Zero ps -> 
         let ((x,y),ps') = uncons ps in
         (x, One (y, ps'))

   let head ts = 
      fst (uncons ts)

   let tail ts = 
      snd (uncons ts)

   let rec lookup i ts = 
      match i,ts with
      | i, Nil -> raise OutOfBound
      | 0, One (x, ps) -> x
      | i, One (x, ps) -> lookup (i-1) (Zero ps)
      | i, Zero ps -> 
         let (x,y) = lookup (i/2) ps in
         if i mod 2 = 0 then x else y

   let rec fupdate f i ts = 
      match i,ts with
      | i, Nil -> raise OutOfBound
      | 0, One (x, ps) -> One (f x, ps)
      | i, One (x, ps) -> cons x (fupdate f (i-1) (Zero ps))
      | i, Zero ps -> 
         let f' (x,y) = if i mod 2 = 0 then (f x, y) else (x, f y) in
         Zero (fupdate f' (i/2) ps)
                      
   let update i y xs = fupdate (fun x -> (y,i,xs))

end

*)