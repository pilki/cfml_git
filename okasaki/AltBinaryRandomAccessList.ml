open Okasaki
open RandomAccessListSig

module AltBinaryRandomAccesList : RandomAccessList =
struct

   (* todo: name conflict with Nil *)
   type 'a rlists = Null | Zero of ('a * 'a) rlists | One of 'a * ('a * 'a) rlists
   type 'a rlist = 'a rlists

   let empty = Null

   let is_empty = function  
      | Null -> true
      | _ -> false

   let rec cons : 'a. 'a -> 'a rlist -> 'a rlist = fun x -> function
      | Null -> One (x, Null)
      | Zero ps -> One (x, ps)
      | One (y, ps) -> Zero (cons (x,y) ps)

   let rec uncons : 'a. 'a rlist -> 'a * 'a rlist = function
      | Null -> raise EmptyStructure
      | One (x, Null) -> (x, Null)
      | One (x, ps) -> (x, Zero ps)
      | Zero ps -> 
         let ((x,y),ps') = uncons ps in
         (x, One (y, ps'))

   let head ts = 
      fst (uncons ts)

   let tail ts = 
      snd (uncons ts)

   let rec lookup : 'a. int -> 'a rlist -> 'a = fun i ts ->
      match i,ts with
      | i, Null -> raise OutOfBound
      | 0, One (x, ps) -> x
      | i, One (x, ps) -> lookup (i-1) (Zero ps)
      | i, Zero ps -> 
         let (x,y) = lookup (i/2) ps in
         if i mod 2 = 0 then x else y

   let rec fupdate : 'a. ('a -> 'a) -> int -> 'a rlist -> 'a rlist = 
      fun f i ts -> match i,ts with
      | i, Null -> raise OutOfBound
      | 0, One (x, ps) -> One (f x, ps)
      | i, One (x, ps) -> cons x (fupdate f (i-1) (Zero ps))
      | i, Zero ps -> 
         let f' (x,y) = if i mod 2 = 0 then (f x, y) else (x, f y) in
         Zero (fupdate f' (i/2) ps)
                      
   let update i y xs = fupdate (fun x -> y) i xs

end

