open Okasaki
open CatenableListSig
open QueueSig
open BankersQueue

(*module Q = BatchedQueue*)

module CatenableListImpl : CatenableList =
struct

   type 'a cats = Empty | Struct of 'a * 'a cats Lazy.t BankersQueue.queue
   type 'a cat = 'a cats

   let empty = Empty

   let is_empty = function 
      | Empty -> true
      | _ -> false

   let link xs s =
      match xs with
      | Empty -> raise BrokenInvariant
      | Struct (x, q) -> Struct (x, BankersQueue.snoc q s)
   
   let rec link_all q =
      let t = !$ (BankersQueue.head q) in
      let q' = BankersQueue.tail q in
      if BankersQueue.is_empty q' 
         then t 
         else link t (lazy (link_all q'))

   let append xs1 xs2 =
      match xs1, xs2 with
      | Empty, _ -> xs2
      | _, Empty -> xs1
      | _ -> link xs1 (lazy xs2)

   let cons x xs = 
      append (Struct (x, BankersQueue.empty)) xs
   
   let snoc xs x =
      append xs (Struct (x, BankersQueue.empty))

   let head = function
      | Empty -> raise EmptyStructure
      | Struct (x, _) -> x

   let tail = function
      | Empty -> raise EmptyStructure
      | Struct (x, q) -> 
         if BankersQueue.is_empty q then Empty else link_all q
   
end


(*
module CatenableListImpl (Q : Queue) : CatenableList =
struct

   type 'a cats = Empty | Struct of 'a * 'a cats Lazy.t Q.queue
   type 'a cat = 'a cats

   let empty = Empty

   let is_empty = function 
      | Empty -> true
      | _ -> false

   let link xs s =
      match xs with
      | Empty -> raise BrokenInvariant
      | Struct (x, q) -> Struct (x, Q.snoc q s)
   
   let rec link_all q =
      let t = !$ (Q.head q) in
      let q' = Q.tail q in
      if Q.is_empty q' 
         then t 
         else link t (lazy (link_all q'))

   let append xs1 xs2 =
      match xs1, xs2 with
      | Empty, _ -> xs2
      | _, Empty -> xs1
      | _ -> link xs1 (lazy xs2)

   let cons x xs = 
      append (Struct (x, Q.empty)) xs
   
   let snoc xs x =
      append xs (Struct (x, Q.empty))

   let head = function
      | Empty -> raise EmptyStructure
      | Struct (x, _) -> x

   let tail = function
      | Empty -> raise EmptyStructure
      | Struct (x, q) -> 
         if Q.is_empty q then Empty else link_all q
   
end
*)
