(*

open Okasaki


module BootstrapHeap =
struct

    module rec BootstrappedElement = struct
      type t = Empty | Struct of Element.t * PrimH.heap
      let leq h1 h2 =
         match h1,h2 with
         | Struct (x,_), Struct (y,_) -> Element.leq x y
         | _ -> raise BrokenInvariant
   end

   and PrimH = MakeH(BootstrappedElement)

   open BootstrappedElement

   type heap = BootstrappedElement.t

   let empty : heap = Empty

   let is_empty = function
     | Empty -> true
     | _ -> false

   let rec merge h1 h2 = 
      match h1, h2 with
      | Empty, _ -> h2
      | _, Empty -> h1
      | Struct (x,p1), Struct (y,p2) ->
         if Element.leq x y 
            then Struct (x, Self.insert h2 p1)
            else Struct (y, Self.insert h1 p2)

   let insert x h = 
      merge (Struct (x, PrimH.empty), h)

   let find_min = function
      | Empty -> raise EmptyStructure
      | Struct (x, _) -> x

   let delete_min = function
      | Empty -> raise EmptyStructure
      | Struct (x, p) -> 
         if PrimH.is_empty p then Empty else
         match PrimH.find_min p with
         | Empty -> raise BrokenInvariant
         | Struct (y, p1) -> 
            let p2 = PrimH.delete_min p in
            Struct (y, PrimH.merge p1 p2)




(*
open OrderedSig
open HeapSig

module type OrderedLight =
sig 
   type t
   val leq : t -> t -> bool
end 

module type HeapLight =
sig
  module Element : OrderedLight

  type heap

  val empty : heap
  val is_empty : heap -> bool

  val insert : Element.t -> heap -> heap
  val merge : heap -> heap -> heap

  val find_min : heap -> Element.t 
  val delete_min : heap -> heap  
end


module type HeapMaker = 
  functor (Element : OrderedLight) ->
    (HeapLight with type Element.t = Element.t)


module BootstrapHeap
  (MakeH : HeapMaker)
  (Element : OrderedLight) =
struct

    module rec BootstrappedElement = struct
      type t = Empty | Struct of Element.t * PrimH.heap
      let leq h1 h2 =
         match h1,h2 with
         | Struct (x,_), Struct (y,_) -> Element.leq x y
         | _ -> raise BrokenInvariant
   end

   and PrimH = MakeH(BootstrappedElement)

   open BootstrappedElement

   type heap = BootstrappedElement.t

   let empty : heap = Empty

   let is_empty = function
     | Empty -> true
     | _ -> false

   let rec merge h1 h2 = 
      match h1, h2 with
      | Empty, _ -> h2
      | _, Empty -> h1
      | Struct (x,p1), Struct (y,p2) ->
         if Element.leq x y 
            then Struct (x, Self.insert h2 p1)
            else Struct (y, Self.insert h1 p2)

   let insert x h = 
      merge (Struct (x, PrimH.empty), h)

   let find_min = function
      | Empty -> raise EmptyStructure
      | Struct (x, _) -> x

   let delete_min = function
      | Empty -> raise EmptyStructure
      | Struct (x, p) -> 
         if PrimH.is_empty p then Empty else
         match PrimH.find_min p with
         | Empty -> raise BrokenInvariant
         | Struct (y, p1) -> 
            let p2 = PrimH.delete_min p in
            Struct (y, PrimH.merge p1 p2)

end
*)
*)
