
let magic = Obj.magic

module type WeakSig = sig 
   type 'a nref = 'a ref
   val null : 'a nref
   val is_null : 'a nref -> bool
end

module Weak : WeakSig = struct
   type 'a nref = 'a ref
   let null = magic (ref ())
   let is_null p = ((magic null) == p)
end

open Weak
type 'a nref = 'a Weak.nref
let null = null
let is_null = is_null


(*
let incr r = 
   r := !r + 1

let not b =
  if b then false else true

let fst (x,y) = x
let snd (x,y) = y
*)
