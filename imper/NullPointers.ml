
let magic = Obj.magic

module type StrongSig = sig 
   type 'a nref = 'a ref
   val null : 'a nref
   val is_null : 'a nref -> bool
   val sref : 'a -> 'b ref
   val sget : 'a ref -> 'b 
   val sset : 'a ref -> 'b -> unit 
   val cast : 'a ref -> 'b ref 
end

module Strong : StrongSig = struct
   type 'a nref = 'a ref
   let null = magic (ref ())
   let is_null p = ((magic null) == p)
   let sref x = magic (ref x)
   let sget p = !(magic p)
   let sset p x = (magic p) := x
   let cast p = magic p
end

open Strong
type 'a nref = 'a Strong.nref
let null = null
let is_null = is_null
let sref = sref
let sget = sget
let sset = sset
let cast = cast

(*
let incr r = 
   r := !r + 1

let not b =
  if b then false else true

let fst (x,y) = x
let snd (x,y) = y
*)
