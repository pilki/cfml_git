
let magic = Obj.magic

module type NullSig = sig 
   val null : 'a ref
   val is_null : 'a ref -> bool
end

module NullImpl : NullSig = struct
   let null = magic (ref ())
   let is_null p = ((magic null) == p)
end

open NullImpl
let null = null
let is_null = is_null

