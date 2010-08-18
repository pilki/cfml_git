type 'a nref = 'a ref
val null : 'a nref
val is_null : 'a nref -> bool
val sref : 'a -> 'b ref
val sget : 'a ref -> 'b 
val sset : 'a ref -> 'b -> unit 
val cast : 'a ref -> 'b ref 

