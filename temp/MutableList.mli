open NullPointers

type 'a mlist = { mutable hd : 'a ; 
                  mutable tl : 'a mlist }

val cps_mappend : 'a mlist -> 'a mlist -> ('a mlist -> 'b) -> 'b 

val miter : ('a -> unit) -> 'a mlist -> unit

val mlength : 'a mlist -> int

val inplace_rev : 'a mlist -> unit




