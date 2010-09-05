open NullPointers

type 'a mlist = ('a * 'a mlist) ref

let tail (l:'a mlist) =
   snd (!l)

let set_tail (l:'a mlist) t =
   let (x,_) = !l in
   l := (x,t)

let rec append (x:'a mlist) (y:'a mlist) (k:'a mlist->'b) : 'b =
  if x == null then k y else
    let f z = (set_tail x z; k x) in 
    append (tail x) y f
    
