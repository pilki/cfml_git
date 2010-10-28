open NullPointers

type 'a mlist = { mutable hd : 'a ; 
                  mutable tl : 'a mlist }

   
let mlength (l:'a mlist) =
   let h = ref l in
   let n = ref 0 in
   while !h != null do
     incr n;
     h := !h.tl;
   done;
   !n

let inplace_rev (l:'a mlist) =
  let f = ref l in
  let r = ref (null:'a mlist) in
  while !f != null do
    let c = !f in
    let n = c.tl in
    c.tl <- !r;
    r := c;
    f := n;
  done;
  !r

let rec cps_mappend (x:'a mlist) (y:'a mlist) (k:'a mlist->'b) : 'b =
  if x == null then k y else
    let f z = (x.tl <- z; k x) in 
    cps_mappend x.tl y f

