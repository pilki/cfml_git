open NullPointers

(** Representation of mutable lists (null pointer describes the empty list) *)

type 'a mlist = { mutable hd : 'a ; 
                  mutable tl : 'a mlist }

(** Imperative version of the CPS append function *)

let rec cps_mappend (x:'a mlist) (y:'a mlist) (k:'a mlist->'b) : 'b =
  if x == null then k y else
    let f z = (x.tl <- z; k x) in 
    cps_mappend x.tl y f

(** Iteration on mutable lists *)

let rec miter (f:'a->unit) (l:'a mlist) =
   let h = ref l in
   while !h != null do
     f (!h.hd);
     h := !h.tl;
   done

(** Length of a mutable lists *)

let mlength (l:'a mlist) =
   let h = ref l in
   let n = ref 0 in
   while !h != null do
     incr n;
     h := !h.tl;
   done;
   !n

(** In place reversal of imperative list *)

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




