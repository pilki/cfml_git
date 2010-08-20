open NullPointers

type 'a mlist = ('a * 'a mlist) ref 

let is_nil (l:'a mlist) =
   l == null

let head (l:'a mlist) =
   fst (!l)

let tail (l:'a mlist) =
   snd (!l)

let set_head (l:'a mlist) x =
   let (_,t) = !l in
   l := (x,t)

let set_tail (l:'a mlist) t =
   let (x,_) = !l in
   l := (x,t)

let append (l1 : 'a mlist) (l2 : 'a mlist) =
   if l1 == null then l2 else
   let h = ref l1 in
   while tail (!h) != null do
      h := tail (!h);
   done;
   set_tail (!h) l2;
   l1
   
let length (l:'a mlist) =
   let h = ref l in
   let n = ref 0 in
   while !h != null do
     incr n;
     h := tail !h;
   done;
   !n

(*--todo: needs to be fixed
    so as to avoid reallocating cells 
let rev (l:'a mlist) =
  let f = ref l in
  let r = ref (null:'a mlist) in
  while !f != null do
    let ((x:'a),t) = !(!f) in
    r := ref (x, !r);
    f := t;
  done;
  !r
*)


(* test
let _ =
  let x = ref (3, ref (5, null)) in
  Printf.printf "%d\n" (length x)
*)
(* 
*)
