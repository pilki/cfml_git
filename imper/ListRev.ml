open MyLib

type 'a mlist = ('a * 'a mlist) ref 
(*todo:nref*)

let mlength (l:'a mlist) =
   let p = ref l in
   let n = ref 0 in
   while not (is_null !p) do
     incr n;
     p := snd !(!p);
   done;
   !n

(* test
let _ =
  let x = ref (3, ref (5, null)) in
  Printf.printf "%d\n" (length x)
*)
(* 
*)
let rev (l:'a mlist) =
  let f = ref l in
  let r = ref (null:'a mlist) in
  while !f != null do
    let ((x:'a),t) = !(!f) in
    r := ref (x, !r);
    f := t;
  done;
  !r



