open MyLib

type 'a mlist = ('a * 'a mlist) nref 

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

let rev (l:'a mlist) =
  let r = ref (null:'a mlist) in
  while l != null do
    let (x,f) = !l in
    r := ref (x, !r);
  done;
  !r



