
let swap i j =
   let t = !i in
   i := !j;
   j := t


(* another test about aliasing *)

let alias () =
   let x = ref 1 in
   let a = ref x in
   let y = !a in
   let b = ref y in
   incr (!b);
   (!a, a)
