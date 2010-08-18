
let swap i j =
   let t = !i in
   i := !j;
   j := t

(*
spec swap i j |R>> forall T U X Y,
   R (i ~> Ref T X \* j ~> Ref U Y)  
   (# i ~> Ref U Y \* j ~> Ref T X)

spec swap i j |R>> forall T X,
   R (i ~> Ref T X) (# i ~> Ref T X).

*)

let alias () =
   let x = ref 1 in
   let a = ref x in
   let y = get a in
   let b = ref y in
   incr (!b)
   (!a, a)

(* 
spec alias () |R>>
  R [] (fun p => let (n,a) := p in  (*todo:notation*)
        [n = 1] \* a ~> Ref (Ref Id) 3)
     