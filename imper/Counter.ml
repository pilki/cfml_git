


let gensym () =
   let x = ref 0 in
   let f () = 
      let n = !x in
      x := n+1;
      n in
   f

let test () =
   let f = gensym() in
   f() + f()
