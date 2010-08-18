


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




(*  list de compteurs, à incrémenter un par un 

let list_init n f =
   let aux i =
      if i = n then [] else (f i)::(aux (i+1)) in
   aux 0

let test_list n =
   let syms = list_init n (fun _ => gensym()) in
   for i = 0 to n do
      let k = Random.int n in
      let f = List.nth k syms in
      ignore (f())
   done;
   let s = List.fold_left (fun acc f => acc + f()) 0 syms in
   assert (s = syms) 

*)