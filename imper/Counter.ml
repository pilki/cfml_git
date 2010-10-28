
let make_counter () =
   let r = ref 0 in
   let f () = incr r; !r in
   f

let rec iter f = function
  | [] -> ()
  | a::l -> f a; iter f l

let ignore x = ()

let step_all (l:(unit->int)list) = 
  iter (fun f -> ignore (f())) l
