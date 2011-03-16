

let fix func =
   let r = ref (fun x -> assert false) in
   let f' x = !r x in
   let f x = func f' x in
   r <- f;
   f
