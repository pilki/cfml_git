
let compose g f x = g (f x)


let incr_ret r = 
   incr r; 
   r

let decr_ret r = 
   decr r; 
   r

let test r = 
  compose decr_ret incr_ret r
