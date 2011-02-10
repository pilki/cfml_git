(*
type heap = { 
  mutable n : int;
  mutable data : int array; }

let create size =
  { n = 0; data = Array.make size 0 }

let add h v =
   h.n <- h.n + 1;
   let k = ref h.n in
   let t = h.data in
   while !k > 1 && v <= t.(k/2) do
     t.(k) <- t.(k/2);
     k := k/2;
   done;
   t.(k) <- v

let pop h =
  let v = h.data.(h.n) in
  h.n <- h.n - 1;
  let k = ref 1 in
  while k < h.n do
      
*)