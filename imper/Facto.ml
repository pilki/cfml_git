
let rec facto_rec n =
  if n = 0 then 1 else n * facto_rec (n-1)

let facto_for n = 
  let r = ref 1 in
  for i = 1 to n do
     r := !r * i
  done

let facto_while n =
  let m = ref 0 in
  let r = ref 1 in
  while !m <= n do
     r := !r * !m;
     m := !m - 1;
  done

