open StrongPointers

let landin bigf =
   let r = sref () in
   let g x = (!r) x in
   let f x = bigf g x in
   sset r f;
   f
