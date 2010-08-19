open StrongPointers

let test_strong () =
   let x = ref () in
   sset x 3;
   let n1 : int = sget x in
   let y : int ref = cast x in
   incr y;
   let n2 = !y in
   sset y true;
   let b : bool = sget x in
   let n3 = if b then 5 else 0 in
   n1 + n2 + n3   (* = 12 *)
   