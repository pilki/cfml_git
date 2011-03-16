(** Union find represented using pointers *)

type cell = content ref
and content = Node of cell | Root

let rec repr x =
   match !x with
   | Root -> x
   | Node y -> 
       let r = repr y in
       x := Node r;
       r

let create () = 
   ref Root

let same x y =
  repr x == repr y

let union x y =
   let rx = repr x in
   let ry = repr y in
   if rx != ry 
      then rx := Node ry 


