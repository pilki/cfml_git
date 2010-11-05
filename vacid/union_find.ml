(** Union find represented using pointers *)

type cell = content ref
and content = Node of cell | Root

let create () = 
   ref Root

let rec repr x =
   match !x with
   | Root -> x
   | Node y -> repr y

let equiv x y =
  repr x == repr y

let union x y =
   let rx = repr x in
   let ry = repr y in
   rx := Node ry 


