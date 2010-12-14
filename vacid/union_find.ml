(** Union find represented using pointers *)

type cell = { 
  mutable parent : content;
  mutable rank : int }
and content = Node of cell | Root

let rec repr x =
   match x.parent with
   | Root -> x
   | Node y -> 
      let r = repr y in
      x.parent <- Node r;
      r

let create () = 
   { parent = Root; rank = 0 }

let same x y =
  repr x == repr y

let union x y =
   let rx = repr x in
   let ry = repr y in
   if rx != ry then begin
      if rx.rank < ry.rank then
         rx.parent <- Node ry
      else if rx.rank > ry.rank then
         ry.parent <- Node rx
      else (
         ry.parent <- Node rx;
         rx.rank <- ry.rank + 1)
   end 

