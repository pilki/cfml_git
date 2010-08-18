
(* todo: why body has type int->'a without annotation?*)

let loop_for a b (body:int->unit) =
   let rec aux i =
      if i <= b then (body i; aux (i+1)) in
   aux a

let loop_while cond (body:unit->unit) =
   let rec aux () =
      if cond() then (body(); aux()) in
   aux()
