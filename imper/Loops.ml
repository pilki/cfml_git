
let myincr r =
  r := !r + 1

let incr_for k l =
  for i = 1 to k do incr l done

let incr_while k l =
  while !k > 0 do incr l; decr k done

(* todo: why body has type int->'a without annotation?*)

let loop_for a b (body:int->unit) =
   let rec aux i =
      if i <= b then (body i; aux (i+1)) in
   aux a

let loop_while cond (body:unit->unit) =
   let rec aux () =
      if cond() then (body(); aux()) in
   aux()
