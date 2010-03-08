type 'a test = E | F of 'a * ('a * 'a) test

type v = E of v

type c = G

(*
let rec size : 'a test -> int = function
   | E -> 1
   | F (x,y) -> 1 + 2 * size y
*)
(* let _ = (print_int 3; fun x -> x) (print_int 4; "ok") in print_newline() *)
