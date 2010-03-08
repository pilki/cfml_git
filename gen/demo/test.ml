


(*

type 'a joiner = Join of 'a * 'a

let test x =
   let f a = 3 in
   let r y = f (Join (x,y)) in
   3
   




let id x = x

let f =
   let id x y = (x,y) in
   id 

let conflict x y z =
   match x + x with
   | y -> match x - x with
         | x -> x

let def x y z =  
   let f a = a + x in
   let m g h u = (u, g (h u) + x) in
   y

 
   
let fixpoint f =
   (fun x -> f (fun y -> x x y)) (fun x -> f (fun y -> x x y))

let id x = x

let crash = assert false


let select21 x y = x

*)


(* todo: pkoi ça bug ?
let f =
   let id x y = (x,y) in
   id 3 
*)


(*
let f (x,y) = y


  





-----------
let f (x,y) u (z,t) = x

let g x = ((x+x), (x+x+x))

let id a = a

let h x = 
  let rec f a _ = 
      let b = a + a in 
      (id f) (b+b) (b*b) in
  ((x + x), (f x x + x + f x x))
-----------------






let num = 3

external (+) : int -> int -> int = ""

let myadd x y = x + y

let testmatch = match (1,2) with (a,b) -> a

let myfst (x,y) = x


(*requires: rectype*)

let fixpoint f =
   (fun x -> f (fun y -> x x y)) (fun x -> f (fun y -> x x y))

open Printf


let x = ref 3 
let y = ref 3


(* todo: overflow
let _ = if x = y then printf "eq" else printf "neq"
*)


(*
type 'a t = ('a * int) t -> int
type 'b u = (('b*'b)*int) u -> int

*)
type 'a t = 'a t -> int
type 'c z = 'c t



let a = let h = assert false in h

let tail = function
   | [] -> []
   | a::q -> q

let h = if (1=1) then 1 else 1


let eq = (=)
let z x = if (eq true true)  then x else x


let tail x = (x = x)


let h =
  let id n = n in
  id 0


let k = match (1,2) with (a,b) -> a

let n = 3



(* good error
let x = fun y -> y
let h x = if tail x then true else true
let y = (x 3, x (fun y -> y))
let k = match y with (a,b) -> b
external (=) : 'a -> 'a -> bool = ""
*)


let rec length = function
    [] -> 0
  | a::l -> 1 + length l

module Tests = struct

type tok = Toka of int | Tokb of tok

let rec f = function
   | Toka r -> r
   | Tokb x -> f x

let v = 3

end


let v = 5

let y = v
let z = Tests.v

type tokx = Toka | Tokb

let x = Tests.Toka 3

*)
