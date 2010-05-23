(* ---------------------------------------------------------*)
(* references *)

let imp1 () = 
   let x = ref 3 in
   let y = !x in
   x := 4;
   let z = !x in
   y + z

let imp2 x y =
   let g n =
      x := n + !y;
      y := n + !x;
      in
   g 2
   


(* ---------------------------------------------------------*)
(* test inhabited types *)

(*

let x = raise Not_found

*)

(* ---------------------------------------------------------*)
(* test polymorphic recursion *)

(*
type 'a tree = Leaf of 'a | Node of ('a * 'a) tree;;

let rec depth : 'a. 'a tree -> int =
  function Leaf _ -> 1 | Node x -> 1 + depth x;;

let rec depth_aux : 'a. int -> 'a tree -> _ =
  fun n ->
  function Leaf _ -> (n+1) | Node x -> depth_aux (n+1) x;;


let rec f : 'a. 'a -> _ = 
  fun x -> 1
and g x = f x;;

type 'a t = Leaf of 'a | Node of ('a * 'a) t;;
let rec depth : 'a. 'a t -> _ =
  function Leaf _ -> 1 | Node x -> 1 + depth x;;

let rec r : 'a. 'a list * 'b list ref = [], ref []
and q () = r;;
let f : 'a. _ -> _ = fun x -> x;;
let zero : 'a. [> `Int of int | `B of 'a] as 'a  = `Int 0;;






type 'a rlist =
  | Nil
  | Zero of ('a * 'a) rlist 
  | One of 'a * ('a * 'a) rlist

let rec cons : 'a -> 'a rlist -> 'a rlist = 
  fun x -> function
  | Nil -> One (x,Nil) 
  | Zero ps -> One (x,ps)
  | One (y,ps) -> Zero (cons (x,y) ps)



*)


(*

let min (a:int) (b:int) = 
  if a <= b then a else b

let max (a:int) (b:int) = 
  if a <= b then b else a

let mult_inter (a,b) (c,d) =
   min (min (a * c) (a * d)) (min (b * c) (b * d)),
   max (max (a * c) (a * d)) (max (b * c) (b * d))


*)

(* ---------------------------------------------------------*)
(* test or-patterns *)

(*

let f (p : int option * int option) = match p with
  | (Some x,_) | (_,Some x) when x > 0 -> x
  | _ -> 0

*)


(* ---------------------------------------------------------*)
(* test lazy *)


(*

(* ---------------------------------------------------------*)
(* test functors *)

module type Ordered = sig
   type t 
   val lt : t -> t -> bool
end

module type Fset = sig
   type elt
   type t
   val empty : t
   val add : elt -> t -> t
end

module OrderedNat = struct
   type t = int
   let lt (x : t) (y : t) = (x < y)
end

module FsetList (O:Ordered) : Fset = struct
   type elt = O.t
   type t = elt list
   let empty : t = []
   let add x e = x::e
end

module FsetListNat : Fset = FsetList(OrderedNat)






(* ---------------------------------------------------------*)
(* test pattern matching *)

let rec length = function
    [] -> 0
  | a::l -> 1 + length l

let unsome (Some x) = x

let testmatch = match (1,2) with (a,b) -> a

let myfst (x,y) = x

let x = match (3,(5,2)) with
   (a, ((b, c) as d)) -> d

let y = match (3,(5,(2,4))) with
   (a, ((b, ((c,d) as e)) as f)) -> e

let tail r =
   match r with
   | [] -> []
   | a::r -> r





(* ---------------------------------------------------------*)
(* test polymorphism *)


(* ---------------------------------------------------------*)
(* test modules *)

module type Queue = sig
   type 'a t 
   val empty : 'a t
   val push : 'a -> 'a t -> 'a t
end

module Myqueue = 
struct
   type 'a t = 'a list
   let empty = []
   let push x q = x::q
end

module Myqueue1 = (Myqueue : Queue)

module Myqueue2 = Myqueue 

module Myqueue3 : Queue = Myqueue 

module Myqueue4 (Q:Queue) = Q
   
module Myqueue5 (Q:Queue) = (Q : Queue)

module type TEST = sig
   type t = Nil | Cons of u
   and u = Go of t
   type v = u
end   

(* ---------------------------------------------------------*)
(* test recursive types *)

let fixpoint f =
   (fun x -> f (fun y -> x x y)) (fun x -> f (fun y -> x x y))

(* ---------------------------------------------------------*)
(* test basic *)

let id x = x

let crash = assert false

let select21 x y = x

let myadd x y = x + y

let testlet = let x = 3 + 3 in x + x

let testnolet = let x = 3 + 3 in 4

let asserts = let h = assert false in let g = h in 1

let test = if (1=1) then 1 else 1

let myplus = (+)



(* ---------------------------------------------------------*)
(* test algebraic types *)

type typea = Ta_none | Ta_some of typea 

type ('a,'b) typeb = Tb_left of 'a | Tb_right of 'b

type 'a tree = Tree of 'a * 'a branches
and 'a branches = Branch of ('a tree) list

type 'a typec = 'a tree * ('a,'a) typeb

 
(* ---------------------------------------------------------*)
(* test scopes *)

module Tests = struct

type tok = Toka of int | Tokb of tok

module Go = struct

type tok = Toka of int | Tokb of tok

let rec f = function
   | Toka r -> r
   | Tokb x -> f x

let tokv = 3

end 
end

let tokv = 5

let toky = tokv

let tokz = Tests.Go.tokv

type tokx = Toka | Tokb

let tokm = Tests.Go.Toka 3

let tokh = Tests.Toka 3




*)





(* ---------------------------------------------------------*)
(* ---------------------------------------------------------*)
(* ---------------------------------------------------------*)
(* unsupported 
module FsetList (O:Ordered) : (Fset with type elt = O.t) = struct
   type elt = O.t
   type t = elt list
   let empty = []
   let add x e = x::e
end

module FsetListNat : (Fset with type elt = int) = FsetList(OrderedNat)
*)

