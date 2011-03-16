module type Ordered = _

module type PqueueSig = _

type _ = _

module NextNode =
struct
type _ = _

let (le : t -> t -> bool) : t -> t -> bool =
fun (_x0 : t) (_x1 : t) ->
match _x0 with
((_p0 : int),(d1 : int)) ->
match _x1 with
((_p0 : int),(d2 : int)) -> Pervasives.<= (d1 : int) (d2 : int)
end
] 

module Dijkstra =
Pqueue : _ ==>struct
let (shortest_path : (int * int) list array -> int -> int -> len) : (int * int) list array -> int -> int -> len =
fun (g : (int * int) list array) (s : int) (e : int) ->
let (n : int) : int =
Array.length (g : (int * int) list array) in
let (b : len array) : len array =
Array.make (n : int) (Infinite : len) in
let (v : bool array) : bool array =
Array.make (n : int) (false : bool) in
let (q : Pqueue.heap) : Pqueue.heap =
Pqueue.create (() : unit) in
Array.set (b : len array) (s : int) (Finite 0 : len)
; Pqueue.push ((s, 0) : Pqueue.Element.t) (q : Pqueue.heap)
; while let (_x62 : bool) : bool =
Pqueue.is_empty (q : Pqueue.heap) in
Pervasives.not (_x62 : bool)
do let (_x20 : Pqueue.Element.t) : Pqueue.Element.t =
Pqueue.pop (q : Pqueue.heap) in
match _x20 with
((x : int),(dx : int)) ->
let (_x25 : bool) : bool =
Array.get (v : bool array) (x : int) in
if Pervasives.not (_x25 : bool)
then Array.set (v : bool array) (x : int) (true : bool)
; let (update : int * int -> unit) : int * int -> unit =
fun (_x33 : int * int) ->
match _x33 with
((y : int),(w : int)) ->
let (dy : int) : int =
Pervasives.+ (dx : int) (w : int) in
let (_x38 : len) : len =
Array.get (b : len array) (y : int) in
let (_x37 : bool) : bool =
match _x38 with
Finite (d : int) -> Pervasives.< (dy : int) (d : int) | Infinite -> true in
if _x37
then Array.set (b : len array) (y : int) (Finite dy : len)
; Pqueue.push ((y, dy) : Pqueue.Element.t) (q : Pqueue.heap)
else () in
let (_x57 : (int * int) list) : (int * int) list =
Array.get (g : (int * int) list array) (x : int) in
List.iter (update : int * int -> unit) (_x57 : (int * int) list)
else ()
done
; Array.get (b : len array) (e : int)
end

] 