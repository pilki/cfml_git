let (compose : ('_A -> '_B) -> ('_C -> '_A) -> '_C -> '_B) : forall '_A '_B '_C. ('_A -> '_B) -> ('_C -> '_A) -> '_C -> '_B =
fun (g : '_A -> '_B) (f : '_C -> '_A) (x : '_C) ->
let (_x1 : '_A) : '_A =
f (x : '_C) in g (_x1 : '_A)

let (incr_ret : int Pervasives.ref -> int Pervasives.ref) : int Pervasives.ref -> int Pervasives.ref =
fun (r : int Pervasives.ref) -> Pervasives.incr (r : int Pervasives.ref) ; r

let (decr_ret : int Pervasives.ref -> int Pervasives.ref) : int Pervasives.ref -> int Pervasives.ref =
fun (r : int Pervasives.ref) -> Pervasives.decr (r : int Pervasives.ref) ; r

let (test : int Pervasives.ref -> int Pervasives.ref) : int Pervasives.ref -> int Pervasives.ref =
fun (r : int Pervasives.ref) ->
compose (decr_ret : int Pervasives.ref -> int Pervasives.ref) (incr_ret : int Pervasives.ref -> int Pervasives.ref) (r : int Pervasives.ref)