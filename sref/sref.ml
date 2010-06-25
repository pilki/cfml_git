
let magic = Obj.magic


(** Standard manipulation of references *)

let ref : 'a -> 'a ref =
   Pervasives.ref

let get : 'a ref -> 'a =
   Pervasives.(!)

let set : 'a ref -> 'a -> unit =
   Pervasives.(:=)


(** Strong manipulation of references *)

let alloc () : 'a ref =
   magic (ref ())
 
let sget (p : 'a ref) : 'b =
   get (magic p)

let sset (p : 'a ref) (v : 'b) : unit = 
   set (magic p) v 

let cast (p : 'a ref) : 'b ref =
   magic p

let cmp (p1 : 'a ref) (p2 : 'b ref) : bool =
   (magic p1) == p2


(** Nullable references *)

let null_impl = ref ()

let null () : 'a ref = 
   magic null_impl

let is_null (p : 'a ref) : bool =
   p == (magic null_impl)


(** Untyped references *)

type sref = unit ref

let sref (v : 'a) : sref =
   magic (ref v)

let salloc : unit -> sref =
   alloc

let snull : sref =
   magic null


(** Test *)

let show n =
   Printf.printf "%d\n" n

let () =

   let a = null() in
   if is_null a then show 1;
   let b = ref 2 in
   if not (is_null b) then show 2;

   let x = salloc () in
   sset x 3;
   let n : int = sget x in
   show n;

   let y : int ref = cast x in
   show (!y);
   show (sget x : int);

   let z : sref = cast (ref 8) in
   show (sget z : int);

   sset x true;
   let r : int = sget x in
   show r;

   sset x (3.54);
   let r : float = sget x in
   print_float r
