
module type StrongSig = sig 
   type sref
   val alloc : unit -> sref
   val ref : 'a -> sref 
   val get : sref -> 'a 
   val set : sref -> 'a -> unit 
   val same : sref -> sref -> bool
   val null : sref 
   val is_null : sref -> bool
end

module type WeakSig = sig 
   (*
   type 'a ref
   val ref : 'a -> 'a ref
   val get : 'a ref -> 'a 
   val set : 'a ref -> 'a -> unit 
   *)

   val alloc : unit -> 'a ref
   val sref : 'a -> 'b ref
   val sget : 'a ref -> 'b 
   val sset : 'a ref -> 'b -> unit 
   
   val same : 'a ref -> 'b ref -> bool
   val cast : 'a ref -> 'b ref 

   val null : 'a ref
   val is_null : 'a ref -> bool
end


let magic = Obj.magic

module Strong : StrongSig = struct
   type sref = unit ref 
   let alloc () = ref ()
   let ref x = magic (ref x)
   let get p = !(magic p)
   let set p x = (magic p) := x
   let same p1 p2 = (p1 == p2)
   let null = ref ()
   let is_null p = same null p
end

module Weak : WeakSig = struct
   (*
   type 'a ref = 'a Pervasives.ref
   let ref = Pervasives.ref
   let get = (!)
   let set = (:=)
   *)

   let alloc () = magic (ref ())
   let sref x = magic (ref x)
   let sget p = !(magic p)
   let sset p x = (magic p) := x
   
   let same p1 p2 = ((magic p1) == p2) 
   let cast p = magic p

   let null = magic (ref ())
   let is_null p = same (magic null) p
end





(*
   let is_null = same (magic nullref)
let is_null (p : 'a ref) : bool =
   p == (magic null_impl)*)



(*

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

*)
