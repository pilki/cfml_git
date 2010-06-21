
type sref = unit ref

let magic = Obj.magic

let sref (v : 'a)  : sref =
   (magic (ref v))

let sget (l : sref) : 'a =
   (!) (magic l)

let sset (l : sref) (v : 'a) : unit =
   (:=) (magic l) v

let sref_of_ref (l : 'a ref) : sref =
   (magic l)

let ref_of_sref (l : sref) : 'a ref =
   (magic l)


let show n =
   Printf.printf "%d\n" n

let () =

   let x = sref 3 in
   let n : int = sget x in
   show n;

   let y : int ref = ref_of_sref x in
   show (!y);
   show (sget x : int);

   let z = sref_of_ref (ref 8) in
   show (sget z : int);

   sset x true;
   let r : int = sget x in
   show r;

   sset x (3.54);
   let r : float = sget x in
   print_float r
