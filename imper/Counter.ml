open MutableList

(** Creation and manipulation of counter functions *)

let make_counter () =
   let r = ref 0 in
   let f () = incr r; !r in
   f

(** Definition of the ignore function used in the example *)

let ignore x = ()

(** Iterating over a mutable list of counter functions *)

let step_all_imper (l : (unit->int) mlist) = 
  miter (fun (f:unit->int) -> ignore (f())) l



