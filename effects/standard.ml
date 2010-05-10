
(** exceptions *)

exception BrokenInvariant
exception EmptyStructure


(** references *)

type 'a ref = { mutable contents : 'a }

let ref x = { contents = x}

let get r = r.contents

let set r x = r.contents <- x


(** *)


