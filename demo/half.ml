
(** This function takes a natural number [n] as input, and
    - returns [n/2] if [n] is a nonnegative even integer
    - is unspecified otherwise

    This simple function is particularly interesting with 
    respect to program verification, as it it a partial, 
    recursive function, whose specification is stated using
    an auxiliary variable. *)



let rec half x = 
   if x = 0 then 0
   else if x = 1 then failwith "error"
   else 1 + half (x-2)



(** Composition of two functions *)

let compose f1 f2 x = f1 (f2 x)


(** Composition of half with itself *)

let quarter = compose half half


(** Composition of half with succ *)

let succ_half = compose half (fun x -> x + 2)
