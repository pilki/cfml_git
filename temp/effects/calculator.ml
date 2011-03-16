
module type CalculatorSig =
sig
   type t
   val make : unit -> t 
   val add : t -> int -> unit
   val sum : t -> int
end

module CalculatorImpl : CalculatorSig =
module
   type t = ref int
   let make () = ref 0
   let add c x = c <- !c + x
   let sum c = !c   
end
