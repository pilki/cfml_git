open OrderedSig

module type Heap =
sig
  module Element : Ordered

  type heap

  val empty : heap
  val is_empty : heap -> bool

  val insert : Element.t -> heap -> heap
  val merge : heap -> heap -> heap

  val find_min : heap -> Element.t 
  val delete_min : heap -> heap  
end
