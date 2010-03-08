open OrderedSig

module type Sortable =
sig
  module Element : Ordered

  type sortable

  val empty : sortable
  val add : Element.t -> sortable -> sortable
  val sort : sortable -> Element.t list
end
