
module type HashedSig =
sig
   type t
   val equal : t -> t -> bool
   val hash : t -> int
end

module type Hashtable =
sig
   type key
   type 'a t
   val create : int -> 'a t
   val add : 'a t -> key -> 'a -> unit
   val rem : 'a t -> key -> unit
   val mem : 'a t -> key -> bool
   val find : 'a t -> key -> 'a
end

module HashtableSimple (H:HashedSig) : Hashtable with key = H.t =
struct

   type key = H.t

   type 'a t = (key * 'a) list array

   let bucket h k =
      (H.hash k) mod (Array.length h)

   let create n = 
      Array.create n []

   let rem h k =      
      let b = bucket h k in
      h.(b) <- List.filter (fun (k',_) -> not (H.equal k k')) h.(b)

   let mem h k =
      let b = bucket h k in
      List.exists (fun (k',_) -> H.equal k k') h.(b)

   let find h k =
      let b = bucket h k in
      snd (List.find (fun (k',_) -> H.equal k k') h.(b))

   let add h k x = 
      if not (mem h k) then begin
         let b = bucket h k in
         h.(b) <- (k,x)::h.(b)
      end

end
