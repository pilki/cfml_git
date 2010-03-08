open Okasaki
open FiniteMapSig

module Trie (M : FiniteMap) : FiniteMap =
struct

   type key = M.key list
   type 'a map = Trie of 'a option * 'a map M.map

   let empty = Trie (None, M.empty)

   let rec lookup ks m =
      match ks,m with
      | [], Trie (None,m) -> None
      | [], Trie (Some x,m) -> Some x
      | k::ks', Trie (v,m) -> 
          match M.lookup k m with
          | None -> None
          | Some m' -> lookup ks' m'

   let rec bind ks x m = 
      match ks,m with
      | [], Trie (_,m) -> Trie (Some x,m)
      | k::ks', Trie (v,m) -> 
         let t = match M.lookup k m with
                 | None -> empty
                 | Some t -> t in
         let t' = bind ks' x t in
         Trie (v, M.bind k t' m)
   
end

