open Okasaki
open FiniteMapSig

(*
type 'a tree = Empty | Node of 'a * 'a tree * 'a tree

module TrieOfTree (M : FiniteMap) : FiniteMap =
struct

   type key = M.key tree
   type 'a map = Trie of 'a option * 'a map map M.map

   let empty = Trie (None, M.empty)

   let rec lookup : key -> 'a map -> 'a option = fun ks m ->
      match ks,m with
      | Empty, Trie (None,m) -> None
      | Empty, Trie (Some x,m) -> Some x
      | Node (k,a,b), Trie (v,m) -> 
          match M.lookup k m with
          | None -> None
          | Some m' -> 
              match lookup a m' with
              | None -> None
              | Some m'' -> lookup b m''

   let rec bind : key -> 'a -> 'a map -> 'a map = fun ks x m ->
      match ks,m with
      | Empty, Trie (_,m) -> Trie (Some x,m)
      | Node (k,a,b), Trie (v,m) -> 
         let tt = match M.lookup k m with
                  | None -> empty
                  | Some t -> t in
         let t = match M.lookup a tt with
                 | None -> empty
                 | Some t -> t in
         let t' = bind b x t in
         let tt' = bind a t' tt in
         Trie (v, M.bind k tt' m)
   
end

*)