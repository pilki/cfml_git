open Okasaki
open QueueSig

module HoodMelvilleQueue : Queue = struct

   type 'a status = 
     | Idle
     | Reversing of int * 'a list * 'a list * 'a list * 'a list
     | Appending of int * 'a list * 'a list 
     | Finished of 'a list 

   type 'a queue = int * 'a list * 'a status * int * 'a list 

   let exec = function
     | Reversing (ok, x::f, f', y::r, r') -> Reversing (ok+1, f, x::f', r, y::r')
     | Reversing (ok, [], f', [y], r') -> Appending (ok, f', y::r')
     | Appending (0, f', r') -> Finished r'
     | Appending (ok, x::f', r') -> Appending (ok-1, f', x::r')
     | s -> s

   let invalidate = function
     | Reversing (ok, f, f', r, r') -> Reversing (ok-1, f, f', r, r')
     | Appending (0, f', x::r') -> Finished r'
     | Appending (ok, f', r') -> Appending (ok-1, f', r')
     | s -> s

   let exec2 (lenf, f, state, lenr, r) = 
     match exec (exec state) with
     | Finished newf -> (lenf, newf, Idle, lenr, r)
     | newstate -> (lenf, f, newstate, lenr, r)

   let check ((lenf, f, state, lenr, r) as q) = 
     if lenr <= lenf 
        then exec2 q                         
        else let newstate = Reversing (0, f, [], r, []) in
             exec2 (lenf+lenr, f, newstate, 0, [])

   let empty : 'a queue = (0, [], Idle, 0, [])

   let is_empty (lenf, _, _, _, _) = (lenf = 0)

   let snoc (lenf, f, state, lenr, r) x =
      check (lenf, f, state, lenr+1, x::r)
      
   let head = function
     | (_,[],_,_,_) -> raise EmptyStructure
     | (_,x::_,_,_,_) -> x

   let tail = function 
     | (_,[],_,_,_) -> raise EmptyStructure
     | (lenf, x::f', state, lenr, r) ->
        check (lenf-1, f', invalidate state, lenr, r)

end

