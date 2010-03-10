open Okasaki

type 'a stream_cell = Nil | Cons of 'a * 'a stream
 and 'a stream = 'a stream_cell Lazy.t

let rec (++) (t1:'a stream) (t2:'a stream) = 
   lazy begin match !$ t1 with
   | Nil -> !$ t2
   | Cons (x, s) -> Cons (x, s ++ t2)
   end

let rec take n s = 
   lazy begin match n, !$ s with
   | 0, _ -> Nil
   | _, Nil -> Nil
   | _, Cons(x,s) -> Cons (x, take (n - 1) s)
   end

let drop n s =
   let rec drop' n (s:'a stream) = 
      lazy begin match n, !$ s with
      | 0, s -> s
      | _, Nil -> Nil
      | _, Cons(x, s) -> !$ (drop' (n - 1) s) end in
   drop' n s

let reverse s =
   let rec reverse' r t = 
      lazy begin match !$ t with
      | Nil -> !$ r
      | Cons(x,s) -> !$ (reverse' (lazy (Cons (x,r))) s)
      end in
   reverse' (lazy Nil) s 

let to_list s = 
   let rec aux acc = function
      | lazy Nil -> List.rev acc
      | lazy (Cons(x,s)) -> aux (x::acc) s
      in
   aux [] s

let of_list l =
   let rec aux acc = function
      | [] -> lazy Nil
      | x::l' -> aux (lazy (Cons (x, acc))) l'
      in
   aux (lazy Nil) l