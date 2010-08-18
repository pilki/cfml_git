

let rec map f = function
    [] -> []
  | a::l -> let r = f a in r :: map f l

let rec iter f = function
    [] -> ()
  | a::l -> f a; iter f l

let rec fold_left f accu l =
  match l with
    [] -> accu
  | a::l -> fold_left f (f accu a) l

let rec fold_right f l accu =
  match l with
    [] -> accu
  | a::l -> f a (fold_right f l accu)

