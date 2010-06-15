
type state = {
   mutable nb_compo : int;
   mutable parent : int array; }

let create size =
   { nb_compo = size;
     parent = Array.init size (fun i -> i) }

let get_nb_compo s =
   s.nb_compo

let rec find s a =
   if s.parent.(a) = a 
      then a   
      else find s s.parent.(a)

let union s a b =
   let ra = find s a in
   let rb = find s b in
   s.parent.(ra) <- rb

let same_compo s a b =
   find s a = find s b


(*
let build_maze n =
   let s = create (n*n) in
   while get_nb_compo s > 1 do
*) 
