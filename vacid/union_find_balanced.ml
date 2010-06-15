
type state = {
   mutable nb_compo : int;
   mutable parent : int array;
   mutable compo_size : int array }

let create size =
   { nb_compo = size;
     parent = Array.init size (fun a -> a);
     compo_size = Array.make size 1; }

let get_nb_compo s =
   s.nb_compo

let rec find s a =
   if s.parent.(a) = a then a else begin
      let p = find s s.parent.(a) in
      s.parent.(a) <- p;
      p
   end

let joins s ra rb =
   s.parent.(ra) <- rb;
   s.compo_size.(rb) <- s.compo_size.(rb) + s.compo_size.(ra);
   s.nb_compo <- s.nb_compo - 1

let union s a b =
   let ra = find s a in
   let rb = find s b in
   if ra <> rb then begin
      if s.compo_size.(ra) < s.compo_size.(rb)
         then joins s ra rb
         else joins s rb ra
   end

let same_compo s a b =
   find s a = find s b
