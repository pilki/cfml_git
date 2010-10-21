
let maxlen = 1000

type sarray = {
   mutable n : int;
   mutable values : int array;
   mutable idx : int array;
   mutable back : int array;
   }

let valid i s =
  let k = s.idx.(i) in
  if 0 <= k && k < s.n 
    then s.back.(k) = i
    else false

(* todo: faire le vrai && à la place du if *)

let get i s =
   if valid i s then s.values.(i) else 0

let set i v s =
   s.values.(i) <- v;
   if not (valid i s) then begin
      let k = s.n in
      s.idx.(i) <- k;
      s.back.(k) <- i;
      s.n <- k + 1
   end

(*

let rand_array () =  
   Array.init maxlen (fun _ -> Random.int max_int)

let create () =
  { n = 0; 
    values = rand_array();
    idx = rand_array();
    back = rand_array(); }

let harness () =
   let a = create 10 in
   let b = create 20 in
   assert (get 6 a = 0);
   assert (get 7 b = 0);
   set 5 1 a; 
   set 7 2 b;
   assert (get 0 a = 0);
   assert (get 0 b = 0)
*)
