
let maxlen = 1000

let rand_array () =  
   Array.init maxlen (fun _ -> Random.int max_int)

type sarray = {
   mutable n : int array;
   mutable values : int array;
   mutable idx : int array;
   mutable back : int array;
   }

let create () =
  { n = 0; 
    values = rand_array();
    idx = rand_array();
    back = rand_array(); }

let valid i s =
   0 <= i && i < maxlen && s.back.(s.idx.(i)) = i

let get i s =
   if valid i s then s.val.(i) else 0

let set i v s =
   s.val.(i) <- v;
   if not (valid i s) then begin
      s.idx.(i) <- s.n;
      s.back.(i) <- i;
      s.n <- s.n + 1
   end

let harness () =
   let a = create 10 in
   let b = create 20 in
   assert (get 6 a = 0);
   assert (get 7 b = 0);
   set 5 1 a; 
   set 7 2 b;
   assert (get 0 a = 0);
   assert (get 0 b = 0)

