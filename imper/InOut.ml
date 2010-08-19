
let std_dup_sum () =
   let nb = read_int() in
   let s = ref 0 in
   for i = 1 to nb do 
      let x = read_int() in
      print_int x;
      s := !s + x;
   done;
   print_int !s

