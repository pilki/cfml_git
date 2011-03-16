
type cell = {
   mutable parent : cell option;
   mutable children : cell list;
   value : int;
   sum : int;
   }

let create v =
   { parent = None;
     children = [];
     value = v;
     sum = v }

let rec delta d c =
   c.sum <- c.sum + d;
   match c.parent with
   | None -> ()
   | Some p -> delta d p

let udpate v c = 
   let diff = v c.value in
   delta diff c

let add_child p c =
   c.parent <- Some p;
   p.children <- c::p.children
   delta c.sum p

let disloge c =
   let p = c.parent in
   p.children <- List.filter ((<>) p) p.children;
   delta c.sum p;
   c.parent <- None
   
let harness () =
   let a = create 5 in
   let b = create 7 in
   add_child a b;
   assert (a.sum = 12);
   update 17 b;
   assert (a.sum = 22);
   let c = create 10 in
   add_child b c;
   dislogde b;
   assert (b.sum = 27)

