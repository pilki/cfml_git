open NullPointers

type 'a mtree = ('a * 'a mtree * 'a mtree) ref

let copy_tree (copy_elem : 'a->'a) (t:'a mtree) : 'a mtree =
  let rec copy (t:'a mtree) : 'a mtree =
     if t == null then null else
     let (x,t1,t2) = !t in
     ref (copy_elem x, copy t1, copy t2)
     in
  copy t  
