open MyLib

type 'a tree = ('a * 'a tree * 'a tree) ref

let copy_tree (copy_elem : 'a->'a) (t:'a tree) : 'a tree =
  let rec copy (t:'a tree) : 'a tree =
     if t == null then null else
     let (x,t1,t2) = !t in
     ref (copy_elem x, copy t1, copy t2)
     in
  copy t  
