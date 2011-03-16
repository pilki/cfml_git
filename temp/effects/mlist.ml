
type 'a mcell = Nil | Cons of 'a * 'a mlist
and 'a mlist = 'a mcell ref 

