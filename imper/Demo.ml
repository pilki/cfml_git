
type 'a cell = {
    content: 'a;
    mutable next: 'a cell
  }

let newx x q1 q2 = 
   let machin = {content = x; next = q1} in 
   machin.next <- q2;
   machin

