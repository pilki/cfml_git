(*

Parameter Channel : forall (L:list dyn) (l:loc), hprop.

Notation "l ~>> L" := (l ~> Channel L)
  (at level 32, no associativity).

Spec ml_read_int () |R>> forall L,
  R (stdin ~>> n::L) (||=n|| \*+ stdin ~>> L)

Spec ml_print_int n |R>> forall L,
  R (stdout ~>> L) (# stdout ~>> L & n)

Spec std_dup_sum () |R>> forall n L Li Lo,  
  n = length L ->
  R (stdin ~>> Channel n::L++Li \* stdout ~>> Lo)
    (# stdin ~>> Li \* stdout ~>> Lo ++ L & (fold plus 0 L))

*)