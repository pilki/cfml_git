Definition L := maxlen.

Definition idx_back_coherent n Back Idx :=
   forall k, index n k -> index L (Back\[k]) /\ Idx\[Back\[k]] = k.

Definition back_pointed n Back i :=
  exists k, index n k /\ i = Back\[k].

Definition repr_valid n Back Val T :=
  forall i, index L i -> 
    If (back_pointed n Back i) 
      then T\[i] = Val\[i] 
      else T\[i] = 0.

(* Definition of "l ~> Sarray T" *)

Definition Sarray (T:array int) (l:loc) : heap -> Prop :=
  hexists n (val idx back : loc) (Val Idx Back : array int),
    l ~> sparse_array_of n val idx back 
  * val ~> Array Pure Val
  * idx ~> Array Pure Idx
  * back ~> Array Pure Back
  * [ size Val = L /\ 
      size Idx = L /\
      size Back = L /\
      idx_back_coherent n Back Idx /\
      repr_valid n Back Val T ].


Lemma used_cell_test_correct : forall n Back Idx i, 
  index L i -> idx_back_coherent n Back Idx ->
  (back_pointed n Back i) <-> (index n (Idx\[i]) /\ Back\[Idx\[i]] = i).

Lemma create_spec :
  Spec create size |R>> (0 <= size <= L) -> 
    R [] (fun l => l ~> Sarray (CoqArray.make size default)).
  
  spec_1 create (fun size R => ...).

Lemma get_spec :
  Spec get i l |R>> forall T, index T i -> 
    R (l ~> Sarray T) (fun v => l ~> Sarray T * [v = T\[i]]).
    
    keep R (l ~> Sarray T) (= T\[i]).

Lemma set_spec :
  Spec set i v l |R>> forall T, index T i ->
    R (l ~> Sarray T) (# l ~> Sarray (T\[i:=v])



(* ---------
invariant:
   0 <= n < size <= maxlen
   forall i, 0 <= i < n -> 0 <= back[i] < sz /\ idx[back[i]] = i
*)

  (*back_pointed: index n (Idx\[i]) /\ Back\[Idx\[i]] = i *)