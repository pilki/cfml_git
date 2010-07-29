Set Implicit Arguments.
Require Import LibCore CFPrim Counter_ml.


(*------------------------------------------------------------------*)
(* code:

let gensym () =
   let x = ref 0 in
   let f () = 
      let n = !x in
      x := n+1;
      n in
   f

*)

(*------------------------------------------------------------------*)

Definition counter_spec I f :=
  Spec f () |R>> forall n, R (I n) (\=n \*+ (I (n+1))).

Lemma gensym_spec : Spec gensym () |R>>
  R [] (fun f => Hexists I:int->hprop, 
          (I 0) \* [counter_spec I f]).
Proof.
  xgo. xfun (counter_spec (fun n => x ~> RefOn n)); xgo*. 
Qed.

(* Details of the proof:

  xcf. xgo. 
  xfun (counter_spec (fun n => x ~> RefOn n)).
    xapp. intro_subst. xapp. xret. ximpl~.
  xret. ximpl~.

*)


