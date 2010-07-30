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
  xgo. sets I: (fun n:int => x ~> Ref Id n).
  xfun (counter_spec I). xgo*. xret. hsimpl~ I.
Qed.

(* Details of the proof:

  xcf. xgo. 
  xfun (counter_spec (fun n => x ~> RefOn n)).
    xapp. intro_subst. xapp. xret. ximpl~.
  xret. ximpl~.

*)

(* details of hsimpl:

hsimpl_setup tt.
hsimpl_step tt.
apply hsimpl_cancel_eq_1.
eapply refl_equal.
hsimpl_step tt.
hsimpl_step tt.
hsimpl_step tt.

*)
