Set Implicit Arguments.
Require Import LibCore.
Require Import CFPrim CFTactics.
Require Import Counter_ml.


Ltac remove_head_unit tt :=
  repeat match goal with 
  | |- unit -> _ => intros _
  end.

Ltac xbody_base_intro tt ::=
  xbody_core ltac:(fun _ => remove_head_unit tt; introv).

Ltac xgo_default solver cont ::=
  match ltac_get_tag tt with
  | tag_ret => xret; cont tt
  | tag_fail => xfail; cont tt
  | tag_done => xdone; cont tt
  | tag_apply => xapp
  | tag_seq => xseq; cont tt
  | tag_let_val => xval; cont tt
  | tag_let_trm => xlet; cont tt
  | tag_let_fun => fail
  | tag_body => fail
  | tag_letrec => fail
  | tag_case => xcases_real; cont tt 
  | tag_casewhen => fail 
  | tag_if => xif; cont tt
  | tag_alias => xalias; cont tt
  | tag_match ?n => xmatch; cont tt
  | tag_top_val => fail
  | tag_top_trm => fail
  | tag_top_fun => fail
  | tag_for => fail
  | tag_while => fail
  end.

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

(* Details:
  xcf. xgo. 
  xfun (counter_spec (fun n => x ~> RefOn n)).
    xapp. intro_subst. xapp. xret. ximpl~.
  xret. ximpl~.
*)


