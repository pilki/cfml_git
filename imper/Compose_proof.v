Set Implicit Arguments.
Require Import CFLib Compose_ml.


Notation "'Let' x ':' T ':=' F1 'in' F2" :=
  (!T (fun H Q => exists Q1, F1 H Q1 /\ forall x:T, F2 (Q1 x) Q))
  (at level 69, a at level 0, x ident, right associativity, only parsing) : charac.



(********************************************************************)
(* ** Verification of Compose *)

Lemma compose_spec : forall A B C,
  Spec compose (g:func) (f:func) (x:A) |R>>
     forall (H:hprop) (Q:C->hprop),
     (Let y:B := App f x; in App g y;) H Q -> R H Q.
Proof. xcf. introv M. apply M. Qed.

Hint Extern 1 (RegisterSpec compose) => Provide compose_spec.


(********************************************************************)
(* ** An example of composition *)

(** [incr_ret] increments a reference and returns its argument *)

Lemma incr_ret_spec : 
   Spec incr_ret r |R>> forall n, 
      R (r ~> Ref Id n) (\= r \*+ r ~> Ref Id (n+1)).
Proof. xgo~. Qed.

Hint Extern 1 (RegisterSpec incr_ret) => Provide incr_ret_spec.

(** [decr_ret] decrements a reference and returns its argument *)

Lemma decr_ret_spec : 
   Spec decr_ret r |R>> forall n, 
      R (r ~> Ref Id n) (\= r \*+ r ~> Ref Id (n-1)).
Proof. xgo~. Qed.

Hint Extern 1 (RegisterSpec decr_ret) => Provide decr_ret_spec.

(** The term [test r] computes [compose incr_ret decr_ret r]. *)

Lemma test_spec :
  Spec test r |R>> forall (n:int),
    R (r ~> Ref Id n) (\= r \*+ r ~> Ref Id n).
Proof.
  xcf. intros. xapp. xapps. xapps. hsimpl.
  math_rewrite (n+1-1 = n). hsimpl~. 
Qed.



