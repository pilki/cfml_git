Set Implicit Arguments.
Require Export LibInt FuncDefs FuncPrint.

Hint Resolve (0%nat) : typeclass_instances.
Hint Resolve (0%Z) : typeclass_instances.
Hint Resolve @nil : typeclass_instances.
Hint Resolve true : typeclass_instances.
Hint Resolve @None : typeclass_instances.
Hint Resolve @pair : typeclass_instances.

Ltac inhab :=
  constructor; intros; try solve 
    [ eauto 10 with typeclass_instances 
    | constructor; eauto 10 with typeclass_instances 
    | apply arbitrary 
    | apply @arbitrary; eauto 10 with typeclass_instances ].


(************************************************************)
(** Representation for base types *)

Hint Extern 1 (@rep _ _ _ _ _) => simpl.

Hint Resolve @rep_unique : rep.

Ltac prove_rep := 
  fequals_rec; 
  try match goal with |- @eq (?T ?A) _ _ => let U := fresh in sets U:(T A) end;
  intuition eauto with rep.
  (* todo : appliquer directement rep_unique sur les buts ? *)

Instance int_rep : Rep int int.
Proof. apply (Build_Rep eq). congruence. Defined.

Instance bool_rep : Rep bool bool.
Proof. apply (Build_Rep eq). congruence. Defined.

Instance list_rep : forall `{Rep a A}, Rep (list a) (list A).
Proof.
  intros. apply (Build_Rep (fun l L => Forall2 rep l L)).
  induction x; introv H1 H2; inverts H1; inverts H2; prove_rep. 
Defined.

Lemma list_rep_cons : forall `{Rep a A} l L x X,
  rep l L -> rep x X -> rep (x::l) (X::L).
Proof. intros. constructors~. Qed.

Hint Resolve @list_rep_cons.

Instance prod_rep : forall `{Rep a1 A1} `{Rep a2 A2},
  Rep (a1 * a2) (A1 * A2).
Proof.
  intros. apply (Build_Rep (fun p P => match p,P with 
   (x,y),(X,Y) => rep x X /\ rep y Y end)).
  intros [x1 x2] [X1 X2] [Y1 Y2] H1 H2; prove_rep.
Defined.

Instance option_rep : forall `{Rep a A},
  Rep (option a) (option A).
Proof.
  intros. apply (Build_Rep (fun o O => match o,O with 
    | None, None => True
    | Some x, Some X => rep x X
    | _,_ => False end)).
  intros [x|] [X|] [Y|] H1 H2; prove_rep.
Defined.

Hint Extern 1 (@rep (list _) _ _ _ _) => simpl.
Hint Extern 1 (@rep (prod _ _) _ _ _ _) => simpl.
Hint Extern 1 (@rep (option _) _ _ _ _) => simpl.


(************************************************************)
(** Axiomatic specification of the primitive functions *)

(** Arithmetic *)

Parameter ml_plus : val.
Parameter ml_plus_spec : Total ml_plus x y >> = (x + y)%Z.
Hint Extern 1 (RegisterSpec ml_plus) => Provide ml_plus_spec.

Parameter ml_minus : val.
Parameter ml_minus_spec : Total ml_minus x y >> = (x - y)%Z.
Hint Extern 1 (RegisterSpec ml_minus) => Provide ml_minus_spec.

Parameter ml_eqb : val.
Parameter ml_eqb_int_spec : Total ml_eqb (x:int) (y:int) >> = (x == y).
Hint Extern 1 (RegisterSpec ml_eqb) => Provide ml_eqb_int_spec.

Parameter ml_leq : val.
Parameter ml_leq_spec : Total ml_leq x y >> = (x <= y)%I.
Hint Extern 1 (RegisterSpec ml_leq) => Provide ml_leq_spec.

Parameter ml_geq : val.
Parameter ml_geq_spec : Total ml_geq x y >> = (x >= y)%I.
Hint Extern 1 (RegisterSpec ml_geq) => Provide ml_geq_spec.

Parameter ml_lt : val.
Parameter ml_lt_spec : Total ml_lt x y >> = (x < y)%I.
Hint Extern 1 (RegisterSpec ml_lt) => Provide ml_lt_spec.

Parameter ml_gt : val.
Parameter ml_gt_spec : Total ml_gt x y >> = (x > y)%I.
Hint Extern 1 (RegisterSpec ml_gt) => Provide ml_gt_spec.

Parameter ml_and : val.
Parameter ml_and_spec : Total ml_and x y >> = (x && y).
Hint Extern 1 (RegisterSpec ml_and) => Provide ml_and_spec.

Parameter ml_or : val.
Parameter ml_or_spec : Total ml_or x y >> = (x || y).
Hint Extern 1 (RegisterSpec ml_and) => Provide ml_or_spec.
