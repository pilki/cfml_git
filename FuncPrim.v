Set Implicit Arguments.
Require Export FuncDefs FuncPrint.
Open Scope comp_scope.

(************************************************************)
(** Representation for base types *)

Instance int_rep : Rep int int := eq.

Instance bool_rep : Rep bool bool := eq.

Instance list_rep : forall `{Rep a A}, Rep (list a) (list A) := 
  fun l L => Forall2 rep l L.


(************************************************************)
(** Axiomatic specification of the primitive functions *)

Parameter ml_list_hd : val.

Parameter ml_list_hd_spec : forall A,
  Spec ml_list_hd (L:list A) |R>>
    forall X T, L = X::T -> R(=X).
Hint Extern 1 (RegisterSpec ml_list_hd) => Provide ml_list_hd_spec.

Parameter ml_list_tl : val.

Parameter ml_list_tl_spec : forall A,
  Spec ml_list_tl (L:list A) |R>>
    forall X T, L = X::T -> R(=T).
Hint Extern 1 (RegisterSpec ml_list_tl) => Provide ml_list_tl_spec.

Parameter ml_list_hd_repspec : forall `{Rep a A},
  RepSpec ml_list_hd (L;list a) |R>>
    forall X T, L = X::T -> R(X ; a).
Parameter ml_list_tl_repspec : forall `{Rep a A},
  RepSpec ml_list_tl (L;list a) |R>>
    forall X T, L = X::T -> R(T ; list a).


Parameter ml_plus : val.
Parameter ml_plus_spec : Total ml_plus x y >> = (x + y)%Z.
Hint Extern 1 (RegisterSpec ml_plus) => Provide ml_plus_spec.

Parameter ml_minus : val.
Parameter ml_minus_spec : Total ml_minus x y >> = (x - y)%Z.
Hint Extern 1 (RegisterSpec ml_minus) => Provide ml_minus_spec.

Parameter ml_eqb : val.
Parameter ml_eqb_int_spec : Total ml_eqb (x:int) (y:int) >> = (x == y).
Hint Extern 1 (RegisterSpec ml_eqb) => Provide ml_eqb_int_spec.

Parameter ml_nth : val.
Parameter ml_nth_spec : forall A, 
  Spec ml_nth (l:list A) (n:int) |R>> 
    ((0 <= n /\ n < length l)%Z -> R (Nth (Zabs_nat n) l)).
Hint Extern 1 (RegisterSpec ml_nth) => Provide ml_nth_spec.

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

Parameter ml_asr : val.
Parameter ml_asr_spec : Spec ml_asr (x:int) (y:int) |R>>
  (y = 1 -> R(= Zdiv x 2)). (* todo: check parentheses needed *)
Hint Extern 1 (RegisterSpec ml_asr) => Provide ml_asr_spec.

Parameter ml_neq : val.
Parameter ml_opp : val.
Parameter ml_mul : val.
Parameter ml_div : val.
Parameter ml_append : val.
Parameter ml_raise : val.
  (* .. yet to specify *)

Parameter compare : val. (* todo: until functors are supported *)

Parameter ml_reverse : val.
Parameter ml_reverse_spec : forall A,
  Total ml_reverse (l:list A) >> = LibList.rev l.
Hint Extern 1 (RegisterSpec ml_reverse) => Provide ml_reverse_spec.
