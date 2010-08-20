Set Implicit Arguments.

Require Import CFPrim.

Notation
"''_m1'" := (`0) (at level 0) : atom_scope.

Notation
"''_x24'" := (`1`0) (at level 0) : atom_scope.

Notation
"''_x19'" := (`2`0) (at level 0) : atom_scope.

Notation
"''_x12'" := (`1`1`0) (at level 0) : atom_scope.

Notation
"''_x7'" := (`1`2`0) (at level 0) : atom_scope.

Notation
"''_m2'" := (`2`1`0) (at level 0) : atom_scope.

Notation
"''_x5'" := (`2`2`0) (at level 0) : atom_scope.

Notation
"''_x8'" := (`1`1`1`0) (at level 0) : atom_scope.

Notation
"''_x1'" := (`1`1`2`0) (at level 0) : atom_scope.

Inductive
term  : Type := 
  | Tvar : (int -> term)
  | Tint
: (int -> term)
  | Tfun : (int -> (term -> term))

 | Tapp : (term -> (term -> term)).

Hint Constructors
term : typeclass_instances.

Global Instance subst_type_inhab
: (Inhab val).

Proof. inhab. Qed.



Parameter subst
: val.

Parameter subst_cf : (tag tag_top_fun None
(tag tag_body None (forall K : (int -> (term -> (term
-> ((hprop -> ((_ -> hprop) -> Prop)) -> Prop)))),
((is_spec_3 K) -> ((forall x : int, (forall v : term,
(forall t : term, ((((K x) v) t) (tag (tag_match 4%nat)
(Some '_m1) (tag tag_case None (local (fun H : hprop
=> (fun Q : (_ -> hprop) => ((Logic.and (forall y :
int, (((Logic.eq t) (Tvar y)) -> (((tag tag_if None
(local (fun H : hprop => (fun Q : (_ -> hprop) => ((Logic.and
(((Logic.eq (((fun _y _z => istrue (_y = _z)) x) y))
true) -> (((tag tag_ret None (local (fun H : hprop
=> (fun Q : (_ -> hprop) => ((pred_le H) (Q v))))))
H) Q))) (((Logic.eq (((fun _y _z => istrue (_y = _z))
x) y)) false) -> (((tag tag_ret None (local (fun H
: hprop => (fun Q : (_ -> hprop) => ((pred_le H) (Q
t)))))) H) Q))))))) H) Q)))) ((forall y : int, (Logic.not
((Logic.eq t) (Tvar y)))) -> (((tag tag_case None (local
(fun H : hprop => (fun Q : (_ -> hprop) => ((Logic.and
(forall _p0 : int, (((Logic.eq t) (Tint _p0)) -> (((tag
tag_ret None (local (fun H : hprop => (fun Q : (_ ->
hprop) => ((pred_le H) (Q t)))))) H) Q)))) ((forall
_p0 : int, (Logic.not ((Logic.eq t) (Tint _p0)))) ->
(((tag tag_case None (local (fun H : hprop => (fun
Q : (_ -> hprop) => ((Logic.and (forall y : int, (forall
b : term, (((Logic.eq t) ((Tfun y) b)) -> (((tag tag_let_trm
(Some '_x7) (local (fun H : hprop => (fun Q : (_ ->
hprop) => (Logic.ex (fun Q1 : (term -> hprop) => ((Logic.and
(((tag tag_if None (local (fun H : hprop => (fun Q
: (_ -> hprop) => ((Logic.and (((Logic.eq (((fun _y
_z => istrue (_y = _z)) x) y)) true) -> (((tag tag_ret
None (local (fun H : hprop => (fun Q : (_ -> hprop)
=> ((pred_le H) (Q b)))))) H) Q))) (((Logic.eq (((fun
_y _z => istrue (_y = _z)) x) y)) false) -> (((tag
tag_let_trm (Some '_x12) (local (fun H : hprop => (fun
Q : (_ -> hprop) => (Logic.ex (fun Q1 : (term -> hprop)
=> ((Logic.and (((tag tag_apply None ((((((((@app_3
int) term) term) term) subst) x) v) b)) H) Q1)) (forall
_x12 : term, (((tag tag_ret None (local (fun H : hprop
=> (fun Q : (_ -> hprop) => ((pred_le H) (Q _x12))))))
(Q1 _x12)) Q))))))))) H) Q))))))) H) Q1)) (forall _x7
: term, (((tag tag_ret None (local (fun H : hprop =>
(fun Q : (_ -> hprop) => ((pred_le H) (Q ((Tfun y)
_x7))))))) (Q1 _x7)) Q))))))))) H) Q))))) ((forall
y : int, (forall b : term, (Logic.not ((Logic.eq t)
((Tfun y) b))))) -> (((tag tag_case None (local (fun
H : hprop => (fun Q : (_ -> hprop) => ((Logic.and (forall
t1 : term, (forall t2 : term, (((Logic.eq t) ((Tapp
t1) t2)) -> (((tag tag_let_trm (Some '_x19) (local
(fun H : hprop => (fun Q : (_ -> hprop) => (Logic.ex
(fun Q1 : (term -> hprop) => ((Logic.and (((tag tag_apply
None ((((((((@app_3 int) term) term) term) subst) x)
v) t1)) H) Q1)) (forall _x19 : term, (((tag tag_let_trm
(Some '_x24) (local (fun H : hprop => (fun Q : (_ ->
hprop) => (Logic.ex (fun Q1 : (term -> hprop) => ((Logic.and
(((tag tag_apply None ((((((((@app_3 int) term) term)
term) subst) x) v) t2)) H) Q1)) (forall _x24 : term,
(((tag tag_ret None (local (fun H : hprop => (fun Q
: (_ -> hprop) => ((pred_le H) (Q ((Tapp _x19) _x24)))))))
(Q1 _x24)) Q))))))))) (Q1 _x19)) Q))))))))) H) Q)))))
((forall t1 : term, (forall t2 : term, (Logic.not ((Logic.eq
t) ((Tapp t1) t2))))) -> (((tag tag_done None (local
(fun H : hprop => (fun Q : (_ -> hprop) => True))))
H) Q))))))) H) Q))))))) H) Q))))))) H) Q))))))))))))
-> ((spec_3 K) subst)))))).

Hint Extern 1 (RegisterCf
subst) => Provide subst_cf.

Global Instance eval_type_inhab
: (Inhab val).

Proof. inhab. Qed.



Parameter eval
: val.

Parameter eval_cf : (tag tag_top_fun None (tag
tag_body None (forall K : (term -> ((hprop -> ((_ ->
hprop) -> Prop)) -> Prop)), ((is_spec_1 K) -> ((forall
t : term, ((K t) (tag (tag_match 3%nat) (Some '_m1)
(tag tag_case None (local (fun H : hprop => (fun Q
: (_ -> hprop) => ((Logic.and (forall y : int, (((Logic.eq
t) (Tvar y)) -> (((tag tag_fail None (local (fun H
: hprop => (fun Q : (_ -> hprop) => False)))) H) Q))))
((forall y : int, (Logic.not ((Logic.eq t) (Tvar y))))
-> (((tag tag_case None (local (fun H : hprop => (fun
Q : (_ -> hprop) => ((Logic.and (forall t1 : term,
(forall t2 : term, (((Logic.eq t) ((Tapp t1) t2)) ->
(((tag tag_let_trm (Some '_x1) (local (fun H : hprop
=> (fun Q : (_ -> hprop) => (Logic.ex (fun Q1 : (term
-> hprop) => ((Logic.and (((tag tag_apply None ((((@app_1
term) term) eval) t1)) H) Q1)) (forall _x1 : term,
(((tag (tag_match 1%nat) (Some '_m2) (tag tag_case
None (local (fun H : hprop => (fun Q : (_ -> hprop)
=> ((Logic.and (forall y : int, (forall b : term, (((Logic.eq
_x1) ((Tfun y) b)) -> (((tag tag_let_trm (Some '_x8)
(local (fun H : hprop => (fun Q : (_ -> hprop) => (Logic.ex
(fun Q1 : (term -> hprop) => ((Logic.and (((tag tag_apply
None ((((@app_1 term) term) eval) t2)) H) Q1)) (forall
_x8 : term, (((tag tag_let_trm (Some '_x5) (local (fun
H : hprop => (fun Q : (_ -> hprop) => (Logic.ex (fun
Q1 : (term -> hprop) => ((Logic.and (((tag tag_apply
None ((((((((@app_3 int) term) term) term) subst) y)
_x8) b)) H) Q1)) (forall _x5 : term, (((tag tag_apply
None ((((@app_1 term) term) eval) _x5)) (Q1 _x5)) Q)))))))))
(Q1 _x8)) Q))))))))) H) Q))))) ((forall y : int, (forall
b : term, (Logic.not ((Logic.eq _x1) ((Tfun y) b)))))
-> (((tag tag_fail None (local (fun H : hprop => (fun
Q : (_ -> hprop) => False)))) H) Q)))))))) (Q1 _x1))
Q))))))))) H) Q))))) ((forall t1 : term, (forall t2
: term, (Logic.not ((Logic.eq t) ((Tapp t1) t2)))))
-> (((tag tag_case None (local (fun H : hprop => (fun
Q : (_ -> hprop) => ((Logic.and (forall _p0 : term,
(((Logic.eq t) _p0) -> (((tag tag_ret None (local (fun
H : hprop => (fun Q : (_ -> hprop) => ((pred_le H)
(Q t)))))) H) Q)))) ((forall _p0 : term, (Logic.not
((Logic.eq t) _p0))) -> (((tag tag_done None (local
(fun H : hprop => (fun Q : (_ -> hprop) => True))))
H) Q))))))) H) Q))))))) H) Q)))))))))) -> ((spec_1
K) eval)))))).

Hint Extern 1 (RegisterCf eval) =>
Provide eval_cf.
