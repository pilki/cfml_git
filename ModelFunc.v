Set Implicit Arguments.
Require Import LibCore.

(** In this development, we give a concrete implementation
    to our axioms, using a deep embedding of the source language.

    We also to define in the logic the sort RType which contains
    all the types that are the reflect of some ML type, and we
    prove that, for each type A of sort RType, there exists a bijection
    between Coq values of type A and a subset of program values. *)


(************************************************************)
(* * Source language syntax and semantics *)

(** Representation of variables *)

Definition var := int.

(** Syntax of the source language *)

Inductive trm : Type :=
  | trm_var : var -> trm
  | trm_int : int -> trm
  | trm_pair : trm -> trm -> trm
  | trm_inj : bool -> trm -> trm
  | trm_fix : var -> var -> trm -> trm
  | trm_let : var -> trm -> trm -> trm
  | trm_app : trm -> trm -> trm.

(** Characterization of values from the source language *)

Inductive value : trm -> Prop := 
  | value_int : forall n,
      value (trm_int n)
  | value_pair : forall v1 v2,
      value v1 -> value v2 -> value (trm_pair v1 v2)
  | value_inj : forall b v1,
      value v1 -> value (trm_inj b v1)
  | value_fix : forall f x t, 
      value (trm_fix f x t).

(** Definition of capture-avoiding substitution *)

Fixpoint subst (x : var) (v : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_var y => if x == y then v else t
  | trm_int n => trm_int n
  | trm_pair t1 t2 => trm_pair (subst x v t1) (subst x v t2)
  | trm_inj b t1 => trm_inj b (subst x v t1)
  | trm_fix f y t1 => if x == y then t else if x == f then t else
                      trm_fix f y (subst x v t1)
  | trm_let y t1 t2 => if x == y then trm_let y (subst x v t1) t2
                       else trm_let y (subst x v t1) (subst x v t2)
  | trm_app t1 t2 => trm_app (subst x v t1) (subst x v t2)
  end.

(** Big-step semantics of the source language *)

Inductive red : trm -> trm -> Prop :=
  | red_val : forall v,
      value v ->
      red v v
  | red_let : forall x t1 t2 v1 v2,
      red t1 v1 ->
      red (subst x v1 t2) v2 ->
      red (trm_let x t1 t2) v2
  | red_fix : forall f x t v1 v2,
      red (subst f (trm_fix f x t) (subst x v1 t)) v2 ->
      red (trm_app (trm_fix f x t) v1) v2.

(** Proof that the source language is deterministic *)

Lemma red_deterministic : forall t v1 v2,
  red t v1 -> red t v2 -> v1 = v2.
Proof.
  introv Red1. gen v2. induction Red1; introv Red2.
  inversions Red2; try solve [inversions H]. auto.
  inversions Red2. inversions H. rewrite~ (IHRed1_1 v3) in IHRed1_2.
  inversions Red2. inversions H. auto. 
Qed.

(** Grammar of ground types *)

Inductive typ : Type :=
  | typ_int   : typ
  | typ_prod  : typ -> typ -> typ
  | typ_sum   : typ -> typ -> typ
  | typ_arrow : typ -> typ -> typ.


(************************************************************)
(* * Construction of the type Func *)

(** Definition of [Func] as the set of ML functions *)

Definition Func := {v:trm | exists f x t, v = trm_fix f x t}.

(** Coercion for viewing a value of type [Func] as the type [trm] *)

Coercion Func_to_trm (F:Func) := let (v,_) := F in v.

(** [Func] is inhabited *)

Instance Func_inhab : Inhab Func.
Proof. constructor. econstructor. exists~ 0%nat 0%nat (trm_int 0). Qed.


(************************************************************)
(* ** Reflected types *)

(** A logical type [A] if "reflected" if there exists a bijection
    between values of type [A] and program values. *)

Class reflected A := 
  { encode : A -> trm;
    decode : trm -> option A;
    encode_decode : forall V, decode (encode V) = Some V; 
    encode_values : forall V, value (encode V) }.
 
(** Since encoders are bijective, they are in injective *)

Lemma encode_inj : forall (A:Type) (HA:reflected A) (V1:A) (V2:A),
  encode V1 = encode V2 -> V1 = V2.
Proof.
  introv Eq. cuts H: (Some V1 = Some V2). inversions~ H.
  do 2 rewrite <- encode_decode. fequals.
Qed.


(************************************************************)
(* ** Reflection of types *)

(** Computation of <T> from a ML type T *)

Definition type_default := int.

Fixpoint lift_typ (T:typ) {struct T} : Type :=
  match T with
  | typ_int => int
  | typ_prod T1 T2 => prod (lift_typ T1) (lift_typ T2)
  | typ_sum T1 T2 => sum (lift_typ T1) (lift_typ T2)
  | typ_arrow T1 T2 => Func
  end.

(** A [RType] is a type equal to the reflection of some closed ML type.
    Note: a value of sort RType also admits the sort Type. *)

Record RType := 
  { RType_type :> Type; 
    RType_typ : typ;
    RType_eq : RType_type = lift_typ RType_typ }.

(** In the following, we show that for any ML type T,
    its reflect <T> is "reflected", in the sense that
    values of type <T> are in bijection with some ML values. 

    Remark: we do not prove that the image of the encoding
    of values of type <T> are exactly values of type T.
    For this to be possible, we would need to restrict 
    [Func] to the set of well-typed functions. This 
    construction is quite technical, and we leave it to
    future work. *)

(** Reflection for [int] *)

Definition encode_int n := 
  trm_int n.

Definition decode_int t :=
  match t with
  | trm_int n => Some n
  | _ => None
  end.

Instance reflected_int : reflected int.
Proof.
  apply~ (@Build_reflected _ encode_int decode_int).
  intros. apply value_int.
Qed.

(** Reflection for [prod] *)

Definition encode_prod {A1 A2} {R1:reflected A1} {R2:reflected A2} V :=
  let (V1,V2) := (V:A1*A2) in trm_pair (encode V1) (encode V2).

Definition decode_prod {A1 A2} {R1:reflected A1} {R2:reflected A2} t 
  : option (A1 * A2) :=
  match t with
  | trm_pair t1 t2 => 
     match decode t1, decode t2 with
     | Some V1, Some V2 => Some (V1,V2)
     | _,_ => None
     end
  | _ => None
  end.

Instance reflected_prod : forall A1 A2 {R1:reflected A1} {R2:reflected A2},
  reflected (A1 * A2)%type.
Proof.
  intros. apply (@Build_reflected _ encode_prod decode_prod).
  intros [V1 V2]. simpl. do 2 rewrite encode_decode. auto.
  intros [V1 V2]. apply value_pair; apply encode_values.
Qed.

(** Reflection for [sum] *)

Definition encode_sum {A1 A2} {R1:reflected A1} {R2:reflected A2} (V:A1+A2) :=
  match V with 
  | inl V1 => trm_inj true (encode V1)
  | inr V2 => trm_inj false (encode V2)
  end.
 
Definition decode_sum {A1 A2} {R1:reflected A1} {R2:reflected A2} t 
  : option (A1 + A2) :=
  match t with
  | trm_inj true t1 => 
     match decode t1 with
     | Some V1 => Some (inl V1)
     | _ => None
     end
  | trm_inj false t1 => 
     match decode t1 with
     | Some V1 => Some (inr V1)
     | _ => None
     end
  | _ => None
  end.

Instance reflected_sum : forall A1 A2 {R1:reflected A1} {R2:reflected A2},
  reflected (A1 + A2)%type.
Proof.
  intros. apply (@Build_reflected _ encode_sum decode_sum).
  intros V. destruct V; simpl; rewrite encode_decode. auto. auto.
  intros V. destruct V; simpl; apply value_inj; apply encode_values.
Qed.

(** Reflection for [Func] *)

Definition encode_func (v:Func) := 
  Func_to_trm v.

(* [decode_func] is the identity modulo the fact that we need
   to prove that a fixpoint is a term that admits the type Func *)

Definition decode_func t :=
  match t as t' return (t = t' -> option Func) with
  | trm_fix f x t1 => fun Eq => Some
      (exist _ t
         (ex_intro _ f
            (ex_intro _ x
               (ex_intro _ t1 Eq))))
  | _ => fun _ => None
  end (refl_equal t).

(* The same definition, using tactics *)

Definition decode_func' (t : trm) : option Func.
Proof.
  gen_eq p: t. case t; introv Eq.
  exact None.
  exact None.
  exact None.
  exact None.
  refine (Some _). eapply exist. exists___. apply Eq.
  exact None.
  exact None.
Defined.

Instance reflected_func : reflected Func.
Proof.
  apply (@Build_reflected _ encode_func decode_func).
  intros F. destruct F as [t [f [x [t1 Eq]]]].
   simpl. destruct t; tryfalse.
   injection Eq. intros. subst.
   simpl. fequals_rec. 
  intros F. destruct F as [t [f [x [t1 Eq]]]].
   simpl. subst. apply value_fix.
Qed.

(** The reflection of any ML type is "reflected", if the type
    variables that it contains are themselves "reflected" *)

Lemma reflected_typ : forall (T:typ),
  reflected (lift_typ T).
Proof.
  intros T. induction T; simpl.
  apply~ reflected_int.
  simpls. apply~ reflected_prod.
  simpls. apply~ reflected_sum.
  apply~ reflected_func.
Qed.

(* All Coq types of sort [RTypes] are "reflected" *)

Lemma reflected_rtype : forall (A:RType), (reflected A).
Proof.
  intros [A T E]. simpl. rewrite E. apply reflected_typ.
Qed.

(** Shorthand to turn a [RType] into as [reflected] *)

Definition refl := reflected_rtype.


(************************************************************)
(* * Construction of AppReturns and its two properties *)

Definition AppReturns {A B:RType} (F:Func) (V:A) (P:B->Prop) :=
  exists V':B, P V' /\ 
  red (trm_app F (@encode _ (refl A) V)) (@encode _ (refl B) V').

Lemma AppReturns_concrete : 
  forall {A B:RType} (F:Func) (V:A) (P:B->Prop),
  AppReturns F V P <-> exists V', P V' /\ AppReturns F V (= V').
Proof.
  split; intros H.
  destruct H as [V' [H1 H2]]. exists V'. split. auto.
   exists V'. split. auto. auto.
  destruct H as [V' [H1 [V'' [H2 H3]]]]. exists V'.
   split. auto. subst. auto.
Qed.

Lemma AppReturns_deterministic :
  forall {A B:RType} (F:Func) (V:A) (V1' V2':B),
  AppReturns F V (= V1') -> AppReturns F V (= V2') -> V1' = V2'.
Proof.
  introv [VA' [H11 H12]] [VB' [H21 H22]]. subst.
  apply* encode_inj. eapply red_deterministic; eauto. 
Qed. 






 