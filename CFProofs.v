Set Implicit Arguments.
Require Import LibCore LibEpsilon.

(** In this development, we give a concrete implementation
    to our axioms, using a deep embedding of the source language.

    We also to define in the logic the sort RType which contains
    all the types that are the reflect of some ML type, and we
    prove that, for each type A of sort RType, there exists a bijection
    between Coq values of type A and a subset of program values. *)


(************************************************************)
(* * Source language syntax *)

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
  | trm_app : trm -> trm -> trm
  | trm_ifz : trm -> trm -> trm -> trm
  | trm_fail : trm.

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


(************************************************************)
(* * Source language semantics *)

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
  | trm_ifz t1 t2 t3 => trm_ifz (subst x v t1) (subst x v t2) (subst x v t3)
  | trm_fail => trm_fail
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
      red (trm_app (trm_fix f x t) v1) v2
  | red_ifz : forall t1 t2 t3 n v,
      red t1 (trm_int n) ->
      red (if n '= 0 then t2 else t3) v ->
      red (trm_ifz t1 t2 t3) v.

(** Proof that the source language is deterministic *)

Lemma red_deterministic : forall t v1 v2,
  red t v1 -> red t v2 -> v1 = v2.
Proof.
  introv Red1. gen v2. induction Red1; introv Red2.
  inversions Red2; try solve [inversions H]. auto.
  inversions Red2. inversions H. rewrite~ (IHRed1_1 v3) in IHRed1_2.
  inversions Red2. inversions H. auto. 
  inversions Red2. inversions H.
    forwards* K: IHRed1_1. inverts K. eauto.
Qed.

(************************************************************)
(* * Source language typign *)

(** Grammar of ground types *)

Inductive typ : Type :=
  | typ_int   : typ
  | typ_prod  : typ -> typ -> typ
  | typ_sum   : typ -> typ -> typ
  | typ_arrow : typ -> typ -> typ.

(** Typing contexts *)

Definition ctx := list (var * typ).

Definition binds x T (E:ctx) :=
  In (x,T) E.

(** Typing judgment *)

Reserved Notation "E |= t ~: T" (at level 69).

Inductive typing : ctx -> trm -> typ -> Prop :=
  | typing_var : forall E x T,
      binds x T E ->
      E |= (trm_var x) ~: T
  | typing_int : forall E n,
      E |= (trm_int n) ~: typ_int
  | typing_pair : forall E t1 t2 T1 T2,
      E |= t1 ~: T1 ->
      E |= t2 ~: T2 ->
      E |= (trm_pair t1 t2) ~: typ_prod T1 T2
  | typing_inj : forall E (b:bool) t1 T1 T2,
      E |= t1 ~: (if b then T1 else T2) ->
      E |= (trm_inj b t1) ~: typ_sum T1 T2
  | typing_fix : forall E T1 T2 f x t1,
      ((f,typ_arrow T1 T2)::(x,T1)::E) |= t1 ~: T2 ->
      E |= (trm_fix f x t1) ~: (typ_arrow T1 T2)
  | typing_app : forall T1 T2 E t1 t2,
      E |= t1 ~: (typ_arrow T1 T2) -> 
      E |= t2 ~: T1 ->
      E |= (trm_app t1 t2) ~: T2
  | typing_let : forall E x T1 T2 t1 t2,
      E |= t1 ~: T1 ->
      ((x,T1)::E) |= t2 ~: T2 ->
      E |= (trm_let x t1 t2) ~: T2
  | typing_ifz : forall E t1 t2 t3 T,
      E |= t1 ~: typ_int ->
      E |= t2 ~: T ->
      E |= t3 ~: T ->
      E |= (trm_ifz t1 t2 t3) ~: T
  | typing_fail : forall E T,
      E |= trm_fail ~: T

where "E |= t ~: T" := (typing E t T).

Notation "|= t ~: T" := (nil |= t ~: T) (at level 68).

(** Well-typed values *)

Definition well_typed_value (v:trm) :=
  value v /\ (exists T, |= v ~: T).


(************************************************************)
(* * Construction of the type Func *)

(** Definition of [Func] as the set of ML functions *)

Definition well_typed_function (v:trm) :=
  exists f x t T1 T2, v = trm_fix f x t /\ |= v ~: typ_arrow T1 T2.

Definition Func : Type := { v:trm | well_typed_function v }.

(** Coercion for viewing a value of type [Func] as the type [trm] *)

Coercion Func_to_trm (F:Func) : trm := let (v,_) := F in v.

(** [Func] is inhabited *)

Instance Func_inhab : Inhab Func.
Proof.
  constructor. econstructor.
  exists 0%nat 0%nat (trm_int 0) typ_int typ_int. split~.
  apply typing_fix. apply typing_int.
Qed.


(************************************************************)
(* ** Reflection of types *)

(** Computation of <T> from a type T *)

Fixpoint lift (T:typ) {struct T} : Type :=
  match T with
  | typ_int => int
  | typ_prod T1 T2 => prod (lift T1) (lift T2)
  | typ_sum T1 T2 => sum (lift T1) (lift T2)
  | typ_arrow T1 T2 => Func
  end.

(** Reflected types are all inhabited *)

Instance lift_inhab : forall T, Inhab (lift T).
Proof.
  constructor. induction T; simpl.
  exact (0%Z).
  exact (IHT1,IHT2).
  exact (inl IHT1).
  exact arbitrary.
Qed.


(************************************************************)
(* ** Reflection of values *)

(** Definition of encoding, as a function of type [forall T, <T> -> trm] *)

Program Definition encode (T:typ) (V:lift T) : trm.
  intros T. induction T; simpl; intro V.
  exact (trm_int V).
  destruct V as (V1,V2). exact (trm_pair (IHT1 V1) (IHT2 V2)).
  destruct V as [V1|V2]. exact (trm_inj true (IHT1 V1)). exact (trm_inj false (IHT2 V2)).
  exact V.
Defined.

Implicit Arguments encode [T].

(** Image of encoding includes only well-typed values *)

Hint Constructors value typing.

Lemma encode_typed_values : forall (T:typ) (V:lift T),
  well_typed_value (encode V).
Proof.
  induction T; simpl; intros V.
  split*.
  destruct V as (V1,V2). intuit (IHT1 V1). intuit (IHT2 V2). split*.
  destruct V as [V1|V2].
    intuit (IHT1 V1). split. eauto. exists* (typ_sum x T2).
    intuit (IHT2 V2). split. eauto. exists* (typ_sum T1 x).
  destruct V as (f,H). simpl. intuit H. subst. split*.
Qed.

(** Injectivity of encoding *)

Lemma encode_inj : forall (T:typ) (V1 V2 :lift T),
  encode V1 = encode V2 -> V1 = V2.
Proof.
  induction T; simpl; intros V1 V2 H.
  inverts~ H.
  destruct V1; destruct V2. inverts H. fequal~.
  destruct V1; destruct V2; inverts H; fequal~.
  destruct V1; destruct V2.
  unfolds Func_to_trm. subst x. pi_rewrite~ w.
Qed.

(** Surjectivity of encoding *)

Lemma encode_surj : forall (T:typ) (v:trm),
  value v -> |= v ~: T ->
  exists V : lift T, v = encode V.
Proof.
  induction T; intros v Hval Htyp.
  inverts Htyp; inverts Hval. exists~ n.
  inverts Htyp; inverts Hval. 
    forwards~ [V1 E1]: (IHT1 t1).
    forwards~ [V2 E2]: (IHT2 t2).
    subst. exists~ (V1,V2).
  inverts Htyp; inverts Hval. destruct b.
    forwards~ [V1 E1]: (IHT1 t1). subst. exists~ (inl (B:=lift T2) V1).
    forwards~ [V2 E2]: (IHT2 t1). subst. exists~ (inr (A:=lift T1) V2).
  asserts K: (well_typed_function v).
    inverts keep Htyp; inverts keep Hval. exists___*.
   exists~ (@exist _ _ v K).
Qed.

(** Definition of decoding as the reciprocal of encoding *)

Definition decode (T:typ) (v:trm) : lift T :=
  epsilon (fun V => v = encode V).


(** Type coercion to exploit equalities between types *)

Program Definition coerce (A:Type) (X:A) (B:Type) (H: A = B) : B.
Proof. intros. refine (@eq_rect Type A (fun T => T) X B H). Defined.

Implicit Arguments coerce [A].

Lemma coerce_inj : forall A B (V1 V2 : A) (E : A = B),
  @coerce A V1 B E = @coerce A V2 B E -> V1 = V2.
Proof.
  unfold coerce. unfold eq_rect. intros. skip.
(*
dependent rewrite H. 
Require Import JMeq.
Print JMeq.
 destruct E.
  intros.
*)
Qed.
  


Require Import Program.

Instance typ_inhab : Inhab typ.
Proof. constructor. exact typ_int. Defined.


(** A reflected type, or [RType], is a Coq type of the form <T> *)

Definition RType := { A : Type | exists T, lift T = A }.
 
Definition unlifts (A:Type) (T:typ) := lift T = A.

Definition unlift (A:Type) := epsilon (unlifts A).

Lemma unlift_spec : forall A, (exists T, lift T = A) ->
  lift (unlift A) = A.
Proof.
  intros. apply (epsilon_spec_exists _ H). 
Qed.

Program Definition Encode (A:RType) (V:`A) : trm.
intros A. case A. simpl. intros.
generalize (unlift_spec e). generalize (unlift x).
intros. subst. exact (encode V). Defined.
Print Encode.


Implicit Arguments Encode [A].

Lemma Encode_inj : forall (A:RType) (V1 V2:`A),
  Encode V1 = Encode V2 -> V1 = V2.
Proof.
  intros A. destruct A. simpl. 
  lets: (unlift_spec e). 
  intros V1 V2.  intros. elim_eq_rect.
  
  unfolds unlift.

   destruct (indefinite_description (fun T : typ => lift T = x) e).
  destruct A as [A T E]. unfold Encode. simpl. intros.
  lets R: (>>> encode_inj H).  
  apply (@coerce_inj _ (lift T) _ _ _ R).
Qed.



(*
Record RType := 
  { RType_coq :> Type; 
    RType_typ : typ;
    RType_eq : RType_coq = lift RType_typ }.
*)



(** Lifting to RType *)

Program Definition Lift (T:typ) : RType :=
  @Build_RType (lift T) T (eq_refl _).

Coercion Lift : typ >-> RType.


(** Encoding on reflected types *)

Definition Encode (A:RType) (V:A) : trm :=
  encode (coerce V _ (RType_eq _)).

Implicit Arguments Encode [A].

Lemma Encode_inj : forall (A:RType) (V1 V2:A),
  Encode V1 = Encode V2 -> V1 = V2.
Proof.
  destruct A as [A T E]. unfold Encode. simpl. intros.
  lets R: (>>> encode_inj H).  
  apply (@coerce_inj _ (lift T) _ _ _ R).
Qed.

(** Decoding on reflected types *)

Definition Decode (A:RType) (v:trm) : A :=
  coerce (decode (RType_typ A) v) _ (sym_eq (RType_eq _)).



(************************************************************)
(* ** Construction of AppEval *)

(** Definition of AppEval *)

Definition AppEval (A B:RType) (F:Func) (V:A) (V':B) :=
  red (trm_app F (Encode V)) (Encode V').

Implicit Arguments AppEval [A B].

Lemma AppEval_deterministic :
  forall (A B:RType) (F:Func) (V:A) (V1' V2':B),
  AppEval F V V1' -> AppEval F V V2' -> V1' = V2'.
Proof.
  introv H1 H2. unfolds AppEval. 
   apply Encode_inj. apply* red_deterministic.
Qed. 



(************************************************************)
(* ** Alternative construction of AppEval *)

(*
Definition Func' : RType := Build_RType Func (typ_int 

Inductive AppEval' : forall (A B:RType) (F:Func) (V:A) (V':B), Prop :=
  | app_eval : forall T T' f v v',
      well_typed_function f -> |= v ~: T -> |= v' ~: T' -> 
      red (trm_app f v) v' ->
      AppEval' (Lift T) (Lift T') (@Decode Func f) (decode T v) (decode T' v').
*)



Inductive AppEval' : forall (A B:RType) (F:Func) (V:A) (V':B), Prop :=
  | app_eval : forall T T' f v v',
      well_typed_function f -> |= v ~: T -> |= v' ~: T' -> 
      red (trm_app f v) v' ->
      AppEval' (Lift T) (Lift T') (decode (typ_arrow T T') f) (decode T v) (decode T' v').

Implicit Arguments AppEval' [A B].

(*
Lemma AppEval_equiv : forall (A B:RType) (F:Func) (V:A) (V':B),
  AppEval F V V' <-> AppEval' F V V'.
Proof.
  unfold AppEval. iff H. 
  destruct A as [A T E]. destruct B as [A' T' E'].   
Qed.
*)






(************************************************************)
(************************************************************)
(************************************************************)

Parameter x : int.

Definition t := trm_ifz (trm_int x) (trm_int 1) (trm_int 2).

Definition T := 
  epsilon (fun V : int => red t (@encode typ_int V)).

Definition cf := 
  fun (P : int -> Prop) => (x = 0 -> P 1) /\ (x <> 0 -> P 2).

Hint Constructors red value.

Lemma T_cf : forall P, cf P -> P T.
Proof.
  intros.
  unfolds in H. destruct H.
  unfold T. unfold t. 
  destruct (classic (x = 0)).
  spec_epsilon as V HV. 
   exists 1. apply* red_ifz. case_if; simple*. 
   inverts HV. inverts H6. case_if; tryfalse. inverts H7. auto.
  skip.
Qed.




(************************************************************)
(************************************************************)
(************************************************************)









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










(** Terms, ML types and Coq types are inhabited *)

Instance trm_inhab : Inhab trm.
Proof. constructor. exact (trm_int 0). Defined.



Instance type_inhab : Inhab Type.
Proof. constructor. exact int. Defined.







(** [ml_type T] holds if [T] is a real ML type,
    i.e. without external components *)

Inductive ml_type : typ -> Prop :=
  | ml_type_int   : ml_type (typ_int)
  | ml_type_prod  : forall T1 T2,
      ml_type T1 -> ml_type T2 -> ml_type (typ_prod T1 T2)
  | ml_type_sum   : forall T1 T2,
      ml_type T1 -> ml_type T2 -> ml_type (typ_sum T1 T2)
  | ml_type_arrow : forall T1 T2,
      ml_type T1 -> ml_type T2 -> ml_type (typ_arrow T1 T2).

(** [lifted_ml_type A] holds if [A] is a Coq type of
    the form <T> for some true ML type T *)

Definition lifted_ml_type (A:Type) :=
  exists T, ml_type T /\ A = lift_typ T.



(************************************************************)
(* ** Definition of encoders and decoders *)

  | trm_ext : forall (A:Type), A -> trm.
  | value_ext : forall A (V:A),
      value (trm_ext V).



(* Conversions difficiles...
Program Fixpoint encode_ml (T : typ) (V : lift_typ T) : trm :=
  match T with
  | typ_int => trm_int (V:int)
  | typ_prod T1 T2 => 
      let (V1,V2) := V in trm_pair (encode_ml T1 V1) (encode_ml T2 V2)
  | _ => trm_fail
  end.
*)

Program Definition encode_ml (T:typ) (V:lift_typ T) : trm.
  intros. induction T; simpl in V.
  exact (trm_int V).
  destruct V as (V1,V2). exact (trm_pair (IHT1 V1) (IHT2 V2)).
  destruct V as [V1|V2]. exact (trm_inj true (IHT1 V1)). exact (trm_inj false (IHT2 V2)).
  exact V.
  exact trm_fail. (* any *)
Defined.
(*Print encode_ml.*)

Lemma encode_ml_injective : forall (T1 T2:typ) V1 V2, 
  lift_typ T1 = lift_typ T2 -> encode_ml T1 V1 = encode_ml T2 V2 -> V1 = V2.
Proof.



Lemma encode_injective : forall (T1 T2:typ) (v1 v2:trm), 
  encode T1 v1 = decode T2 v2 -> v1 = v2.
Proof.






Definition get_ml_type (A:Type) (H:lifted_ml_type A) 
   : { T : typ | ml_type T /\ A = lift_typ T }.
Proof.
  intros A H. apply indefinite_description. destruct H as (x&U&V). eauto.
Defined.
(* Print get_ml_type.*)

(** [encode A V] encoders the Coq value [V] into an ML value *)



Lemma prop_dec : forall (P:Prop), {P}+{~P}.
Proof. 
  intros. destruct (classicT P). left~. right~.
Qed.

Inductive exists_result (A:Type) (P:A->Prop) : Type :=
  | exists_result_yes : forall X, P X -> exists_result P
  | exists_result_no : (~ (exists X, P X)) -> exists_result P.

Axiom indefinite_description' : forall (A : Type) (P : A->Prop), 
   (ex P) -> { x : A | P x }.

Definition exists_dec : forall (A:Type) (P:A->Prop), exists_result P. 
Proof.
  intros. destruct (classicT (ex P)).
  destruct (indefinite_description' e). apply* exists_result_yes.
  apply exists_result_no. intros (x&K). eauto.
Defined.


Definition is_lifted_ml_type (A:Type) (T:typ) :=
  ml_type T /\ A = lift_typ T.


Program Definition encode (A:Type) (V:A) : trm :=
  match exists_dec (is_lifted_ml_type A) with
  | exists_result_yes T (conj M N) => encode_ml T (coerce V _ _) 
  | exists_result_no H => trm_ext V 
  end.

Lemma encode_injective : forall (A:Type) (V1 V2:A),
  encode V1 = encode V2 -> V1 = V2.
Proof.
  introv H. unfolds encode.
  case (exists_dec (is_lifted_ml_type A)).


  destruct (classicT (lifted_ml_type A)).
  case l. intros T (E&F).
  destruct (get_ml_type (encode_obligation_1 V1 l)).
  destruct (get_ml_type (encode_obligation_1 V2 l)).
  destruct (get_ml_type (encode_obligation_2 V1 l a)).
  destruct (get_ml_type (encode_obligation_2 V2 l a0)).

  rewrite proof_

  destruct (classic (lifted_ml_type A)) as [(T&H1&H2)|].
  exists T. exists (encode V). split. auto.
    unfold decode.  (* encode injective sur ml *) skip.
  exists (typ_ext A) (trm_ext V). split.
    auto. unfold decode. skip.
Qed.


(*
Program Definition encode (A:Type) (V:A) : trm :=
  If (lifted_ml_type A) 
    then let (T,H) := @get_ml_type A _ in
         encode_ml T (coerce V _ _) 
    else trm_ext V.
*)

 (*let 'T := epsilon (fun T => ml_type T /\ A = lift_typ T) in
        encode_ml (T:typ) (V:lift_typ T)
Next Obligation.
  sets P: (fun T : typ => ml_type T /\ A = lift_typ T).
  forwards: (epsilon_spec_exists' P).
  destruct H. eauto.
  sets X :(epsilon P). subst P. clearbody X. simpls. destruct H0 as [M E]. clear H.
  subst A. exact (encode_ml X V).
Defined.
*) 


(*
Hint Extern 1 (Inhab ?A) =>
  match goal with H:A |- _ => constructor; exists H end : typeclass_instances.

Program Definition test (A:Type) (V:A) :=
  @epsilon _ _ (fun x:A => True).
Next Obligation. typeclass. Qed.
*)

(** [decode A v] is the inverse function of [encode] *)

Program Definition decode (A:Type) (H:Inhab A) (v:trm) : A :=
  epsilon (fun V:A => v = encode V).






(** [decoding] is surjective *)

Program Definition decode_surjective_statment := forall (A:Type) (V:A),
  exists T v, A = lift_typ T /\ V = @decode A _ v.
Next Obligation. typeclass. Qed.

Lemma decode_surjective : decode_surjective_statment.
Proof.
  intros_all. 
  destruct (classic (lifted_ml_type A)) as [(T&H1&H2)|].
  exists T. exists (encode V). split. auto.
    unfold decode.  (* encode injective sur ml *) skip.
  exists (typ_ext A) (trm_ext V). split.
    auto. unfold decode. skip.
Qed.

Lemma encode_injective : forall (A:Type) (V1 V2:A),
  encode V1 = encode V2 -> V1 = V2.
Proof.
  introv H. unfolds encode.
  destruct (classicT (lifted_ml_type A)).
  case l. intros T (E&F).
  destruct (get_ml_type (encode_obligation_1 V1 l)).
  destruct (get_ml_type (encode_obligation_1 V2 l)).
  destruct (get_ml_type (encode_obligation_2 V1 l a)).
  destruct (get_ml_type (encode_obligation_2 V2 l a0)).

  rewrite proof_

  destruct (classic (lifted_ml_type A)) as [(T&H1&H2)|].
  exists T. exists (encode V). split. auto.
    unfold decode.  (* encode injective sur ml *) skip.
  exists (typ_ext A) (trm_ext V). split.
    auto. unfold decode. skip.
Qed.



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
  intros t.
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






 