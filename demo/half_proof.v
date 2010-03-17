(** Commented verification script for the function [half] *)

(** Import the verification library *)

Set Implicit Arguments.
Require Import FuncTactics LibInt.


(************************************************************)
(* ** Source code *)

(** The file [half.ml] contains the definition of the function [half] 
   
   let rec half n = 
      if n = 0 then 0
      else if n = 1 then failwith "error"
      else 1 + half (n-2)

*)

(************************************************************)
(* ** Generated characteristic formula *)

(** The characteristic formula generator produces a file
     called [half_ml.v] *)

Require Import half_ml. 

(* TODO
Lemma half_specif : forall n x,
  n >= 0 -> x = 2 * n -> app_1 half x (= n).
Proof.
  induction n using peano_induction.
  apply half_cf. (* apply the characteristic formula *)
  repeat intro. auto. (* prove [is_spec_1] for the specification *)
  intros n IH k Pos Eq. (* introduces arguments and pre-conditions *)
  split; intros C1; fold_bool; fold_prop. (* case analysis on [n = 0] *)
  hnf. math. (* prove [n = k + k] and [n = 0] implies [k = 0] *)
  split; intros C2; fold_bool; fold_prop. (* case analysis on [n = 1] *)
  hnf. math. (* prove that [n = 1] is absurd considering [n = k + k] *)
  esplit. split. (* reason on the let binding *)
  (* --reasoning on the recursive call-- *)
  apply (spec_elim_1_1 IH). (* apply the elimination lemma *)
  intros R WR HR. apply HR with (k:=k-1). (* start proving its hypothesis *)
    unfolds. math. (* show that the measure decreases *)
    math. (* check [k-1 >= 0] *)
    math. (* check [n-2 = k-1 + k-1] *)
  (* --reasong on the addition [_x21+1]-- *)
  intros k' Hk'. (* use the name [k'] in place of [_x21] *)
  hnf. math. (* concludes by showing [k' = k-1] implies [1+k' = k] *)
Qed.
*)

(** This file first contains an axiom to describe the function [half].

       Axiom half : val.   

    Note: [val] is a synonymous for [Func], and [Axiom] is the same
    as [Parameter].

    It also produces an axiom corresponding to its characteristic formula,
    which is not intended to be read.

       Axiom half_cf : (tag tag_topfun no_name (tag tag_body no_name
       (forall K : (int -> (((_ -> Prop) -> Prop) -> Prop)), ((is_spec_1 K)
       -> ((forall n : int, ((K n) (tag tag_if no_name (fun P : (_ -> Prop) 
       => ((Logic.and (((eq (((@obj_beq_lock _) n) (0)%Z)) true) -> ((tag
       tag_ret no_name (fun P : (_ -> Prop) => (P (0)%Z))) P))) (((eq 
       (((@obj_beq_lock _) n) (0)%Z)) false) -> ((tag tag_if no_name 
       (fun P : (_ -> Prop) => ((Logic.and (((eq (((@obj_beq_lock _) n)
       (1)%Z)) true) -> ((tag tag_fail no_name (fun P : (_ -> Prop) => False))
       P))) (((eq (((@obj_beq_lock _) n) (1)%Z)) false) -> ((tag tag_let 
       no_name (fun P : (_ -> Prop) => (ex (fun P1 : (int -> Prop) => 
       ((Logic.and ((tag tag_apply no_name ((((@app_1 int) int) half)
       ((Coq.ZArith.BinInt.Zminus n) (2)%Z))) P1)) (forall _x21 : int
       ((@P1 _x21) -> ((tag tag_ret no_name (fun P : (_ -> Prop) =>
       (P ((Coq.ZArith.BinInt.Zplus (1)%Z) _x21)))) P)))))))) P))))) P)))))))
       -> ((spec_1 K) half)))))).

   Indeed, Coq is able to pretty-print this formula as follows:

       LETFUNC := Body half n =>
         (_If (n == 0) Then Ret 0
          Else (_If (n == 1) Then Fail  
          Else (Let _x21 := App half (n - 2) ;
                in (Ret 1 + _x21))

   Compare with the source code of the program after normalization:
   
       let rec half n =
          if n = 0 then 0
          else if n = 1 then assert false
          else let _x21 = half (n - 2) in 1 + _x21

   Note: the program name [_x21] has been introduced to name the
   subterm [half(n-2)]. This name has been generated according to
   the position of that subterm in the expression where it occurs:
   [_x] is the standard prefix, the number [2] comes from the fact
   that [half(n-2)] occurs in the second argument of [+], and the number
   [1] comes from the fact that it is the first (and only) subterm
   that needed to be named in the second argument of [+]. This strategy
   to generate name depending on their position in the syntax tree aims
   at being relatively robust with respect to modification of the source 
   code. Remark that the user can use a more meaningful name instead of
   [_x21] during its interactive proof (see further on). 

   Finally, the generator produces a command to register the characteristic
   formula in a database, so that the lemma can be exploited by tactics.

       Hint Extern 1 (RegisterCf half) => Provide half_cf.

*)

(* Hint for automation with maths *)
Hint Rewrite double quadruple : rew_maths.

Ltac auto_tilde ::= try solve [ auto | math ].

Ltac math_0 ::= unfold downto in *.


(************************************************************)
(* ** Specification *)

(** We can state the specification of [half] as a lemma. 
    The lemma states that if [half] is applied to a value [n]
    when there exists a nonnegative [k] such that [n] is the
    double of [k], then the function returns a value equal to [k]. 

    Remark: we write [k+k] instead of [2*k] for the time being,
    until we can rely on an efficient decision procedure with
    support for multiplication. *)


(************************************************************)
(* ** Verification: step 1 *)

Lemma half_spec_0 : Spec_1 half (fun x R => 
   forall n:int, n >= 0 -> x = 2*n -> R (= n)).
Proof.
  apply (spec_induction_1 (int_downto_wf 0)). 
  apply half_cf. repeat intro; auto. (* characteristic formula *)
  intros x IH n Pos Eq. 
  split; intros C1; fold_bool; fold_prop. (* case analysis on n *)
  hnf. math. (* prove [x = 2*n] and [x = 0] implies [n = 0] *)
  split; intros C2; fold_bool; fold_prop. (* case analysis on n *)
  hnf. math. (* prove that [x = 1] is absurd since [x = 2*n] *)
  esplit. split. (* reason on the let binding *)
  (* --reasoning on the recursive call-- *)
  eapply (spec_elim_1_1' IH). (* apply the elimination lemma *)
  intros R HR. apply HR with (n:=n-1). (* prove premises *)
    unfolds. math. (* show that the measure decreases *)
    math. (* check [n-1 >= 0] *)
    math. (* check [x-2 = 2*(n-1) *)
    apply pred_le_refl. (* post condition is infered *)
  (* --reasong on the addition [_x21+1]-- *)
  intros n' Hn'. (* use the name [n'] in place of [_x21] *)
  hnf. math. (* concludes: [n' = n-1] implies [1+n' = n] *)
Qed.



(** The proof of this lemma can be carried out using 
    only standard Coq tactics. ([math] is an optimized
    version of [omega], the linear-arithmetic decision
    procedure. *)

Lemma half_spec_1 : Spec_1 half (fun n R => 
   forall k:int, k >= 0 -> n = 2* k -> R (= k)).
Proof.
  apply (spec_induction_1 (int_downto_wf 0)). (* set up the induction *)
  apply half_cf. (* apply the characteristic formula *)
  repeat intro. auto. (* prove [is_spec_1] for the specification *)
  intros n IH k Pos Eq. (* introduces arguments and pre-conditions *)
  split; intros C1; fold_bool; fold_prop. (* case analysis on [n = 0] *)
  hnf. math. (* prove [n = k + k] and [n = 0] implies [k = 0] *)
  split; intros C2; fold_bool; fold_prop. (* case analysis on [n = 1] *)
  hnf. math. (* prove that [n = 1] is absurd considering [n = k + k] *)
  esplit. split. (* reason on the let binding *)
  (* --reasoning on the recursive call-- *)
  eapply (spec_elim_1_1' IH). (* apply the elimination lemma *)
  intros R HR. apply HR with (k:=k-1). (* start proving its hypothesis *)
    unfolds. math. (* show that the measure decreases *)
    math. (* check [k-1 >= 0] *)
    math. (* check [n-2 = k-1 + k-1] *)
    apply pred_le_refl. (* post condition is infered *)
  (* --reasong on the addition [_x21+1]-- *)
  intros k' Hk'. (* use the name [k'] in place of [_x21] *)
  hnf. math. (* concludes by showing [k' = k-1] implies [1+k' = k] *)
Qed.


(************************************************************)
(* ** Verification: step 2 *)

(** To make proof script more concise, we have design a set of
    high-level tactics. They can be easily recognized: their name
    starts with the letter [x]. Let us complete the same proof
    as above, using our tactics this time.

    We also use an ad-hoc syntax for specifications, starting
    with the keyword [Spec] and binding the arguments and the
    predicate [R] without an explicit [fun] construction. *)

Lemma half_spec_2 : Spec half x |R>>
    forall n:int, n >= 0 -> x = 2*n -> R (= n).
Proof.
  xinduction (int_downto_wf 0). (* set up the induction *)
  xcf. (* apply the characteristic formula *)
  introv IH Pos Eq. (* name pre-conditions explicitly *)
  xcase. (* case analysis following if/else-if/else *)
  xret. math. (* completes the case [n = 0] *)
  xfail. math. (* completes the case [n = 1] *)
  xlet as k'. (* reason on the let binding *)
  xapp (n-1); math. (* reason on recursive call *)
  xret. math. (* conclude *)
Qed.


(************************************************************)
(* ** Verification: step 3 *)

(** In order to reflect the structure of the program in the
    source script, we rely mainly on identation. We use explicit
    comments only for large programs. For example, the above
    proof script is presented as follows. *)

Lemma half_spec_3 : Spec half n |R>>
  forall k:int, k >= 0 -> n = 2*k -> R (= k).
Proof.
  xinduction (int_downto_wf 0). xcf. introv IH Pos Eq. xcase.
    xret. math. 
    xfail. math. 
    xlet as k'. 
      xapp (k-1); try math. auto.
      xret. math. 
Qed.


(************************************************************)
(* ** Verification: step 4 *)

(** Many of the tactics occuring in a proof script such as this one
    are "mechanical" in that they are routinely applied following
    the structure of the program. For instance, [xret] is used on
    each terminal value, [xlet] is used at each let-binding, and
    [xapp] is used at each application node. 

    Thus, we have developped a tactic called [xgo] which automates
    the process. *)
(*todo
Lemma half_spec_4 : Spec half n |R>>
  forall k:int, k >= 0 -> n = 2*k -> R (= k).
Proof.
  xinduction (int_downto_wf 0). xgo. 
    math. 
    math. math.
    xapp (k-1); auto with maths. 
    math.
Qed.
*)

(************************************************************)
(* ** Verification: step 5 *)

(** For programs whose correction relies a lot on mathematical
    properties, such as [half], we indicate Coq to try and
    apply the tactic [math] when calling automation. For convenience,
    we have set the tilde symbol, [~], to denote a call to automation. *)

Ltac auto_tilde ::= try solve [ auto | math ].

Lemma half_spec_5 : Spec half x |R>>
  forall n:int, n >= 0 -> x = 2*n -> R (= n).
Proof.
  xinduction (int_downto_wf 0). 
  xcf. intros. xgo~ '_x2 (Xargs (n-1)).
Qed.






(************************************************************)
(************************************************************)
(* ** Function composition *)

(** Specification of compose as a function of three arguments *)

Lemma compose_spec : forall A B C,
  Spec compose (f1:val) (f2:val) (x:A) |R>> 
    forall K1 K2, @spec_1 B C K1 f1 -> @spec_1 A B K2 f2 ->
    K2 x (fun P => exists y, P y /\ K1 y R).
Proof. 
  xcf.
    intros f1 f2 x. intros R R' HR WR. introv H1 H2. 
    applys (spec_is_spec_1 H2). sapply (HR K1 K2 H1 H2).
    intros P (y&Py&Hy). exists y. split~. applys* (spec_is_spec_1 H1). 
  introv H1 H2.
  lets: (spec_elim_1 H2 x). sapply (spec_is_spec_1 H2). eauto.
  intros P HP. 
  destruct (app_1_witness HP) as (y&U&V). exists y. split~. 
  lets: (spec_elim_1 H1 y). sapply* (spec_is_spec_1 H1).
  intros P' HP'. 
  xlet*. substs; eauto. (* todo: fix substs* *)
Qed.

(** Specification of compose as a function of two arguments *)

Lemma compose_spec_2args : forall B A C : Type,
  Spec compose (f1:val) (f2:val) |R>> 
    forall K1 K2, @spec_1 B C K1 f1 -> @spec_1 A B K2 f2 ->
    R (spec_1 (fun x R => K2 x (fun P => exists y, P y /\ K1 y R))).
Proof.
  intros. 
  lets M: (spec_3_2 (@compose_spec A B C)).
  applys_to M total_2_spec_2. 
  xweaken as f1 f2. introv H1 H2.
  applys WR. sapply HR. clear HR.
  intros g Hg. xweaken. 
    intros_all. sapply (spec_is_spec_1 H2). sapply H.
     intros Q (y&Py&Ky). exists y. split~. 
     sapply* (spec_is_spec_1 H1).
  clears R. simpl. introv WR HR.
  specializes HR H1 H2. auto.
Qed.

Hint Extern 1 (RegisterSpec compose) => Provide compose_spec_2args.

(** Specification [quarter] as the composition of [half] with itself *)

(*-todo
Lemma quarter_spec : Spec quarter n |R>>
  forall k:int, k >= 0 -> n = 4*k -> R (= k).
Proof.
  xgo. xapp (@compose_spec_2args int int int) as.
  specializes HR half_spec_5 half_spec_5. sapply HR.
  intros g Hg. xweaken as x. clear Hg.
  intros k Posk Quadk.  
  specializes HR (2*k) __ __. auto~. auto~.
  destruct HR as (y&E&H). apply~ H.
Qed.
*)




