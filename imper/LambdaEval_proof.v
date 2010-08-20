(**************************************************************************
* Proving functional programs through a deep embedding                    *
* Lambda-term evaluator : verification                                    *
***************************************************************************)

Set Implicit Arguments.
Require Import CFPrim VerifEval_ml.


(*==========================================================*)
(* * Definitions at the logical level *)
(*==========================================================*)

(************************************************************)
(* ** Specification of substitution *)

Fixpoint Subst (x : int) (v : Term) (t : Term) {struct t} : Term :=
  match t with
  | Tvar y => if x == y then v else t
  | Tint n => Tint n
  | Tfun y b => Tfun y (if x == y then b else Subst x v b)
  | Tapp t1 t2 => Tapp (Subst x v t1) (Subst x v t2)  
  end.


(************************************************************)
(* ** Specification of big-step reduction *)

Inductive Reds : Term -> Term -> Prop :=
  | Reds_int : forall n,
      Reds (Tint n) (Tint n)
  | Reds_fun : forall y b,
      Reds (Tfun y b) (Tfun y b)
  | Reds_app : forall x b v2 t1 t2 v,
      Reds t1 (Tfun x b) ->
      Reds t2 v2 ->
      Reds (Subst x v2 b) v ->
      Reds (Tapp t1 t2) v.

(************************************************************)
(* ** Subterm relationship, to argue for termination *)

Inductive Term_sub : Term -> Term -> Prop :=
  | Term_sub_fun : forall x t,
     Term_sub t (Tfun x t)
  | Term_sub_app_1 : forall t1 t2,
     Term_sub t1 (Tapp t1 t2) 
  | Term_sub_app_2 : forall t1 t2,
     Term_sub t2 (Tapp t1 t2).
  
Hint Constructors Term_sub.

Lemma Term_sub_wf : well_founded Term_sub.
Proof.
  intros t. induction t; apply Acc_intro;
    introv H; inverts H; auto.
Qed.

Hint Resolve Term_sub_wf : wf.


(*==========================================================*)
(* * Verification of the code *)
(*==========================================================*)

Lemma subst_spec :
  spec subst [x:_Int] [v:_Term] [t:_Term] 
    is >> _Term st = Subst x v t.
Proof.
  xinduction (unproj33 int Term Term_sub).
  xintros x v t. intros IH. xred. 
  destruct t as [ y | n | y b | t1 t2]; xpat.
    xapplys. xcase as H; simpl.
      xreturns. rewriteb~ H.
      #xreturns. rewriteb~ H.
    #xreturns.
    xapplys. xcase as H; simpl.
      #xreturns. rewriteb~ H.
      xapplys~. #xreturns. rewriteb~ H.
    xapplys~. xapplys~. #xreturns.
Qed.

Lemma eval_spec :
  spec eval [t:_Term] = r is
    forall v, Reds t v -> r >> _Term st = v.
Proof.
  introv Red. induction Red; xred; xpat.
    #xreturns.
    #xreturns. 
    xinouts~. xreds 2. xinouts~. xapplys~ subst_spec. 
Qed.





