(**************************************************************************
* Proving functional programs through a deep embedding                    *
* Lambda-term evaluator : verification                                    *
***************************************************************************)

Set Implicit Arguments.
Require Import CFPrim LambdaEval_ml.


(*==========================================================*)
(* * Definitions at the logical level *)
(*==========================================================*)

(************************************************************)
(* ** Specification of substitution *)

Fixpoint Subst (x : int) (v : term) (t : term) : term :=
  match t with
  | Tvar y => if x '= y then v else t
  | Tint n => Tint n
  | Tfun y b => Tfun y (if x '= y then b else Subst x v b)
  | Tapp t1 t2 => Tapp (Subst x v t1) (Subst x v t2)  
  end.


(************************************************************)
(* ** Specification of big-step reduction *)

Inductive Reds : term -> term -> Prop :=
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

Inductive term_sub : term -> term -> Prop :=
  | term_sub_fun : forall x t,
     term_sub t (Tfun x t)
  | term_sub_app_1 : forall t1 t2,
     term_sub t1 (Tapp t1 t2) 
  | term_sub_app_2 : forall t1 t2,
     term_sub t2 (Tapp t1 t2).
  
Hint Constructors term_sub.

Lemma term_sub_wf : wf term_sub.
Proof.
  intros t. induction t; apply Acc_intro;
    introv H; inverts H; auto.
Qed.

Hint Resolve term_sub_wf : wf.


(*==========================================================*)
(* * Verification of the code *)
(*==========================================================*)

Tactic Notation "xintros" simple_intropattern(x1) :=
  xintros; intros x1.
Tactic Notation "xintros" simple_intropattern(x1) simple_intropattern(x2) :=
  xintros; intros x1 x2.
Tactic Notation "xintros" simple_intropattern(x1) simple_intropattern(x2)
  simple_intropattern(x3) :=
  xintros; intros x1 x2 x3.
Tactic Notation "xintros" simple_intropattern(x1) simple_intropattern(x2)
  simple_intropattern(x3) simple_intropattern(x4) :=
  xintros; intros x1 x2 x3 x4.

Tactic Notation "xrets" :=
  xret; xsimpl.
Tactic Notation "xrets" "~" :=
  xrets; xauto~.
Tactic Notation "xapps" "~" :=
  xapps; xauto~.

(*todo:remove*)
Ltac xapps_core spec args solver ::=
  let cont1 tt :=
    xapp_with spec args solver in
  let cont2 tt :=
    instantiate; xextract; try intro_subst in    
  match ltac_get_tag tt with
  | tag_let_trm => xlet; [ cont1 tt | cont2 tt ]
  | tag_seq =>     xseq; [ cont1 tt | cont2 tt ]
  end.

Tactic Notation "xlets" constr(Q) :=
  xlet Q; [ | intro_subst ].

Lemma subst_spec :
  Spec subst x v t |R>> R [] \[= Subst x v t].
Proof.
  xinduction (unproj33 int term term_sub). 
  xintros x v t. intros IH. 
  apply app_spec_3. xcf. intro_subst_arity 3%nat.  (* todo : tactic *)
  xmatch; simpl. (* destruct t as [ y | n | y b | t1 t2] *)
  destruct (x '= y); xif; xrets~. (* todo: better *) 
  xrets~.
  xlets (\[ = (if x '= y then b else Subst x v b) ]). (* todo: auto *)
    xif.
      xrets. case_if~. false.
      xapps~. xrets~. case_if~. false.
   xrets~.
  xapps~. xapps~. xrets~.
Qed.

Hint Extern 1 (RegisterSpec subst) => Provide subst_spec.


Lemma app_weaken_1 : forall B H1 Q1 H2 A1 (x1:A1) f H (Q:B->hprop),
  app_1 f x1 H1 Q1 -> 
  H ==> H1 \* H2 -> 
  Q1 \*+ H2 ===> Q ->
  app_1 f x1 H Q.
Proof. intros. applys* local_wframe. Qed.

Lemma app_weaken_2 : forall B H1 Q1 H2 A1 A2 (x1:A1) (x2:A2) f H (Q:B->hprop),
  app_2 f x1 x2 H1 Q1 -> 
  H ==> H1 \* H2 -> 
  Q1 \*+ H2 ===> Q ->
  app_2 f x1 x2 H Q.
Proof. intros. applys* local_wframe. Qed.

Lemma app_weaken_3 : forall B H1 Q1 H2 A1 A2 A3 (x1:A1) (x2:A2) (x3:A3) f H (Q:B->hprop),
  app_3 f x1 x2 x3 H1 Q1 -> 
  H ==> H1 \* H2 -> 
  Q1 \*+ H2 ===> Q ->
  app_3 f x1 x2 x3 H Q.
Proof. intros. applys* local_wframe. Qed.

Lemma app_weaken_4 : forall B H1 Q1 H2 A1 A2 A3 A4 (x1:A1) (x2:A2) (x3:A3) (x4:A4) f H (Q:B->hprop),
  app_4 f x1 x2 x3 x4 H1 Q1 -> 
  H ==> H1 \* H2 -> 
  Q1 \*+ H2 ===> Q ->
  app_4 f x1 x2 x3 x4 H Q.
Proof. intros. applys* local_wframe. Qed.

Ltac get_app_weaken_x x :=
  match x with
     | 1%nat => constr:(app_weaken_1)
     | 2%nat => constr:(app_weaken_2)
     | 3%nat => constr:(app_weaken_3)
     | 4%nat => constr:(app_weaken_4)
  end.


          
Ltac try_app_hyp f cont :=
  match goal with
  | H: context [ app_1 f _ _ _ ] |- _ => cont (H)
  | H: context [ app_2 f _ _ _ _ ] |- _ => cont (H)
  | H: context [ app_3 f _ _ _ _ _ ] |- _ => cont (H) 
  | H: context [ app_4 f _ _ _ _ _ _ ] |- _ => cont (H) 
  end.

Tactic Notation "xapp'" :=
  xuntag tag_apply; 
  let f := spec_goal_fun tt in 
  try_app_hyp f ltac:(fun H =>
  (*let n := spec_term_arity H in*)
  let n := spec_goal_arity tt in
  let W := get_app_weaken_x n in
  eapply W; [ apply H | hsimpl | try apply rel_le_refl ]).

Tactic Notation "xapps'" :=
  xlet; [ xapp' | try xextract; try intro_subst ].

Lemma eval_spec :
  Spec eval t |R>> forall v, Reds t v -> R [] (\= v).
Proof.
  xintros t. introv Red. induction Red;
  apply app_spec_1; xcf; intro_subst_arity 1%nat; 
  xmatch.  (* todo : tactic *)
  xrets~.
  xrets~.
  xapps'. xmatch; [ | false* C0 ]. (* tactic todo *)
  xapps'.
  xapps. xapp'. xsimpl~.
Qed.





