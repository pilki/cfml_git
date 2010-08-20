(**************************************************************************
* Bytecode compiler and interpreter : verification                        *
***************************************************************************)

Set Implicit Arguments.
Require Import CFPrim VerifByte_ml LibList LibClosure.

(*==========================================================*)
(* * Definitions at the logical level *)
(*==========================================================*)

(************************************************************)
(* ** Big-step evaluation of source programs *)

Inductive eval : Env -> Term -> Value -> Prop :=
  | eval_var : forall e i v,
      Nth i e v ->
      eval e (Tvar i) v
  | eval_int : forall e n,
      eval e (Tint n) (Vint n)
  | eval_fun : forall e t1,
      eval e (Tfun t1) (Vclo t1 e)
  | eval_app : forall e t1 t2 c1 e1 v2 v,
      eval e t1 (Vclo c1 e1) ->
      eval e t2 v2 ->
      eval (v2 :: e1) c1 v ->
      eval e (Tapp t1 t2) v.

Definition computes := eval nil.


(************************************************************)
(* ** Compilation scheme *)

Fixpoint compile_term (t : Term) (k : Mcode) {struct t} : Mcode :=
  match t with
  | Tvar i => Ivar i :: k
  | Tint n => Iint n :: k
  | Tfun t1 => Iclo (compile_term t1 (Iret :: nil)) :: k
  | Tapp t1 t2 => compile_term t1 (compile_term t2 (Iapp :: k))
  end.

Fixpoint compile_value (v : Value) : Mvalue :=
  match v with
  | Vint n => Mint n
  | Vclo t e => Mclo (compile_term t (Iret :: nil)) 
                     (List.map compile_value e)
  end.

Definition compile_env := List.map compile_value.


(************************************************************)
(* ** Semantics of the target machine *)

Definition state := (Mcode * Menv * Mstack)%type.

Inductive trans : state -> state -> Prop :=
  | trans_var : forall n k e s v,
      Nth n e v ->
      trans ((Ivar n)::k, e, s)
            (k, e, (Sval v)::s)
  | trans_int : forall n k e s,
      trans ((Iint n)::k, e, s)
            (k, e, (Sval(Mint n))::s)
  | trans_clo : forall c k e s,
      trans ((Iclo c)::k, e, s)
            (k, e, (Sval(Mclo c e))::s)
  | trans_app : forall k e v k' e' s,
      trans (Iapp::k, e, (Sval v)::(Sval(Mclo k' e'))::s)
            (k', v::e', (Sret k e)::s)
  | trans_ret : forall k e v k' e' s,
      trans (Iret::k, e, (Sval v)::(Sret k' e')::s)
            (k', e', (Sval v)::s).


(************************************************************)
(* ** Compiler correctness for terminating programs *)

Hint Constructors Nth.
Lemma find_var_match: forall e n v,
  Nth n e v -> Nth n (compile_env e) (compile_value v).
Proof.
  induction e; destruct n; simpl; introv H; inverts~ H.
Qed.

Lemma compile_eval: forall e t v k s,
  eval e t v ->
  plus trans (compile_term t k, compile_env e, s)
             (k, compile_env e, Sval(compile_value v) :: s).
Proof.
  introv Eva. gen k s. induction Eva; simpl; introv.
    apply plus_once. apply trans_var. apply* find_var_match.
    apply plus_once. apply trans_int.
    apply plus_once. apply trans_clo.
    apply* plus_trans. apply* plus_trans. apply* plus_step_plus.
     simpl compile_value at 2. sapply* trans_app. apply* plus_trans.
     apply plus_once. apply trans_ret.
Qed.

(************************************************************)
(* ** Subterm relationship on terms, 
      used to argue for termination *)

Inductive Term_sub : Term -> Term -> Prop :=
  | Term_sub_fun : forall t,
     Term_sub t (Tfun t)
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
(* * Tactics for decoding -- should be generated *)
(*==========================================================*)

Ltac decode3 dec v :=
  match v with
  | (mint#(?v1))%val =>
    dec v1; let _A1 := _get in _rem; let V1 := _get in _rem; 
    _put2 _Mvalue (Mint V1)
  | (mclo#(?v1,?v2))%val =>
    dec v1; let _A1 := _get in _rem; let V1 := _get in _rem; 
    dec v2; let _A2 := _get in _rem; let V2 := _get in _rem; 
    _put2 _Mvalue (Mclo V1 V2)
  | (sval#(?v1))%val =>
    dec v1; let _A1 := _get in _rem; let V1 := _get in _rem; 
    _put2 _Slot (Sval V1)
  | (sret#(?v1,?v2))%val =>
    dec v1; let _A1 := _get in _rem; let V1 := _get in _rem; 
    dec v2; let _A2 := _get in _rem; let V2 := _get in _rem; 
    _put2 _Slot (Sret V1 V2)
  | (ivar#(?v1))%val =>
    dec v1; let _A1 := _get in _rem; let V1 := _get in _rem; 
    _put2 _Instr (Ivar V1)
  | (iint#(?v1))%val =>
    dec v1; let _A1 := _get in _rem; let V1 := _get in _rem; 
    _put2 _Instr (Iint V1)
  | (iclo#(?v1))%val =>
    dec v1; let _A1 := _get in _rem; let V1 := _get in _rem; 
    _put2 _Instr (Iclo V1)
  | (iapp#)%val =>
    _put2 _Instr (Iapp)
  | (iret#)%val =>
    _put2 _Instr (Iret)
  | _ => decode2 dec v
  end.

Tactic Notation "xdecode" :=
  xdecode_with decode3 (@nil hint_code_type).
Tactic Notation "xdecode" constr(h1) :=
  xdecode_with decode3 ((hint h1)::nil).
Tactic Notation "xdecode" constr(h1) constr(h2) :=
  xdecode_with decode3 ((hint h1)::(hint h2)::nil).
Tactic Notation "#" tactic(tac) :=  
  xreds; xdecode; tac.


(*==========================================================*)
(* * Verification of the code *)
(*==========================================================*)


Lemma compile_spec :
  spec compile [k:_Mcode] [t:_Term] is
    >> _Mcode st = compile_term t k.
Proof.
  xinduction (unproj22 Mcode Term_sub).
  xintros k t. intros IH. xcase.
    #xreturns.
    #xreturns. xreds. xdecode _Instr. xapplys~. #xreturns.
    #xapplys~. #xapplys~. xreturns.
Qed.

Lemma run_spec : 
   spec run [e:_Menv] [s:_Mstack] [k:_Mcode] = r is
    forall e' v s', star trans (k,e,s) (nil,e',(Sval v)::s') ->
    r >> _Mvalue st = v.
Proof.
  xintros_all e s k. introv Red.
  match type of Red with star trans ?A ?B =>
   gen_eq s1: A; gen_eq s2: B end.
   gen e s k. gen e' v s'.
  induction Red as [ | s1 s2 s3 R RS IH]; introv S1 S2.
  subst x. inverts S2. xreds1 3. #xreturns.
  subst s2 s3. xreds1 2. xred. inverts R as Nth K.
   xreds. xapply (@nth_spec _ _Mvalue).
    split. math. apply int_nat_lt. apply* Nth_lt_length.  
    xred. rewrite <- (@abs_pos_nat n) in Nth.
    rewrite (@Nth_func _ _ _ _ _ PX Nth).
    #fapplys* IH.
   xreds. #fapplys* IH.
   xreds. #fapplys* IH.
   xreds. #fapplys* IH.
   xreds. #fapplys* IH.
Qed.
 
Lemma exec_spec :
  spec exec [t:_Term] = r is
    forall n, (computes t (Vint n)) -> r >> _Int st = n.
Proof.
  xintros t. introv C. xreds. xdecode _Instr. 
  xapplys compile_spec. xreds. xdecode _Mvalue _Slot.
  xapplys run_spec. apply plus_star. 
  apply* (compile_eval nil nil C). simpl. #xreturns.
Qed.



