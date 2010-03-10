Set Implicit Arguments.
Require Import FuncTactics LibCore.
Require Import QueueSig_ml QueueSig_proof.
Require Import HoodMelvilleQueue_ml.

Module HoodMelvilleQueueSpec <: QueueSigSpec.

(** instantiations *)

Module Import Q <: MLQueue := MLHoodMelvilleQueue.
Import MLHoodMelvilleQueue.

(** invariant *)

Section Invariant.
Variables (a A : Type) (RA:Rep a A).

Record base (lf lenf lenr : int) (r g : list a) (Q:list A) :=
  { base_lenr : lenr = length r;
    base_lenf : lenf = lf;
    base_lval : Forall2 rep (g ++ rev r) Q }.

Record oper lenf f lenr r (g :list a) Q (d n m p : int) : Prop := 
  { oper_base : base (2*m + 1 - p) lenf lenr r g Q;
    oper_npos : n >= 0;
    oper_mpos : m >= 0;
    oper_ppos : p >= 0;
    oper_nval : n + d = 2*p + 2*lenr + 2;
    reve_lf   : length f = m - p :> int; 
    oper_fval : f = take (length f) Q }.

Record reve `{Rep a A} (f f' f'' r' r'' g : list a) Q (ok n m p : int) : Prop :=
  { reve_gval : g = rev (take (abs ok) f') ++ f'' ++ rev r'' ++ r';
    reve_lf'  : length f' = n :> int;
    reve_lf'' : length f'' = m - n :> int;
    reve_lr'  : length r' = n :> int;
    reve_lr'' : length r'' = m + 1 - n :> int;
    reve_okval: ok = n - p;
    reve_nle : n <= m }.

Record appe (f f' r' g:list a) Q (ok n m p : int) : Prop :=
  { appe_gval : g = rev (take (abs ok) f') ++ r';
    appe_lf'  : length f' = 2*m + 1 - n :> int;
    appe_lr'  : length r' = n :> int;
    appe_okval: ok = 2*m + 1 - n - p; 
    appe_okpos: ok >= 0;
    appe_nge  : n >= m;
    appe_nle  : n <= 2*m + 1 }.

Definition inv (c:bool) (d:int) (q:queue a) (Q:list A) : Prop :=
  let '(lenf,f,s,lenr,r) := q in
  match s with
  | Idle => base (length f) lenf lenr r f Q /\ lenr <= lenf
  | Done f' => c /\ base (length f') lenf lenr r f' Q /\ lenr <= lenf
  | Reversing ok f'' f' r'' r' => exists n m p g,
        oper lenf f lenr r g Q d n m p 
     /\ reve f f' f'' r' r'' g Q ok n m p  
  | Appending ok f' r' => exists n m p g,
        oper lenf f lenr r g Q d n m p 
     /\ appe f f' r' g Q ok n m p  
  end.

End Invariant.

Global Instance queue_rep `{Rep a A} : Rep (queue a) (list A) :=
  inv false 0.

(** automation *)

Hint Constructors Forall2.
Hint Resolve Forall2_last.
Hint Extern 1 (@rep (queue _) _ _ _ _) => simpl.
Ltac auto_tilde ::= eauto.

(** useful facts *)

Section Polymorphic.
Variables (a A : Type) (RA:Rep a A).
Implicit Types Q : list A.

Definition check_precondition q Q :=
  let '(lenf,f,s,lenr,r) := q in
    (lenr <= lenf /\ inv true 2 q Q)    
 \/ (lenr = lenf + 1 /\ base (length f) lenf lenr r f Q).

Lemma base_self_nil : forall lenf lenr r f lf Q,
  base lf lenf lenr r f Q ->
  lf >= length f ->
  lenr <= lenf ->
  lenf = 0 ->
  Q = nil.
Proof.
  introv B L. intros. destruct B as [? ? E]. 
  rewrite~ (@length_zero_inv _ r) in E.
  rewrite~ (@length_zero_inv _ f) in E.
Qed.

Lemma base_self_nil_inv : forall lenf lenr r g lf Q,
  base lf lenf lenr r g Q ->
  Q = nil -> lf >= 0 -> lf <= length g ->  
  lenf = 0.
Proof.
  introv B E Ge Le. subst Q. destruct B.
  destruct~ (@nil_eq_app_rev_inv _ g r).
  subst. calc_list in *. math.
Qed.

Lemma repr_fnil : forall Q lenf lenr r s,
  rep (lenf, nil, s, lenr, r) Q -> Q = nil.
Proof.
  introv R.
  destruct s as  [|ok f'' f' r'' r'|ok f' r'|f']; simpl in R.
  (* subcase: idle *)
  destruct R as ([E1 E2 E3]&L). 
  rewrite~ (@length_zero_inv _ r) in E3.
  (* subcase: reversing *)
  false. destruct R as (n&m&p&g&Op&Re).
  destruct Re. destruct Op. destruct oper_base0.
  calc_length in *. 
  cuts: (length g = 2*m + 1 - p :> int). math.
    subst g. calc_length~.
  (* subcase: appending *)
  false. destruct R as (n&m&p&g&Op&Ap).
  destruct Ap. destruct Op. destruct oper_base0.
  calc_length in *. 
  cuts: (length g = 2*m + 1 - p :> int). math.
    subst g. calc_length~.
  (* subcase: done *)
  destruct R as (C&_&_). false.
Qed.

Lemma repr_fcons : forall x X Q lenf f s lenr r,
 rep (lenf, x :: f, s, lenr, r) (X :: Q) -> rep x X.
Proof. (* todo: rep unique *)
  introv R. destruct s as [|ok f'' f' r'' r'|ok f' r'|f']. 
  (* subcase: idle *)
  destruct R as ([E1 E2 E3]&L). calc_list in E3. inversion~ E3. 
  (* subcase: reversing *)
  destruct R as (n&m&p&g&Op&Re). lets H: (oper_fval Op).
  calc_length in H. simpl in H. inversion H. auto. (* todo: bug inversions H*)
  (* subcase: appending *)
  destruct R as (n&m&p&g&Op&Ap). lets H: (oper_fval Op).
  calc_length in H. simpl in H. inversion H. auto.
  (* subcase: done *)
  destruct R as (C&_&_). false.
Qed.

(** verification *)

Lemma exec_spec : 
  Spec exec (s:status a) |R>>
    forall Q lenf f lenr r d, d > 0 -> d <= 2 -> 
     inv true d (lenf,f,s,lenr,r) Q -> 
     R (fun s' => inv true (d-1) (lenf,f,s',lenr,r) Q).
Proof. (* Admitted. *)
  xcf. introv Dinf Dsup Inv. xgo.
  (* reversing *)
  destruct Inv as (n&m&p&g&Op&Re).
  destruct Op. destruct Re. destruct oper_base0.
  simpl. exists (n+1) m p g. split.
    constructor~.
      constructor~.
    constructor; calc_length in *; auto~. (* slow! *)
      rewrite~ take_cons_int. calc_list in reve_gval0. calc_list~.
  (* reversing to appending *)
  destruct Inv as (n&m&p&g&Op&Re).
  destruct Op. destruct Re. destruct oper_base0.
  simpl. exists (n+1) m p g. split.
    constructor~.
      constructor~.
    constructor; calc_length in *; auto~.
  (* appending to done *)
  clear C C0 H. destruct Inv as (n&m&p&g&Op&Ap).
  destruct Op. destruct Ap. destruct oper_base0.
  simpl. splits~.
    renames appe_gval0 to K. simpl in K. calc_list in K. 
     constructor~. congruence.
  (* appending *)
  clear C C0 H. 
  asserts: (ok <> 0). intros K. subst ok. applys* C1. clear C1.
  destruct Inv as (n&m&p&g&Op&Ap).
  destruct Op. destruct Ap. destruct oper_base0.
  simpl. exists (n+1) m p g. split.
    constructor~. 
      constructor~.
      constructor; calc_length in *; auto~.
        renames appe_gval0 to M.
        rewrite~ take_cons_pred_int in M. calc_list~ in M. 
  (* other *)
  destruct s as [|ok f'' f' r'' r'|ok f' r'|f']; simpl.
  auto. 
  false. destruct Inv as (n&m&p&g&Op&Re). destruct Re.
   asserts~ L: (S (length f'') = length r'').
   destruct f'' as [|x f'']; destruct r'' as [|y [|z r'']];
    calc_length in L; simpl in L; tryfalse.
     applys* C0. applys* C.
  false. destruct Inv as (n&m&p&g&Op&Ap). destruct Ap.
   testsb: (ok == 0).
     rewriteb Test in C1. applys* C1. (* todo: substb bug *)
     destruct f'.
       calc_length in appe_lf'0. destruct Op. math.
       applys* C2.
  auto.
Qed.

Hint Extern 1 (RegisterSpec exec) => Provide exec_spec.

Lemma invalidate_spec : 
  Spec invalidate (s:status a) |R>>
    forall Q x ft lenf lenr r,
     repr (x::Q) (lenf,x::ft,s,lenr,r) -> 
     R (fun s' => check_precondition (lenf-1,ft,s',lenr,r) Q).
Proof. 
  xcf. introv Inv. xgo.
  (* case reversing *)
  renames r0 to r'', f to f''. clear H.
  left. destruct Inv as (n&m&p&g&Op&Re).
  destruct Op. destruct Re. destruct oper_base0. split.
  math.
  asserts Lg: (length g = 2*m + 1 - p :> int). 
    subst g. sets_eq ok': (abs ok : int). 
    asserts: (ok' = n - p). subst ok'. rewrite~ abs_pos.
    calc_length. rewrite~ length_take.
  destruct g as [|y g']. false. math.
  exists n m (p+1) g'. calc_length in *. split.
    constructor~.
      constructor~.
        calc_app in base_lval0. inversions~ base_lval0. 
      simpl in oper_fval0. injection oper_fval0. auto.
    constructor~. renames reve_gval0 to H.
     lets~ [z E]: (@take_last_int _ f' ok). 
     rewrite E in H. calc_list in H. inversion~ H.
  (* case appending to done *)
  renames x0 to y. clear H.
  left. destruct Inv as (n&m&p&g&Op&Ap).
  destruct Op. destruct Ap. destruct oper_base0. split.
  math.
  calc_length in *. simpl. splits~.
    constructor~.
      renames base_lval0 to H.
       subst g. simpl in H. calc_list in H. inversions~ H.
  (* case appending *)
  clear H.
  left. destruct Inv as (n&m&p&g&Op&Ap).
  destruct Op. destruct Ap. destruct oper_base0. split.
  math.
  asserts Lg: (length g = 2*m + 1 - p :> int). 
    subst g. sets_eq ok': (abs ok : int). 
    asserts: (ok' = 2*m + 1 - n - p). subst ok'. rewrite~ abs_pos.
    calc_length. rewrite~ length_take.
  asserts OkPos: (ok <> 0).
    intros E. destruct r'.
      math.
      applys C0. rewrite~ E.
  destruct g as [|y g']. false. math.
  exists n m (p+1) g'. calc_length in *. split.
    constructor~.
      constructor~.
        calc_app in base_lval0. inversions~ base_lval0. 
      simpl in oper_fval0. injection oper_fval0. auto.
    constructor~. renames appe_gval0 to H.
     lets~ [z E]: (@take_last_int _ f' ok).
     rewrite E in H. calc_list in H. inversion~ H.
  (* case other *)
  clear H. destruct s as [|ok f'' f' r'' r'|ok f' r'|f'].
  clear C C0 C1. destruct Inv as (B&L). destruct B. 
   calc_list in *. inversion base_lval0. simpl. 
    testsb E: (lenr == lenf).
      right. split~. constructor~.
      left. splits~. constructor~.
  false. destruct Inv as (n&m&p&g&Op&Re). apply~ C.
  false. destruct Inv as (n&m&p&g&Op&Ap).
   testsb: (ok == 0).
     destruct r'.
       destruct Op. destruct Ap. destruct oper_base0. math.
       applys* C0.
     applys* C1.
  false. destruct Inv as (F&_&_). auto.
Qed.

Hint Extern 1 (RegisterSpec invalidate) => Provide invalidate_spec.

Lemma exec2_spec : 
  Spec exec2 (q:queue a) |R>>
    forall Q, inv true 2 q Q -> 
    R (Q ; queue a).
Proof. 
  xcf. introv Inv. xgo.
  applys~ (>>>Hyps HR __ __ Inv).
  applys~ (>>>Hyps HR __ __ P_x11).
  destruct P_x11 as (_&B&L). constructor~.
  destruct newstate; simpl in P_x11; auto. false* C.
Qed.

Hint Extern 1 (RegisterSpec exec2) => Provide exec2_spec.

Lemma check_spec : 
  Spec check (q:queue a) |R>>
    forall Q, check_precondition q Q -> R (Q ; queue a).
Proof.
  xcf. introv H. xgo; destruct H as [[L Inv]|[L Inv]]; tryfalse by math/.
  auto. 
  apply refl_equal.
  clear H0. subst newstate. simpl. exists 0 lenf 0 (f++rev r).
   destruct Inv as (B&Le). split.
     constructor~.
       constructor~. calc_list~.
       subst Q. rewrite~ take_app_length.
     constructor~. simpl. calc_list~.
Qed.

Hint Extern 1 (RegisterSpec check) => Provide check_spec.

Lemma empty_spec : 
  rep (@empty a) (@nil A).
Proof.
  generalizes RA A. apply (empty_cf a). xgo.
  intros. simpl. rew_list~. 
Qed.
(*
  intros. 
  assert (@empty A A A = (0,nil,Idle,0,nil)).
    apply (Caml.empty_cf A A A (fun C B A p => p = (0,nil,Idle,0,nil))).
    xret~.
  unfold repr. rewrite H. split~. constructor~. 
*)

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma is_empty_spec : 
  RepTotal is_empty (Q;queue a) >> bool_of (Q = nil).
Proof.
  simpl. xcf. introv H. xgo. clear H0. 
  renames _p1 to f, _p2 to s, _p3 to lenr, _p4 to r.
  hnf in H. destruct s as [|ok f'' f' r'' r'|ok f' r'|f']; simpl.
  destruct H as (B&L).
   split; intros K.
     applys~ base_self_nil B.
     applys~ base_self_nil_inv B.
  destruct H as (n&m&p&g&Op&Re). 
   destruct Op. destruct Re. lets H: oper_base0. destruct oper_base0.
   split; intros K. 
     applys~ base_self_nil H.
     applys~ base_self_nil_inv H.
       sets_eq ok': (abs ok : int). 
        asserts: (ok' = n - p). subst ok'. rewrite~ abs_pos.
        subst g. calc_length. rewrite~ length_take.
  destruct H as (n&m&p&g&Op&Ap).
   destruct Op. destruct Ap. lets H: oper_base0. destruct oper_base0.
   split; intros K. 
     applys~ base_self_nil H.
     applys~ base_self_nil_inv H.
      sets_eq ok': (abs ok : int). 
        asserts: (ok' = 2*m + 1 - n - p). subst ok'. rewrite~ abs_pos.
        subst g. calc_length. rewrite~ length_take.
  false*. 
Qed.

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty.

Lemma snoc_spec : 
  RepTotal snoc (Q;queue a) (X;a) >> (Q & X) ; queue a.
Proof.
  xcf. intros x _p Q Re. xgo; clear H. 
  asserts [[L St]|L]: ((lenr = lenf /\ state = Idle) \/ (lenr < lenf)).
    destruct state as [|ok f'' f' r'' r'|ok f' r'|f'].
      destruct Re as (B&L). destruct B.
       testsb: (lenr == lenf). left~. right~.
      right. destruct Re as (n&m&p&g&Op&Re). destruct Op.
       destruct Re. destruct oper_base0. math.
      right. destruct Re as (n&m&p&g&Op&Ap). destruct Op.
       destruct Ap. destruct oper_base0. math.
      destruct Re as (C&_&_). false.
  (* case start rotation *)
  right. split~. subst state. inversion Re as [[E1 E2 E3] Le].
  constructor. calc_length~. auto. subst Q. calc_list~. 
  (* case continue rotation *)
  left. split~. destruct state as [|ok f'' f' r'' r'|ok f' r'|f'].
  (* subcase: idle *)
  destruct Re as ([E1 E2 E3]&_). split~.
    constructor. calc_length~. math. subst Q. calc_list~.
  (* subcase: reversing *)
  destruct Re as (n&m&p&g&Op&Re). exists n m p g. split.
    destruct Op. constructor~. 
      destruct oper_base0. constructor.
        calc_length~.
        math.
        subst Q. calc_rev~.
      rewrite~ take_app_l. destruct Re. destruct oper_base0. 
       subst g Q. calc_length~.
    destruct Re. constructor~.
  (* subcase: appending *)
  destruct Re as (n&m&p&g&Op&Ap). exists n m p g. split.
    destruct Op. constructor~. 
      destruct oper_base0. constructor.
        calc_length~.
        math.
        subst Q. calc_rev~.
      rewrite~ take_app_l. destruct Ap. destruct oper_base0. 
       subst g Q. calc_length~.
    destruct Ap. constructor~.
  (* subcase: done *)
  destruct Re as (C&_&_). false. 
Qed.

Hint Extern 1 (RegisterSpec snoc) => Provide snoc_spec.

Lemma head_spec : 
  RepSpec head (Q;queue a) |R>>
     Q <> nil -> R (is_head Q ;; a).
Proof.
  xcf. introv R. xgo.
  lets: (>>> repr_fnil R). false.
  applys* repr_fcons.
Qed.

Hint Extern 1 (RegisterSpec head) => Provide head_spec.

Lemma tail_spec :
  RepSpec tail (Q;queue a) |R>> 
     Q <> nil -> R (is_tail Q ;; queue a).
Proof.
  xcf. introv R. destruct _p as ((((lenf,f),s),lenr),r). xgo.
  lets: (>>> repr_fnil R). false.
  renames x0 to y, r0 to r, lenr0 to lenr, lenf0 to lenf.
  lets: (>>> Hyps repr_fcons R). subst.
  applys (>>> Hyps HR R).
  cbv beta in *. auto.
Qed.

Hint Extern 1 (RegisterSpec tail) => Provide tail_spec.

End Polymorphic.

End HoodMelvilleQueueSpec.


