Set Implicit Arguments.
Require Import LibCore FuncTactics.
Require Import QueueSig_ml QueueSig_proof.
Require Import HoodMelvilleQueue_ml.

Module HoodMelvilleQueueSpec <: QueueSigSpec.

(** instantiations *)

Module Import Q <: MLQueue := MLHoodMelvilleQueue.
Import MLHoodMelvilleQueue.

(** invariant *)

Section Invariant.
Context `{RA:Rep a A}. 

Record base (lf lenf lenr : int) (r g : list a) (Q:list A) :=
  { base_lenr : lenr = length r;
    base_lenf : lenf = lf;
    base_lval : rep (g ++ rev r) Q }.

Record oper lenf f lenr r (g :list a) Q (d n m p : int) : Prop := 
  { oper_base : base (2*m + 1 - p) lenf lenr r g Q;
    oper_npos : n >= 0;
    oper_mpos : m >= 0;
    oper_ppos : p >= 0;
    oper_nval : n + d = 2*p + 2*lenr + 2;
    reve_lf   : length f = m - p :> int; 
    oper_fval : rep f (take (length f) Q) }.

Record reve (f f' f'' r' r'' g : list a) (ok n m p : int) : Prop :=
  { reve_gval : g = rev (take (abs ok) f') ++ f'' ++ rev r'' ++ r';
    reve_lf'  : length f' = n :> int;
    reve_lf'' : length f'' = m - n :> int;
    reve_lr'  : length r' = n :> int;
    reve_lr'' : length r'' = m + 1 - n :> int;
    reve_okval: ok = n - p;
    reve_nle : n <= m }.

Record appe (f f' r' g:list a) (ok n m p : int) : Prop :=
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
  | Finished f' => c /\ base (length f') lenf lenr r f' Q /\ lenr <= lenf
  | Reversing ok f'' f' r'' r' => exists n m p g,
        oper lenf f lenr r g Q d n m p 
     /\ reve f f' f'' r' r'' g ok n m p  
  | Appending ok f' r' => exists n m p g,
        oper lenf f lenr r g Q d n m p 
     /\ appe f f' r' g ok n m p  
  end.

End Invariant.

(** model *)

Global Instance queue_rep `{Rep a A} : Rep (queue a) (list A).
Proof.
  intros. apply (Build_Rep (inv false 0)).
  cuts* K: (forall q c1 d1 Q1 c2 d2 Q2, 
    inv c1 d1 q Q1 -> inv c2 d2 q Q2 -> Q1 = Q2).
  destruct q as ((((lenf,f),state),lenr),r).
  introv K1 K2. destruct state; intuit K1; intuit K2.
  intuit H0; intuit H2. prove_rep.
  intuit H0; intuit H1; intuit H2; intuit H3.
   intuit oper_base0; intuit oper_base1; subst; apply* @rep_unique.
  intuit H0; intuit H1; intuit H2; intuit H3.
   intuit oper_base0; intuit oper_base1; subst; apply* @rep_unique.
  intuit H1; intuit H4. prove_rep.
Defined.

(** automation *)

Hint Constructors Forall2.
Hint Resolve Forall2_last.
Ltac auto_tilde ::= auto with maths.
Ltac auto_star ::= try solve [ intuition (eauto with maths) ].

(** useful facts *)

Section Polymorphic.
Variables (a A : Type) (RA:Rep a A).
Implicit Types Q : list A.

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
  inverts~ E.
Qed.

Lemma base_self_nil_inv : forall lenf lenr r g lf Q,
  base lf lenf lenr r g Q ->
  Q = nil -> lf >= 0 -> lf <= length g ->  
  lenf = 0.
Proof.
  introv B E Ge Le. subst Q. destruct B.
  inverts base_lval0.
  destruct~ (@nil_eq_app_rev_inv _ g r).
  subst. rew_length in *. math.
Qed.

Lemma repr_fnil : forall Q lenf lenr r s,
  rep (lenf, nil, s, lenr, r) Q -> Q = nil.
Proof.
  introv R.
  destruct s as  [|ok f'' f' r'' r'|ok f' r'|f']; simpl in R.
  (* subcase: idle *)
  destruct R as ([E1 E2 E3]&L). rew_length in *. 
  rewrite~ (@length_zero_inv _ r) in E3. inverts~ E3.
  (* subcase: reversing *)
  false. destruct R as (n&m&p&g&Op&Re).
  destruct Re. destruct Op. destruct oper_base0.
  rew_length in *. 
  cuts: (length g = 2*m + 1 - p :> int). math.
    subst g. rew_length~.
  (* subcase: appending *)
  false. destruct R as (n&m&p&g&Op&Ap).
  destruct Ap. destruct Op. destruct oper_base0.
  rew_length in *. 
  cuts: (length g = 2*m + 1 - p :> int). math.
    subst g. rew_length~.
  (* subcase: done *)
  destruct R as (C&_&_). false.
Qed.

Lemma repr_fcons : forall x X Q lenf f s lenr r,
 rep (lenf, x :: f, s, lenr, r) (X :: Q) -> rep x X.
Proof. (* todo: rep unique *)
  introv R. destruct s as [|ok f'' f' r'' r'|ok f' r'|f']. 
  (* subcase: idle *)
  destruct R as ([E1 E2 E3]&L). rew_list in E3. inversion~ E3. 
  (* subcase: reversing *)
  destruct R as (n&m&p&g&Op&Re). lets H: (oper_fval Op).
  rew_length in H. simpl in H. inversion H. auto. (* todo: bug inversions H*)
  (* subcase: appending *)
  destruct R as (n&m&p&g&Op&Ap). lets H: (oper_fval Op).
  rew_length in H. simpl in H. inversion H. auto.
  (* subcase: done *)
  destruct R as (C&_&_). false.
Qed.

(** verification *)

Definition check_precondition q Q :=
  let '(lenf,f,s,lenr,r) := q in
    (lenr <= lenf /\ inv true 2 q Q)    
 \/ (lenr = lenf + 1 /\ base (length f) lenf lenr r f Q).

Lemma exec_spec : 
  Spec exec (s:status a) |R>>
    forall Q lenf f lenr r d, d > 0 -> d <= 2 -> 
     inv true d (lenf,f,s,lenr,r) Q -> 
     R (fun s' => inv true (d-1) (lenf,f,s',lenr,r) Q).
Proof.
  xcf. introv Dinf Dsup Inv. xgo.
  (* reversing *)
  destruct Inv as (n&m&p&g&Op&Re).
  destruct Op. destruct Re. destruct oper_base0.
  simpl. exists (n+1) m p g. split.
    constructor~.
      constructor~.
    constructor; rew_length in *; auto~. (* slow! *)
      rewrite~ take_cons_int. rew_list in reve_gval0. rew_list~.
  (* reversing to appending *)
  destruct Inv as (n&m&p&g&Op&Re).
  destruct Op. destruct Re. destruct oper_base0.
  simpl. exists (n+1) m p g. split.
    constructor~.
      constructor~.
    constructor; rew_length in *; auto~.
  (* appending to done *)
  clear C C0 H. destruct Inv as (n&m&p&g&Op&Ap).
  destruct Op. destruct Ap. destruct oper_base0.
  simpl. splits~.
    renames appe_gval0 to K. simpl in K. rew_list in K. 
     constructor~. congruence.
  (* appending *)
  clear C C0 H. 
  asserts: (ok <> 0). intros K. subst ok. applys* C1. clear C1.
  destruct Inv as (n&m&p&g&Op&Ap).
  destruct Op. destruct Ap. destruct oper_base0.
  simpl. exists (n+1) m p g. split.
    constructor~. 
      constructor~.
      constructor; rew_length in *; auto~.
        renames appe_gval0 to M.
        rewrite~ take_cons_pred_int in M. rew_list~ in M. 
  (* other *)
  destruct _x0 as [|ok f'' f' r'' r'|ok f' r'|f']; simpl.
  auto. 
  false. destruct Inv as (n&m&p&g&Op&Re). destruct Re.
   asserts~ L: (S (length f'') = length r'').
   destruct f'' as [|x f'']; destruct r'' as [|y [|z r'']];
    rew_length in L; simpl in L; tryfalse.
  false. destruct Inv as (n&m&p&g&Op&Ap). destruct Ap.
   testsb: (ok == 0).
     rewriteb Test in C1. applys* C1.
     destruct f'.
       rew_length in appe_lf'0. destruct Op. math.
       applys* C2.
  auto.
Qed.

Hint Extern 1 (RegisterSpec exec) => Provide exec_spec.

Lemma invalidate_spec : 
  Spec invalidate (s:status a) |R>>
    forall x X Q ft lenf lenr r,
     rep (lenf,x::ft,s,lenr,r) (X::Q) -> 
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
    rew_length. rewrite~ length_take.
  destruct g as [|y g']. false. rew_length in *. math.
  exists n m (p+1) g'. rew_length in *. split.
    constructor~.
      constructor~.
        rew_app in base_lval0. inversions~ base_lval0. 
      simpl in oper_fval0. inverts~ oper_fval0.
    constructor~. renames reve_gval0 to H.
     lets~ [z E]: (@take_last_int _ f' ok). 
     rewrite E in H. rew_list in H. inversion~ H.
  (* case appending to done *)
  renames x0 to y. clear H.
  left. destruct Inv as (n&m&p&g&Op&Ap).
  destruct Op. destruct Ap. destruct oper_base0. split.
  math.
  rew_length in *. simpl. splits~.
    constructor~.
      renames base_lval0 to H.
       subst g. simpl in H. rew_list in H. inversions~ H.
  (* case appending *)
  clear H.
  left. destruct Inv as (n&m&p&g&Op&Ap).
  destruct Op. destruct Ap. destruct oper_base0. split.
  math.
  asserts Lg: (length g = 2*m + 1 - p :> int). 
    subst g. sets_eq ok': (abs ok : int). 
    asserts: (ok' = 2*m + 1 - n - p). subst ok'. rewrite~ abs_pos.
    rew_length. rewrite~ length_take.
  asserts OkPos: (ok <> 0).
    intros E. destruct r'.
      rew_length in *. math.
      applys C0. rewrite~ E.
  destruct g as [|y g']. false. rew_length in *. math.
  exists n m (p+1) g'. rew_length in *. split.
    constructor~.
      constructor~.
        rew_app in base_lval0. inversions~ base_lval0. 
      simpl in oper_fval0. inverts~ oper_fval0. 
    constructor~. renames appe_gval0 to H.
     lets~ [z E]: (@take_last_int _ f' ok).
     rewrite E in H. rew_list in H. inversion~ H.
  (* case other *)
  clear H. renames _x0 to s.
  destruct s as [|ok f'' f' r'' r'|ok f' r'|f'];
   try solve [false; simpls; intuition].
  clear C C0 C1. destruct Inv as (B&L). destruct B. 
   rew_list in *. inversion base_lval0. simpl. 
    testsb E: (lenr == lenf).
      right. split~. constructor~.
      left. splits~. constructor~.
Qed.

Hint Extern 1 (RegisterSpec invalidate) => Provide invalidate_spec.

Lemma exec2_spec : 
  Spec exec2 (q:queue a) |R>>
    forall Q, inv true 2 q Q -> 
    R (Q ;- queue a).
Proof. 
  xcf. introv Inv. xmatch. xapp~ Inv. xapp~ P_x2. xmatch.
  intuit P_x1. constructor~.
  destruct _x1; simpls~. false* C.
Qed.

Hint Extern 1 (RegisterSpec exec2) => Provide exec2_spec.

Lemma Forall2_take : forall A1 A2 (P:A1->A2->Prop) n l t,
  Forall2 P l t ->
  Forall2 P (take n l) (take n t).
Proof. induction n; introv H; inverts H; simple~. Qed.

Lemma check_spec : 
  Spec check (q:queue a) |R>>
    forall Q, check_precondition q Q -> R (Q ;- queue a).
Proof.
  xcf. introv H. xgo; destruct H as [[L Inv]|[L Inv]];
    tryfalse by math/; try ximpl_nointros.
  subst~.
  apply refl_equal.
  subst newstate. simpl. exists 0 lenf 0 (f++rev r).
   destruct Inv as (B&Le). split.
     constructor~.
       constructor~. rew_list~.
       forwards~ M: (@Forall2_take _ _ rep (length f) (f++rev r) Q).
        rewrite~ take_app_length in M. 
     constructor~. simpl. rew_list~.
Qed.

Hint Extern 1 (RegisterSpec check) => Provide check_spec.

Lemma empty_spec : 
  rep (@empty a) (@nil A).
Proof.
  generalizes RA A. apply (empty_cf a). xgo.
  intros. simpl. split~. constructors~. rew_list~.
Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

(* todo move *)
Section BoolOf.
Variables (b:bool) (P:Prop).

Lemma bool_of_prove : (b <-> P) -> bool_of P b.
Proof. intros. extens*. Qed.
End BoolOf.

Hint Rewrite isTrue_istrue istrue_isTrue : rew_istrue.
Ltac rew_istrue := autorewrite with rew_istrue.


Ltac fix_bool_of_known tt ::= 
  match goal with 
  | H: bool_of ?P true |- _ => 
     applys_to H bool_of_true_in
  | H: bool_of ?P false |- _ => 
     applys_to H bool_of_false_in
  | H: bool_of ?P ?b, Hb: isTrue ?b |- _ => 
     applys_to H (@bool_of_true_back b P Hb); clear Hb
  | H: bool_of ?P ?b, Hb: isTrue (! ?b) |- _ => 
     applys_to H (@bool_of_false_back b P Hb); clear Hb 
  | |- bool_of ?P true => 
     apply bool_of_true_in_forw
  | |- bool_of ?P false => 
     apply bool_of_false_in_forw
  | |- bool_of ?P ?b =>
     apply bool_of_prove; rew_istrue
  end.


Lemma is_empty_spec : 
  RepTotal is_empty (Q;queue a) >> bool_of (Q = nil).
Proof.
  simpl. xcf. introv H. xgo. clear H0. 
  renames _p0 to f, _p1 to s, _p2 to lenr, _p3 to r.
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
        subst g. rew_length. rewrite~ length_take.
  destruct H as (n&m&p&g&Op&Ap).
   destruct Op. destruct Ap. lets H: oper_base0. destruct oper_base0.
   split; intros K. 
     applys~ base_self_nil H.
     applys~ base_self_nil_inv H.
      sets_eq ok': (abs ok : int). 
        asserts: (ok' = 2*m + 1 - n - p). subst ok'. rewrite~ abs_pos.
        subst g. rew_length. rewrite~ length_take.
  false*. 
Qed.

Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty.

Lemma Forall2_length : forall A1 A2 (P:A1->A2->Prop) l t,
  Forall2 P l t -> length l = length t.
Proof. introv H. induction H. simple~. rew_length~. Qed.


Lemma snoc_spec : 
  RepTotal snoc (Q;queue a) (X;a) >> (Q & X) ;- queue a.
Proof.
  xcf. intros x _p Q X Re RX. xgo; clear H; try ximpl_nointros. 
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
  constructor. rew_length~. auto.
    rewrite rev_cons. rewrite <- app_assoc. rapply Forall2_last; eauto.
  (* case continue rotation *)
  left. split~. destruct state as [|ok f'' f' r'' r'|ok f' r'|f'].
  (* subcase: idle *)
  destruct Re as ([E1 E2 E3]&_). split~.
    constructor. rew_length~. math. 
     rewrite rev_cons. rewrite <- app_assoc. sapply* Forall2_last.  
  (* subcase: reversing *)
  destruct Re as (n&m&p&g&Op&Re). exists n m p g. split.
    destruct Op. constructor~. 
      destruct oper_base0. constructor.
        rew_length~.
        math.
        rewrite rev_cons. rewrite <- app_assoc. sapply* Forall2_last.
      rewrite~ take_app_l. destruct Re. destruct oper_base0. 
       subst g. forwards M: (Forall2_length base_lval0). rew_length in M. math.
    destruct Re. constructor~.
  (* subcase: appending *)
  destruct Re as (n&m&p&g&Op&Ap). exists n m p g. split.
    destruct Op. constructor~. 
      destruct oper_base0. constructor.
        rew_length~.
        math.
        rewrite rev_cons. rewrite <- app_assoc. sapply* Forall2_last.
      rewrite~ take_app_l. destruct Ap. destruct oper_base0. 
       subst g. forwards M: (Forall2_length base_lval0). rew_length in M. math.
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
  destruct Q. false. forwards: (>>> repr_fcons R). xrep*.
Qed.

Hint Extern 1 (RegisterSpec head) => Provide head_spec.

Lemma tail_spec :
  RepSpec tail (Q;queue a) |R>> 
     Q <> nil -> R (is_tail Q ;; queue a).
Proof.
  xcf. introv R NE. destruct _x0 as ((((lenf,f),s),lenr),r).
  xmatch.
  lets: (>>> repr_fnil R). false.
  destruct Q. false. lets: (>>> repr_fcons R). 
   xapp*. xapp*. ximpl*.
Qed.

Hint Extern 1 (RegisterSpec tail) => Provide tail_spec.

End Polymorphic.

End HoodMelvilleQueueSpec.


