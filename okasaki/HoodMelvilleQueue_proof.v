
(* todo: migrate *)

(**************************************************************************
* Queue : batch implementation                                            *
***************************************************************************)

Set Implicit Arguments.
Require queue_hood_melville_ml.
Module Caml := queue_hood_melville_ml.
Require Import FuncTactics LibList.
Require Import LibInt.
Import Caml.

Hint Rewrite double : rew_maths.
Ltac auto_tilde ::= auto with maths.

(* ---------------------------------------------------------------------- *)
(** ** Invariants *)

Definition queue A := 
  (int * list A * status A * int * list A)%type.

Record base A (lf lenf lenr : int) (r g l:list A) :=
  { base_lenr : lenr = length r;
    base_lenf : lenf = lf;
    base_lval : l = g ++ rev r }.

Record oper A lenf f lenr r (g l:list A) (d n m p : int) : Prop := 
  { oper_base : base (2*m + 1 - p) lenf lenr r g l;
    oper_npos : n >= 0;
    oper_mpos : m >= 0;
    oper_ppos : p >= 0;
    oper_nval : n + d = 2*p + 2*lenr + 2;
    reve_lf   : length f = m - p :> int; 
    oper_fval : f = take (length f) l }.

Record reve A (f f' f'' r' r'' g l : list A) (ok n m p : int) : Prop :=
  { reve_gval : g = rev (take (abs ok) f') ++ f'' ++ rev r'' ++ r';
    reve_lf'  : length f' = n :> int;
    reve_lf'' : length f'' = m - n :> int;
    reve_lr'  : length r' = n :> int;
    reve_lr'' : length r'' = m + 1 - n :> int;
    reve_okval: ok = n - p;
    reve_nle : n <= m }.

Record appe A (f f' r' g l:list A) (ok n m p : int) : Prop :=
  { appe_gval : g = rev (take (abs ok) f') ++ r';
    appe_lf'  : length f' = 2*m + 1 - n :> int;
    appe_lr'  : length r' = n :> int;
    appe_okval: ok = 2*m + 1 - n - p; 
    appe_okpos: ok >= 0;
    appe_nge  : n >= m;
    appe_nle  : n <= 2*m + 1 }.

Definition inv (c:bool) (d:int) A (l:list A) (q:queue A) : Prop :=
  let '(lenf,f,s,lenr,r) := q in
  match s with
  | Idle => base (length f) lenf lenr r f l /\ lenr <= lenf
  | Done f' => c /\ base (length f') lenf lenr r f' l /\ lenr <= lenf
  | Reversing ok f'' f' r'' r' => exists n m p g,
        oper lenf f lenr r g l d n m p 
     /\ reve f f' f'' r' r'' g l ok n m p  
  | Appending ok f' r' => exists n m p g,
        oper lenf f lenr r g l d n m p 
     /\ appe f f' r' g l ok n m p  
  end.

Definition repr := inv false 0.

(** pre-condition for [check] *)
Definition check_pre A (l:list A) q :=
  let '(lenf,f,s,lenr,r) := q in
    (lenr <= lenf /\ inv true 2 l q)    
 \/ (lenr = lenf + 1 /\ base (length f) lenf lenr r f l).
    (* note: (lenr <= lenf) could also be derived *)


(* ---------------------------------------------------------------------- *)
(** ** Facts *)

Lemma base_self_nil : forall A lenf lenr r f lf (l:list A),
  base lf lenf lenr r f l ->
  lf >= length f ->
  lenr <= lenf ->
  lenf == 0 ->
  l = nil.
Proof.
  introv B L. intros. destruct B as [? ? E]. 
  rewrite~ (@length_zero_inv _ r) in E.
  rewrite~ (@length_zero_inv _ f) in E.
Qed.

Lemma base_self_nil_inv : forall A lenf lenr r g lf l,
  @base A lf lenf lenr r g l ->
  l = nil -> lf >= 0 -> lf <= length g ->  
  lenf == 0.
Proof.
  introv B E Ge Le. subst l. destruct B.
  destruct~ (@nil_eq_app_rev_inv _ g r).
  subst. calc_list in *. math.
Qed.

Lemma repr_fnil : forall A (l:list A) lenf lenr r s,
  repr l (lenf, nil, s, lenr, r) -> l = nil.
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

Lemma repr_fcons : forall A x y (l:list A) lenf f s lenr r,
 repr (x :: l) (lenf, y :: f, s, lenr, r) -> y = x.
Proof.
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


(* ---------------------------------------------------------------------- *)
(** ** Verification *)

Lemma exec_spec : forall A,
  Spec exec (s:status A) |R>>
    forall l lenf f lenr r d, d > 0 -> d <= 2 -> 
     inv true d l (lenf,f,s,lenr,r) -> 
     R (fun s' => inv true (d-1) l (lenf,f,s',lenr,r)).
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

Lemma invalidate_spec : forall A,
  Spec invalidate (s:status A) |R>>
    forall l x ft lenf lenr r,
     repr (x::l) (lenf,x::ft,s,lenr,r) -> 
     R (fun s' => check_pre l (lenf-1,ft,s',lenr,r)).
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

Lemma exec2_spec : forall A,
  Spec exec2 (q:queue A) |R>>
    forall l, inv true 2 l q -> 
    R (repr l).
Proof. 
  xcf. introv Inv. xgo.
  applys~ (>>>Hyps HR __ __ Inv).
  applys~ (>>>Hyps HR __ __ P_x11).
  destruct P_x11 as (_&B&L). constructor~.
  destruct newstate; simpl in P_x11; auto. false* C.
Qed.

Hint Extern 1 (RegisterSpec exec2) => Provide exec2_spec.

Lemma check_spec : forall A,
  Spec check (q:queue A) |R>>
    forall l, check_pre l q -> R (repr l).
Proof.
  xcf. introv H. xgo; destruct H as [[L Inv]|[L Inv]]; tryfalse by math/.
  auto. 
  apply refl_equal.
  clear H0. subst newstate. simpl. exists 0 lenf 0 (f++rev r).
   destruct Inv as (B&Le). split.
     constructor~.
       constructor~. calc_list~.
       subst l. rewrite~ take_app_length.
     constructor~. simpl. calc_list~.
Qed.

Hint Extern 1 (RegisterSpec check) => Provide check_spec.

Lemma empty_spec : forall A, repr nil (@empty A A A).
Proof.
  intros. 
  assert (@empty A A A = (0,nil,Idle,0,nil)).
    apply (Caml.empty_cf A A A (fun C B A p => p = (0,nil,Idle,0,nil))).
    xret~.
  unfold repr. rewrite H. split~. constructor~. 
Qed.

Hint Extern 1 (RegisterSpec empty) => Provide empty_spec.

Lemma isEmpty_spec : forall A,
  Spec isEmpty (q:queue A) |R>> 
    forall l, repr l q -> R (fun b => trueb b <-> l = nil).
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

Lemma snoc_spec : forall A,
  Spec Caml.snoc (x:A) (q:queue A) |R>>
    forall l, repr l q -> R (repr (l & x)).
Proof.
  xcf. intros x _p l Re. xgo; clear H. 
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
  constructor. calc_length~. auto. subst l. calc_list~. 
  (* case continue rotation *)
  left. split~. destruct state as [|ok f'' f' r'' r'|ok f' r'|f'].
  (* subcase: idle *)
  destruct Re as ([E1 E2 E3]&_). split~.
    constructor. calc_length~. math. subst l. calc_list~.
  (* subcase: reversing *)
  destruct Re as (n&m&p&g&Op&Re). exists n m p g. split.
    destruct Op. constructor~. 
      destruct oper_base0. constructor.
        calc_length~.
        math.
        subst l. calc_rev~.
      rewrite~ take_app_l. destruct Re. destruct oper_base0. 
       subst g l. calc_length~.
    destruct Re. constructor~.
  (* subcase: appending *)
  destruct Re as (n&m&p&g&Op&Ap). exists n m p g. split.
    destruct Op. constructor~. 
      destruct oper_base0. constructor.
        calc_length~.
        math.
        subst l. calc_rev~.
      rewrite~ take_app_l. destruct Ap. destruct oper_base0. 
       subst g l. calc_length~.
    destruct Ap. constructor~.
  (* subcase: done *)
  destruct Re as (C&_&_). false. 
Qed.

Hint Extern 1 (RegisterSpec snoc) => Provide snoc_spec.

Lemma head_spec : forall A,
  Spec Caml.head (q:queue A) |R>>
    forall x l, repr (x::l) q -> R (= x).
Proof.
  xcf. introv R. xgo.
  lets: (>>> repr_fnil R). false.
  applys* repr_fcons.
Qed.

Hint Extern 1 (RegisterSpec head) => Provide head_spec.

Lemma tail_spec : forall A,
  Spec Caml.tail (q:queue A) |R>>
    forall x l, repr (x::l) q -> R (repr l).
Proof.
  xcf. introv R. destruct _p as ((((lenf,f),s),lenr),r). xgo.
  lets: (>>> repr_fnil R). false.
  renames x0 to y, r0 to r, lenr0 to lenr, lenf0 to lenf.
  lets: (>>> Hyps repr_fcons R). subst.
  applys (>>> Hyps HR R).
  cbv beta in *. auto.
Qed.

Hint Extern 1 (RegisterSpec tail) => Provide tail_spec.
