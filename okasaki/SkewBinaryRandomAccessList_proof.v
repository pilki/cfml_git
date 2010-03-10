(**************************************************************************
* Skew binary lists                                            *
***************************************************************************)

Set Implicit Arguments.
Require list_skew_binary_ml.
Module Caml := list_skew_binary_ml.
Require Import FuncTactics LibList.
Require Import LibInt.
Import Caml.
Import list_skew_binary_ml. (* todo *)

Hint Rewrite double : rew_maths.
Ltac auto_tilde ::= auto with maths.

Require Import Zpower.

(* ---------------------------------------------------------------------- *)
(** ** Facts *)

Implicit Arguments fst [[A] [B]].
Implicit Arguments snd [[A] [B]].

Section NthApp.
Variables (A:Type).
Implicit Types l : list A.
Axiom Nth_app_l : forall i l1 l2 x,
  (i < length l1)%N -> Nth i l1 x -> Nth i (l1++l2) x.
Axiom Nth_app_r : forall i l1 l2 x,
  (i >= length l1)%N -> Nth (i-length l1)%nat l2 x -> Nth i (l1++l2) x.
End NthApp.

Axiom div2_even : forall n, 
  (2 * n) / 2 = n.
Axiom div2_odd : forall n, 
  (2 * n + 1) / 2 = n.
Axiom div2_lt : forall n,
  n > 0 -> n / 2 < n.

Tactic Notation "unfolds" "~" :=
  unfolds; auto_tilde.



(* ---------------------------------------------------------------------- *)
(** ** Invariants *)

Definition rlist A := list (int * tree A).

Fixpoint tree_items A (t:tree A) : list A :=
  match t with
  | Leaf x => x::nil
  | Node x t1 t2 => x::(tree_items t1)++(tree_items t2)
  end.

Definition rlist_items A (l:rlist A) :=
  flatten (map (fun wt:int*tree A => let (w,t) := wt in tree_items t) l).

Inductive size A : int -> tree A -> Prop :=
  | size_leaf : forall x,
      size 1 (Leaf x)
  | size_node : forall n x t1 t2,
      size n t1 ->
      size n t2 ->
      size (2*n+1) (Node x t1 t2).
     
Definition sizes A (l:rlist A) := 
  Forall (fun wt:int*tree A => let (w,t) := wt in size w t) l.

Definition is_size w := exists n, 
  n > 0 /\ w = 2 ^ n - 1 :> int.

Inductive ordered : bool -> list int -> Prop :=
  | ordered_nil : forall b,
      ordered b nil
  | ordered_one : forall b w,
      is_size w ->
      ordered b (w::nil)
  | ordered_same : forall w ws,
      ordered false (w::ws) ->
      is_size w ->
      ordered true (w::w::ws)
  | ordered_cons : forall b w1 w2 ws,
      ordered false (w2::ws) ->
      is_size w1 ->
      w1 < w2 ->
      ordered b (w1::w2::ws).

Definition skew := ordered true.

Definition skewed A (l:rlist A) := 
  skew (map fst l).

Record repr A (L:list A) (l:rlist A) : Prop := {
  Item: L = rlist_items l;
  Size: sizes l;
  Skew: skewed l }. 


(* ---------------------------------------------------------------------- *)
(** ** Lemmas *)

Hint Constructors Forall.
Hint Constructors size.
Hint Unfold sizes.

Lemma tree_items_leaf : forall A (x:A),
  tree_items (Leaf x) = x::nil.
Proof. auto. Qed.

Lemma tree_items_node : forall A (x:A) t1 t2,
  tree_items (Node x t1 t2) = x::(tree_items t1)++(tree_items t2).
Proof. auto. Qed.

Hint Rewrite tree_items_leaf tree_items_node : rew_list. 

Lemma repr_nil_l : forall A (L:list A) l,
  repr L l -> l = nil -> L = nil.
Proof.
  introv R E. destruct R. subst. auto.
Qed.

Lemma repr_nil_r : forall A (L:list A) l,
  repr L l -> L = nil -> l = nil.
Proof.
  introv R E. destruct R. destruct~ l as [|[w t] l].
  false. inversions Size0. simpls.
  unfold rlist_items in E. inversions H2;
   calc_list in E; simpl in E; calc_list in E; false.
Qed.


Lemma size_is_size : forall w A (t:tree A),
  size w t -> is_size w.
Proof.
  introv S. induction S. 
  exists~ 1.
  destruct IHS1 as (n'&P&E). exists (n'+1).
  subst n. split~. skip. (*math*)
Qed.

Lemma ordered_inv_size : forall b w ws,
  ordered b (w::ws) -> is_size w.
Proof. introv O. inversions~ O. Qed.

Lemma is_size_intro : forall n w,
  w = 2 ^ n - 1 -> n > 0 -> is_size w.
Proof. intros. exists~ n. Qed.

Lemma is_size_next : forall w,
  is_size w -> is_size (2*w+1).
Proof. introv (n&P&E). exists (n+1). subst. split~.
       skip. (* math *) Qed.
Hint Resolve is_size_next.

Lemma is_size_one : is_size 1.
Proof. intros. exists~ 1. Qed.
Hint Resolve is_size_one.


Section Skew.
Hint Constructors ordered. 
Hint Unfold skew.

(*
Lemma ordered_strenghten : forall ws,
  ordered false ws -> ordered true ws.
Proof. introv S. inversions~ S. Qed.
*)

Lemma skew_tail : forall w ws,
  skew (w::ws) -> skew ws.
Proof.
  introv S. inverts S as S.
  auto.
  inversions~ S. (* ordered strengthen *)
  inversions~ S.
Qed.

Lemma skewed_tail : forall A wt (l:rlist A),
  skewed (wt::l) -> skewed l.
Proof.
  unfolds skewed. intros. calc_list in *.
  apply* skew_tail. 
Qed.

Axiom pow2_lt : forall n m, 
  n < m -> 2 ^ n < 2 ^ m.

Lemma skew_one : forall w1 w2 ws,
  skew (w1::w2::ws) ->
  w1 <> w2 ->
  skew (1::w1::w2::ws).
Proof.
  introv S D. inverts S as S.
    false~ D.
    lets (n&Pn&En): H5. testsb: (n == 1).
      subst w1. apply~ ordered_same.
      apply~ ordered_cons.
      forwards~: (pow2_lt 1 n). simpl in H.
       unfold Zpower_pos in H. simpl in H. math.
Qed.

Lemma skew_add : forall w ws,
  skew (w::w::ws) ->  
  skew ((2*w+1)::ws).
Proof. 
  introv S. inverts S as S.
  inverts S as S.
    constructor~.
    lets I: (ordered_inv_size S).
    lets (n&P&E): H6. lets (n'&P'&E'): I.
     testsb:(n+1 == n').
       skip_rewrite (2*w+1 = w2). apply~ ordered_same.
       apply~ ordered_cons. 
         skip: (n+1 < n').
         skip: (2^n <= 4 * 2^n').
         skip. (* math *)
  false. math.   
Qed.

(*
Lemma skewed_one : forall A (x:A) l,
  skewed l ->
  (forall 
  skewed ((1,Leaf x)::l).
*)

Lemma is_size_div2 : forall w,
  is_size w -> w > 2 -> is_size (w / 2).
Proof.
  introv (n&E&P) W. exists (n-1). split.
  testsb:(n==0). substs. false.
   testsb:(n==1). substs. false.
   math.
  subst w. skip. (* power *)
Qed.
Hint Resolve is_size_div2.

Lemma skew_div2 : forall w ws,
  skew (w :: ws) -> 
  w > 2 ->
  skew (w/2 :: w/2 :: ws).
Proof.
  introv S W. skip: (w/2 > 1). (* TODO *)
  inverts S as S.
  auto~.
  lets~: (div2_lt w).
  forwards~: (div2_lt w). 
Qed.

End Skew.

Lemma length_tree_items : forall w A (t:tree A),
  size w t ->
  length (tree_items t) = w :> int.
Proof.
  introv S. induction S; calc_list~.
Qed.

Lemma size_pos : forall w A (t:tree A),
  size w t -> w > 0.
Proof. introv S. induction~ S. Qed.


Inductive tree_sub A : tree A -> tree A -> Prop :=
  | tree_sub_node_1 : forall x t1 t2,
      tree_sub t1 (Node x t1 t2)
  | tree_sub_node_2 : forall x t1 t2,
      tree_sub t2 (Node x t1 t2).

Lemma tree_sub_wf : forall A, well_founded (@tree_sub A).
Proof.
  intros A t. induction t; constructor; intros y H; inversions~ H.
Qed.
Hint Resolve tree_sub_wf : wf.

(* ---------------------------------------------------------------------- *)
(** ** Specifications *)

Parameter ml_div_spec : Spec ml_div (x:int) (y:int) |R>>(
  y <> 0 -> R(= Zdiv x y)).
Hint Extern 1 (RegisterSpec ml_div) => Provide ml_div_spec.


Ltac xlet_intro2_simpl tt ::= 
  intro; 
  let x := get_last_hyp tt in 
  let Hx := fresh "P" x in
  intro Hx; instantiate; cbv beta in Hx.

Ltac xlet_intro2_subst tt ::= 
  let x := fresh "TEMP" in let H := fresh "TEMP" in
  intros x H; instantiate; cbv beta in H; substs x.



Axiom lt_nat_int : forall (a b:nat),
  (a < b)%I -> (a < b)%N.
Axiom ge_nat_int : forall (a b:nat),
  (a >= b)%I -> (a >= b)%N.
Axiom eq_nat_int : forall (a b:nat),
  (a = b :> int)%I -> (a = b :> nat).


Lemma Nth_eq_pos : forall (n' n:nat) A (l:list A) x,
  Nth n' l x -> n = n' -> Nth n l x.
Proof. intros. subst~. Qed.



Lemma lookupTree_spec : forall A,
  Spec lookupTree (w:int) (i:int) (t:tree A) |R>> 
    size w t -> 0 <= i -> i < w ->
    R (Nth (abs i) (tree_items t)).
Proof.
  Hint Constructors Nth tree_sub.
  intros. xinduction (unproj33 int int (@tree_sub A)).
  xcf. introv IH S Ge Lt. xcase.
  xgo. simple~. math.
  inversions S. xlets n. xapp. auto~. subst. rewrite~ div2_odd. xcase.
    xgo. rewriteb H0. simple~.
    xgo~. simpl. rewrite~ (@abs_spos i). apply~ Nth_next.
     apply~ Nth_app_l. apply lt_nat_int. rewrite~ abs_pos. 
     rewrite~ (@length_tree_items n).
    xgo~. simpl. rewrite~ (@abs_spos i). apply~ Nth_next.
     apply~ Nth_app_r. apply ge_nat_int. rewrite~ abs_pos. 
     rewrite~ (@length_tree_items n).
     lets: (length_tree_items H2).
     applys Nth_eq_pos Px0. skip. (*math *)
  xgo. inversions S. applys* C. applys* C0.
Qed.


Hint Extern 1 (RegisterSpec lookupTree) => Provide lookupTree_spec.


Lemma lookup_spec : forall A,
  Spec lookup (i:int) (l:rlist A) |R>>
    forall L, repr L l -> 0 <= i -> i < length l->
    R (Nth (abs i) L).
Proof.
  intros. xinduction (unproj22 int (@list_sub (int*tree A))).
  xcf. introv IH R Ge Lt. xcase.
  applys_to R repr_nil_l. math.
  destruct R as [I S K]. inverts S as M S.
   unfolds rlist_items. calc_list in I.
   xcase.
  (* call to lookupTree *)
  xapp~. subst L. apply~ Nth_app_l.
   apply lt_nat_int. rewrite (length_tree_items S). rewrite~ abs_pos.
  (* call to lookup *)
  applys_to K skewed_tail.
  match type of I with _ = _ ++ ?Lp => set (L' := Lp) in * end.
  asserts R: (repr L' ts). constructor~. 
  xapp.
    auto.
    apply R.
    math.
    calc_length in Lt. lets~: (size_pos S).
  subst L. apply Nth_app_r.
    apply ge_nat_int. rewrite (length_tree_items S). rewrite~ abs_pos.
    math_rewrite~ ((abs i - length (tree_items t))%nat = abs (i-w):> nat).
      apply eq_nat_int. lets: (length_tree_items S). skip. (* math *) 
Qed.

Lemma empty_spec : forall A,
  repr (@nil A) (@empty _). (* todo: maximal arg for empty *)
Proof. Admitted.

Lemma isEmpty_spec : forall A,
  Spec isEmpty (l:rlist A) |R>>
    forall L, repr L l -> R (fun b:bool => b <-> L = nil).
Proof.
  xcf. intros l L R. xgo.
  split~. intros _. apply* repr_nil_l.
  split; intros; false.  applys C. apply* repr_nil_r.
Qed.

Lemma cons_spec : forall A,
  Spec cons_ (x:A) (l:rlist A) |R>>
    forall L, repr L l -> R (repr (x::L)).
Proof.
  Hint Constructors ordered.
  Hint Unfold skew. 
  xcf. introv [I S K]. xgo. 
  constructor.
    unfolds rlist_items. calc_list in *. fequals.
    inverts S as S S1. inverts S as S S2. rewriteb C in S1.
     asserts_rewrite~ ((1 + w2)%I + w2 = 2*w2+1).   
    unfolds skewed. calc_list in *. rewriteb C in K.
     asserts_rewrite~ ((1 + w2)%I + w2 = 2*w2+1).   
     unfold fst in *. apply~ skew_add.
  constructor.
    inversions~ I.
    auto.
    unfolds skewed. calc_list in *. simpls. 
     inverts S as _ S1. apply~ skew_one.
  constructor.
    inversions~ I.
    auto.  
    unfolds skewed. destruct ts as [|[w a] ts]; calc_list. 
      auto~.
      destruct ts as [|[w' a'] ts]; calc_list.
        inversions S. simpl.
         lets: (size_pos H3). lets:(size_is_size H3).
         testsb:(w==1); constructor~.
        false* C. 
Qed.

Lemma head_spec : forall A,
  Spec head (l:rlist A) |R>>
    forall x L, repr (x::L) l -> R (= x). 
Proof.
  xcf. introv R. xgo.
  false (repr_nil_l R). auto.
  destruct R. unfolds rlist_items. calc_list in Item0. inversions~ Item0.
  destruct R. unfolds rlist_items. calc_list in Item0. inversions~ Item0.
  destruct R. destruct _p as [|[w [a|a t1 t2]] l]. 
    applys~ C.
    inversions Size0. inversions H2. applys* C0.
    applys* C1.
Qed.



Lemma tail_spec : forall A,
  Spec tail (l:rlist A) |R>>
    forall x L, repr (x::L) l -> R (repr L). 
Proof.
  xcf. introv R. xgo~.
  false (repr_nil_l R). auto.
  destruct R as [I S K]. constructor.
   unfold rlist_items in I. calc_list in I. inversions~ I.
   inversions~ S.
   apply* skew_tail.
  destruct R as [I S K]. constructor.
   unfold rlist_items in I. calc_list in I. inversions~ I.
   substs. inverts S as S M. inverts M. rewrite~ div2_odd.
   substs. unfolds skewed. calc_list in *. simpls.
    inversions S. inversions H3. (* todo: invert should protect goal *)
    applys~ skew_div2 K. forwards: (@size_pos n). eauto. math.
  (* todo: factoriser copier-coller *)
  destruct R. destruct _p as [|[w [a|a t1 t2]] l]. 
    applys~ C.
    inversions Size0. inversions H2. applys* C0.
    applys* C1.
Qed.












