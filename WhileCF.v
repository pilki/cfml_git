Require Import LibTactics Arith Omega List.
Opaque mult. (* to prevent simpl to do too much *)


Notation "x == y" := (eq_nat_dec x y) (at level 68).

Ltac math_rewrite E :=
  let H := fresh "TEMP" in 
  assert (H:E); [ omega | rewrite H; clear H].

Ltac math_fequal := repeat fequal; try omega.



(********************************************************************)
(* ** Syntax *)

Definition loc := nat.

Inductive binop :=
  | binop_add : binop
  | binop_sub : binop
  | binop_mul : binop.

Inductive val :=
  | val_nat : nat -> val
  | val_op : binop -> val -> val -> val
  | val_read : loc -> val.

Inductive trm :=
  | trm_done : trm 
  | trm_seq : trm -> trm -> trm
  | trm_write : loc -> val -> trm
  | trm_while : val -> trm -> trm.

Definition heap := list (loc * nat).

(********************************************************************)
(* ** Semantics *)

Fixpoint heap_get (h:heap) (l:loc) : nat :=
  match h with
  | nil => 0
  | (l',n)::h' => if l == l' then n else heap_get h' l
  end.

Fixpoint heap_set (h:heap) (l:loc) (n:nat) : heap :=
  match h with
  | nil => (l,n)::nil
  | (l',n')::h' => if l == l' then (l,n)::h' else (l',n')::(heap_set h' l n)
  end.

Fixpoint eval (h:heap) (v:val) : nat :=
  match v with
  | val_nat n => n
  | val_op op v1 v2 =>
      let n1 := eval h v1 in
      let n2 := eval h v2 in
      match op with
      | binop_add => n1 + n2
      | binop_sub => n1 - n2
      | binop_mul => n1 * n2
      end
  | val_read l => heap_get h l
  end.

Inductive red : trm -> heap -> heap -> Prop :=
  | red_done : forall h,
      red trm_done h h
  | red_seq : forall h1 h2 h3 t1 t2,
      red t1 h1 h2 ->
      red t2 h2 h3 ->
      red (trm_seq t1 t2) h1 h3
  | red_write : forall l v h n,
      n = eval h v ->
      red (trm_write l v) h (heap_set h l n)
  | red_while_stop : forall h v t1,
      eval h v = 0 ->
      red (trm_while v t1) h h
  | red_while_step : forall h1 h2 h3 v t1,
      eval h1 v <> 0 ->
      red t1 h1 h2 ->
      red (trm_while v t1) h2 h3 ->
      red (trm_while v t1) h1 h3.

(********************************************************************)
(* ** Characteristic Formula *)

Definition formula := heap -> heap -> Prop.

Definition cf_done (h h':heap) := 
  h' = h.

Definition cf_seq (F1 F2:formula) (h h':heap) :=
  exists h'', F1 h h'' /\ F2 h'' h'.

Definition cf_write (l:loc) (v:val) (h h':heap) :=
  h' = heap_set h l (eval h v).

Definition cf_while (v:val) (F1:formula) (h h':heap) :=
  exists A:Type, exists P:A->Prop, 
  exists I:A->heap, exists R:A->A->Prop,
    well_founded R /\ (exists X, P X /\ h = I X) /\
    (forall X, P X -> if (eval (I X) v == 0) 
       then h' = I X
       else exists Y, P Y /\ R Y X /\ F1 (I X) (I Y)).

Fixpoint cf (t:trm) : formula :=
  match t with
  | trm_done => cf_done 
  | trm_seq t1 t2 => cf_seq (cf t1) (cf t2)
  | trm_write l v => cf_write l v 
  | trm_while v t1 => cf_while v (cf t1)
  end.
  
(********************************************************************)
(* ** Notation for formulae *)

Coercion val_nat : nat >-> val.

Notation "v1 '+ v2" := (val_op binop_add v1 v2)
  (at level 40) : cf_scope.

Notation "v1 '- v2" := (val_op binop_sub v1 v2)
  (at level 40) : cf_scope.

Notation "v1 '* v2" := (val_op binop_mul v1 v2)
  (at level 40) : cf_scope.

Notation "! l" := (val_read l)
  (at level 30) : cf_scope.

Notation "'Done'" := (cf_done)
  (at level 0) : cf_scope.

Notation "F1 ;; F2" := (cf_seq F1 F2)
  (at level 68, right associativity) : cf_scope.

Notation "l '<-' v" := (cf_write l v)
  (at level 66) : cf_scope.

Notation "'While' v 'Do' F1 'Done'" := (cf_while v F1)
  (at level 67, F1 at level 69) : cf_scope.

Open Scope cf_scope.


(********************************************************************)
(* ** Soundness proof *)

Lemma cf_sound : forall t h h',
  cf t h h' -> red t h h'.
Proof.
  induction t; intros h h' Hyp; hnf in Hyp.
  subst. apply red_done.
  destruct Hyp as (h''&H1&H2). eapply red_seq; eauto.
  subst. apply red_write. auto.
  destruct Hyp as (A&P&I&R&W&(X0&P0&I0)&IS).
   rewrite I0. generalize X0 P0. clear X0 P0 I0.
   intros X. pattern X. apply (well_founded_ind W). clear X.
   intros X IH PX. specialize (IS X PX).
   destruct (eval (I X) v == 0) as [E|E].
     rewrite IS. apply red_while_stop. auto.
     destruct IS as (Y&PY&RYX&CFY). eapply red_while_step.
       auto. eauto. apply IH. auto. auto.
Qed.
  

(********************************************************************)
(* ** Maths for the demo *)

Fixpoint fact (n:nat) : nat :=
  match n with
  | 0 => 1
  | S n' => n * (fact n')
  end.

Fixpoint prod_from (n:nat) (k:nat) : nat :=
  match k with
  | 0 => 1
  | S k' => n * prod_from (S n) k'
  end.

Lemma prod_from_cut : forall m n, m <= n ->
  fact (n-m) * prod_from (S(n-m)) m = fact n.
Proof.
  intros m n. induction m; intros Le.
  simpl. math_rewrite (n-0=n). omega.
  rewrite <- IHm; try omega.
  simpl. math_rewrite (n-m=S(n-(S m))). simpl. ring.
Qed.

Lemma prod_from_zero : forall n, n > 0 ->
  prod_from 1 n = fact n.
Proof.
  intros. destruct n. omega.
  rewrite <- (prod_from_cut n); try omega.
  math_rewrite (S n - n = 1). simpl. auto.
Qed.

Lemma prod_from_succ : forall i k,
  prod_from i (S k) = i * prod_from (S i) k.
Proof. auto. Qed.


(********************************************************************)
(* ** Demo *)

Definition var_n := 2.
Definition var_m := 3.
Notation "'N'" := (var_n) : cf_scope.
Notation "'M'" := (var_m) : cf_scope.

Notation "'[ x := n ; y := m ]" :=
  ((x,n)::(y,m)::nil)
  (x at level 0, n at level 69,
   y at level 0, m at level 69) : cf_scope.

Definition facto : trm :=
  trm_while (!N) (trm_seq (trm_write M (!N '* !M)) 
                          (trm_write N (!N '- 1))).

Definition facto_cf : formula := Eval simpl in (cf facto).

Print facto_cf.

Lemma facto_proof : forall n, n > 0 ->
  red facto '[N := n; M := 1] '[N := 0; M := fact n].
Proof.
  intros. apply cf_sound. simpl.
  (* reasoning on the loop *)
  hnf. exists nat.
       exists (fun i => i <= n).
       exists (fun i => '[N:=i; M:=prod_from (S i) (n-i)]).
       exists lt.
       split; [|split].
  apply lt_wf.
  exists n. split. 
    omega. 
    repeat fequal. math_rewrite (n-n=0). auto.
  simpl. intros i Le. destruct (i == 0).
    subst i. rewrite prod_from_zero; math_fequal.
    exists (i-1). split; [|split]; try omega. 
  (* body of the loop *)
  hnf. esplit. split.
  hnf. simpl. apply refl_equal.
  hnf. simpl. rewrite <- prod_from_succ. math_fequal.
Qed.


(********************************************************************)
(* ** Tactics *)

Ltac xcf :=
  intros; apply cf_sound; simpl.

Ltac xdone := 
  hnf.

Ltac xseq :=
  esplit; split.

Ltac xwrite :=
  hnf; simpl; try reflexivity.

Ltac xwhile P I W X0 :=
  esplit; exists P; exists I; exists W; 
  split; [|split; [exists X0; split|]].

Lemma facto_proof' : forall n, n > 0 ->
  red facto '[N := n; M := 1] '[N := 0; M := fact n].
Proof.
  xcf.
  xwhile (fun i => i <= n)
         (fun i => '[N:=i; M:=prod_from (S i) (n-i)])
         lt 
         n.  
  apply lt_wf.
  omega. 
  repeat fequal. math_rewrite (n-n=0). auto.
  (* loop *)
  simpl. intros i Le. destruct (i == 0).
    subst i. rewrite prod_from_zero; math_fequal. 
    exists (i-1). split; [|split]; try omega.
  (* body of the loop *)
  xseq.
  xwrite.
  xwrite. rewrite <- prod_from_succ. math_fequal.
Qed.

 



