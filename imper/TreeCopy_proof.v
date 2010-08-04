Set Implicit Arguments.
Require Import LibCore CFPrim TreeCopy_ml.


(*****************)

(** Tup3 *)

Definition Tup3 A1 A2 A3 a1 a2 a3 (T1:A1->a1->hprop) (T2:A2->a2->hprop) (T3:A3->a3->hprop) P p :=
  let '(X1,X2,X3) := P in let '(x1,x2,x3) := p in x1 ~> T1 X1 \* x2 ~> T2 X2 \* x3 ~> T3 X3.

Lemma focus_tup3 : forall a1 a2 a3 (p:a1*a2*a3) A1 A2 A3 (T1:htype A1 a1) (T2:htype A2 a2) (T3:A3->a3->hprop) V1 V2 V3,
  p ~> Tup3 T1 T2 T3 (V1,V2,V3) ==> let '(x1,x2,x3) := p in x1 ~> T1 V1 \* x2 ~> T2 V2 \* x3 ~> T3 V3.
Proof. auto. Qed.

Lemma unfocus_tup3 : forall a1 (x1:a1) a2 (x2:a2) a3 (x3:a3) A1 A2 A3 (T1:htype A1 a1) (T2:htype A2 a2) (T3:A3->a3->hprop) V1 V2 V3,
  x1 ~> T1 V1 \* x2 ~> T2 V2 \* x3 ~> T3 V3 ==> (x1,x2,x3) ~> Tup3 T1 T2 T3 (V1,V2,V3).
Proof. intros. unfold Tup3. hdata_simpl. auto. Qed.

Opaque Tup3.

(** Rec3 *)

Definition Rec3 A1 A2 A3 a1 a2 a3 (T1:A1->a1->hprop) (T2:A2->a2->hprop) (T3:A3->a3->hprop) P l :=
  l ~> Ref (Tup3 T1 T2 T3) P.

Lemma focus_rec3 : forall (l:loc) a1 a2 a3 A1 A2 A3 (T1:htype A1 a1) (T2:htype A2 a2) (T3:A3->a3->hprop) V1 V2 V3,
  l ~> Rec3 T1 T2 T3 (V1,V2,V3) ==> Hexists (x1:a1) (x2:a2) (x3:a3),
  l ~> Ref Id (x1,x2,x3) \* x1 ~> T1 V1 \* x2 ~> T2 V2 \* x3 ~> T3 V3.
Proof.
  intros. unfold Rec3. hdata_simpl. hchange (@focus_ref l). hextract as. 
  intros p [[x1 x2] x3] H. hchange (focus_tup3 p). destruct p as [[y1 y2] y3].
  inversions H. hsimpl~. 
Qed.

Lemma unfocus_rec3 : forall (l:loc) a1 (x1:a1) a2 (x2:a2) a3 (x3:a3) A1 A2 A3 (T1:htype A1 a1) (T2:htype A2 a2) (T3:A3->a3->hprop) V1 V2 V3,
  l ~> Ref Id (x1,x2,x3) \* x1 ~> T1 V1 \* x2 ~> T2 V2 \* x3 ~> T3 V3 ==>
  l ~> Rec3 T1 T2 T3 (V1,V2,V3).
Proof.
  intros. unfold Rec3. hdata_simpl. hchange (unfocus_tup3 x1 x2 x3). 
  hchange (@unfocus_ref l _ (x1,x2,x3)). hsimpl.
Qed.

Opaque Rec3.


(** Rec3 *)

Definition Ref3 A1 A2 A3 a1 a2 a3 (T1:A1->a1->hprop) (T2:A2->a2->hprop) (T3:A3->a3->hprop) (V1:A1) (V2:A2) (V3:A3) l :=
  l ~> Ref (Tup3 T1 T2 T3) (V1,V2,V3).

Lemma focus_ref3 : forall (l:loc) a1 a2 a3 A1 A2 A3 (T1:htype A1 a1) (T2:htype A2 a2) (T3:A3->a3->hprop) V1 V2 V3,
  l ~> Ref3 T1 T2 T3 V1 V2 V3 ==> Hexists (x1:a1) (x2:a2) (x3:a3),
  l ~> Ref Id (x1,x2,x3) \* x1 ~> T1 V1 \* x2 ~> T2 V2 \* x3 ~> T3 V3.
Proof.
  intros. unfold Ref3. hdata_simpl. hchange (@focus_ref l). hextract as. 
  intros p [[x1 x2] x3] H. hchange (focus_tup3 p). destruct p as [[y1 y2] y3].
  inversions H. hsimpl~. 
Qed.

Lemma unfocus_ref3 : forall (l:loc) a1 (x1:a1) a2 (x2:a2) a3 (x3:a3) A1 A2 A3 (T1:htype A1 a1) (T2:htype A2 a2) (T3:A3->a3->hprop) V1 V2 V3,
  l ~> Ref Id (x1,x2,x3) \* x1 ~> T1 V1 \* x2 ~> T2 V2 \* x3 ~> T3 V3 ==>
  l ~> Ref3 T1 T2 T3 V1 V2 V3.
Proof.
  intros. unfold Ref3. hdata_simpl. hchange (unfocus_tup3 x1 x2 x3). 
  hchange (@unfocus_ref l _ (x1,x2,x3)). hsimpl.
Qed.

Opaque Ref3.


(*
Definition Hor (H1 H2 : hprop) := fun h => H1 h \/ H2 h.
*)

Inductive tree A :=
  | Leaf : tree A
  | Node : A -> tree A -> tree A -> tree A.

Implicit Arguments Leaf [[A]].

Fixpoint Tree A a (T:htype A a) (t:tree A) (l:loc) : hprop :=
  match t with
  | Leaf => [l = null]
  | Node x t1 t2 => l ~> Ref3 T (Tree T) (Tree T) x t1 t2
  end.

Fixpoint tree_set A (t:tree A) : set A :=
  match t with
  | Leaf => \{}
  | Node x t1 t2 => \{x} \u (tree_set t1) \u (tree_set t2)
  end.

Definition TreeSet A a (T:htype A a) (E:set A) (l:loc) :=
  Hexists (t:tree A), l ~> Tree T t \* [E = tree_set t].
  

Lemma focus_leaf : forall A a (T:A->a->hprop),
  [] ==> null ~> Tree T Leaf.
Proof. intros. simpl. hdata_simpl. hsimpl~. Qed.

Lemma unfocus_leaf : forall (l:loc) A a (T:A->a->hprop),
  l ~> Tree T Leaf ==> [l = null].
Proof. intros. simpl. hdata_simpl. hsimpl~. Qed.

Lemma unfocus_leaf' : forall A (t:tree A) a (T:A->a->hprop),
  null ~> Tree T t ==> [t = Leaf].
Proof.
  intros. destruct t.
  simpl. unfold hdata. xsimpl~.
  skip. (* todo: focus_ref'  
  unfold hdata, Tree. hchange (focus_ref_null). hextract. false. *)
Qed.

(* todo: qui l'a remis transparent?.  ==> fixer les preuves plus haut avec *)
Opaque Ref.

Lemma focus_node : forall (l:loc) a A (x:A) (t1 t2:tree A) (T:A->a->hprop),
  l ~> Tree T (Node x t1 t2) ==>
  Hexists (lx:a) (lt1:loc) (lt2:loc),
  l ~> Ref Id (lx,lt1,lt2) \* (lx ~> T x) \* (lt1 ~> Tree T t1) \* (lt2 ~> Tree T t2).
Proof.
  intros. simpl. hdata_simpl. hchange (@focus_ref3 l).
  hextract as x1 x2 x3. hsimpl.
Qed.

Lemma focus_node' : forall (l:loc) a A (t:tree A) (T:A->a->hprop),
  [l <> null] \* (l ~> Tree T t) ==> 
  Hexists (lx:a) (lt1:loc) (lt2:loc), Hexists (x:A) (t1:tree A) (t2:tree A),
    l ~> Ref Id (lx,lt1,lt2) \* lx ~> T x \* lt1 ~> Tree T t1 \* lt2 ~> Tree T t2. 
Proof.
  intros. destruct t.
  hextract. false. (* todo: simplifier dans focus_cons *)
  hchange (@focus_node l). hextract as lx lt1 lt2 E. hsimpl~.  
Qed.

Lemma unfocus_node : forall (l:loc) a (lx:a) (lt1 lt2:loc) A (x:A) (t1 t2:tree A) (T:A->a->hprop),
  l ~> Ref Id (lx,lt1,lt2) \* (lx ~> T x) \* (lt1 ~> Tree T t1) \* (lt2 ~> Tree T t2) ==>
  l ~> Tree T (Node x t1 t2).
Proof.
  intros. simpl. hdata_simpl. hchange (@unfocus_ref3 l _ lx _ lt1 _ lt2). hsimpl.
Qed.

Opaque Tree.

Inductive tree_sub {A} : binary (tree A) :=
  | tree_sub_1 : forall x t1 t2,
      tree_sub t1 (Node x t1 t2)
  | tree_sub_2 : forall x t1 t2,
      tree_sub t2 (Node x t1 t2).

Lemma tree_sub_wf : forall A, wf (@tree_sub A).
Proof.
  intros A t. induction t; constructor; intros t' H; inversions~ H.
Qed.

Hint Resolve tree_sub_wf : wf.


Ltac xbody_base_nointro tt ::=
  xbody_core ltac:(fun _ => remove_head_unit tt).
Tactic Notation "xfun_nointro" constr(s) :=
  xfun_core s ltac:(fun _ => first [ xbody_base_nointro tt | xfun_namebody tt ] ).

Tactic Notation "xapp" "as" simple_intropattern(x) :=
  xlet as x; [ xapp | instantiate; xextract ].

Lemma copy_tree_spec : forall a,
  Spec copy_tree (copy_elem:val) (l:mtree a) |R>> 
     forall A (T:A->a->hprop) (E:tree A),
     (Spec copy_elem (x:a) |R>> forall X,
        keep R (x ~> T X) (~> T X)) ->
     keep R (l ~> Tree T E) (~> Tree T E).
Proof.
  xcf. introv Sce. 
  xfun_nointro (fun f => Spec f (l:mtree a) |R>> forall E,
           keep R (l ~> Tree T E) (~> Tree T E)).
  skip IH: (Spec copy (l:mtree a) |R>> forall E,
           keep R (l ~> Tree T E) (~> Tree T E)).
  (* todo: induction *)
    clear t E. intros t E.
    xapp. intro_subst. xif.
    xret. hchange (unfocus_leaf' E). hextract. subst. hsimpl~.
     do 2 hchange focus_leaf. hsimpl.
    xchange~ (@focus_node' t). xextract. intros lx lt1 lt2 x t1 t2.
     xapp. intro_subst. xmatch.
     xapp as lx'. 
     xapp as lt1'.
     xapp as lt2'.
     xapp. intros r.
      hchange_debug (@unfocus_node r _ lx' lt1' lt2').

 hsimpl_setup tt.
 hsimpl_step tt.
 hsimpl_step tt.
 hsimpl_step tt.
 hsimpl_step tt.
 hsimpl_step tt.

 hsimpl_step tt.     
  xapp. hsimpl.
Qed.


(* todo: spec with TreeSet *)
(*(fun l' => l ~> Tree T E \* l' ~> Tree T E).*)





