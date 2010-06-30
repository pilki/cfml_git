Set Implicit Arguments.
(* Require Import FuncTactics.*)
Require Import LibCore.
Require Import CFPrim.
Require Import test_ml.

Opaque heap_is_empty hdata heap_is_single heap_is_empty_st RefOn.

Tactic Notation "xextract" := 
  simpl; hclean. (* ou unfold starpost *)

Tactic Notation "xret" := 
  let r := fresh "r" in
  xret_pre ltac:(fun _ => xret_core; xclean; intros r).
Tactic Notation "xret" "as" := 
  xret_pre ltac:(fun _ => xret_core; xclean).
Tactic Notation "xret" "as" ident(r) := 
  xret_pre ltac:(fun _ => xret_core; xclean; intros r).

Lemma hsimpl_prop_1 : forall (P1:Prop),
  P1 -> [] ==> [P1].
Proof. introv H K. (*surprenant: destruct K.*)
  skip. (* todo *)
Qed.


Notation "'For' i '=' a 'To' b 'Do' Q1 'Done'" :=
  (!For (fun H Q => (a > (b)%Z -> H ==> (Q tt)) /\ (a <= (b)%Z -> exists I,
     H ==> I a /\ (forall i, a <= i /\ i <= (b)%Z -> Q1 (I i) (# I(i+1))) /\ (I ((b)%Z+1) ==> Q tt))))
  (at level 69, i ident) : charac.

Notation "'While' Q1 'Do' Q2 'Done'" :=
  (!While (fun H Q => exists A, exists I, exists R,
       wf R 
     /\ (exists x, H ==> I x)
     /\ (forall x, exists Q', 
            Q1 (I x) Q'
         /\ Q2 (Q' true) (# Hexists y, (I y) \* [R y x])
         /\ (Q' false ==> Q tt))))
  (at level 69) : charac.

Notation "Q1 ;; Q2" :=
  (!Seq fun H Q => exists H', Q1 H (#H') /\ Q2 H' Q)
  (at level 68, right associativity) : charac.

Tactic Notation "xseq" constr(H) :=
  xlet_def (fun _ => exists H) (fun _ => idtac) (fun _ => try xextract).
Tactic Notation "xseq" :=
  xlet_def (fun _ => esplit) (fun _ => idtac) (fun _ => idtac).

Notation "'Ret' v" :=
  (!R (fun H Q => H ==> Q v))
  (at level 69) : charac.


(** Full garbage collection on postcondition from [local] 

Lemma local_gc_post_all : forall B Q (F:~~B) H HG (P:B->Prop),
  is_local F -> 
  Q ===> \[P] \*+ HG ->
  F H Q ->
  F H (\[P]).
Proof. intros. apply* local_gc_post. Qed.

Tactic Notation "xgc_post_all" := 
  eapply local_gc_pre with (H' := H);
    [ try xlocal
    | hsimpl
    | ].

*)


Lemma local_gc_pre_all : forall B Q (F:~~B) H,
  is_local F -> 
  F [] Q ->
  F H Q.
Proof. intros. apply* (@local_gc_pre H). hsimpl. Qed.

Tactic Notation "xgc_all" := 
  eapply local_gc_pre_all; [ try xlocal | ].

Lemma xret_gc_lemma : forall HG B (v:B) H (Q:B->hprop),
  H ==> Q v \* HG -> 
  local (fun H' Q' => H' ==> Q' v) H Q.
Proof.  
  introv W. eapply (@local_gc_pre HG).
  auto. rewrite star_comm. apply W.
  apply~ local_erase.
Qed.

Lemma xret_lemma : forall B (v:B) H (Q:B->hprop),
  H ==> Q v -> 
  local (fun H' Q' => H' ==> Q' v) H Q.
Proof.  
  introv W. apply~ local_erase.
Qed.

Ltac xret_gc :=
  eapply xret_gc_lemma.

Ltac xret_core :=
  apply xret_lemma.

Tactic Notation "xret" := 
  xret_pre ltac:(fun _ => xret_core; xclean).


Ltac xfor_bounds_intro tt :=
  intro; let i := get_last_hyp tt in
  let Hli := fresh "Hl" i in
  let Hui := fresh "Hu" i in
  intros [Hli Hui].

Ltac xfor_core I := (* todo: add xframe *)
  let Hi := fresh "Hfor" in
  apply local_erase; split;
  [ intros Hfor 
  |  intros Hfor; exists (I:int->hprop); splits (3%nat); 
     [ (* todo : hsimpl *)
     | xfor_bounds_intro tt
     | (* todo: hsimpl *) ] 
  ].



(********************************************************)
(* while loops *)

Lemma decr_while_spec : Spec decr_while x |R>> 
  forall n, n >= 0 -> R (x ~> RefOn n) (# x ~> RefOn 0).
Proof.
  xcf.



(********************************************************)
(* for loops *)

Lemma decr_spec : Spec decr x |R>> 
  forall n, R (x ~> RefOn n) (# x ~> RefOn (n-1)).
Proof.
  xcf. intros.
  xlet. xapp. xextract. intro_subst.
  xapp. intros _. hsimpl.
Qed.

Hint Extern 1 (RegisterSpec decr) => Provide decr_spec.

Lemma sum_spec : Spec sum (n:int) |R>> n > 0 -> R [] (\= 0).
Proof.
  xcf. intros.
  xapp. xextract.
  xseq (x ~> RefOn 0).
  xfor_core (fun i => (x ~> RefOn (n+1-i))). math.
    math_rewrite (n+1-1 = n). hsimpl.
    xapp. intros _. hsimpl. math_rewrite (n + 1 - i - 1 = n + 1 - (i + 1)). auto.
    math_rewrite (n+1-(n+1) = 0). auto.
  xapp. xextract. intros.
  xgc_all. xret.
  (*  hsimpl. *) skip_cuts (r = 0). 
  auto. 
Qed.


  (* details of xfor:
  apply local_erase. split; intros M. math.
  exists ((fun i => (x ~> RefOn (n+1-i))) : int -> hprop). splits (3%nat).  (*todo splits*)
    math_rewrite (n+1-1 = n). hsimpl.
    intros i Hi. xapp. intros _. hsimpl. math_rewrite (n + 1 - i - 1 = n + 1 - (i + 1)). auto.
    math_rewrite (n+1-(n+1) = 0). auto.
  *)



(********************************************************)
(* imperative *)



Lemma imp1_spec : Specs imp1 () >> [] (\=7).
Proof.
  xcf.
  xlet.
  xapp.
  xextract.
  xlet.
  xapp.
  xextract.
  intros Py.
  xseq.
  xapp.
  xextract.
  xlet.
  xapp.
  xextract. 
  intros Pz.
  xgc - [].
  xret.
  apply heap_extract_prop. intros Pr.
  apply hsimpl_prop_1. math.
Qed.
   
Opaque heap_is_star.

Tactic Notation "xgc_post" :=
  eapply local_gc_post; [ xlocal | | ].


Lemma imp2_spec : Specs imp2 () >> [] (\=5).
Proof.
  xcf.
  xlet.
  xapp.
  xextract.
  xlet as u.
  xapp.
  xextract.
  intros Pu.
  xlet.
  xapp.
  xextract.
  xlet as v.
  (* details de xapp *)
  eapply local_wframe.
    xlocal.
    eapply spec_elim_1_1. apply ml_get_spec.
    intros R LR KR. simpl in KR. sapply KR.
    hsimpl.
    xok.
    simpl.
  xextract. 
  intros Pv.
  xseq.
  xapp.
  xextract.
  xgc_post.
  xapp.
  intros m.
  hsimpl.
  skip. (*htactics*)
Admitted.
    




  (* détails de xapp
  xapp_manual. applys KR. hsimpl.

  xfind ml_ref; let H := fresh in intro H.
  lets K: spec_elim_1_1.
  xapp_manual as.
  xapp_inst (>>>) ltac:(fun _ => eauto).
  hsimpl.
  *)



  

Ltac xapp_compact KR args :=
  let args := ltac_args args in
  match args with (boxer ?mode)::?vs => 
  let args := constr:((boxer mode)::(boxer KR)::vs) in
  constr:(args)
  end.

Ltac xapp_inst args solver :=
  let R := fresh "R" in let LR := fresh "L" R in 
  let KR := fresh "K" R in let IR := fresh "I" R in
  intros R LR KR;
  let H := xapp_compact KR args in
  forwards IR: H; solver tt; try sapply IR. 



  eapply local_wframe.
     [ try xlocal
     | eapply K; [ apply H | idtac ] 
     | hsimpl 
     | xok ].
  xapp_inst (>>>) ltac:(fun _ => eauto).
  
  eapply local_wframe; 
     [ xlocal
     | eapply K; [ apply H | idtac ] 
     | hsimpl 
     | xok ].
  xapp_inst (>>>) ltac:(fun _ => eauto).
  intros R LR KR.
   forwards IR: (>>> KR); eauto; try sapply IR. hsimpl.






xapp_manual.

Qed.



(*
Print imp1_cf.
Print imp2_cf.
*)



(********************************************************)
(* or patterns *)

(*
Open Scope comp_scope.

Lemma f_spec : Spec f (x:option int * option int) |R>> R(fun a:int => a=a).
Proof.
  xcf. intros. xmatch. (*todo tactics*)
  skip.
Qed.




(********************************************************)
(* test polymorphic recursion *)

Fixpoint tree_depth (A:Type) (t:tree A) :=
  match t with
  | Leaf _ => 1
  | Node t' => 1 + tree_depth t'
  end.

Fixpoint tree_size (A:Type) (t:tree A) : nat :=
  match t with
  | Leaf _ => 1%nat
  | Node t' => (2 * (tree_size t'))%nat
  end.

Lemma tree_size_pos : forall A (t:tree A),
  tree_size t > 0.
Proof. induction t; simpl; math. Qed.
  

Lemma depth_spec : 
  forall A, Total depth (t:tree A) >> (= tree_depth t).
Proof.
  intros. apply spec_intro_1. xisspec. split. intros t.
  sets_eq k: (tree_size t). gen A.
  induction k using peano_induction. intros.
  xcf_app; eauto. xisspec.
  xmatch.
    xret~.
    xlets. xapp~. forwards: (tree_size_pos x). simpls. math.
     xret~.
Qed.
  
Lemma depth_aux_spec : 
  forall A, Total depth_aux (n:int) (t:tree A) >> (= n + tree_depth t).
Proof.
  intros. apply spec_intro_2. xisspec.
  apply (@curried_prove_2 int (tree A) int). xcf; eauto. xisspec.
    (*todo: improve*)
  intros n t.
  sets_eq k: (tree_size t). gen n A.
  induction k using peano_induction. intros.
  xcf_app; eauto. xisspec.
  xmatch.
    xret~.
    xlets. xret~. xapp~. forwards: (tree_size_pos x). simpls. math. 
     change (tree_depth (Node x)) with (1 + tree_depth x). math.
Qed.
  


(********************************************************)
(* test functors *)

Module Type OrderedSpec.
Declare Module O : Ordered.
Import O.
Parameter R : t -> t -> Prop.
Parameter R_order : order _ R.
Parameter compare_spec : Total lt (x:t) (y:t) >>
  (fun b => isTrue b <-> R x y).  
End OrderedSpec.

Module Type FsetSpec.
Declare Module F : Fset.
Import F.
Parameter empty_not_add : 
  Total add (x:elt) (e:t) >> 
    (fun e' => e' <> empty).
End FsetSpec.

Module OrderedNatSpec 
  <: OrderedSpec with Module O := OrderedNat.
Module Import O := OrderedNat.
Definition R (x y : t) := (x < y : Prop).
Axiom R_order : order _ R.
Lemma compare_spec : Total lt (x:t) (y:t) >>
  (fun b => isTrue b <-> R x y).  
Proof. xgo. unfold R. auto*. Qed.
End OrderedNatSpec.

Module FsetListSpec (O:Ordered) (OS:OrderedSpec with Module O:=O) 
  (*: FSetSpec with Module F := FSetList O. -- why fails? *)
   <: FsetSpec.  
Module Import F <: Fset := FsetList O.
Lemma empty_is_nil : empty = nil.
Proof. xcf. xret~. Qed.
Lemma empty_not_add : 
  Total add (x:elt) (e:t) >> 
    (fun e' => e' <> empty).
Proof. xgo. rewrite empty_is_nil. intros H. inversion H. Qed.
End FsetListSpec.

(* Recall: Module FsetListNat <: Fset := FsetList OrderedNat. *)

Module FSetNatSpec  
  : FsetSpec with Definition F.elt := int  
  := FsetListSpec OrderedNat OrderedNatSpec.


(* pkoi ça marche pas ?
Module FSetNatSpec' : FsetSpec with Module F := FsetListNat  
  := FsetListSpec OrderedNat OrderedNatSpec.
*)



(********************************************************)
(* test patterns *)

Check length_cf.

Check unsome_cf.

Check testmatch_cf.

Check myfst_cf.

Lemma x_spec : x = (5,2).
Proof.
  dup 3.
  xcf. xgo. auto.
  xcf. xmatch. xalias. xret. auto.
  xcf. xmatchs. xcase. xalias. xret. auto.
Qed.

Lemma y_spec : y = (2,4).
Proof.
  xcf. xgo. auto.
Qed.

Check tail_cf.



(********************************************************)
(* test basic *)

Lemma id_spec : forall A,
  Total id (x:A) >> (=x).
Proof.
  xcf. xgo. auto.
Qed.

Check crash_cf.

Check select21_cf.

Check test_cf.

Check myplus_cf.

Check testlet_cf.

Check testnolet_cf.

Check asserts_cf.
(*todo: 
  let bindant valeurs polymorphes autres que fonctions *)


(********************************************************)
(* test functors *)


*)