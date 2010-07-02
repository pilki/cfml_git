Set Implicit Arguments.
(* Require Import FuncTactics.*)
Require Import LibCore.
Require Import CFPrim.
Require Import test_ml.

Opaque heap_is_empty hdata heap_is_single heap_is_empty_st RefOn.



(********************************************************)
(* references *)

Lemma decr_spec : Spec decr x |R>> 
  forall m, R (x ~> RefOn m) (# x ~> RefOn (m-1)).
Proof.
  xcf. intros.
  xapp. intro_subst.
  xapp. hsimpl. 
Qed.


Hint Extern 1 (RegisterSpec decr) => Provide decr_spec.



(********************************************************)
(* advanced applications *)

(** [get_tail E] is a tactic that decomposes an application
    term [E], ie, when applied to a term of the form [X1 ... XN] 
    it returns a pair made of [X1 .. X(N-1)] and [XN]. *)

Ltac get_tail E :=
  match E with
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X => constr:((X1 X2 X3 X4 X5 X6,X))
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X => constr:((X1 X2 X3 X4 X5,X))
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X => constr:((X1 X2 X3 X4,X))  
  | ?X1 ?X2 ?X3 ?X4 ?X => constr:((X1 X2 X3,X))
  | ?X1 ?X2 ?X3 ?X => constr:((X1 X2,X)) 
  | ?X1 ?X2 ?X => constr:((X1,X))
  | ?X1 ?X => constr:((X1,X))
  end.

Ltac post_is_meta tt :=
  match goal with |- ?E => 
  match get_tail E with (_,?Q) =>
  match Q with
  | Q => constr:(false) 
  | _ => constr:(true)
  end end end.

Ltac xif_post H :=
   calc_partial_eq tt;
   try fold_bool; fold_prop;
   try fix_bool_of_known tt;
   try solve [ discriminate | false; congruence ];
   first [ subst_hyp H; try fold_bool; try rewriteb H 
         | rewriteb H
         | idtac ];
   try fix_bool_of_known tt. 

Ltac xif_core_nometa H cont :=
  apply local_erase; split; intros H; cont tt.

Ltac xif_core_meta H cont :=
  xif_core_nometa H cont.

Ltac xif_base H cont :=
  match post_is_meta tt with
  | false => xif_core_nometa H cont
  | true => xif_core_meta H cont
  end. 

Ltac xif_base_with_post H :=
  xif_base H ltac:(fun _ => xif_post H).

Tactic Notation "xif_manual" ident(H) :=
  xif_base H ltac:(fun _ => idtac).
Tactic Notation "xif_manual" :=
  let H := fresh "C" in xif_manual H.
Tactic Notation "xif" ident(H) :=
  xif_base_with_post H.
Tactic Notation "xif" :=
  let H := fresh "C" in xif H.


Ltac idcont tt := idtac.

Ltac xok_core cont := 
  solve [ apply rel_le_refl
        | apply pred_le_refl
        | hextract; hsimpl; cont tt ].

Tactic Notation "xok" := 
  xok_core ltac:(idcont).
Tactic Notation "xok" "~" := 
  xok_core ltac:(fun _ => auto~).
Tactic Notation "xok" "*" := 
  xok_core ltac:(fun _ => auto*).

Ltac xauto_common cont ::=
  check_not_a_tag tt;  
  try solve [ cont tt 
            | solve [ apply refl_equal ]
            | xok_core ltac:(fun _ => solve [ cont tt | substs; cont tt ] ) 
            | substs; if_eq; solve [ cont tt | apply refl_equal ]  ].


Lemma decr_pos_spec : Spec decr_pos x |R>> 
  forall m, m > 0 -> R (x ~> RefOn m) (# x ~> RefOn (m-1)).
Proof.
  xcf. intros.
  xapp. intro_subst.
  xif. 
  xapp. 
  xok. 
Qed.

Hint Extern 1 (RegisterSpec decr_pos) => Provide decr_pos_spec.

Lemma local_wframe' : forall B H1 H2 Q1 (F:~~B) H Q,
  is_local F -> 
  H ==> H1 \* H2 -> 
  F H1 Q1 -> 
  Q1 \*+ H2 ===> Q ->
  F H Q.
Proof. intros. apply* local_wframe. Qed.

Ltac xapp_final HR :=
  eapply local_wframe; 
     [ xlocal
     | apply HR
     | hsimpl
     | try xok ].

Ltac xapp_inst args solver ::=
  let R := fresh "R" in let LR := fresh "L" R in 
  let KR := fresh "K" R in let IR := fresh "I" R in
  intros R LR KR; hnf in KR; (* lazy beta in *)
  let H := xapp_compact KR args in
  forwards_then H ltac:(fun HR => xapp_final HR);    
  solver tt.

Ltac xapp_spec_core H cont ::=
   let arity_goal := spec_goal_arity tt in
   let arity_hyp := spec_term_arity H in
   match constr:(arity_goal, arity_hyp) with (?n,?n) => idtac | _ => fail 1 end;
   let lemma := get_spec_elim_x_y arity_hyp arity_goal in
   eapply lemma; [ apply H | cont tt ]. 

Ltac xapp_manual_intros tt ::=
  let R := fresh "R" in let LR := fresh "L" R in 
  let KR := fresh "K" R in intros R LR KR; lazy beta in KR.


Tactic Notation "xapp_manual_no_intros" := 
  xapp_then ___ ltac:(idcont).


Lemma hsimpl_cancel_eq_1 : forall H H' HA HR HT,
  H = H' -> HT ==> HA \* HR -> H \* HT ==> HA \* (H' \* HR).
Proof. intros. subst. apply~ hsimpl_cancel_1. Qed.

Lemma hsimpl_cancel_eq_2 : forall H H' HA HR H1 HT,
  H = H' -> H1 \* HT ==> HA \* HR -> H1 \* H \* HT ==> HA \* (H' \* HR).
Proof. intros. subst. apply~ hsimpl_cancel_2. Qed.

Lemma hsimpl_cancel_eq_3 : forall H H' HA HR H1 H2 HT,
  H = H' -> H1 \* H2 \* HT ==> HA \* HR -> H1 \* H2 \* H \* HT ==> HA \* (H' \* HR).
Proof. intros. subst. apply~ hsimpl_cancel_3. Qed.

Lemma hsimpl_cancel_eq_4 : forall H H' HA HR H1 H2 H3 HT,
  H = H' -> H1 \* H2 \* H3 \* HT ==> HA \* HR -> H1 \* H2 \* H3 \* H \* HT ==> HA \* (H' \* HR).
Proof. intros. subst. apply~ hsimpl_cancel_4. Qed.

Lemma hsimpl_cancel_eq_5 : forall H H' HA HR H1 H2 H3 H4 HT,
  H = H' -> H1 \* H2 \* H3 \* H4 \* HT ==> HA \* HR -> H1 \* H2 \* H3 \* H4 \* H \* HT ==> HA \* (H' \* HR).
Proof. intros. subst. apply~ hsimpl_cancel_5. Qed.

Lemma hsimpl_cancel_eq_6 : forall H H' HA HR H1 H2 H3 H4 H5 HT,
  H = H' -> H1 \* H2 \* H3 \* H4 \* H5 \* HT ==> HA \* HR -> H1 \* H2 \* H3 \* H4 \* H5 \* H \* HT ==> HA \* (H' \* HR).
Proof. intros. subst. apply~ hsimpl_cancel_6. Qed.

Ltac hsimpl_find_data H HL ::=
  match H with hdata _ ?l =>
  match HL with
  | hdata _ l \* _ => apply hsimpl_cancel_eq_1
  | _ \* hdata _ l \* _ => apply hsimpl_cancel_eq_2
  | _ \* _ \* hdata _ l \* _ => apply hsimpl_cancel_eq_3
  | _ \* _ \* _ \* hdata _ l \* _ => apply hsimpl_cancel_eq_4
  | _ \* _ \* _ \* _ \* hdata _ l \* _ => apply hsimpl_cancel_eq_5
  | _ \* _ \* _ \* _ \* _ \* hdata _ l \* _ => apply hsimpl_cancel_eq_6
  end end; [ fequal; fequal | ].

Ltac hsimpl_step tt ::=
  match goal with |- ?HL ==> ?HA \* (?H \* ?HR) =>
    first  (* hsimpl_find_same H HL |*)
          [ hsimpl_try_same tt 
          | hsimpl_find_data H HL  
          | apply hsimpl_extract_prop
          | hsimpl_extract_exists_step tt
          | apply hsimpl_keep ]
  end.

Tactic Notation "xsimpl" := try hextract; hsimpl.
Tactic Notation "xsimpl" "~" := xsimpl; xauto~.
Tactic Notation "xsimpl" "*" := xsimpl; xauto*.


Lemma decr_pos_test_spec : Spec decr_pos_test x |R>> 
  forall m, m > 1 -> R (x ~> RefOn m) (# x ~> RefOn (m-1)).
Proof.
  xcf. intros. dup 6.
  (* details of xapp *)
  eapply spec_elim_1_1. apply decr_pos_spec.
  intros R LR KR. lazy beta in KR.
  forwards_then KR ltac:(fun CR => 
    eapply local_wframe; [ xlocal | apply CR | hsimpl |  ]).
    math. xok.
  (* xapp manual *)
  xapp_manual. forwards HR: KR; [ | xapp_final HR ]. skip.
  (* xapp without arguments *)
  xapp. skip.
  (* xapp manual with arguments *)
  skip: (m = 3).
  xapp_manual. let K := xapp_compact KR (>>> 3) in
  forwards HR: K; [ | xapp_final HR ]. math. math. xsimpl*. 
  (* xapp with arguments *)
  skip: (m = 3). xapp 3. math. math. hsimpl. math.
  (* xapp with arguments and automation *)
     (* --Ltac auto_star ::= eauto with maths. *)
  skip: (m = 3). xapp* 3. math.
Qed.


(********************************************************)
(* imperative *)

Ltac check_goal_himpl tt :=
  match goal with 
  | |- @rel_le unit _ _ _ => let t := fresh "_tt" in intros t; destruct t
  | |- @rel_le _ _ _ _ => let r := fresh "r" in intros r
  | |- pred_le _ _ => idtac
  end.

Ltac hsimpl_main tt ::=
  check_goal_himpl tt;
  hsimpl_setup tt;
  (repeat (hsimpl_step tt));
  hsimpl_cleanup tt.

Ltac hextract_main tt ::=
  check_goal_himpl tt;
  hextract_setup tt;
  (repeat (hextract_step tt));
  hextract_cleanup tt.

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
  xapp. (*details of xapp: xapp_manual. forwards HR: KR. xapp_final HR. *)
  xlet.
  xapp.
  xextract as Pz.
  xgc_all. (* xgc - []. *)
  xret. hsimpl. math. (* or just [xret*] *)
Qed.
   
Opaque heap_is_star.

Lemma local_gc_post' : forall H' B (F:~~B) H Q,
  is_local F -> 
  F H (Q \*+ H') ->
  F H Q.
Proof. intros. apply* local_gc_post. Qed.

Ltac xgc_if_post_meta tt :=
  match post_is_meta tt with
  | false => xgc
  | true => idtac
  end.


Ltac xapp_pre cont ::=  (*todo:move xgc*)
  match ltac_get_tag tt with
  | tag_apply => 
    match post_is_meta tt with
    | false => xgc; [ xuntag tag_apply; cont tt | ]
    | true => xuntag tag_apply; cont tt
    end
  | tag_let_trm => xlet; [ xuntag tag_apply; cont tt | instantiate; xextract ]
  | tag_seq => xseq; [ xuntag tag_apply; cont tt | instantiate; xextract ]
  end.

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
  xapp.
  xextract as Pv.
  dup.
  (* details *)
  xseq.
  xapp.
  xgc.
  xapp.
  xsimpl.  
  math.
  (* short *)
  xapp.
  xapp. 
  xsimpl. 
  math.
Qed.
 
(*
Print imp1_cf.
Print imp2_cf.
*)



(********************************************************)
(* while loops *)

Ltac hsimpls := repeat progress (hsimpl).
(* todo: modifier hsimpl pour nommer que le dernier élément par défaut *)


Lemma decr_while_spec : Spec decr_while x |R>> 
  forall n, n >= 0 -> R (x ~> RefOn n) (# x ~> RefOn 0).
Proof.
  xcf. intros.
  xwhile (fun i:int => x ~> RefOn i \* [i >= 0]) (fun i:int => abs i). hsimpl~.
  (* todo: xwhile_cond with readonly *)
  intros i. exists (\[ bool_of (i>0)] \*+ (x ~> RefOn i \* [i >= 0])). (* todo: optimize read_only *)
  splits (3%nat).
  xapp. intro_subst. intros P. xret. hsimpl~. skip.
  xextract as M1 M2. xapp. hsimpl. skip.
  math.
  hextract. xclean. math_rewrite (i = 0). (*todo: equality generates*) hsimpl.
Qed.

(* todo: hsimpl_right *) 


(********************************************************)
(* for loops *)

Lemma sum_spec : Spec sum (n:int) |R>> n > 0 -> R [] (\= 0).
Proof.
  xcf. intros.
  xapp.
  xseq. (* xseq (x ~> RefOn 0). *)
  xfor (fun i => (x ~> RefOn (n+1-i))). 
    math_rewrite (n+1-1 = n). hsimpl. (* todo: hsimpl generates equalities!! *)
    xapp. intros _. hsimpl. math_rewrite (n + 1 - i - 1 = n + 1 - (i + 1)). auto.
  math_rewrite (n+1-(n+1) = 0).
  xgc_core. xapp. hsimpl.
Qed.






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