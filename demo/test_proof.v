Set Implicit Arguments.
(* Require Import FuncTactics.*)
Require Import LibCore.
Require Import CFPrim.
Require Import test_ml.

Opaque heap_is_empty hdata heap_is_single heap_is_empty_st Ref.

Ltac xfor_base I cont1 cont2 := 
  apply local_erase; split; 
    [ cont1 tt 
    | cont2 tt; esplit; exists I; splits 3%nat; 
       [ hsimpl 
       | xfor_bounds_intro tt
       | instantiate; hsimpl ]
    ].

Ltac xfor_core_gen I H :=
  xfor_base I ltac:(fun _ => intros H)
              ltac:(fun _ => intros H).

Lemma xfor_contradict_lemma : forall (a b : int),
  (a > b) -> (a <= b) -> False.
Proof. math. Qed.

Ltac xfor_contradict tt :=
  let H := fresh "TEMP" in
  intros H; false;
  apply (xfor_contradict_lemma H); clear H.

Ltac xfor_core_le I := 
  xfor_base I ltac:(fun _ => xfor_contradict tt; try math)
              ltac:(fun _ => intros _).

Ltac xfor_pre cont :=
  match ltac_get_tag tt with
  | tag_seq => xseq; [ cont tt | ]
  | tag_for => cont tt
  end.

Ltac xfor_base_gen I H :=
  xfor_pre ltac:(fun _ => xfor_core_gen I H).

Ltac xfor_base_le I :=
  xfor_pre ltac:(fun _ => xfor_core_le I).

Tactic Notation "xfor" constr(I) := 
  xfor_base_le I.
Tactic Notation "xfor_general" constr(I) "as" ident(H) := 
  xfor_base_gen I H.
Tactic Notation "xfor_general" constr(I) := 
  let H := fresh "Hfor" in xfor_general I as H.


(********************************************************)
(* for loops *)

Lemma sum_spec : Spec sum (n:int) |R>> n > 0 -> R [] (\= 0).
Proof.
  xcf. intros.
  xapp.
  xfor (fun i => (x ~> Ref Id (n+1-i))). math.
    xapp. hsimpl. math.
  xapp. xsimpl. math.
Qed.


(********************************************************)
(* while loops *)


Ltac protect_evars_in H ::=
   match H with context [ ?X ] =>
     let go tt := 
       match X with
       | _ \* _ => fail 1
       | X => fail 1 
       | ?x ~> ?R => 
           match x with
           | x => idtac             
           | _ => fail 20 "Uninstantiated argument at left of ~>"
           end;
           let TR := type of R in
           let K := fresh "TEMP" in 
           sets_eq K: (R : ltac_tag_subst TR)
       | [ ?R ] => 
           let TR := type of R in
           let K := fresh "TEMP" in 
           sets_eq K: (R : ltac_tag_subst TR)
       | _ => let K := fresh "TEMP" in
              sets_eq K: (X : ltac_tag_subst hprop)
       end in
     match type of X with 
     | hprop => go tt
     | heap -> Prop => go tt
     end
  end.


Ltac hsimpls := repeat progress (hsimpl).
(* todo: modifier hsimpl pour nommer que le dernier élément par défaut *)

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
     first [ apply refl_equal 
           | apply bool_of_prove; 
             try (check_noevar_goal; rew_istrue) ]
  end.

Tactic Notation "xclean" :=
  calc_partial_eq tt; 
  repeat fix_bool_of_known tt;
  fold_bool; fold_prop. 

Lemma not_isTrue_istrue_forw : forall P,
  ~ isTrue (istrue P) -> ~ P.
Proof. intros P. apply contrapose_not. rewrite~ isTrue_istrue. Qed.

Lemma not_isTrue_not_istrue_forw : forall P,
  ~ isTrue (! istrue P) -> P.
Proof.
  intros P. rewrite <- (@not_not P). apply contrapose_not.
  rewrite~ isTrue_neg_istrue. 
Qed. (* todo: missing lemma from lib logic about ~A->B *)

Lemma not_isTrue_istrue_back : forall P,
  ~ P -> ~ isTrue (istrue P).
Proof. intros P. apply contrapose_not. rewrite~ isTrue_istrue. Qed.

Lemma not_isTrue_not_istrue_back : forall P:Prop,
  P -> ~ isTrue (! istrue P).
Proof. 
  intros P. rewrite <- (@not_not P). apply contrapose_not.
  rewrite~ isTrue_neg_istrue. 
Qed.


Ltac fold_prop ::= 
  repeat match goal with 
  | H: isTrue (istrue ?P) |- _ => applys_to H isTrue_istrue_forw
  | H: isTrue (! istrue ?P) |- _ => applys_to H isTrue_not_istrue_forw
  | H: ~ isTrue (istrue ?P) |- _ => applys_to H not_isTrue_istrue_forw
  | H: ~ isTrue (! istrue ?P) |- _ => applys_to H not_isTrue_not_istrue_forw
  | H: (?P = True) |- _ => applys_to H prop_eq_True_forw
  | H: (?P = False) |- _ => applys_to H prop_eq_False_forw
  | H: (True = ?P) |- _ => symmetry in H; applys_to H prop_eq_True_forw
  | H: (False = ?P) |- _ => symmetry in H; applys_to H prop_eq_False_forw
  | H: ~ (~ ?P) |- _ => applys_to H not_not_elim 
  | |- isTrue (istrue ?P) => apply isTrue_istrue_back
  | |- isTrue (! istrue ?P) => apply isTrue_not_istrue_back
  | |- ~ isTrue (istrue ?P) => apply not_isTrue_istrue_back
  | |- ~ isTrue (! istrue ?P) => apply not_isTrue_not_istrue_back
  | |- (?P = True) => apply prop_eq_True_back
  | |- (?P = False) => apply prop_eq_False_back
  | |- (True = ?P) => symmetry; apply prop_eq_True_back
  | |- (False = ?P) => symmetry; apply prop_eq_False_back
  | |- ~ (~ ?P) => apply not_not_intro
  end.



(**


Ltac xwhile_body_handle :=
  intros; eapply esplit_boolof; splits.

*)

Ltac xwhile_core I R X0 :=
  apply local_erase; esplit; esplit; exists I; 
  first [ exists R | exists (measure R) ]; splits 3%nat;
    [ prove_wf
    | instantiate; match X0 with __ => esplit | _ => exists X0 end; hsimpl
    | instantiate; intro; let X := get_last_hyp tt in xextract; revert X ].

Ltac xwhile_core_debug I R X0 :=
  apply local_erase; esplit; esplit; exists I; 
  first [ exists R | exists (measure R) ]; splits 3%nat.

Ltac xwhile_pre cont :=
  match ltac_get_tag tt with
  | tag_seq => xseq; [ cont tt | ]
  | tag_while => cont tt
  end.

Ltac xwhile_base I R X0 :=
  xwhile_pre ltac:(fun _ => xwhile_core I R X0).

Tactic Notation "xwhile" constr(I) constr(R) constr(X0) := 
  xwhile_base I R X0.
Tactic Notation "xwhile" constr(I) constr(R) := 
  xwhile_base I R __.

Ltac xcond_core P :=
   match goal with |- local _ ?H _ => 
     match P with 
     | __ => let R := fresh in evar (R:Prop); 
             apply local_erase; 
             exists (\[ bool_of R ] \*+ H);
             subst R
     | _ => apply local_erase; exists (\[ bool_of P ] \*+ H)
   end end; splits 3%nat.

Ltac xcond_base P :=
  xcond_core P; [ | try xextract | try xextract ].


Tactic Notation "xcond" constr(P) :=
  xcond_base P.
Tactic Notation "xcond" :=
  xcond_base __.



Lemma decr_while_spec : Spec decr_while x |R>> 
  forall n, n >= 0 -> R (x ~> Ref Id n) (# x ~> Ref Id 0).
Proof.
  xcf. intros.
  xwhile (fun i:int => x ~> Ref Id i \* [i >= 0]) (downto 0).
   auto. intros i Li. xcond.
     xapp. intro_subst. xret. hsimpl~. xclean.
     intros. xclean. xapp. hsimpl; auto with maths.
     xsimpl. xclean. math.
Qed.

(* details:
  xcf. intros.
  apply local_erase. esplit. esplit.
    exists (fun i:int => x ~> Ref Id i \* [i >= 0]). 
    exists (downto 0).
    splits 3%nat.
    prove_wf.
    esplit. hsimpl. auto. (* ou bien exists X *)
    intros i. 
      match goal with |- local _ ?H _ => 
        let P := fresh in evar (P:Prop); apply local_erase; exists (\[ bool_of P ] \*+ H); subst P 
        (* ou exists (\[ bool_of P ] \*+ H) *) 
      end. splits 3%nat.
      xextract. intros. xapp. intro_subst. xret. hsimpl. auto. xclean.
      xextract. intros. xapp. xclean. hsimpl; auto with maths.
  hextract. xclean. hsimpl. math. 
*)



(********************************************************)
(* arrays

Lemma arrays_spec : Spec arrays () |R>> R [] (\=3).
Proof.
  xcf.
  xlet. xapp. xextract as t Ht.
  xlet. xapp. skip. xextract as e.
  xseq. xapp. skip. xextract as t' Ht'.
  xfun (fun f => Spec f (i:int) |R>> R [] (\=i)). xret*.
  xlet. skip. 
  skip.
Admitted.

 *)


(********************************************************)
(* records test

Record
myrecord (A : Type) (B : Type) : Type := myrecord_of
{ 
 myrecord_myrecord_one : A;
myrecord_myrecord_two
: B }.

Definition test := @myrecord_of _ _ 2 3.
Print test.
{ myrecord_myrecord_one := 2; myrecord_myrecord_two := 2 }.
 *)

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