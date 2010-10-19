Set Implicit Arguments.
(* Require Import FuncTactics.*)
Require Import LibCore.
Require Import CFPrim CFTactics. (* todo: group as CF *)
Require Import test_ml.

Opaque heap_is_empty hdata heap_is_single heap_is_empty_st Ref.


(********************************************************)
(* for loops *)

Lemma sum_spec : Spec sum (n:int) |R>> n > 0 -> R [] (\= 0).
Proof.
  xcf. intros.
  xapp.
  (*
xfor (fun i => (x ~> Ref Id (n+1-i))). math.
    xapp. hsimpl. math.
  xapp. xsimpl. math.
Qed.
*)
Admitted.


(********************************************************)
(* while loops *)


(*todo: sort !! *)

Lemma xpost_lemma : forall B Q' Q (F:~~B) H,
  is_local F -> 
  F H Q' -> 
  Q' ===> Q ->
  F H Q.
Proof. intros. applys* local_weaken. Qed.

Tactic Notation "xpost" :=
  eapply xpost_lemma; [ try xlocal | | ].



Notation "'While' Q1 'Do' Q2 'Done'" :=
  (!While (fun H Q => forall R:~~unit, is_local R ->
        (forall H Q, (exists Q', Q1 H Q' 
           /\ (local (fun H Q => exists Q', Q2 H Q' /\ R (Q' tt) Q) (Q' true) Q)
           /\ Q' false ==> Q tt) -> R H Q) 
        -> R H Q))
  (at level 69) : charac.


Notation "'GWhile' Q1 Q2" :=
  (!While (fun H Q => forall R:~~unit, is_local R ->
        (forall H Q, (exists Q', Q1 H Q' 
           /\ (local (fun H Q => exists Q', Q2 H Q' /\ R (Q' tt) Q) (Q' true) Q)
           /\ Q' false ==> Q tt) -> R H Q) 
        -> R H Q))
  (at level 69, only parsing, Q1 at level 0, Q2 at level 0) : charac.


Definition loop_cf' (F1:~~bool) (F2:~~unit) :=
  (fun H Q => exists A:Type, exists I:A->hprop, exists J:A->bool->hprop, exists lt:binary A,
      wf lt 
   /\ (exists X0, H ==> (I X0))
   /\ (forall X, F1 (I X) (J X)
              /\ F2 (J X true) (# Hexists Y, (I Y) \* [lt Y X])
              /\ J X false ==> Q tt)).

Definition loop_cf (F1:~~bool) (F2:~~unit) :=
  (fun (H:hprop) (Q:unit->hprop) => forall R:~~unit, is_local R ->
    (forall H Q, (exists Q', F1 H Q' 
       /\ (local (fun H Q => exists Q', F2 H Q' /\ R (Q' tt) Q) (Q' true) Q)
       /\ Q' false ==> Q tt) -> R H Q) 
    -> R H Q).

Axiom local_extract_exists : forall B (F:~~B) A (J:A->hprop) Q,
  is_local F ->
  (forall x, F (J x) Q) -> 
  F (heap_is_pack J) Q.

Lemma loop_inv : forall (F1:~~bool) (F2:~~unit),
  loop_cf' F1 F2 ===> loop_cf F1 F2.
Proof.
  intros F1 F2 H Q (A&I&J&lt&Wlt&(X0&M0)&M) R LR W.
  applys~ local_weaken M0. generalize X0.
  intros X. induction_wf IH: Wlt X.
  destruct (M X) as (M1&M2&M3).
  apply W. exists (J X). splits~.
  apply local_erase. esplit. split. apply M2.
  apply~ local_extract_exists. intros x.
  rewrite star_comm. apply~ CFHeaps.local_intro_prop.
Qed.


Ltac xwhile_core_inner I J R X0 cont1 cont2 cont3 ::=
  esplit; esplit; exists I; exists J;
  first [ exists R | exists (measure R) ]; splits 3%nat;
  [ cont1 tt 
  | match X0 with __ => esplit | _ => exists X0 end; cont2 tt 
  | cont3 tt ].
Ltac xwhile_pre cont ::= cont tt.

Lemma decr_while_spec : Spec decr_while x |R>> 
  forall n, n >= 0 -> R (x ~> Ref Id n) (# x ~> Ref Id 0).
Proof.
  xcf. introv Le. dup.
  (* details *)
  apply local_erase. intros R LR HR.
  gen Le. induction_wf IH: (int_downto_wf 0) n. intros Le.
  apply HR; clear HR. esplit. splits 3%nat.
  xapp. intro_subst. xret. 
  simpl. xextract. intros. xclean. apply local_erase. esplit. split.
  xapp.
  simpl. xextract. (*todo:xwframe*) apply IH. auto with maths. auto with maths.
  simpl. xsimpl. xclean. math.
  (* inv *)
  match goal with |- (GWhile (?P) (?Q)) _ _ => lets H: (@loop_inv P Q) end.
  apply local_erase. apply H. clear H. unfold loop_cf'.

  

  xwhile_manual (fun i:int => x ~> Ref Id i \* [i >= 0]) (fun i => i > 0) (downto 0).
  hsimpl. auto.
  xextract. intros Ge. xapp. intro_subst. xret. hsimpl~. xclean. auto*.
  xextract. intros Ge M. xclean. xapp. hsimpl; auto with maths.
  hextract. hsimpl. xclean. math.
    
  (* auto *)
  xwhile (fun i:int => x ~> Ref Id i \* [i >= 0]) (fun i => i > 0) (downto 0).
  auto.
  intros Ge. xapp. intro_subst. xret. hsimpl~. xclean. auto*.
  intros Ge M. xapp. hsimpl; auto with maths.
  hextract. xclean. hsimpl. math.
Qed.

(* with old while

  (* details *)
  xwhile_manual (fun i:int => x ~> Ref Id i \* [i >= 0]) (fun i => i > 0) (downto 0).
  hsimpl. auto.
  xextract. intros Ge. xapp. intro_subst. xret. hsimpl~. xclean. auto*.
  xextract. intros Ge M. xclean. xapp. hsimpl; auto with maths.
  hextract. hsimpl. xclean. math.
  (* auto *)
  xwhile (fun i:int => x ~> Ref Id i \* [i >= 0]) (fun i => i > 0) (downto 0).
  auto.
  intros Ge. xapp. intro_subst. xret. hsimpl~. xclean. auto*.
  intros Ge M. xapp. hsimpl; auto with maths.
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
  forall m, R (x ~> Ref Id m) (# x ~> Ref Id (m-1)).
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