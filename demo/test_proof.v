Set Implicit Arguments.
(* Require Import FuncTactics.*)
Require Import LibCore.
Require Import CFPrim CFTactics. (* todo: group as CF *)
Require Import test_ml.

Opaque heap_is_empty hdata heap_is_single heap_is_empty_st Ref.

(********************************************************)
(* records test *)

Lemma x_cf : Specs x () >> [] (fun r => [_recone (_B:=int) r = 6]).
Proof.
  xcf. 
  xfun (fun g:val => Specs g (x:int) >> [] (\=x)). xret~.
  xret~.
Qed.

Definition Any {A:Type} (X:unit) (x:A) := [].


Lemma Myrecord_focus: forall _A _B A B C (TA:htype A _A) (TB:htype B int) (TC:htype C val) X Y Z (l:loc),
   l ~> Myrecord _B TA TB TC X Y Z ==>
  Hexists (x:_A) (y:int) (z:val),
  l ~> Myrecord _B Id Id Id x y z \* TA X x \* TB Y y \* TC Z z.
Proof.
  intros. unfold Myrecord at 1. hdata_simpl. hextract. hsimpl x x0 x1.
  unfold Myrecord at 1. hsimpl. hdata_simpl. hsimpl.
  unfold Id. hdata_simpl. hsimpl~.
Qed.

Lemma Myrecord_unfocus: forall _A _B A B C (TA:htype A _A) (TB:htype B int) (TC:htype C val) X Y Z (l:loc), 
  forall (x:_A) (y:int) (z:val),
  l ~> Myrecord _B Id Id Id x y z \* TA X x \* TB Y y \* TC Z z ==>
   l ~> Myrecord _B TA TB TC X Y Z.
Proof.
  intros. unfold Myrecord at 1. hdata_simpl. hextract.
  unfold Myrecord at 1. hdata_simpl. subst. hsimpl~.
Qed.

(*---
Definition Myrecord _A _B A B C (TA:htype A _A) (TB:htype B int) (TC:htype C val) X Y Z (l:loc) :=
  Hexists (x:_A) (y:int) (z:val), heap_is_single l (@_myrecord_of _A _B x y z) \* TA X x \* TB Y y \* TC Z z.


Parameter _get_rectwo_spec : forall _A _B (A C:Type),
  Spec _get_rectwo (l:loc) |R>> forall (TA:htype A _A) (TC:htype C val) X Y Z,
    keep R (l ~> Myrecord _B TA Id TC X Y Z) (\= Y).

Parameter _set_recone_spec : forall _A _B (B C:Type),
  Spec _set_recone (l:loc) (X':_A) |R>> forall (TB:htype B int) (TC:htype C val) (X:_A) Y Z,
    R (l ~> Myrecord _B Id TB TC X Y Z) (# l ~> Myrecord _B Id TB TC X' Y Z).

Hint Extern 1 (RegisterSpec _get_rectwo) => Provide _get_rectwo_spec.
Hint Extern 1 (RegisterSpec _set_recone) => Provide _set_recone_spec.
*)

Lemma f_spec : Spec f (a:loc) |R>> forall (n m:int),
  R (a ~> Myrecord int Id Id Any n m tt)
  (# a ~> Myrecord int Id Id Any (m+1) m tt).
Proof.
  apply (@f_cf int). xisspec. (* xcf. => has evars :: xcf should take a list to instantiate *)
  intros.
  xlet. xapp.
  xapp. xsimpl. congruence.
Qed.



(********************************************************)
(* for loops *)

Lemma sum_spec : Spec sum (n:int) |R>> n > 0 -> R [] (\= 0).
Proof.
  xcf. intros.
  xapp.
  xseq.
  apply local_erase. intros S LS HS.
  cuts: (forall i, i <= n+1 -> S i (x ~> Ref Id (n+1-i)) (# x ~> Ref Id 0)).
    applys_eq H0 2. math. fequals. fequals. math.
    intros i. induction_wf IH: (int_upto_wf (n+1)) i.
    intros Le. apply HS. split; intros; try solve [ false;math ].
      (*-->todo use tag for let *)
    apply local_erase. esplit. split. (* use xlet *)
    xapp.
    forwards M: IH (i+1); auto with maths. 
    applys~ local_wframe M.
    hsimpl. math.
    hsimpl.
    hsimpl. math.
  xapp. xsimpl. math.
Admitted.

Lemma sum_spec' : Spec sum (n:int) |R>> n > 0 -> R [] (\= 0).
Proof.
  xcf. intros.
  xapp.
  xseq.
  apply for_loop_cf_to_inv. apply local_erase. split. intros. false. math.
   (*-->todo only one side! *)
  intros _. esplit. exists (fun i => (x ~> Ref Id (n+1-i))). splits.
    hsimpl. math.
    intros i Le. xapp. hsimpl. math.
    hsimpl.
  xapp. xsimpl. math.
(*
xfor (fun i => (x ~> Ref Id (n+1-i))). math.
*)
Admitted.


(********************************************************)
(* while loops *)



(*
Ltac xwhile_core_inner I J R X0 cont1 cont2 cont3 ::=
  esplit; esplit; exists I; exists J;
  first [ exists R | exists (measure R) ]; splits 3%nat;
  [ cont1 tt 
  | match X0 with __ => esplit | _ => exists X0 end; cont2 tt 
  | cont3 tt ].
Ltac xwhile_pre cont ::= cont tt.
*)

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