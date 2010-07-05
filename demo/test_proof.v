Set Implicit Arguments.
(* Require Import FuncTactics.*)
Require Import LibCore.
Require Import CFPrim.
Require Import test_ml.

Opaque heap_is_empty hdata heap_is_single heap_is_empty_st RefOn.

Implicit Arguments Base [[A]].

Notation "m \( x )" := (LibBag.read m x)
  (at level 29, format "m \( x )") : container_scope.
Notation "m \( x := v )" := (update m x v)
  (at level 29, format "m \( x := v )") : container_scope.



Parameter ml_array_make_spec : forall A,
  Spec ml_array_make (n:int) (v:A) |R>> 
     R [] (fun l => Hexists t, l ~> Array Base t \* [t = array_make n v]).

Parameter ml_array_get_spec : forall `{Inhabited A},
  Spec ml_array_get (l:loc) (i:int) |R>> 
    forall (t:array A), index t i ->
    Read (R:~~A) (l ~> Array Base t) (\= t\(i)).

Parameter ml_array_set_spec : forall A,
  Spec ml_array_set (l:loc) (i:int) (v:A) |R>> 
    forall (t:array A), index t i -> 
    R (l ~> Array Base t) (# Hexists t', l ~> Array Base t' \* [t' = t\(i:=v)]).


Hint Extern 1 (RegisterSpec ml_array_make) => Provide ml_array_make_spec.
Hint Extern 1 (RegisterSpec ml_array_get) => Provide ml_array_get_spec.
Hint Extern 1 (RegisterSpec ml_array_set) => Provide ml_array_set_spec.

(********************************************************)
(* arrays *)

Ltac xapp_show_spec := 
  xuntag; let f := spec_goal_fun tt in
  xfind f; let H := fresh in intro H.


Lemma hclean_exists : forall B (F:~~B) H1 H2 A (J:A->hprop) Q,
  is_local F -> 
  (forall x, F (H1 \* (J x) \* H2) Q) ->
   F (H1 \* (heap_is_pack J \* H2)) Q.
Proof. 
  intros. rewrite star_comm_assoc. apply~ local_intro_exists.
  intros. rewrite~ star_comm_assoc.
Qed. 

Ltac hclean_relinearize tt :=
  let go Hpre := match Hpre with ?H \* (_ \* _) =>
    let T := fresh "TEMP" in 
    sets T: H; 
    autorewrite with hsimpl_assoc; 
    subst T
    end in
  hclean_onH ltac:(go).
 
Ltac hclean_step tt ::=
  let go H :=
    match H with ?HA \* ?HX \* ?HR => match HX with
    | [?P] => apply hclean_prop; [ xlocal | intro ]
    | heap_is_pack ?J => apply hclean_exists; [ xlocal | intro; hclean_relinearize tt ]
    | _ => apply hclean_step
    end end in
  hclean_onH ltac:(go).

Ltac xapp_spec_core H cont ::=
   let arity_goal := spec_goal_arity tt in
   let arity_hyp := spec_term_arity H in
   match constr:(arity_goal, arity_hyp) with (?n,?n) => idtac | _ => fail 1 end;
   let lemma := get_spec_elim_x_y arity_hyp arity_goal in
   eapply lemma; [ sapply H | cont tt ]. 

Instance inhabited_Z : Inhabited Z.
Admitted.


Open Scope container_scope.

Ltac xfun_core s cont ::=
  apply local_erase;
  intro; let f := get_last_hyp tt in
  let Sf := fresh "S" f in
  exists s; split; [ cont tt | intros Sf ].

Lemma post_le_unit : forall H H' : hprop,
  H ==> H' -> (#H) ===> (#H').
Proof. intros_all~. Qed.



Lemma arrays_spec : Spec arrays () |R>> R [] (\=3).
Proof.
  xcf.
  xlet. xapp. xextract as t Ht.
  xlet. xapp. skip. xextract as e.
  xseq. xapp. skip. simpl. apply rel_le_refl. . xextract as e'.
  xfun (fun f => Spec f (i:int) |R>> R [] (\=i)). xret*.
  xlet.
    


post_le_unit


Qed.


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