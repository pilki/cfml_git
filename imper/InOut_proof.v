Set Implicit Arguments.
Require Import CFPrim InOut_ml.


Ltac xfor_base_manual I cont1 cont2 := 
  apply local_erase; split; 
    [ cont1 tt 
    | cont2 tt; esplit; exists I; splits 3%nat; 
       [  
       | xfor_bounds_intro tt
       | ]
    ].

Ltac xfor_core_gen_manual I H :=
  xfor_base_manual I ltac:(fun _ => intros H)
                     ltac:(fun _ => intros H).

Ltac xfor_base_gen_manual I H :=
  xfor_pre ltac:(fun _ => xfor_core_gen_manual I H).

Tactic Notation "xfor_general_manual" constr(I) "as" ident(H) := 
  xfor_base_gen_manual I H.
Tactic Notation "xfor_general_manual" constr(I) := 
  let H := fresh "Hfor" in xfor_general_manual I as H.



Tactic Notation "hextract" "as" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5) := 
  hextract as; intros I1 I2 I3 I4 I5. 
Tactic Notation "hextract" "as" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) := 
  hextract as; intros I1 I2 I3 I4 I5 I6. 
Tactic Notation "hextract" "as" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) := 
  hextract as; intros I1 I2 I3 I4 I5 I6 I7. 


Opaque Ref.

(********************************************************************)

Implicit Arguments dyn [[dyn_type]].

Definition list_dyn A (L:list A) :=
  LibList.map dyn L.

Lemma list_dyn_nil : forall A,
  list_dyn (@nil A) = nil.
Proof. auto. Qed.

Lemma list_dyn_cons : forall A X (L:list A),
  list_dyn (X::L) = (dyn X)::(list_dyn L).
Proof. auto. Qed.

Lemma list_dyn_last : forall A X (L:list A),
  list_dyn (L&X) = (list_dyn L)&(dyn X).
Proof. intros. unfold list_dyn. rew_list~. Qed.

Hint Rewrite list_dyn_nil : rew_app.
Hint Rewrite list_dyn_nil : rew_map.
Hint Rewrite list_dyn_nil : rew_list.
Hint Rewrite list_dyn_cons : rew_app.
Hint Rewrite list_dyn_cons : rew_map.
Hint Rewrite list_dyn_cons : rew_list.
Hint Rewrite list_dyn_last : rew_app.
Hint Rewrite list_dyn_last : rew_map.
Hint Rewrite list_dyn_last : rew_list.

Lemma length_app_nil2_inv : forall A (l:list A) l1 l2,
  l = l1 ++ l2 -> 
  length l = length l1 ->
  l2 = nil.
Proof.
  intros. destruct l2. auto. subst l. rew_length in H0. math.
Qed.

Opaque Zplus LibList.fold_left.

Lemma std_dup_sum_spec :
  Spec std_dup_sum () |R>> forall (n:int) (L:list int) Li Lo,  
  n = length L ->
  R (stdin ~>> (dyn n :: list_dyn L ++ Li) \* stdout ~>> Lo)
    (# stdin ~>> Li \* stdout ~>> (Lo ++ list_dyn L & dyn (fold_left Zplus 0 L))).
Proof.
  xcf. introv E.
  xapp. intro_subst.
  xapp.
  xfor_general_manual (fun i => 
    Hexists (S:int), Hexists L1 L2, 
      [i = 1+length L1 /\ L = L1 ++ L2 /\ S = fold_left Zplus 0 L1] \*
      s ~> Ref Id S \* stdin ~>> (list_dyn L2 ++ Li) \* stdout ~>> (Lo ++ list_dyn L1)).
    skip. (* todo: case no exec *)
    (* forwards N: (@length_zero_inv _ L). math. subst L. rew_length in E. subst n. *)
    (* loop start *)
    hsimpl (0%Z) (@nil int) L.
      rew_list~.
      splits. rew_length. math. auto. auto.
    (* loop body *)
    xextract as S L1 L2 (En&EL&ES).
    destruct L2 as [|X L2']. rew_app in EL. subst L1. math. rew_app.
    xapp. intro_subst.
    xapp.
    xapp. intro_subst.
    xapp. hsimpl (L1 & X). 
      rew_list~.
      splits.
        rew_length. math.
        rew_app~.
        rew_list. math.
    (* loop end *)
    hextract as S L1 L2 (En&EL&ES).
    forwards: (>>> length_app_nil2_inv EL). math. 
    subst L2. rew_list in EL. subst L1.
    rew_map. subst S. hsimpl.
  (* conclusion *)
  xapp. intro_subst.
  xapp. hsimpl. rew_list~.
Qed.

