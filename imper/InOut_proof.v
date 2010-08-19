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


(********************************************************************)

Implicit Arguments dyn [[dyn_type]].

Definition list_dyn A (L:list A) :=
  LibList.map dyn L.

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
      unfold list_dyn. rew_list~.
      splits. rew_length. math. auto. auto.
    (* loop body *)
    
    (* loop end *)
  


  

Qed.

