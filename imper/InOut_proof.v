Set Implicit Arguments.
Require Import CFPrim InOut_ml.

Opaque Ref Zplus LibList.fold_left.

(*todo:move to lists*)
Lemma length_app_nil2_inv : forall A (l:list A) l1 l2,
  l = l1 ++ l2 -> 
  length l = length l1 ->
  l2 = nil.
Proof.
  intros. destruct l2. auto. subst l. rew_length in H0. math.
Qed.

(********************************************************************)

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

