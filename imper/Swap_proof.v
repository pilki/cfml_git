Set Implicit Arguments.
Require Import CFLib Swap_ml.


(********************************************************************)
(* ** Swap for non-aliased references *)

Lemma swap_spec_neq : forall a,
  Spec swap i j |R>> forall A (T:htype A a) X Y,
   R (i ~> Ref T X \* j ~> Ref T Y)  
   (# i ~> Ref T Y \* j ~> Ref T X).
Proof.
  xcf. intros.
  xchange (@focus_ref i) as x.
  xchange (@focus_ref j) as y.
  xapps. xapps. xapp. xapp. 
  hchange (unfocus_ref i y).
  hchanges (unfocus_ref j x).
Qed.

(********************************************************************)
(* ** Swap for aliased references *)

Lemma swap_spec_equal : forall a,
  Spec swap i j |R>> forall A (T:htype A a) X,
    i = j -> keep R (i ~> Ref T X) (#[]).
Proof.
  xcf. introv E. subst j.
  xchange (focus_ref i) as x. 
  xapps. xapps. xapp. xapp.
  hchanges (unfocus_ref i x).
Qed.

(********************************************************************)
(* ** General version of swap, with a group region *)

Lemma swap_spec_group : forall a,
  Spec swap i j |R>> forall `{Inhab A} (T:htype A a) (M:map loc A),
    index M i -> index M j ->
    let M' := M\(j:=M\(i))\(i:=M\(j)) in
    R (Group (Ref T) M) (# Group (Ref T) M').
Proof.
  xcf. introv Ii Ij. intro. tests (j = i).
  (* case aliased references *)
  subst M' j. 
  xchange~ (Group_rem i).
  xchange (focus_ref i) as x.
  xapps. xapps. xapp. xapp.
  hchange (unfocus_ref i).
  hchange~ (Group_add' i).
  rewrite~ update_update_eq.         (* map specific *)
  (* case non-aliased references *)
  forwards*: (dom_restrict_in i j).  (* map specific *)
  xchange~ (Group_rem i).
  xchange~ (Group_rem j). 
  xchange (focus_ref i) as x.
  xchange (focus_ref j) as y.
  xapps. xapps. xapp. xapp.
  hchange (unfocus_ref i y). 
  hchange (unfocus_ref j x).
  hchange~ (Group_add' j).
  rewrite~ restrict_update.          (* map specific *)
  rewrite~ restrict_read.            (* map specific *)
  hchange~ (Group_add' i). 
  rewrite~ dom_update_in.            (* map specific *)
Qed.

