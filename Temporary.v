(* TODO
  introv M1 M2.
  introv Hh. specializes M1 Hh. destruct M1 as (H1&H2&Q1&H'&?&(Q''&Ap1&Ap2)&Po).
  exists (= h) [] Q []. splits; rew_heap~.
  exists (Q'' \*+ H2). split.
    applys* local_wframe. intros h'. intro_subst~.
    intros.
  renames Ap2 to M1. specializes M1 g. clears h H1.
  intros h0 (h&h'&Hh&Hh'&HD&HU). specializes M1 Hh.
   destruct M1 as (H1&H2'&Q1'&H''&(h1&h2&?&?&?&?)&(Q'''&Ap1&Ap2)&Po').
  exists (= h1) (= h2 \+ h') Q (= h2 \+ h'). splits; rew_heap~. 
  exists h1 (h2 \+ h'). subst h0 h. splits~.
    rew_disjoint*.
    rewrite~ heap_union_assoc.
  exists Q'''. split.
    (* applys* local_wframe. intro. intro_subst~. exists h1 heap_empty. splits*. apply heap_is_empty_prove. *) skip.
    intros. apply local_erase. exists __. split.
       apply* local_wframe. skip.
       intros g'. specializes Po g'. applys* local_wgframe.
 
    intros

  exists (Q'' \*+ H2). split.
    applys* local_wframe. intros h'. intro_subst~.
    intros. apply local_erase. exists __. split.
       apply* local_wframe.
       intros g'. specializes Po g'. applys* local_wgframe.

apply local_erase. exists __. split.
       apply* local_wframe.
       intros g'. specializes Po g'. applys* local_wgframe.
*)
skip.


(** List *) 

Parameter ml_list_iter : func.

  (* TODO *)
     (* (fun l => Hexists t, l ~> Array Id t \* [t = array_make n v]). *)
      (* (# Hexists t', l ~> Array Id t' \* [t' = t\(i:=v)]).*)

 (* todo: where is local_intro_prop' rebound ? *)

 
  (*todo:*)
  Parameter ml_min_int : int.
  Parameter ml_max_int : int.
  Parameter ml_rand_int : func.



(*------------------------------------------------------------------*)
(* ** MListsSeg *)

(* TODO: define MList as MListSeg null *)

Fixpoint MListSeg (e:loc) A a (T:A->a->hprop) (L:list A) (l:loc) : hprop :=
  match L with
  | nil => [l = e]
  | X::L' => l ~> Ref2 T (MListSeg e T) X L'
  end.

Lemma focus_msnil : forall (e:loc) A a (T:A->a->hprop),
  [] ==> e ~> MListSeg e T nil.
Proof. intros. simpl. hdata_simpl. hsimpl~. Qed.

Lemma unfocus_msnil : forall (l e:loc) A a (T:A->a->hprop),
  l ~> MListSeg e T nil ==> [l = e].
Proof. intros. simpl. hdata_simpl. hsimpl~. Qed.

Lemma unfocus_msnil' : forall A (L:list A) (e:loc) a (T:A->a->hprop),
  null ~> MListSeg e T L ==> [L = nil] \* [e = null].
Proof.
  intros. destruct L.
  simpl. unfold hdata. hextract. hsimpl~. 
  unfold hdata, MListSeg. hchange focus_ref2_null. hextract. false.
Qed.

Lemma focus_mscons : forall (l e:loc) a A (X:A) (L':list A) (T:A->a->hprop),
  (l ~> MListSeg e T (X::L')) ==>
  Hexists x l', (x ~> T X) \* (l' ~> MListSeg e T L') \* (l ~> Ref Id (x,l')).
Proof.
  intros. simpl. hdata_simpl. hchange (@focus_ref2 l). hextract. hsimpl.
Qed.

Lemma focus_mscons' : forall (l e:loc) a A (L:list A) (T:A->a->hprop),
  [l <> e] \* (l ~> MListSeg e T L) ==> 
  Hexists x l', Hexists X L', 
    [L = X::L'] \*  (l ~> Ref Id (x,l')) \* (x ~> T X) \* (l' ~> MListSeg e T L').
Proof.
  intros. destruct L. lets: (@unfocus_msnil l e _ _ T). (* Show Existentials. *)
  hextract. false~.
  hchange (@focus_mscons l e). hextract as x l' E. hsimpl~.  
Qed.

Lemma unfocus_mscons : forall (l:loc) a (x:a) (l' e:loc) A (X:A) (L':list A) (T:A->a->hprop),
  (l ~> Ref Id (x,l')) \* (x ~> T X) \* (l' ~> MListSeg e T L') ==> 
  (l ~> MListSeg e T (X::L')).
Proof.
  intros. simpl. hdata_simpl. hchange (@unfocus_ref2 l _ x _ l'). hsimpl.
Qed.

Implicit Arguments unfocus_msnil [ ].
Implicit Arguments focus_mscons [ a A ].
Implicit Arguments unfocus_mscons [ a A ].

Lemma focus_msapp : forall (l l' e:loc) a A (L L':list A) (T:A->a->hprop),
  l ~> MListSeg l' T L \* l' ~> MListSeg e T L' ==> l ~> MListSeg e T (L++L').
Proof.
  intros l l' e a A L L' T. gen l. induction L as [|X R]; intros.
  hchange (unfocus_msnil l). hextract. subst. auto.
  rew_app. hchange (focus_mscons l). hextract as x r. hchange (IHR r).
   hchange (unfocus_mscons l x r e X (R++L')). hsimpl.
Qed.

Axiom mlistseg_to_mlist : forall (l:loc) a A (T:htype A a) L,
   l ~> MListSeg null T L ==> l ~> MList T L.
Axiom mlist_to_mlistseg : forall (l:loc) a A (T:htype A a) L,
   l ~> MList T L ==> l ~> MListSeg null T L.
(* --todo-- *)

Global Opaque MListSeg.



(*------------------------------------------------------------------*)
(* ** Record 2 *)

Definition Ref2 A1 A2 a1 a2 (T1:A1->a1->hprop) (T2:A2->a2->hprop) (V1:A1) (V2:A2) l :=
  l ~> Ref (Tup2 T1 T2) (V1,V2).

Lemma focus_ref2 : forall (l:loc) a1 a2 A1 A2 (T1:htype A1 a1) (T2:htype A2 a2) V1 V2,
  l ~> Ref2 T1 T2 V1 V2 ==> Hexists (x1:a1) (x2:a2),
  l ~> Ref Id (x1,x2) \* x1 ~> T1 V1 \* x2 ~> T2 V2 .
Proof.
  intros. unfold Ref2. hdata_simpl. hchange (@focus_ref l).
  hextract as [x1 x2]. hchange (focus_tup2 (x1,x2)). hsimpl.
Qed.

Lemma unfocus_ref2 : forall (l:loc) a1 (x1:a1) a2 (x2:a2) A1 A2 (T1:htype A1 a1) (T2:htype A2 a2) V1 V2,
  l ~> Ref Id (x1,x2) \* x1 ~> T1 V1 \* x2 ~> T2 V2 ==>
  l ~> Ref2 T1 T2 V1 V2.
Proof.
  intros. unfold Ref2. hdata_simpl. hchange (unfocus_tup2 x1 x2). 
  hchange (@unfocus_ref l _ (x1,x2)). hsimpl.
Qed.

Lemma focus_ref2_null : forall a1 a2 A1 A2 (T1:htype A1 a1) (T2:htype A2 a2) V1 V2,
  null ~> Ref2 T1 T2 V1 V2 ==> [False]. 
Proof.
  intros. unfold hdata, Ref2. hchange focus_ref_null. hsimpl. 
Qed.

Opaque Ref2.


(*------------------------------------------------------------------*)
(* ** MLists *)

Fixpoint MList A a (T:A->a->hprop) (L:list A) (l:loc) : hprop :=
  match L with
  | nil => [l = null]
  | X::L' => l ~> Ref2 T (MList T) X L'
  end.

Lemma focus_mnil : forall A a (T:A->a->hprop),
  [] ==> null ~> MList T nil.
Proof. intros. simpl. hdata_simpl. hsimpl~. Qed.

Lemma unfocus_mnil : forall (l:loc) A a (T:A->a->hprop),
  l ~> MList T nil ==> [l = null].
Proof. intros. simpl. hdata_simpl. hsimpl~. Qed.

Lemma unfocus_mnil' : forall A (L:list A) a (T:A->a->hprop),
  null ~> MList T L ==> [L = nil].
Proof.
  intros. destruct L.
  simpl. unfold hdata. hextract. hsimpl~. 
  unfold hdata, MList. hchange focus_ref2_null. hextract. false.
Qed.

Lemma unfocus_mnil'' : forall (l:loc) A (L:list A) a (T:A->a->hprop),
  l ~> MList T L ==> [l = null <-> L = nil] \* l ~> MList T L.
Proof. skip. (*todo*) Qed.

Lemma focus_mcons : forall (l:loc) a A (X:A) (L':list A) (T:A->a->hprop),
  (l ~> MList T (X::L')) ==>
  Hexists x l', (x ~> T X) \* (l' ~> MList T L') \* (l ~> Ref Id (x,l')).
Proof.
  intros. simpl. hdata_simpl. hchange (@focus_ref2 l). hextract. hsimpl.
Qed.

Lemma focus_mcons' : forall (l:loc) a A (L:list A) (T:A->a->hprop),
  [l <> null] \* (l ~> MList T L) ==> 
  Hexists x l', Hexists X L', 
    [L = X::L'] \*  (l ~> Ref Id (x,l')) \* (x ~> T X) \* (l' ~> MList T L').
Proof.
  intros. destruct L. lets: (@unfocus_mnil l _ _ T). (* Show Existentials. *)
  hextract. false~.
  hchange (@focus_mcons l). hextract as x l' E. hsimpl~.  
Qed.

Lemma unfocus_mcons : forall (l:loc) a (x:a) (l':loc) A (X:A) (L':list A) (T:A->a->hprop),
  (l ~> Ref Id (x,l')) \* (x ~> T X) \* (l' ~> MList T L') ==> 
  (l ~> MList T (X::L')).
Proof.
  intros. simpl. hdata_simpl. hchange (@unfocus_ref2 l _ x _ l'). hsimpl.
Qed.

Global Opaque MList.

Implicit Arguments unfocus_mnil [ ].
Implicit Arguments unfocus_mcons [ a A ].
Implicit Arguments focus_mcons [ a A ].



(*TODO

Ltac get_app_intro_x_y x y :=
  match constr:(x,y) with
  | (1%nat,1%nat) => constr:(id_proof)
  | (1%nat,2%nat) => constr:(app_intro_1_2)
  | (1%nat,3%nat) => constr:(app_intro_1_3)
  | (1%nat,4%nat) => constr:(app_intro_1_4)
  | (2%nat,1%nat) => constr:(app_intro_2_1)
  | (2%nat,2%nat) => constr:(id_proof)
  | (2%nat,3%nat) => constr:(app_intro_2_3)
  | (2%nat,4%nat) => constr:(app_intro_2_4)
  | (3%nat,1%nat) => constr:(app_intro_3_1)
  | (3%nat,2%nat) => constr:(app_intro_3_2)
  | (3%nat,3%nat) => constr:(id_proof)
  | (3%nat,4%nat) => constr:(app_intro_3_4)
  | (4%nat,1%nat) => constr:(app_intro_4_1)
  | (4%nat,2%nat) => constr:(app_intro_4_2)
  | (4%nat,3%nat) => constr:(app_intro_4_3)
  | (4%nat,4%nat) => constr:(id_proof)
  end.
*)

(* --old
Ltac xauto_common cont :=
  check_not_a_tag tt;  
  try solve [ cont tt 
            | solve [ apply refl_equal ]
            | substs; if_eq; solve [ cont tt | apply refl_equal ] ].
*)

(* bin
Ltac xgc_if_post_meta tt :=
  match post_is_meta tt with
  | false => xgc
  | true => idtac
  end.
*)
(*--------------------------------------------------------*)
(* ** [ximpl] --- TODO

(** Defines an alias of [pred_le] to prevent [auto]
    from solving goals [P ==> Q] when both sides are
    not yet fully instantiated. *)

Definition post_le := pred_le.

Notation "P ==>' Q" := (@post_le _ P Q) (at level 69).

Lemma post_le_intro : forall A (P Q : A -> Prop),
  (P ==>' Q) -> (P ==> Q).
Proof. introv H. apply H. Qed.

(** [ximpl] simplifies a goal of the form [P ==>' Q] *)

Ltac ximpl_base tt :=
  first [ match goal with |- bool_of ?P ==>' bool_of ?Q =>
             apply pred_le_bool_of end 
        | apply pred_le_refl
        | unfold post_le ].

Tactic Notation "ximpl_nointros" :=
  ximpl_base tt.

Ltac check_post_le_no_meta_left tt :=
  match goal with |- ?P ==>' _ =>
    match goal with |- P ==>' _ => idtac end end.

Tactic Notation "ximpl" "as" simple_intropattern(x) :=
  let H := fresh "H" x in intros x Hx.
Tactic Notation "ximpl" "~" "as" simple_intropattern(x) :=
  ximpl as x; xauto_tilde.
Tactic Notation "ximpl" "*" "as" simple_intropattern(x) :=
  ximpl as x; xauto_star.
Tactic Notation "ximpl" "as" simple_intropattern(x) simple_intropattern(Hx) :=
  intros x Hx.

Tactic Notation "ximpl" :=
  let x := fresh "x" in ximpl as x.
Tactic Notation "ximpl" "~" :=
  ximpl; xauto_tilde.
Tactic Notation "ximpl" "*" :=
  ximpl; xauto_star.

 *)


(*
Ltac xapp_spec_core H cont_r cont_w :=
   let arity_goal := spec_goal_arity tt in
   let arity_hyp := spec_term_arity H in
   let lemma := get_spec_elim_x_y arity_hyp arity_goal in
   first [ eapply lemma; [ apply H 
                         | apply post_le_intro; instantiate; cont_w tt ]
         | eapply lemma; [ apply H 
                         | instantiate; cont_r tt 
                         | apply post_le_intro; instantiate; cont_w tt ] ].

Ltac xapp_core cont_r cont_w :=
  let f := spec_goal_fun tt in
  first [ let H := get_spec_hyp f in 
          first [ xapp_spec_core H cont_r cont_w | fail 2 ]
        | let H := get_app_hyp f in 
          let n := spec_term_arity H in
          let m := spec_goal_arity tt in
          let W := get_app_weaken_x n in
          let L := get_app_intro_x_y n m in
          first [ apply L; first [ sapply H
                                 | substs; sapply H  
                (* todo: apply H modulo equality on arguments *)
                                 | eapply W; [ sapply H | ] ] (* todo: cont ? *)
                | fail 2 ]
          (* limitation: continuation applied on premises of H *)
        | xfind f; let H := fresh in 
          intro H; xapp_spec_core H cont_r cont_w; clear H
        | fail 1 "cannot find a specification" ].

Ltac xapp_cont_w_auto tt :=
  first [ check_post_le_no_meta_left tt; ximpl_nointros | idtac ].

Ltac xapp_cont_w_manual x :=
  let Hx := fresh "H" x in intros x Hx.

Ltac xapp_cont_r_no_apply tt :=
  let R := fresh "R" in let HR := fresh "HR" in 
  intros R HR; cbv beta in HR.

Ltac xapp_cont_r E :=
  let R := fresh "R" in let HR := fresh "HR" in intros R HR;
  instantiate; cbv beta in HR;    (*needs instantiate?*)
  match list_boxer_of E with
  | (>>>) => sapply HR; clear R HR
  | ?E' => applys (boxer HR :: E'); try clear R HR
  | _ => idtac
  end.

Ltac xapp_cont_r_with E solver := (* todo factorize with above *)
  let R := fresh "R" in let HR := fresh "HR" in intros R HR;
  instantiate; cbv beta in HR;    (*needs instantiate?*)
  match list_boxer_of E with
  | (>>>) => sapply HR; clear R HR; solver tt
  | ?E' => applys (boxer HR :: E'); try clear R HR; solver tt
  | ?E' => fapplys (boxer HR :: E'); try clear R HR; solver tt 
  | _ => idtac
  end.
*)




(*--------------------------------------------------------*)
(* ** [xweak] --TODO

Ltac xweak_partial cont := 
  cont tt.

Ltac xweak_normal cont :=
   let R := fresh "R" in let WR := fresh "WR" in let HR := fresh "HR" in
   intros R WR HR; instantiate; cbv beta in HR;
   first [ sapply HR; clear HR WR R
         | eapply WR; clear WR; 
            [ try (sapply HR; try clear HR R)
            | (try clear HR R); cont tt ] ]. (* no need to clear? *)

Ltac xweak_base cont :=
  match goal with
  | |- (_ ==> _) => xweak_partial cont
  | |- _ => xweak_normal cont
  end.

Ltac xweak_weaken_solve :=     
  solve [ 
  try fold_bool; calc_partial_eq tt; repeat substs_core; repeat injects_core;
  sapply pred_le_refl ].

Tactic Notation "xweak" "as" :=
   xweak_base ltac:(fun _ => idtac).
Tactic Notation "xweak" "as" ident(x) ident(Hx) :=
   xweak_base ltac:(fun _ => intros x Hx; instantiate; cbv beta in Hx).
Tactic Notation "xweak" "as" ident(x) :=
   let Hx := fresh "P" x in xweak as x Hx.
Tactic Notation "xweak" :=
   xweak_base ltac:(fun _ => first 
     [ xweak_weaken_solve
     | let x := fresh "x" in let Hx := fresh "P" x in 
       intros x Hx; instantiate; cbv beta in Hx ] ).
Tactic Notation "xweaks" := 
   xweak_base ltac:(fun _ => first 
     [ xweak_weaken_solve
     | let x := fresh "x" in let Hx := fresh "P" x in 
       intros x Hx; instantiate; cbv beta in Hx; try if_eq in Hx;
       try substs x ]).

*)(** Lemmas to set up induction for two mutually-recursive functions. 

Lemma mutual_update_2 : forall (P' Q' P Q : Prop),
  (P' -> P) -> (Q' -> Q) -> (P' /\ Q') -> (P /\ Q).
Proof. auto*. Qed.

Lemma mutual_quantif_2 : forall T (P Q : T -> Prop),
  (forall n, P n /\ Q n) -> (forall n, P n) /\ (forall n, Q n).
Proof. introv H. split; intros; eapply H. Qed.

*)



(*--------------------------------------------------------*)
(* ** [xfor]--old

Ltac xfor_bounds_intro tt :=
  intro; let i := get_last_hyp tt in
  let Hli := fresh "Hl" i in
  let Hui := fresh "Hu" i in
  intros [Hli Hui].

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


(* todo: improve *)

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

*)

(*--------------------------------------------------------*)
(* ** [xwhile] --old

Ltac xwhile_core_inner I J R X0 cont1 cont2 cont3 :=
  apply local_erase; esplit; esplit; exists I; exists J;
  first [ exists R | exists (measure R) ]; splits 3%nat;
  [ cont1 tt 
  | match X0 with __ => esplit | _ => exists X0 end; cont2 tt 
  | cont3 tt ].

Ltac xwhile_fixj I J :=
  match type of J with
  | _ -> bool => constr:(fun X B => I X \* [B = J X])
  | _ -> Prop => constr:(fun X B => I X \* [bool_of (J X) B])
  end.

Ltac xextract_post_clean tt :=
  try ( pose ltac_mark; intros; xclean; gen_until_mark ).
(* todo: hextract with clean in it ! *)

Ltac xwhile_core I J R X0 X cont2 cont31 cont32 cont33 :=
  let J' := xwhile_fixj I J in
  xwhile_core_inner I J' R X0 
    ltac:(fun _ => prove_wf)
    ltac:(cont2)
    ltac:(fun _ => intros X; splits 3%nat; [ cont31 tt | cont32 tt | cont33 tt ]).
    
Ltac xwhile_pre cont :=
  match ltac_get_tag tt with
  | tag_seq => xseq; [ cont tt | ]
  | tag_while => cont tt
  end.

Ltac xwhile_base I J R X0 X :=
  xwhile_pre ltac:(fun _ => xwhile_core I J R X0 X
    ltac:(fun _ => hsimpl)
    ltac:(fun _ => try xextract)
    ltac:(fun _ => try xextract; xextract_post_clean tt)
    ltac:(fun _ => idtac)).

Ltac xwhile_base_manual I J R X0 X :=
  xwhile_pre ltac:(fun _ => xwhile_core I J R X0 X
    ltac:(idcont) ltac:(idcont) ltac:(idcont) ltac:(idcont)).

Tactic Notation "xwhile" constr(I) constr(J) constr(R) constr(X0) "as" simple_intropattern(X) := 
  xwhile_base I J R X0 X.
Tactic Notation "xwhile" constr(I) constr(J) constr(R) constr(X0) := 
  let X := fresh "X" in xwhile I J R X0 as X.
Tactic Notation "xwhile" constr(I) constr(J) constr(R) := 
  xwhile I J R __.

Tactic Notation "xwhile_manual" constr(I) constr(J) constr(R) constr(X0) "as" simple_intropattern(X) := 
  xwhile_base_manual I J R X0 X.
Tactic Notation "xwhile_manual" constr(I) constr(J) constr(R) constr(X0) := 
  let X := fresh "X" in xwhile_manual I J R X0 as X.
Tactic Notation "xwhile_manual" constr(I) constr(J) constr(R) := 
  xwhile_manual I J R __.

*)

(*--------------------------------------------------------*)
(* ** [xwhile] --old while

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

*)




(* --deprecated

Tactic Notation "xif_core" ident(H) tactic(cont) :=
  xuntag tag_if; split; intros H; fold_bool; [ | cont tt ].

Tactic Notation "xpat_core" ident(H) tactic(cont) :=
  xuntag tag_case;
  match goal with 
  | |- ?P /\ ?Q => split; [ introv H | introv H; xtag_negpat H; cont tt ]
  | |- forall _, _ => introv H
  end.

Tactic Notation "xif_core_anonymous" tactic(cont) :=
  let H := fresh "C" in xif_core H cont.

Tactic Notation "xpat_core_anonymous" tactic(cont) :=
  let H := fresh "C" in xpat_core H cont.

Tactic Notation "xcase_one" "as" ident(H) :=
  match ltac_get_tag tt with
  | tag_case => xpat_core H (fun _ => idtac)
  | tag_if => xif_core H (fun _ => idtac)
  end.
  
Tactic Notation "xcase_one" :=
  match ltac_get_tag tt with
  | tag_case => xpat_core_anonymous (fun _ => idtac)
  | tag_if => xif_core_anonymous (fun _ => idtac)
  end.
  
Ltac xpats_core :=
  xpat_core_anonymous (fun _ => try xpats_core).

Ltac xifs_core :=
  xif_core_anonymous (fun _ => try xifs_core).

Tactic Notation "xcases" :=
  match ltac_get_tag tt with
  | tag_case => xpats_core
  | tag_if => xifs_core
  end; try fold_bool; fold_prop.

Tactic Notation "xcases_subst" := 
  xcases; try invert_first_hyp.

Tactic Notation "xcase_one_real" := 
   xcase_one; try solve [ discriminate | false; congruence ];
  (* TODO: simulate total coverage *)
  try match ltac_get_tag tt with tag_done => split end;
  try invert_first_hyp; 
  try fold_bool; fold_prop.

Tactic Notation "xcases_real" := 
   xcases; try solve [ discriminate | false; congruence ];
  (* TODO: simulate total coverage *)
  try match ltac_get_tag tt with tag_done => split end;
  try invert_first_hyp; 
  try fold_bool; fold_prop.

Tactic Notation "xcase" := xcases_real.
*)


(* xcases avec nommage *) 
    
(* todo: avec substitution 
Ltac xpats_core :=
  let E := fresh "M" in
  match goal with 
  | |- ?P /\ ?Q => 
    split; [ introv E; hnf in E; try subst_eq E
           | introv E; xpats_core ]
  | |- forall _, _ => introv E; hnf in E; try subst_eq E
  end.
*)

(* _nometa
Ltac xif_core_meta H cont :=
  xif_core_nometa H cont.

Ltac xif_base H cont :=
  match post_is_meta tt with
  | false => xif_core_nometa H cont
  | true => xif_core_meta H cont
  end. 
*)
(*
Ltac xif_base H cont :=
  xif_core H; cont tt.

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
*)

(*---deprecated
Ltac post_is_meta tt :=
  match goal with
  | |- ?F ?P => match P with P => constr:(false) end 
  | |- _ => constr:(true)
  end.

Ltac arg_of_if tt :=
  match goal with |- (?x = _ -> _) /\ (?x = _ -> _) => x end.

(*TODO
Lemma analysis_for_if : forall (B: Type) x t1 l1 t2 l2,
  forall (P1 P2:(B->Prop)) (Q1 Q2:~~B),
  (x = true -> ((tag t1 l1 Q1) P1)) -> 
  (x = false -> ((tag t2 l2 Q2) P2)) ->
     (x = true -> (tag t1 l1 Q1) (if x then P1 else P2))
  /\ (x = false -> (tag t2 l2 Q2) (if x then P1 else P2)).
Proof. intros. case_if; split; intros; auto; tryfalse. Qed.

Lemma analysis_for_if_eq : forall (B: Type) x t1 l1 t2 l2,
  forall (V1 V2:B) (Q1 Q2:~~B),
  (x = true -> ((tag t1 l1 Q1) (= V1))) -> 
  (x = false -> ((tag t2 l2 Q2) (= V2))) ->
     (x = true -> (tag t1 l1 Q1) (= if x then V1 else V2))
  /\ (x = false -> (tag t2 l2 Q2) (= if x then V1 else V2)).
Proof. intros. case_if; split; intros; auto; tryfalse. Qed.
*)

Ltac xif_core_meta H :=
 fail.
(* TODO
  xuntag tag_if; let x := arg_of_if tt in
  calc_partial_eq tt; try subst x; 
  (* sapply analysis_for_if;*)
  first [ let K := fresh in forwards K: analysis_for_if; [ | | apply K ]
        | let K := fresh in forwards K: analysis_for_if_eq; [ | | apply K ] ];
  intros H; xif_post H.
*)

Tactic Notation "xif" :=
  xif_core.
Tactic Notation "xcond" ident(H) :=
  xif_post H.

Ltac xif_post H :=
   calc_partial_eq tt;
   try fold_bool; fold_prop;
   try fix_bool_of_known tt;
   try solve [ discriminate | false; congruence ];
   first [ subst_hyp H; try fold_bool; try rewriteb H 
         | rewriteb H
         | idtac ];
   try fix_bool_of_known tt.  

Ltac xif_core_nometa H :=
  xuntag tag_if; split; intros H; xif_post H.

Tactic Notation "xif" ident(H) :=
  match post_is_meta tt with
  | false => xif_core_nometa H
  | true => xif_core_meta H
  end. 

Tactic Notation "xif" :=
  let H := fresh "C" in xif H.
*)

(*
   | Xlets ?S =>
     match tag with
     | tag_let_trm => xlets S; cont tt
     | tag_let_fun => xfun S
     end
*)


--deprecated
Ltac xapps_core spec args solver :=
  let cont tt := 
    xapp_inst args solver in
  match ltac_get_tag tt with
  | tag_let_trm => xlet; [ xuntag tag_apply; cont tt | instantiate; xextract; intro_subst ]
  | tag_seq =>     xseq; [ xuntag tag_apply; cont tt | instantiate; xextract; intro_subst ]
  end.



Lemma hclean_demo_1 : forall A (x X:A) H1 H2 H3 B (F:~~B) P Q,  
   is_local F ->
   F (H1 \* [] \* H2 \* [P] \* x ~> Id X \* H3) Q.
Proof.
  intros. dup.
  (* details *)
  hclean_setup tt.
  pose ltac_mark.
  hclean_step tt.
  hclean_step tt.
  hclean_step tt.
  hclean_step tt.
  hclean_step tt.
  hclean_step tt.
  try hclean_step tt.
  autorewrite with hsimpl_neutral.
  unprotect_evars tt.
  gen_until_mark.
  skip.
  (* short *)
  hclean.
  skip.
Qed.  



Lemma hextract_demo_1 : forall n J H2 H3 H4 H',
  H4 \* (Hexists y, [y = 2]) \* (Hexists x, [n = x + x] \* J x \* H2) \* H3 ==> H'.
Proof.
  intros. dup 3.
  (* details *)
  hextract_setup tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  try hextract_step tt.
  hextract_cleanup tt.
  intros.
  skip.
  (* short *)
  hextract. skip.
  (* if needed *)
  hextract_if_needed tt. intros.
  try hextract_if_needed tt. skip.
Qed.

Lemma hextract_demo_2 : forall H1 H' (G:Prop),
  (forall H2, H1 \* (Hexists y, [y = 2]) \* H2 ==> H' -> G) ->
  G.
Proof.
  introv W. eapply W. dup.
  (* details *)
  hextract_setup tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  hextract_step tt.
  try hextract_step tt.
  hextract_cleanup tt.
  intros y Hy.
  skip.
  (* short *)
  hextract. skip.
Admitted.

Lemma hsimpl_demo : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* H3 \* H4 ==> H4 \* H3 \* H5 \* H2.
Proof.
  intros. dup. 
  (* details *)
  hsimpl_setup tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_cleanup tt.
  skip.
  (* short *)
  hsimpl. skip.
Qed.

Lemma hsimpl_demo_2 : forall (l1 l2:loc) S1 S2 H1 H2 H3 H',
  (forall X S1' HG, X ==> H1 \* l1 ~> S1' \* H2 \* HG -> X ==> H') ->
  H1 \* l1 ~> S1 \* l2 ~> S2 \* H3 ==> H'.
Proof.
  intros. dup.
  (* details *) 
  eapply H.
  hsimpl_setup tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_cleanup tt.
  skip.
  (* short *)
  eapply H.
  hsimpl. skip.
Admitted.

Lemma hsimpl_demo_3 : forall (l1 l2:loc) S1 S2 H1 H2 H',
  (forall X S1' HG, X ==> H1 \* l1 ~> S1' \* HG -> HG = HG -> X ==> H') ->
  H1 \* l1 ~> S1 \* l2 ~> S2 \* H2 ==> H'.
Proof.
  intros. dup.
  (* details *)
  eapply H.  
  hsimpl_setup tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_cleanup tt.
  auto.
  (* short *)
  eapply H.
  hsimpl.
  auto.
Admitted.

Lemma hsimpl_demo_4 : forall n m J H2 H3 H4,
  n = m + m ->
  H2 \* J m \* H3 \* H4 ==> H4 \* (Hexists y, y ~> Id 2) \* (Hexists x, [n = x + x] \* J x \* H2) \* H3.
Proof.
  intros. dup.
  (* details *)
  hsimpl_setup tt.
  hsimpl_step tt.
  hsimpl_step tt. 
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_step tt.
  hsimpl_cleanup tt.
  auto.
  eauto.
  (* short *)
  hsimpl.
  auto.
  eauto.
Qed.

Lemma hsimpl_demo_5 : forall n J H,
  n = 2 ->
  J n \* H ==> H \* Hexists y, [y <> 3] \* J y.
Proof.
  intros. dup 3.
  hsimpl. math.
  hsimpl n. math.
  hsimpl 2. subst~. math.
Qed.