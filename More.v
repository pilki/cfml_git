Parameter ml_neq : val.
Parameter ml_opp : val.
Parameter ml_mul : val.
Parameter ml_div : val.
Parameter ml_append : val.
Parameter ml_raise : val.
  (* .. yet to specify *)

Parameter compare : val. (* todo: until functors are supported *)


(*--demo  --todo:update?
Definition mytag (P:Prop) := P.
Lemma test_add_tag : True.
Proof. ltac_add_tag mytag. split. Qed.
--*)



(********************************************************************)
(********************************************************************)
(********************************************************************)
(* * Technical Appendix

(************************************************************)
(** Appendix: a proof that characteristic formulae defined
    in terms of AppReturns are equivalent to those defined
    in terms of Spec. *)

(* for arity one *)

Lemma equiv_1 : forall A B (Pf : val -> Prop) (Q : A ->(B->Prop)->Prop),
  (forall f, (forall x P, Q x P -> app_1 f x P) -> Pf f) 
  <->
  (forall f, (forall K:A->~~B->Prop, is_spec_1 K ->
     (forall x, K x (Q x)) -> spec_1 K f) -> Pf f).
Proof.
  split.
  (* correctness *)
  introv H1 H2. apply H1.
  apply (H2 (fun x R => forall P, Q x P -> R P)). 
    intros_all~. 
    auto.
  (* completeness *)
  introv H1 H2. apply H1. introv SK HK. split~. intros x.
  applys* SK. applys* H2.
Qed.

(* for arity two *)

Lemma equiv_2 : forall A1 A2 B (Pf : val -> Prop) 
    (Q : A1 -> A2 ->(B->Prop)->Prop),
  (forall f, (forall K1:A1->~~val->Prop, is_spec_1 K1 ->
    (forall x, K1 x (fun P', forall g, 
      (forall K2:A2->~~B->Prop, is_spec_1 K2 ->
         (forall y, K2 y (Q x y)) -> spec_1 K2 g)
      -> P' g)) -> spec_1 K1 f) -> Pf f)
  <->
  (forall f, (forall K:A1->A2->~~B->Prop, is_spec_2 K ->
     (forall x y, K x y (Q x y)) -> spec_2 K f) -> Pf f).
Proof.
  split.
  (* correctness *)
  introv H1 H2. apply H1. clear H1. introv SK1 HK1.
  applys spec_weaken_1. 
  specializes H2 (fun x y R' =>
    forall K2:A2->~~B->Prop, is_spec_1 K2 -> K2 y (Q x y) -> K2 y R').
  sapply~ H2; clear H2.
    intros x y. intros_all. forwards* M: H. applys* H1. auto.
  simpl. intros x R WR HR. sapply SK1. sapply HK1.
  intros P' HP'. sapply WR. apply HR. clear HR.
  intros g Hg. apply HP'. clear HP'.
  introv SK2 HK2. applys spec_weaken_1. apply Hg. auto. clear Hg.
  simpl. intros y R' WR' HR'. intros. applys SK2. sapply HK2.
  intros z Hz. apply (HR' (fun (_:A2) (R':(B->Prop)->Prop) => R' z)).
    intros_all~. auto.
  (* completeness *)
  introv H1 H2. apply H1. clear H1. introv SK HK. split~.
  apply H2. intros_all~. clear H2. introv Hg.
  applys spec_weaken_1. apply~ (Hg (K x)). auto. auto.
Qed.
  

 *)



(* todo bin: old versions *)

Ltac old_get_spec_intro_x x :=
  match x with
     | 1%nat => constr:(spec_intro_1)
     | 2%nat => constr:(spec_intro_2)
     | 3%nat => constr:(spec_intro_3)
     | 4%nat => constr:(spec_intro_4)
  end.

Ltac old_xintros_core cont1 cont2 cont3 :=
   let arity := spec_goal_arity tt in
   let lemma := old_get_spec_intro_x arity in
   apply lemma; [ instantiate; cont1 tt 
                | instantiate; cont2 tt 
                | instantiate; cont3 tt ]. 

Tactic Notation "old_xintros" :=
  old_xintros_core ltac:(fun _ => try xisspec) 
               ltac:(fun _ => try xcurried) 
               ltac:(fun _ => idtac).

Tactic Notation "old_xintros_noauto" :=
  old_xintros_core ltac:(fun _ => idtac) 
               ltac:(fun _ => idtac) 
               ltac:(fun _ => idtac).


(*bin
Notation "'Xhint_do' a" := (tag _ (Some a) _ _)
  (at level 69, only parsing).
*)
  (*
  | Xcase : Xhint_cmd
  | Xcases : Xhint_cmd
  | Xcasenosubst : Xhint_cmd.
  *)

(*--------------------------------------------------------*)
(* ** [xfunc]  -- todo: deprecated

Ltac xfunc_core f :=
  let Pf := fresh "TEMP" in 
  esplit; split; [ | intros Pf; xret; pattern f; apply Pf ].

Tactic Notation "xfunc" :=
  intro; let f := get_last_hyp tt in xfunc_core f; try xbody.

Tactic Notation "xfunc" "as" "f" :=
  intros f; xfunc_core f; try xbody.

*)
      (*xpat_core_new  todo: deprecated
      match goal with 
      | |- ?P /\ ?Q => 
      | |- forall _, _ => introv H
      end. *)

(*--todo: deprecated?
Tactic Notation "xok" := 
  first [ apply_last_hyp | apply refl_equal ].
*)


(*-------todo: deprecated ----------*)

Tactic Notation "xweaken_post" constr(P') := 
  match goal with
  |- tag _ _ _ ?P => asserts_rewrite (P = P'); [ try apply bool_of_eq | ]
  end.

Lemma xweaken_post_lemma : forall T O A (F:(A->Prop)->Prop) (P Q:A->Prop),
  tag T O F Q -> P = Q -> tag T O F P.
Proof. intros. subst~. Qed.

Tactic Notation "xweaken_post" := 
  eapply xweaken_post_lemma; [ | try apply bool_of_eq ].


(* --old

Ltac xgo_core optStopAt :=
  first [
  let tag := ltac_get_tag tt in
  let label := ltac_get_label tt in
  match optStopAt with
  | Some label => fail
  | _ => 
  match tag with
  | tag_ret => xret
  | tag_fail => xfail
  | tag_done => split
  | tag_apply => xapp_old
  | tag_let => xlet
  | tag_letfun => fail
  | tag_body => fail
  | tag_letrec => fail
  | tag_case => xcases_real
  | tag_if => xif
  | tag_alias => xalias
  | tag_toplet => fail
  | tag_match ?n => xmatch
  | tag_topfun  => fail
  end end
  | let f := spec_goal_fun tt in xcf f
  | progress(intros) ].


Ltac xgo_repeat optStopAt n :=
  match nat_from_number n with
  | 0%nat => idtac
  | S ?n' => xgo_core optStopAt; instantiate;
             try xgo_repeat optStopAt n'
  end.

Tactic Notation "xgo" := 
  xgo_repeat (@None tag_name) (100%nat).

Tactic Notation "xgo" constr(nOrStopAt) := 
  match type of nOrStopAt with
  | tag_name => xgo_repeat nOrStopAt (100%nat)
  | _ => xgo_repeat (@None tag_name) nOrStopAt
  end.

Tactic Notation "xgon" constr(n) := 
  xgo_repeat (@None tag_name) n.

Tactic Notation "xgo" "~" := xgo; xauto~; instantiate; xauto~.
Tactic Notation "xgo" "*" := xgo; xauto*; instantiate; xauto*.
Tactic Notation "xgo" "~" constr(stopAt) := xgo stopAt; xauto~; instantiate; xauto~.
Tactic Notation "xgo" "*" constr(stopAt) := xgo stopAt; xauto*; instantiate; xauto*.
Tactic Notation "xgon" "~" constr(n) := xgon n; xauto~; instantiate; xauto~.
Tactic Notation "xgon" "*" constr(n) := xgon n; xauto*; instantiate; xauto*.

Tactic Notation "xgos" := xgo 1; try solve [ xgo~ ]. 
Tactic Notation "xgos" "~" := xgo 1; try solve [ xgo~ ].
Tactic Notation "xgos" "*" := xgo 1; try solve [ xgo* ].

*)

Axiom foreach_weaken : forall A (P Q:A->Prop) (E:set A),
  foreach P E -> P ==> Q -> foreach Q E.
Axiom foreach_union_inv : forall A (P:A->Prop) (E F:set A),
  foreach P (E \u F) -> foreach P E /\ foreach P F.
Axiom foreach_union_eq : forall A (P:A->Prop) (E F:set A),
  foreach P (E \u F) = (foreach P E /\ foreach P F).
Axiom foreach_single_eq : forall A (P:A->Prop) (X:A),
  foreach P (\{X}:set A) = P X.
(* new versions *)


Hint Rewrite foreach_union_eq : rew_foreach.
Tactic Notation "rew_foreach" hyp(H) := autorewrite with rew_foreach in H.
Tactic Notation "rew_foreach" := autorewrite with rew_foreach.

Tactic Notation "rew_foreach" "~" constr(H) :=
  rew_foreach H; auto~.
Tactic Notation "rew_foreach" "*" constr(H) :=
  rew_foreach H; auto*.


(*--------------------------------------------------------*)
(* ** [xapply_old] *)

Ltac xapply_old_of_core H cont :=
   let arity_goal := spec_goal_arity tt in
   let arity_hyp := spec_term_arity H in
   let lemma := get_spec_elim_x_y arity_hyp arity_goal in
   eapply lemma; [ apply H | instantiate; cont tt ].

Ltac xapply_old_core cont := (* todo: cut in pieces *)
  let f := spec_goal_fun tt in
  first [ let H := get_spec_hyp f in 
          first [ xapply_old_of_core H cont | fail 2 ]
        | let H := get_app_hyp f in 
          let n := spec_term_arity H in
          let m := spec_goal_arity tt in
          let W := get_app_weaken_x n in
          let L := get_app_intro_x_y n m in
          first [ apply L; first [ sapply H
                                 | substs; sapply H
                (* todo: apply H modulo equality on arguments *)
                                 | eapply W; [ sapply H | ] ]; 
                  try cont tt
                | fail 2 ]
          (* limitation: continuation applied on premises of H *)
        | xfind f; let H := fresh in 
          intro H; xapply_old_of_core H cont; clear H
        | fail 1 "cannot find a specification" ].

(* old
Ltac xapply_old_core cont :=
  let f := spec_goal_fun tt in
  first [ let H := get_spec_hyp f in 
          first [ xapply_old_of_core H cont | fail 2 ]
        | xfind f; let H := fresh in 
          intro H; xapply_old_of_core H cont; clear H
        | fail 1 "cannot find a specification" ].
*)

Ltac xapply_old_pre := 
  match ltac_get_tag tt with
  | tag_apply => xuntag tag_apply
  | tag_let => xlet; xuntag tag_apply
  end.  

Tactic Notation "xapply_old" "by" tactic(cont) := 
   xapply_old_pre; xapply_old_core cont.
Tactic Notation "xapply_old" constr(H) "by" tactic(cont) :=
   xapply_old_pre; xapply_old_of_core H cont.
Tactic Notation "xapply_old" := 
   xapply_old by (fun _ => idtac).
Tactic Notation "xapply_old" constr(H) :=
   xapply_old H by (fun _ => idtac).



(*--------------------------------------------------------*)
(* ** [xapp_old] *)

Tactic Notation "xapp_old" := 
  xapply_old by (fun _ => xweak).
Tactic Notation "xapp_old" "as" :=
  xapply_old by (fun _ => xweak as).
Tactic Notation "xapp_old" "as" ident(x) :=
  xapply_old by (fun _ => xweak as x).
Tactic Notation "xapp_old" "as" ident(x) ident(Hx) := 
  xapply_old by (fun _ => xweak as x Hx).
Tactic Notation "xapp_olds" := 
  xapply_old by (fun _ => xweaks).

Tactic Notation "xapp_old" constr(S) := 
  xapply_old S by (fun _ => xweak).
Tactic Notation "xapp_old" constr(S) "as" :=
  xapply_old S by (fun _ => xweak as).
Tactic Notation "xapp_old" constr(S) "as" ident(x) :=
  xapply_old by (fun _ => xweak as x).
Tactic Notation "xapp_old" constr(S) "as" ident(x) ident(Hx) := 
  xapply_old S by (fun _ => xweak as x Hx).
Tactic Notation "xapp_olds" constr(S) := 
  xapply_old S by (fun _ => xweaks).

Tactic Notation "xapp_old" "~" := xapp_old; xauto~.
Tactic Notation "xapp_old" "*" := xapp_old; xauto*.
Tactic Notation "xapp_olds" "~" := xapp_olds; xauto~.
Tactic Notation "xapp_olds" "*" := xapp_olds; xauto*.
Tactic Notation "xapp_old" "~" "as" ident(x) := xapp_old as x; auto~.
Tactic Notation "xapp_old" "*" "as" ident(x) := xapp_old as x; auto*.
Tactic Notation "xapp_old" "~" constr(S) := xapp_old S; xauto~.
Tactic Notation "xapp_old" "*" constr(S) := xapp_old S; xauto*.
Tactic Notation "xapp_olds" "~" constr(S) := xapp_olds S; xauto~.
Tactic Notation "xapp_olds" "*" constr(S) := xapp_olds S; xauto*.
Tactic Notation "xapp_old" "~" constr(S) "as" ident(x) := xapp_old S as x; xauto~.
Tactic Notation "xapp_old" "*" constr(S) "as" ident(x) := xapp_old S as x; xauto*.

(************************************************************)
(* ** [xcmp] -- TODO: doc *)

Tactic Notation "xcmp" "as" ident(x) :=
  let Px := fresh "TEMP" in 
  let R1 := fresh "R1" x in let R2 := fresh "R2" x in
  xlet as x Px; [ xapp_old | instantiate; destruct Px as [R1 R2]; xif ]. 

Tactic Notation "xcmp" :=
  let x := fresh "r" in xcmp as x.
Ltac get_spec_elim_x_y x y :=
  match constr:(x,y) with
     | (1%nat,1%nat) => constr:(spec_elim_1_1)
     | (1%nat,2%nat) => constr:(spec_elim_1_2)
     | (1%nat,3%nat) => constr:(spec_elim_1_3)
     | (1%nat,4%nat) => constr:(spec_elim_1_4)
     | (2%nat,1%nat) => constr:(spec_elim_2_1)
     | (2%nat,2%nat) => constr:(spec_elim_2_2)
     | (2%nat,3%nat) => constr:(spec_elim_2_3)
     | (2%nat,4%nat) => constr:(spec_elim_2_4)
     | (3%nat,1%nat) => constr:(spec_elim_3_1)
     | (3%nat,2%nat) => constr:(spec_elim_3_2)
     | (3%nat,3%nat) => constr:(spec_elim_3_3)
     | (3%nat,4%nat) => constr:(spec_elim_3_4)
     | (4%nat,1%nat) => constr:(spec_elim_4_1)
     | (4%nat,2%nat) => constr:(spec_elim_4_2)
     | (4%nat,3%nat) => constr:(spec_elim_4_3)
     | (4%nat,4%nat) => constr:(spec_elim_4_4)
   end.


(*
Ltac xapp_cont_r_with E solver := (* todo factorize with above *)
  let R := fresh "R" in let HR := fresh "HR" in intros R HR;
  instantiate; cbv beta in HR;    (*needs instantiate?*)
  match list_boxer_of E with
  | (>>>) => sapply HR; clear R HR; solver tt
  | ?E' => applys (boxer HR :: E'); try clear R HR; solver tt
  | _ => idtac
  end.

Ltac xapp_cont_r_with E solver := (* todo factorize with above *)
  let R := fresh "R" in let HR := fresh "HR" in intros R HR;
  instantiate; cbv beta in HR;    (*needs instantiate?*)
  match list_boxer_of E with
  | (>>>) => sapply HR; clear R HR; solver tt
  | ?E' => applys (boxer HR :: E'); try clear R HR; solver tt
  | ?E' => let M := fresh "TEMP" in forwards: (boxer HR :: E'); 
     match goal with
     | |- R _ => first [ apply M | fail 1 ]
     | |- _ => try clear R HR; solver tt
     end
  | _ => idtac
  end.
todo: check next version always ok *)



