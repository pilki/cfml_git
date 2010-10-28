Set Implicit Arguments.
Require Export LibInt CFSpec CFPrint.


(********************************************************************)
(* ** Tactics *)

(*--------------------------------------------------------*)
(* ** Tools for specifications *)

(** [spec_fun_arity S] returns the function which is being
    specified or reasoned about in the term [S], together
    with its arity, as a pair [(n,f)]. The tactic [spec_fun S]
    returns only the function [f], while the tactic [spec_arity S] 
    returns only the arity [n]. *)

Ltac spec_fun_arity S :=
  match S with 
  | spec_1 _ ?f => constr:(1%nat,f)
  | spec_2 _ ?f => constr:(2%nat,f)
  | spec_3 _ ?f => constr:(3%nat,f)
  | spec_4 _ ?f => constr:(4%nat,f)
  | app_1 ?f _ _ _ => constr:(1%nat,f)
  | app_2 ?f _ _ _ _ => constr:(2%nat,f)
  | app_3 ?f _ _ _ _ _ => constr:(3%nat,f)
  | app_4 ?f _ _ _ _ _ _ => constr:(4%nat,f)
  | curried_1 _ _ ?f => constr:(1%nat,f)
  | curried_2 _ _ _ ?f => constr:(2%nat,f)
  | curried_3 _ _ _ _ ?f => constr:(3%nat,f)
  | curried_4 _ _ _ _ _ ?f => constr:(4%nat,f)
  | context [ spec_1 _ ?f ] => constr:(1%nat,f)
  | context [ spec_2 _ ?f ] => constr:(2%nat,f)
  | context [ spec_3 _ ?f ] => constr:(3%nat,f)
  | context [ spec_4 _ ?f ] => constr:(4%nat,f)
  | context [ app_1 ?f _ _ _ ] => constr:(1%nat,f)
  | context [ app_2 ?f _ _ _ _ ] => constr:(2%nat,f)
  | context [ app_3 ?f _ _ _ _ _ ] => constr:(3%nat,f)
  | context [ app_4 ?f _ _ _ _ _ _ ] => constr:(4%nat,f)
  end. 

Ltac spec_fun S :=
  match spec_fun_arity S with (_,?f) => constr:(f) end.

Ltac spec_arity S :=
  match spec_fun_arity S with (?n,_) => constr:(n) end.

(** [spec_term_arity] is similar to [spec_arity] except that
    it can perform one step of unfolding in order to get to
    a form on which [spec_arity] can succeed. *)

Ltac spec_term_arity T := 
  let S := type of T in
  match tt with
  | tt => spec_arity S 
  | _ => let h := get_head S in 
         let S' := (eval unfold h in S) in
         spec_arity S'
         (* todo: several unfold: call spec_term_arity T' -- check no loop *)
  end.

(** [spec_goal_fun] and [spec_goal_arity] are specialized versions
   of [spec_fun] and [spec_arity] that apply to the current goal *)

Ltac spec_goal_fun tt :=
  match goal with |- ?S => spec_fun S end.

Ltac spec_goal_arity tt :=
  match goal with |- ?S => spec_arity S end.

(** [get_spec_hyp f] returns the hypothesis that contains a 
    specification for the function [f]. *)

Ltac get_spec_hyp f :=
  match goal with 
  | H: context [ spec_1 _ f ] |- _ => constr:(H)
  | H: context [ spec_2 _ f ] |- _ => constr:(H)
  | H: context [ spec_3 _ f ] |- _ => constr:(H) 
  | H: context [ spec_4 _ f ] |- _ => constr:(H) 
  | H: ?P f |- _ => constr:(H) (* todo: higher order pattern *)
  | H: context [ ?P f ] |- _ => constr:(H)
  end.

(** [get_app_hyp f] returns the hypothesis that contains
    a proposition regarding an application of [f] to arguments *)

Ltac get_app_hyp f :=
  match goal with
  | H: context [ app_1 f _ _ ] |- _ => constr:(H)
  | H: context [ app_2 f _ _ _ ] |- _ => constr:(H)
  | H: context [ app_3 f _ _ _ _ ] |- _ => constr:(H) 
  | H: context [ app_4 f _ _ _ _ ] |- _ => constr:(H) 
  end.

(*--------------------------------------------------------*)
(* ** Return lemmas from [FuncDefs] depending on the arity *)

(** Returns the lemma [app_spec_n] *)

Ltac get_app_spec_x n :=
  match n with
  | 1%nat => constr:(app_spec_1)
  | 2%nat => constr:(app_spec_2)
  | 3%nat => constr:(app_spec_3)
  end.

(** Returns the lemma [spec_elim_n_m] *)

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

(** Returns the lemma [spec_intro_n] *)

Ltac get_spec_intro_x x :=
  match x with
     | 1%nat => constr:(spec_intro_1)
     | 2%nat => constr:(spec_intro_2)
     | 3%nat => constr:(spec_intro_3)
     | 4%nat => constr:(spec_intro_4)
  end.

(** Returns the lemma [spec_weaken_n] *)

Ltac get_spec_weaken_x x :=
  match x with
     | 1%nat => constr:(spec_weaken_1)
     | 2%nat => constr:(spec_weaken_2)
     | 3%nat => constr:(spec_weaken_3)
     | 4%nat => constr:(spec_weaken_4)
  end.

(** Returns the lemma [get_app_intro_n_m] *)

Lemma id_proof : forall (P:Prop), P -> P.
Proof. auto. Qed.

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

(*--------------------------------------------------------*)
(* ** tools for post-conditions *)

Ltac post_is_meta tt :=
  match goal with |- ?E => 
  match get_fun_arg E with (_,?Q) =>
  match Q with
  | Q => constr:(false) 
  | _ => constr:(true)
  end end end.

(*--------------------------------------------------------*)
(* ** [xclean] *)

(** [xclean] performs some basic simplification is the
    context in order to beautify hypotheses that have been 
    inferred. *)

Ltac xclean_core :=
  calc_partial_eq tt; 
  repeat fix_bool_of_known tt;
  fold_bool; fold_prop. 

Tactic Notation "xclean" :=
  xclean_core.

(*--------------------------------------------------------*)
(* ** [xok] *)

Ltac xok_core cont := 
  solve [ cbv beta; apply rel_le_refl
        | apply pred_le_refl
        | hextract; hsimpl; cont tt ].

Tactic Notation "xok" := 
  xok_core ltac:(idcont).
Tactic Notation "xok" "~" := 
  xok_core ltac:(fun _ => auto~).
Tactic Notation "xok" "*" := 
  xok_core ltac:(fun _ => auto*).


(*--------------------------------------------------------*)
(* ** [xauto] *)

(* [xauto] is a specialized version of [auto] that works
   well in program verification. One of its main strength
   is the ability to perform substitution before calling auto. *)

Ltac math_0 ::= xclean.

Ltac check_not_a_tag tt :=
  match goal with 
  | |- tag _ _ _ _ => fail 1 (* todo: not needed? *)
  | |- tag _ _ _ _ _ => fail 1
  | |- _ => idtac
  end.


Ltac xauto_common cont :=
  check_not_a_tag tt;  
  try solve [ cont tt 
            | solve [ apply refl_equal ]
            | xok_core ltac:(fun _ => solve [ cont tt | substs; cont tt ] ) 
            | substs; if_eq; solve [ cont tt | apply refl_equal ]  ].

(* --old
Ltac xauto_common cont :=
  check_not_a_tag tt;  
  try solve [ cont tt 
            | solve [ apply refl_equal ]
            | substs; if_eq; solve [ cont tt | apply refl_equal ] ].
*)

Ltac xauto_tilde_default cont := xauto_common cont.
Ltac xauto_star_default cont := xauto_common cont.

Ltac xauto_tilde := xauto_tilde_default ltac:(fun _ => auto_tilde).
Ltac xauto_star := xauto_star_default ltac:(fun _ => auto_star). 

Tactic Notation "xauto" "~" := xauto_tilde.
Tactic Notation "xauto" "*" := xauto_star.
Tactic Notation "xauto" := xauto~.

Tactic Notation "hsimpl" "~" constr(L) :=
  hsimpl L; xauto~.
Tactic Notation "hsimpl" "~" constr(X1) constr(X2) :=
  hsimpl X1 X2; xauto~.
Tactic Notation "hsimpl" "~" constr(X1) constr(X2) constr(X3) :=
  hsimpl X1 X2 X3; xauto~.


(*--------------------------------------------------------*)
(* ** [xisspec] *)

(** [xisspec] is a helper function to prove a goal of the
    form [is_spec K], which basically amounts to showing
    that [K x1 .. xN] is weakenable. The tactic [intuition eauto]
    called by [xisspec] discharges this obligation is most cases.
    Cases that are not handled by this tactic are typically those
    involving case analysis. *)

Ltac xisspec_core :=
  solve [ intros_all; unfolds rel_le, pred_le; auto; auto* ].

Tactic Notation "xisspec" :=
  check_noevar_goal; xisspec_core.


(*--------------------------------------------------------*)
(* ** [xlocal] *)

Ltac xlocal_core tt ::=
  first [ assumption
 	| apply local_is_local 
        | apply app_local_1
   (* not needed
        | apply app_local_2
        | apply app_local_3
        | apply app_local_4 *) ].

Tactic Notation "xlocal" :=
  xlocal_core tt.


(*--------------------------------------------------------*)
(* ** [xcf] *)

(** [xcf] applies to a goal of the form [Spec_n f K]
    and uses the characteristic formula known for [f]
    in order to get started proving the goal. *)

Ltac remove_head_unit tt :=
  repeat match goal with 
  | |- unit -> _ => intros _
  end.

Ltac xcf_post tt :=
  cbv beta; remove_head_unit tt.

Ltac solve_type :=
  match goal with |- Type => exact unit end.

Ltac xcf_for_core f :=
  ltac_database_get database_cf f;
  let H := fresh "TEMP" in intros H; 
  match type of H with
  | @tag tag_top_fun _ _ _ => sapply H; instantiate; try solve_type; [ try xisspec | ]
  | _ => sapply H; try solve_type
  end; clear H; xcf_post tt.

Ltac xcf_core :=
  intros; first 
  [ let f := spec_goal_fun tt in xcf_for_core f 
  | match goal with |- ?f = _ => xcf_for_core f end ].

Tactic Notation "xcf" constr(f) := xcf_for_core f.
Tactic Notation "xcf" := xcf_core.

(** [xcf_app] applies to a goal of the form 
    [app_n f x1 .. xN P], and exploits the characteristic
    formula for [f] in order to get started proving the goal. *)

Ltac intro_subst_arity n :=
  let x1 := fresh "TEMP" in let x2 := fresh "TEMP" in
  let x3 := fresh "TEMP" in let x4 := fresh "TEMP" in 
  let H1 := fresh "TEMP" in let H2 := fresh "TEMP" in
  let H3 := fresh "TEMP" in let H4 := fresh "TEMP" in
  match n with
  | 1%nat => intros x1 H1; subst x1
  | 2%nat => intros x1 x2 H1 H2; subst x1 x2
  | 3%nat => intros x1 x2 x3 H1 H2 H3; subst x1 x2 x3
  | 4%nat => intros x1 x2 x3 x4 H1 H2 H3 H4; subst x1 x2 x3 x4
  end.

Ltac xcf_app_core :=
  let n := spec_goal_arity tt in 
  let H := get_app_spec_x n in
  apply H; xcf_core; try intro_subst_arity n.

Tactic Notation "xcf_app" := xcf_app_core.


(*--------------------------------------------------------*)
(* ** [xfind] *)

Ltac xfind_db f :=
  ltac_database_get database_spec f.

Ltac xfind_ctx f :=
  let H := get_spec_hyp f in generalize H.

(** [xfind f] displays the specification registered with [f],
    (by inserting it as new hypothesis at head of the goal). *)

Tactic Notation "xfind" constr(f) :=  
  first [ xfind_ctx f | xfind_db f ].

(** [xfind] without argument calls [xfind f] for the function
    [f] that appear in the current goal *)

Tactic Notation "xfind" := 
  let f := spec_goal_fun tt in xfind f.


(*--------------------------------------------------------*)
(* ** [xcurried] *)

(** [xcurried] helps proving a goal of the form [curried_n f],
    by proving that [f] admits [True] as post-condition.
    The latter proof is set up by invoking the characteristic
    formula for [f]. *)

Ltac xcurried_core :=
  unfold curried_1, curried_2, curried_3, curried_4;
  try solve [ xcf; auto ].
  (*  let arity := spec_goal_arity tt in *)

Tactic Notation "xcurried" := xcurried_core.

(*--------------------------------------------------------*)
(* ** [xextract], [xsimpl] *)

Ltac xextract_core :=
  simpl; hclean; instantiate.

(* todo: use continuations *)
Tactic Notation "xextract" := 
  xextract_core; xclean.
Tactic Notation "xextract" "as" simple_intropattern(I1) := 
  xextract; intros I1; xclean.
Tactic Notation "xextract" "as" simple_intropattern(I1) simple_intropattern(I2) := 
  xextract; intros I1 I2; xclean. 
Tactic Notation "xextract" "as" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) := 
  xextract; intros I1 I2 I3; xclean.
Tactic Notation "xextract" "as" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) simple_intropattern(I4) := 
  xextract; intros I1 I2 I3 I4; xclean.
Tactic Notation "xextract" "as" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5) := 
  xextract; intros I1 I2 I3 I4 I5; xclean.
Tactic Notation "xextract" "as" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) := 
  xextract; intros I1 I2 I3 I4 I5 I6; xclean.
Tactic Notation "xextract" "as" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) := 
  xextract; intros I1 I2 I3 I4 I5 I6 I7; xclean.

Tactic Notation "xsimpl" := try hextract; try hsimpl.
Tactic Notation "xsimpl" "~" := xsimpl; xauto~.
Tactic Notation "xsimpl" "*" := xsimpl; xauto*.


(*--------------------------------------------------------*)
(* ** [xlet] *)

(** [xlet] is used to reason on a let-node, i.e. on a goal
    of the form [(Let x := Q1 in Q2) P]. The general form
    is [xlet Q as y], where [y] is the name to be used
    in place of [x].
    The arguments are optional, so the following forms are
    allowed: [xlet], [xlet as x], [xlet Q], [xlet Q as x]. *)

Ltac xlet_core cont0 cont1 cont2 :=
  apply local_erase; cont0 tt; split; [ | cont1 tt; cont2 tt ].

Tactic Notation "xlet_def" tactic(c0) tactic(c1) tactic(c2) :=
  xlet_core ltac:(c0) ltac:(c1) ltac:(c2).

Tactic Notation "xlet" constr(Q) "as" ident(x) :=
  xlet_def (fun _ => exists Q) (fun _ => intros x) (fun _ => try xextract).
Tactic Notation "xlet" constr(Q) :=
  xlet_def (fun _ => exists Q) (fun _ => intro) (fun _ => try xextract).
Tactic Notation "xlet" "as" ident(x) :=
  xlet_def (fun _ => esplit) (fun _ => intros x) (fun _ => idtac).
Tactic Notation "xlet" :=
  xlet_def (fun _ => esplit) (fun _ => intro) (fun _ => idtac).

Tactic Notation "xseq" constr(H) :=
  xlet_def (fun _ => exists H) (fun _ => idtac) (fun _ => try xextract).
Tactic Notation "xseq" :=
  xlet_def (fun _ => esplit) (fun _ => idtac) (fun _ => idtac).

Tactic Notation "xlet" "~" := xlet; auto~. (*todo: xauto ! *)
Tactic Notation "xlet" "~" "as" ident(x) := xlet as x; auto~.
Tactic Notation "xseq" "~" := xseq; auto~. (*todo: xauto ! *)
Tactic Notation "xlet" "~" constr(Q) := xlet Q; auto~.
Tactic Notation "xlet" "~" constr(Q) "as" ident(x) := xlet Q as x; auto~.
Tactic Notation "xseq" "~" constr(H) := xseq H; auto~.
Tactic Notation "xlet" "*" := xlet; auto*.
Tactic Notation "xlet" "*" "as" ident(x) := xlet as x; auto*.
Tactic Notation "xseq" "*" := xseq; auto*. (*todo: xauto ! *)
Tactic Notation "xlet" "*" constr(Q) := xlet Q; auto*.
Tactic Notation "xlet" "*" constr(Q) "as" ident(x) := xlet Q as x; auto*.
Tactic Notation "xseq" "*" constr(H) := xseq H; auto*.


(*--------------------------------------------------------*)
(* ** [xval] *)

(** [xval] is used to reason on a let-node binding a value. *)

Tactic Notation "xval" "as" ident(x) ident(Hx) :=
  intros x Hx.

Tactic Notation "xval" "as" ident(x) :=
  let Hx := fresh "P" x in xval as x Hx.

Tactic Notation "xval" :=
  intro; let x := get_last_hyp tt in revert x; xval as x.

(** [xvals] substitutes the bound value right away. *)

Tactic Notation "xvals" :=
  intro; intro_subst.

(** [xval_st P] is used to assign an abstract specification to the value *)

Tactic Notation "xval_st" constr(P) "as" ident(x) ident(Hx) :=
  intros x; asserts Hx: (P x); [ intro_subst | intros _ ].

Tactic Notation "xval_st" constr(P) "as" ident(x) :=
  let Hx := fresh "P" x in xval_st P as x Hx.

Tactic Notation "xval_st" constr(P) :=
  intro; let x := get_last_hyp tt in revert x; xval_st P as x.


(*--------------------------------------------------------*)
(* ** [xfail], [xdone] *)

(** [xfail] simplifies a proof obligation of the form [Fail],
    which is in fact equivalent to [False].
    [xfail_noclean] is also available. *)

Tactic Notation "xfail_noclean" :=
  xuntag tag_fail; apply local_erase.
Tactic Notation "xfail" := 
  xfail_noclean; xclean.
Tactic Notation "xfail" "~" :=  
  xfail; xauto~.
Tactic Notation "xfail" "*" :=  
  xfail; xauto*.

(** [xdone] proves a goal of the form [Done],
    which is in fact equivalent to [True]. *)

Tactic Notation "xdone" :=
  xuntag tag_done; apply local_erase; split.


(*--------------------------------------------------------*)
(* ** [xret] *)

(** [xret]. *)

Ltac xret_gc :=
  eapply xret_gc_lemma.

Ltac xret_core :=
  first [ apply xret_lemma_unify
        | apply xret_lemma ].

Ltac xret_pre cont := 
  cont tt.

(* todo: special treatment of xlet/xret
Ltac xret_pre cont := 
  match ltac_get_tag tt with
  | tag_ret => cont tt
  | tag_let_pure => xlet; [ cont tt | instantiate ]
  end. *)

Tactic Notation "xret_noclean" := 
  xret_pre ltac:(fun _ => xret_core).
Tactic Notation "xret" := 
  xret_pre ltac:(fun _ => xret_core; xclean).
Tactic Notation "xret" "~" :=  
  xret; xauto~.
Tactic Notation "xret" "*" :=  
  xret; xauto*.

(*--------------------------------------------------------*)
(* ** [xpost] *)

Tactic Notation "xpost" :=
  eapply xpost_lemma; [ try xlocal | | ].

(*--------------------------------------------------------*)
(* ** [xgc] *)

(* bin
Ltac xgc_if_post_meta tt :=
  match post_is_meta tt with
  | false => xgc
  | true => idtac
  end.
*)

Ltac xgc_core :=
  eapply local_gc_post; 
  [ xlocal | | ].

Ltac xgc_remove_core H :=
  eapply local_gc_pre with (HG := H);
    [ try xlocal
    | hsimpl
    | ].

Ltac xgc_keep_core H :=
  eapply local_gc_pre with (H' := H);
    [ try xlocal
    | hsimpl
    | ].

Tactic Notation "xgc" constr(H) := 
  xgc_remove_core H.

Tactic Notation "xgc" "-" constr(H) := 
  xgc_keep_core H.

Tactic Notation "xgc" := 
  xgc_core.

Tactic Notation "xgc_all" := 
  eapply local_gc_pre_all; [ try xlocal | ].


(*--------------------------------------------------------*)
(* ** [xframe] *)

Ltac xframe_remove_core H :=
  eapply xframe_lemma with (H2 := H);
    [ try xlocal
    | hsimpl
    | 
    | ].

Ltac xframe_keep_core H :=
  eapply xframe_lemma with (H1 := H);
    [ try xlocal
    | hsimpl
    | 
    | ].

Tactic Notation "xframe" constr(H) := 
  xframe_remove_core H.

Tactic Notation "xframe" "-" constr(H) := 
  xframe_keep_core H.


(*--------------------------------------------------------*)
(* ** [xchange] *)


Ltac xchange_apply L cont :=
   eapply xchange_lemma; 
     [ try xlocal | applys L | cont tt | ].

(* note: modif should be himpl_proj1 or himpl_proj2 *)
Ltac xchange_forwards L modif cont :=
  forwards_nounfold_then L ltac:(fun K =>
  match modif with
  | __ => 
     match type of K with
     | _ = _ => xchange_apply (@pred_le_proj1 _ _ _ K) cont
     | _ => xchange_apply K cont
     end
  | _ => xchange_apply (@modif _ _ _ K) cont
  end).

Ltac xchange_with_core H H' :=
  eapply xchange_lemma with (H1:=H) (H1':=H'); 
    [ try xlocal | | hsimpl | ].

Ltac xchange_core E modif :=
  match E with
  | ?H ==> ?H' => xchange_with_core H H'
  | _ => xchange_forwards E modif ltac:(fun _ => instantiate; hsimpl)
  end.

Tactic Notation "xchange_debug" constr(E) :=
  xchange_forwards E __ ltac:(idcont).
Tactic Notation "xchange_debug" "->" constr(E) :=
  xchange_forwards E pred_le_proj1 ltac:(idcont).
Tactic Notation "xchange_debug" "<-" constr(E) :=
  xchange_forwards pred_le_proj2 ltac:(idcont).

Tactic Notation "xchange" constr(E) :=
  xchange_core E __.
Tactic Notation "xchange" "->" constr(E) :=
  xchange_core E pred_le_proj1.
Tactic Notation "xchange" "<-" constr(E) :=
  xchange_core E pred_le_proj2.



Tactic Notation "xchange" constr(E) "as" := 
  xchange E; try xextract.
Tactic Notation "xchange" constr(E) "as" simple_intropattern(I1) := 
  xchange E; try xextract as I1.
Tactic Notation "xchange" constr(E) "as" simple_intropattern(I1) simple_intropattern(I2) := 
  xchange E; try xextract as I1 I2.
Tactic Notation "xchange" constr(E) "as" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) := 
  xchange E; try xextract as I1 I2 I3.
Tactic Notation "xchange" constr(E) "as" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) := 
  xchange E; try xextract as I1 I2 I3 I4. 
Tactic Notation "xchange" constr(E) "as" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5) := 
  xchange E; try xextract as I1 I2 I3 I4 I5. 

Tactic Notation "xchange" "~" constr(E) :=
  xchange E; auto_tilde.
Tactic Notation "xchange" "~" constr(E) "as" := 
  xchange~ E; try xextract.
Tactic Notation "xchange" "~" constr(E) "as" simple_intropattern(I1) := 
  xchange~ E; try xextract as I1.
Tactic Notation "xchange" "~" constr(E) "as" simple_intropattern(I1) simple_intropattern(I2) := 
  xchange~ E; try xextract as I1 I2.
Tactic Notation "xchange" "~" constr(E) "as" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) := 
  xchange~ E; try xextract as I1 I2 I3.
Tactic Notation "xchange" "~" constr(E) "as" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) := 
  xchange~ E; try xextract as I1 I2 I3 I4. 
Tactic Notation "xchange" "~" constr(E) "as" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5) := 
  xchange~ E; try xextract as I1 I2 I3 I4 I5. 



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


(*--------------------------------------------------------*)
(* ** [xapp] *)

Ltac xapp_show_spec := 
  xuntag; let f := spec_goal_fun tt in
  xfind f; let H := fresh in intro H.

(* todo: when arities differ *)

Ltac xapp_compact KR args :=
  let args := ltac_args args in
  match args with (boxer ?mode)::?vs => 
  let args := constr:((boxer mode)::(boxer KR)::vs) in
  constr:(args)
  end.

Ltac xapp_final HR :=
  eapply local_wframe; 
     [ xlocal
     | apply HR
     | hsimpl
     | try xok ].

Ltac xapp_inst args solver :=
  let R := fresh "R" in let LR := fresh "L" R in 
  let KR := fresh "K" R in let IR := fresh "I" R in
  intros R LR KR; hnf in KR; (* lazy beta in *)
  let H := xapp_compact KR args in
  forwards_then H ltac:(fun HR => try xapp_final HR);    
  try clears R; solver tt.
(* todo: should clear R in indirect subgoals *)

Ltac xapp_spec_core H cont :=
   let arity_goal := spec_goal_arity tt in
   let arity_hyp := spec_term_arity H in
   match constr:(arity_goal, arity_hyp) with (?n,?n) => idtac | _ => fail 1 end;
   let lemma := get_spec_elim_x_y arity_hyp arity_goal in
   eapply lemma; [ sapply H | cont tt ]. 

Ltac xapp_manual_intros tt :=
  let R := fresh "R" in let LR := fresh "L" R in 
  let KR := fresh "K" R in intros R LR KR; lazy beta in KR.

   
Ltac xapp_core spec cont :=
  match spec with
  | ___ =>
      let f := spec_goal_fun tt in
      xfind f; let H := fresh in intro H;
      xapp_spec_core H cont; clear H
  | ?H => xapp_spec_core H cont
  end.

Ltac xapp_pre cont :=  (*todo:move xgc*)
  match ltac_get_tag tt with
  | tag_apply => 
    match post_is_meta tt with
    | false => xgc; [ xuntag tag_apply; cont tt | ]
    | true => xuntag tag_apply; cont tt
    end
  | tag_let_trm => xlet; [ xuntag tag_apply; cont tt | instantiate; xextract ]
  | tag_seq => xseq; [ xuntag tag_apply; cont tt | instantiate; xextract ]
  end.

Ltac xapp_then spec cont :=
  xapp_pre ltac:(fun _ => xapp_core spec cont).

Ltac xapp_with spec args solver :=
  xapp_then spec ltac:(fun _ => xapp_inst args solver).

Tactic Notation "xapp" := 
  xapp_with ___ (>>>) ltac:(fun _ => idtac).
Tactic Notation "xapp" constr(E) := 
  xapp_with ___ E ltac:(fun _ => idtac).
Tactic Notation "xapp" constr(E1) constr(E2) := 
  xapp (>>> E1 E2).
Tactic Notation "xapp" constr(E1) constr(E2) constr(E3) := 
  xapp (>>> E1 E2 E3).
Tactic Notation "xapp" constr(E1) constr(E2) constr(E3) constr(E4) := 
  xapp (>>> E1 E2 E3 E4).
Tactic Notation "xapp" constr(E1) constr(E2) constr(E3) constr(E4) constr(E5) := 
  xapp (>>> E1 E2 E3 E4 E5).

Tactic Notation "xapp" "~" := 
  xapp_with ___ (>>>) ltac:(fun _ => xauto~). (* ; xauto~.*)
Tactic Notation "xapp" "~" constr(E) := 
  xapp_with ___ E ltac:(fun _ => xauto~).
Tactic Notation "xapp" "~" constr(E1) constr(E2) := 
  xapp~ (>>> E1 E2).
Tactic Notation "xapp" "~" constr(E1) constr(E2) constr(E3) := 
  xapp~ (>>> E1 E2 E3).
Tactic Notation "xapp" "~" constr(E1) constr(E2) constr(E3) constr(E4) := 
  xapp~ (>>> E1 E2 E3 E4).
Tactic Notation "xapp" "~" constr(E1) constr(E2) constr(E3) constr(E4) constr(E5) :=
   xapp~ (>>> E1 E2 E3 E4 E5).

Tactic Notation "xapp" "*" := 
  xapp_with ___ (>>>) ltac:(fun _ => xauto*).
Tactic Notation "xapp" "*" constr(E) := 
  xapp_with ___ E ltac:(fun _ => xauto*).
Tactic Notation "xapp" "*" constr(E1) constr(E2) := 
  xapp* (>>> E1 E2).
Tactic Notation "xapp" "*" constr(E1) constr(E2) constr(E3) := 
  xapp* (>>> E1 E2 E3).
Tactic Notation "xapp" "*" constr(E1) constr(E2) constr(E3) constr(E4) := 
  xapp* (>>> E1 E2 E3 E4).
Tactic Notation "xapp" "*" constr(E1) constr(E2) constr(E3) constr(E4) constr(E5) :=
   xapp* (>>> E1 E2 E3 E4 E5).

Tactic Notation "xapp_spec" constr(H) := 
  xapp_with H (>>>) ltac:(fun _ => idtac).
Tactic Notation "xapp_spec" constr(H) constr(E) := 
  xapp_with H E ltac:(fun _ => idtac).
Tactic Notation "xapp_spec" "~" constr(H) := 
  xapp_with H (>>>) ltac:(fun _ => xauto~). (* ; xauto~.*)
Tactic Notation "xapp_spec" "~" constr(H) constr(E) := 
  xapp_with H E ltac:(fun _ => xauto~).
Tactic Notation "xapp_spec" "*" constr(H) := 
  xapp_with H (>>>) ltac:(fun _ => xauto*).
Tactic Notation "xapp_spec" "*" constr(H) constr(E) := 
  xapp_with H E ltac:(fun _ => xauto*).

Tactic Notation "xapp_manual" := 
  xapp_then ___ ltac:(xapp_manual_intros).
Tactic Notation "xapp_spec_manual" constr(H) := 
  xapp_then H ltac:(xapp_manual_intros).
Tactic Notation "xapp_manual" "as" := 
  xapp_then ___ ltac:(fun _ => idtac).
Tactic Notation "xapp_spec_manual" constr(H) "as" := 
  xapp_then H ltac:(fun _ => idtac).

Tactic Notation "xapp" "as" simple_intropattern(x) :=
  xlet as x; [ xapp | instantiate; xextract ].

Ltac xapps_core spec args solver :=
  let cont tt := 
    xapp_inst args solver in
  match ltac_get_tag tt with
  | tag_let_trm => xlet; [ xuntag tag_apply; cont tt | instantiate; xextract; intro_subst ]
  | tag_seq =>     xseq; [ xuntag tag_apply; cont tt | instantiate; xextract; intro_subst ]
  end.

Tactic Notation "xapps" := 
  xapps_core ___ (>>>) ltac:(fun _ => idtac).
Tactic Notation "xapps" constr(E) := 
  xapps_core ___ E ltac:(fun _ => idtac).
Tactic Notation "xapps" constr(E1) constr(E2) := 
  xapps_core (>>> E1 E2).
Tactic Notation "xapps" constr(E1) constr(E2) constr(E3) := 
  xapps_core (>>> E1 E2 E3).
Tactic Notation "xapps" constr(E1) constr(E2) constr(E3) constr(E4) := 
  xapps_core (>>> E1 E2 E3 E4).
Tactic Notation "xapps" constr(E1) constr(E2) constr(E3) constr(E4) constr(E5) := 
  xapps_core (>>> E1 E2 E3 E4 E5).

Tactic Notation "xapps" "~" := 
  xapps; auto_tilde.
Tactic Notation "xapps" "*" := 
  xapps; auto_star.
Tactic Notation "xapps" "~" constr(E) := 
  xapps E; auto_tilde.
Tactic Notation "xapps" "*" constr(E) := 
  xapps E; auto_star.

(* todo: when hypothesis in an app instance *)

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

*)

(*--------------------------------------------------------*)
(* ** [xinduction] *)

(** [xinduction E] applies to a goal of the form 
    [Spec_n f (fun x1 .. xN R => forall x0, L x0 x1 xN R)] 
    and replaces it with a weaker goal, which describes the same
    specification but including an induction hypothesis. 
    The argument [E] describes the termination arguments. 
    If [f] has type [A1 -> .. -> AN -> B], then [E] should be one of
    - a measure of type [A0*A1*..*AN -> nat] 
    - a binary relation of type [A0*A1*..*AN -> A1*..*AN -> Prop] 
    - a proof that a well-foundedness for such a relation.
    
    Measures and binary relations can also be provided in
    a curried fashion, at type [A0 -> A1 -> .. -> AN -> nat] and
    [A0 -> A0 -> A1 -> A1 -> A2 -> A2 -> .. -> AN -> AN -> Prop], respectively.
    
    The combinators [unprojNK] are useful for building new binary
    relations. For example, if [R] has type [A->A->Prop], then
    [unproj21 B R] has type [A*B -> A*B -> Prop] and compares pairs
    with respect to their first component only, using [R]. *)

(* todo: reimplement using  goal_arity and options *)

Ltac xinduction_base_lt lt :=
  first   
    [ apply (spec_induction_1 (lt:=lt))
    | apply (spec_induction_2 (lt:=lt))
    | apply (spec_induction_3 (lt:=lt)) 
    | apply (spec_induction_4 (lt:=lt))
    | apply (spec_induction_2 (lt:=uncurryp2 lt))
    | apply (spec_induction_3 (lt:=uncurryp3 lt))
    | apply (spec_induction_4 (lt:=uncurryp4 lt)) 
    | apply (spec_induction_1_noarg (lt:=lt)) ];
  [ try prove_wf | try xisspec | unfolds_wf ].

Ltac xinduction_base_wf wf :=
  first   
    [ apply (spec_induction_1 wf)
    | apply (spec_induction_2 wf)
    | apply (spec_induction_3 wf) 
    | apply (spec_induction_4 wf) 
    | apply (spec_induction_1_noarg wf) ];
   [ try xisspec | unfolds_wf ].

Ltac xinduction_base_measure m :=
  first   
    [ apply (spec_induction_1 (measure_wf m))
    | apply (spec_induction_2 (measure_wf m))
    | apply (spec_induction_3 (measure_wf m))
    | apply (spec_induction_4 (measure_wf m))
    | apply (spec_induction_2 (measure_wf (uncurry2 m)))
    | apply (spec_induction_3 (measure_wf (uncurry3 m)))
    | apply (spec_induction_3 (measure_wf (uncurry4 m)))
    | apply (spec_induction_1_noarg (measure_wf m)) ];
    [ try xisspec | unfolds_wf; unfold measure ].

Tactic Notation "xinduction_heap" constr(arg) :=
  first [ xinduction_base_lt arg
        | xinduction_base_wf arg
        | xinduction_base_measure arg ].


Ltac xinduction_noheap_base_lt lt :=
  first   
    [ apply (spec_induction_1_noheap (lt:=lt))
    | apply (spec_induction_2_noheap (lt:=lt))
    | apply (spec_induction_3_noheap (lt:=lt)) 
    | apply (spec_induction_4_noheap (lt:=lt)) 
    | apply (spec_induction_2_noheap (lt:=uncurryp2 lt))
    | apply (spec_induction_3_noheap (lt:=uncurryp3 lt))
    | apply (spec_induction_4_noheap (lt:=uncurryp4 lt)) ];
  [ try prove_wf | unfolds_wf ].

Ltac xinduction_noheap_base_wf wf :=
  first   
    [ apply (spec_induction_1_noheap wf)
    | apply (spec_induction_2_noheap wf)
    | apply (spec_induction_3_noheap wf) 
    | apply (spec_induction_4_noheap wf) ];
   [ unfolds_wf ].

Ltac xinduction_noheap_base_measure m :=
  first   
    [ apply (spec_induction_1_noheap (measure_wf m))
    | apply (spec_induction_2_noheap (measure_wf m))
    | apply (spec_induction_3_noheap (measure_wf m))
    | apply (spec_induction_4_noheap (measure_wf m))
    | apply (spec_induction_2_noheap (measure_wf (uncurry2 m)))
    | apply (spec_induction_3_noheap (measure_wf (uncurry3 m)))
    | apply (spec_induction_4_noheap (measure_wf (uncurry4 m))) ];
    [ unfolds_wf; unfold measure ].

Tactic Notation "xinduction" constr(arg) :=
  first [ xinduction_noheap_base_lt arg
        | xinduction_noheap_base_wf arg
        | xinduction_noheap_base_measure arg ].


(** Lemmas to set up induction for two mutually-recursive functions. 

Lemma mutual_update_2 : forall (P' Q' P Q : Prop),
  (P' -> P) -> (Q' -> Q) -> (P' /\ Q') -> (P /\ Q).
Proof. auto*. Qed.

Lemma mutual_quantif_2 : forall T (P Q : T -> Prop),
  (forall n, P n /\ Q n) -> (forall n, P n) /\ (forall n, Q n).
Proof. introv H. split; intros; eapply H. Qed.

*)


(*--------------------------------------------------------*)
(* ** [xname_spec] *)

(** [xname_spec s] applies to a goal of the form [Spec_n f K]
    and defines [s] as the predicate [fun f => Spec_n f K]. *)

Tactic Notation "xname_spec" ident(s) :=
  let f := spec_goal_fun tt in pattern f;
  match goal with |- ?S _ => set (s := S) end;
  unfold s.


(*--------------------------------------------------------*)
(* ** [xbody] *)

(** [xbody] applies to a goal of the form 
    [H: (Body f x1 .. xN => Q) |- Spec_n f K]
    where H is the last hypothesis in the goal.
    It applies this hypothesis to prove the goal. 
    Two subgoals are generated. The first one
    is [is_spec_n K], and [xisspec] is called to try and solve it.
    The second one is [forall x1 .. xN, K x1 .. xN Q].
    The arguments are introduces automatically, unless the
    tactic [xbody_nointro] is called.

    The tactic [xbody H] can be used to specify explicitly
    the hypothesis [H] (of the form [Body ..]) to be used for 
    proving a goal [Spec_n f K], and it does not clear [H]. *)

Ltac xbody_core cont :=
   let Bf := fresh "TEMP" in 
   intros Bf; sapply Bf; clear Bf;
   [ try xisspec | cont tt ].

Ltac xbody_pre tt :=
  let H := get_last_hyp tt in generalizes H.

Ltac xbody_base_intro tt :=
  xbody_core ltac:(fun _ => remove_head_unit tt; introv).

Ltac xbody_base_nointro tt :=
  xbody_core ltac:(fun _ => remove_head_unit tt).

Tactic Notation "xbody" :=
  xbody_pre tt; xbody_base_intro tt.
Tactic Notation "xbody_nointro" :=
  xbody_pre tt; xbody_base_nointro tt.

Tactic Notation "xbody" ident(Bf) :=
  generalizes Bf; xbody_base_intro tt.
Tactic Notation "xbody_nointro" ident(Bf) :=
  generalizes Bf; xbody_base_nointro tt.

(* -- todo: add xuntag body *)

(*--------------------------------------------------------*)
(* ** [xfun] *)

(** [xfun S] applies to a goal of the form [LetFunc f := Q1 in Q].
    [S] is the specification for [f1], which should be a predicate
    of type [Val -> Prop]. Typically, [S] takes the form
    [fun f => Spec f K]. By default, the tactic [xbody] is
    called subsequently, so as to exploit the body assumption
    stored in [Q1]. This behaviour can be modified by calling
    [xfun_noxbody S]. The variant [xfun_noxbody S as H] allows to 
    name explicitly the body assumption. *)

Ltac xfun_core s cont :=
  apply local_erase;
  intro; let f := get_last_hyp tt in
  let Sf := fresh "S" f in
  exists s; split; [ cont tt | intros Sf ].

Ltac xfun_namebody tt :=
  let f := get_last_hyp tt in 
  let Bf := fresh "B" f in
  intros Bf.

Tactic Notation "xfun" constr(s) :=
  xfun_core s ltac:(fun _ => first [ xbody_base_intro tt | xfun_namebody tt ] ).
Tactic Notation "xfun_nointro" constr(s) :=
  xfun_core s ltac:(fun _ => first [ xbody_base_nointro tt | xfun_namebody tt ] ).
Tactic Notation "xfun" constr(s) "as" ident(B) :=
  xfun_core s ltac:(fun _ => intros B).
    (* --todo: rename to xfun_noxbody *)
Tactic Notation "xfun_noxbody" constr(s) :=
  xfun_core s ltac:(xfun_namebody).

(** [xfun_mg] is equivalent to [xfun S] where [S] is the most
    general specification that can be provided for the function.
    This specification is simply defined in terms of the 
    body assumption. --todo: be more precise 
    This tactic is useful to simulate the inlining of the 
    function at its call sites, and reason only on particular
    applications of the function. *)

Tactic Notation "xfun_mg" :=
  intro; let f := get_last_hyp tt in let H := fresh "S" f in
  esplit; split; intros H; [ pattern f in H; eexact H | ].

(** [xfun S1 S2] allows to specify a pair of mutually-recursive
    functions, be providng both their specifications. *)

Tactic Notation "xfun" constr(s1) constr(s2) :=
  intro; let f1 := get_last_hyp tt in
  intro; let f2 := get_last_hyp tt in
  let Bf1 := fresh "B" f1 in let Bf2 := fresh "B" f2 in
  let Sf1 := fresh "S" f1 in let Sf2 := fresh "S" f2 in
  exists s1; exists s2; split; [ intros Bf1 Bf2 | intros Sf1 Sf2 ].

  (*--todo: higher degrees *)

(** [xfun_induction S I] is the same as [xfun] except that
    it sets up a proof by induction for a recursive function.
    More precisely, it combines [xfun S] with [xinduction I]. 
    The tactic [xfun_induction_nointro S I] is similar except
    that it does not introduces the arguments of the function. *)
  (* --todo: en général les noms des arguments sont perdus,
       donc le défaut pourrait etre nointro, ou un mode "as" *)
  (* --todo: xfun_induction I S *)

Ltac unfolds_to_spec tt := 
  match goal with 
  | |- spec_1 _ ?f => idtac
  | |- spec_2 _ ?f => idtac
  | |- spec_3 _ ?f => idtac
  | |- spec_4 _ ?f => idtac
  | _ => progress(unfolds); unfolds_to_spec tt
  end. 

(* -- TODO *)

Tactic Notation "xfun_induction" constr(S) constr(I) :=
  xfun_core S ltac:(fun _ => 
    intro; unfolds_to_spec tt; xinduction I; xbody).

Tactic Notation "xfun_induction_nointro" constr(S) constr(I) :=
  xfun_core S ltac:(fun _ => 
    intro; unfolds_to_spec tt; xinduction I; xbody_nointro).

Tactic Notation "xfun_induction_heap" constr(S) constr(I) :=
  xfun_core S ltac:(fun _ => 
    intro; unfolds_to_spec tt; xinduction_heap I; xbody).

Tactic Notation "xfun_induction_heap_nointro" constr(S) constr(I) :=
  xfun_core S ltac:(fun _ => 
    intro; unfolds_to_spec tt; xinduction_heap I; xbody_nointro).



(*--------------------------------------------------------*)
(* ** [xfor] *)

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


Tactic Notation "xgeneralize" constr(E) "as" ident(H) :=
  cuts H: E; [ eapply local_weaken_pre; [xlocal | | ] | ].

Tactic Notation "xgeneralize" constr(E) :=
  let H := fresh "Inv" in xgeneralize E as H.

Ltac xwhile_intros tt :=
  let R := fresh "R" in let LR := fresh "L" R in
  let HR := fresh "H" R in 
  apply local_erase; intros R LR HR.

Ltac xwhile_pre cont :=
  match ltac_get_tag tt with
  | tag_seq => xseq; [ cont tt | ]
  | tag_while => cont tt
  end.

Tactic Notation "xwhile" :=
  xwhile_pre ltac:(fun _ => xwhile_intros tt).
Tactic Notation "xwhile" constr(E) :=
  xwhile_pre ltac:(fun _ => xwhile_intros tt; xgeneralize E).


(*--------------------------------------------------------*)
(* ** [xfor] *)


Ltac xfor_intros tt :=
  let S := fresh "S" in let LS := fresh "L" S in
  let HS := fresh "H" S in 
  apply local_erase; intros S LS HS.

Ltac xfor_pre cont :=
  match ltac_get_tag tt with
  | tag_seq => xseq; [ cont tt | ]
  | tag_for => cont tt
  end.

Tactic Notation "xfor" :=
  xfor_pre ltac:(fun _ => xfor_intros tt).
Tactic Notation "xfor" constr(E) :=
  xfor_pre ltac:(fun _ => xfor_intros tt; xgeneralize E).

Ltac xlocal_core tt ::=
  first [ assumption
 	| apply local_is_local 
        | apply app_local_1 
        | match goal with H: is_local_1 ?S |- is_local (?S _) => apply H end ].



(*--------------------------------------------------------*)
(* ** [xintros] *)

(** [xintros] applies to a goal of the form [Spec_n f K]
    where [K] has the form [fun x1 .. xN R => H R]. 
    It replaces the goal with [H (App_n f x1 .. xN)],
    where [x1 .. xN] are fresh variables. [xintros] allows 
    proving a function by induction on the structure of a proof.
    Two side-conditions are also generated, [is_spec_n K]
    and [curried_n f], both of which are attempted to be 
    discharged automatically (using [xisspec] and [xcurried]) *)

Ltac xintros_core cont1 cont2 cont3 :=
   let arity := spec_goal_arity tt in
   let lemma := get_spec_intro_x arity in
   apply lemma; [ instantiate; cont1 tt 
                | instantiate; cont2 tt 
                | instantiate; cont3 tt ]. 

Tactic Notation "xintros" :=
  xintros_core ltac:(fun _ => try xisspec) 
               ltac:(fun _ => try xcurried) (* try solve [ xcf; auto ] *)
               ltac:(fun _ => idtac).

Tactic Notation "xintros_noauto" :=
  xintros_core ltac:(fun _ => idtac) 
               ltac:(fun _ => idtac) 
               ltac:(fun _ => idtac).


(*--------------------------------------------------------*)
(* ** [xweaken] *)

(** [xweaken S] applies to a goal of the form [Spec_n f K]
    when [S] has type [Spec_n f K']. It leaves as goal the
    proposition that [K] is weaker than [K'], that is,
    [forall x1 .. xN R, weakenable R -> K' x1 .. xN R -> K x1 .. xN)].
    
    The tactic [xweaken] without argument looks for [S] in 
    the database of specifications. 
    
    [xweaken_noauto] is similar, but does not attempt to 
    discharge the subgoals automatically. *)

Ltac xweaken_core cont1 cont2 :=
  let arity := spec_goal_arity tt in
  let lemma := get_spec_weaken_x arity in
  eapply lemma; [ cont1 tt | try xisspec | cont2 tt ].
  (*  todo: prendre 3 continuations *)

Ltac xweaken_try_find_spec tt :=
  let f := spec_goal_fun tt in
  first [ let S := get_spec_hyp f in
          sapply S
        | xfind f; let H := fresh in 
          intro H; sapply H; clear H
        | idtac ].  

Ltac xweaken_post tt :=
  let R := fresh "R" in let WR := fresh "W" R in
  let HR := fresh "H" R in intros R WR HR;
  instantiate; cbv beta in HR.

Tactic Notation "xweaken_noauto" :=
  xweaken_core 
    ltac:(fun _ => idtac) 
    ltac:(fun _ => idtac).
Tactic Notation "xweaken" :=
  xweaken_core 
    ltac:(xweaken_try_find_spec) 
    ltac:(fun _ => idtac).
Tactic Notation "xweaken" "as" ident(x1) :=
  xweaken_core 
    ltac:(xweaken_try_find_spec) 
    ltac:(fun _ => intros x1; xweaken_post tt).
Tactic Notation "xweaken" "as" ident(x1) ident(x2) :=
  xweaken_core 
    ltac:(xweaken_try_find_spec) 
    ltac:(fun _ => intros x1 x2; xweaken_post tt).
Tactic Notation "xweaken" "as" ident(x1) ident(x2) ident(x3) :=
  xweaken_core 
    ltac:(xweaken_try_find_spec) 
    ltac:(fun _ => intros x1 x2 x3; xweaken_post tt).

Tactic Notation "xweaken" constr(S) :=
  xweaken_core 
   ltac:(fun _ => sapply S) 
   ltac:(fun _ => idtac).
Tactic Notation "xweaken" constr(S) "as" ident(x1) :=
  xweaken_core 
    ltac:(fun _ => sapply S) 
    ltac:(fun _ => intros x1; xweaken_post tt).
Tactic Notation "xweaken" constr(S) "as" ident(x1) ident(x2) :=
  xweaken_core 
    ltac:(fun _ => sapply S) 
    ltac:(fun _ => intros x1 x2; xweaken_post tt).
Tactic Notation "xweaken" constr(S) "as" ident(x1) ident(x2) ident(x3) :=
  xweaken_core 
    ltac:(fun _ => sapply S) 
    ltac:(fun _ => intros x1 x2 x3; xweaken_post tt).

Tactic Notation "xweaken" "~" := xweaken; auto~.
Tactic Notation "xweaken" "*" := xweaken; auto*.
Tactic Notation "xweaken" "~" constr(S) := xweaken S; auto~.
Tactic Notation "xweaken" "*" constr(S) := xweaken S; auto*.


(*--------------------------------------------------------*)
(* ** [xapply] *)

Tactic Notation "xapply_local" constr(E) :=
  forwards_nounfold_then E ltac:(fun K => 
    eapply local_wframe; [xlocal | sapply K | | ]).

Tactic Notation "xapply_local" "~" constr(E) :=
  xapply_local E; auto_tilde.
Tactic Notation "xapply_local" "*" constr(E) :=
  xapply_local E; auto_star.

(*todo*)
Tactic Notation "xapply_local_pre" constr(E) :=
  eapply local_weaken_pre; [xlocal | sapply E | ].



(*--------------------------------------------------------*)
(* ** [xcase] *)

Definition xnegpat (P:Prop) := P.

Lemma xtag_negpat_intro : forall (P:Prop), P -> xnegpat P.
Proof. auto. Qed.

Ltac xuntag_negpat := 
  unfold xnegpat in *.

Ltac xtag_negpat H :=
  applys_to H xtag_negpat_intro.

Ltac xcleanpat_core :=
  repeat match goal with H: xnegpat _ |- _ => clear H end.

Tactic Notation "xcleanpat" :=
  xcleanpat_core.

(**--todo clean up *)

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

(************************************************************)
(* ** [xif] -- todo : cleanup *)

Ltac xif_post H :=
   calc_partial_eq tt;
   try fold_bool; fold_prop;
   try fix_bool_of_known tt;
   try solve [ discriminate | false; congruence ];
   first [ subst_hyp H; try fold_bool; try rewriteb H 
         | rewriteb H
         | idtac ];
   try fix_bool_of_known tt;
   try (check_noevar_hyp H; rew_logicb in H; rew_logic in H).

Ltac xif_core :=
  xuntag tag_if; apply local_erase; esplit; splits 3%nat.

Ltac xif_after_core H :=
  xextract as H; xif_post H.

Tactic Notation "xif_after" ident(H) :=
  xif_after_core H.

Tactic Notation "xif_after" :=
  let H := fresh "H" in xif_after H.


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

Tactic Notation "xif" :=
  xif_core.
Tactic Notation "xcond" ident(H) :=
  xif_post H.


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

Tactic Notation "xif" ident(H) :=
  match post_is_meta tt with
  | false => xif_core_nometa H
  | true => xif_core_meta H
  end. 

Tactic Notation "xif" :=
  let H := fresh "C" in xif H.
*)




(*--useless?--*)

Ltac xpat_base H cont :=
  apply local_erase;
  match goal with 
  | |- ?P /\ ?Q => split; [ introv H | introv H; xtag_negpat H; cont tt ]
  | |- forall _, _ => introv H
  end.

Ltac xpat_base_anonymous cont :=
  let H := fresh "C" in xpat_base H cont.

Tactic Notation "xcase_one" "as" ident(H) :=
  xpat_base H ltac:(idcont).
  
Tactic Notation "xcase_one" :=
  xpat_base_anonymous ltac:(idcont).

Ltac xcases_core :=
  xpat_base_anonymous ltac:(fun _ => try xcases_core);
  try fold_bool; fold_prop.

Ltac xcases_subst_core :=
  xcases_core; try invert_first_hyp.

Tactic Notation "xcases" :=
  xcases_core.
Tactic Notation "xcases_subst" := 
  xcases_subst_core. 

Ltac xcase_post :=
  try solve [ discriminate | false; congruence ];
  try match ltac_get_tag tt with tag_done => xdone end; 
  try invert_first_hyp; 
  try fold_bool; fold_prop.

Tactic Notation "xcase_one_real" := 
   xcase_one; xcase_post.

Tactic Notation "xcases_real" := 
  xcases; xcase_post.

Tactic Notation "xcase" := 
  xcases_real.




(************************************************************)
(* ** [xalias] *)

(** [xalias as H] applies to a goal of the form  
    [(Alias x := v in Q) P] and adds an assumption [H] of 
    type [x = v]. It leaves [Q P] as new subgoal.
    [xalias] finds automatically a name for [H]. 
    [xalias as x H] allows to modify the name [x].
    [xalias_subst] substitutes the equality right away. *)

Tactic Notation "xalias" "as" ident(x) ident(H) :=
  xuntag tag_alias; intros x H.

Tactic Notation "xalias" "as" ident(x) :=
  let HE := fresh "E" x in xalias as x Hx.

Tactic Notation "xalias" :=
  xuntag tag_alias; intro; 
  let H := get_last_hyp tt in
  let HE := fresh "E" H in 
  intro HE.

Tactic Notation "xalias_subst" :=
  let x := fresh "TEMP" in let Hx := fresh "TEMP" in
  xalias as x Hx; subst x.


(************************************************************)
(* **  *)

Ltac xpat_core_new H cont1 cont2 :=
  xuntag tag_case; apply local_erase; split; 
    [ introv H; cont1 H 
    | introv H; xtag_negpat H; cont2 H ].

Ltac xpat_post H :=
  try solve [ discriminate | false; congruence ]; 
  try (symmetry in H; inverts H).

Tactic Notation "xpat" :=
  let H := fresh in
  xpat_core_new H ltac:(fun _ => idtac) ltac:(fun _ => idtac);
  xpat_post H.


(************************************************************)
(* ** [xmatch] *)

(** [xmatch] applies to a pattern-matching goal of the form
    [(Match Case x = p1 Then Q1 
       Else Case x = p2 Then Alias y := v in Q2
       Else Done/Fail) P].
    Several variants are available:
    - [xmatch] performs all the case analyses, 
      and introduces all aliases.
    - [xmatch_keep_alias] performs all case analyses,
      and does not introduces aliases.
    - [xmatch_subst_alias] performs all case analyses,
      and introduces and substitutes all aliases.
    - [xmatch_simple] performs all case analyses, 
      but does not try and invoke the inversion tactic on 
      deduced equalities. Tactics [xmatch_simple_keep_alias]
      and [xmatch_simple_subst_alias] are also available. 
    - [xmatch_nocases] simply remove the [Match] tag and
      leaves the cases to be solved manually using [xcase]. *)

Ltac xmatch_core cont :=
  let tag := ltac_get_tag tt in
  match tag with
  | tag_match ?n => xuntag (tag_match n); cont n
  end.

Ltac xmatch_case cont :=
  let H := fresh "C" in 
  xpat_core_new H ltac:(xpat_post) ltac:(fun _ => cont tt).

Ltac xmatch_case_simple cont :=
  let H := fresh "C" in 
  xpat_core_new H ltac:(idtac) ltac:(fun _ => cont tt).

Ltac xmatch_cases case_tactic n :=
  match n with
  | 0%nat => first [ xdone | xfail | idtac ]
  | S ?n' => case_tactic ltac:(fun _ => xmatch_cases case_tactic n')
  | _ => idtac
  end.

Tactic Notation "xmatch_nocases" :=
  xmatch_core ltac:(fun _ => idtac).

Tactic Notation "xmatch_keep_alias" :=
  xmatch_core ltac:(fun n => xmatch_cases xmatch_case n).
Tactic Notation "xmatch_simple_keep_alias" :=
  xmatch_core ltac:(fun n => xmatch_cases xmatch_case_simple n).
Tactic Notation "xmatch" :=
   xmatch_keep_alias; repeat xalias.
Tactic Notation "xmatch_simple" :=
   xmatch_simple_keep_alias; repeat xalias.
Tactic Notation "xmatch_subst_alias" :=
   xmatch_keep_alias; repeat xalias_subst.
Tactic Notation "xmatch_simple_subst_alias" :=
   xmatch_simple_keep_alias; repeat xalias_subst.



(************************************************************)
(* ** [xgo] *)

(**)

Inductive Xhint_cmd :=
  | Xstop : Xhint_cmd
  | XstopNoclear : Xhint_cmd
  | XstopAfter : Xhint_cmd
  | XstopInside : Xhint_cmd
  | Xtactic : Xhint_cmd
  | XtacticNostop : Xhint_cmd
  | XtacticNoclear : Xhint_cmd
  | XsubstAlias : Xhint_cmd
  | XspecArgs : list Boxer -> list Boxer -> Xhint_cmd
  | Xargs : forall A, A -> Xhint_cmd
  | Xlet : forall A, A -> Xhint_cmd
  | Xlets : forall A, A -> Xhint_cmd
  | Xsimple : Xhint_cmd.

Inductive Xhint (a : tag_name) (h : Xhint_cmd) :=
  | Xhint_intro : Xhint a h.

Ltac add_hint a h :=
  let H := fresh "Hint" in
  lets H: (Xhint_intro a h).

Ltac clear_hint a :=
  match goal with H: Xhint a _ |- _ => clear H end.

Ltac clears_hint tt :=
  repeat match goal with H: Xhint _ _ |- _ => clear H end.

Ltac find_hint a :=
  match goal with H: Xhint a ?h |- _ => constr:(h) end.

Ltac xgo_default solver cont :=
  match ltac_get_tag tt with
  | tag_ret => xret; cont tt
  | tag_fail => xfail; cont tt
  | tag_done => xdone; cont tt
  | tag_apply => xapp
  | tag_seq => xseq; cont tt
  | tag_let_val => xval; cont tt
  | tag_let_trm => xlet; cont tt
  | tag_let_fun => fail
  | tag_body => fail
  | tag_letrec => fail
  | tag_case => xcases_real; cont tt 
  | tag_casewhen => fail 
  | tag_if => xif; cont tt
  | tag_alias => xalias; cont tt
  | tag_match ?n => xmatch; cont tt
  | tag_top_val => fail
  | tag_top_trm => fail
  | tag_top_fun => fail
  | tag_for => fail
  | tag_while => fail
  end.

Ltac xtactic tag := idtac.

Ltac run_hint h cont :=
  let tag := ltac_get_tag tt in
  match h with
  | Xstop => clears_hint tt; idtac
  | XstopNoclear => idtac
  | XstopAfter => 
      match tag with
      | tag_let_trm => fail (* todo: xlet_with cont ltac:(fun _ => idtac)*)
      | _ => xgo_default ltac:(fun _ => idtac) ltac:(fun _ => idtac) 
      end 
  | XstopInside => 
      match tag with
      | tag_let_trm => fail (*todo: xlet_with ltac:(fun _ => idtac) cont *)
      end
  | Xtactic => clears_hint tt; xtactic tag
  | XtacticNostop => xtactic tag; cont tt
  | XtacticNoclear => xtactic tag
  | XsubstAlias => xmatch_subst_alias; cont tt
  | Xargs ?E => 
      match tag with
      | tag_let_trm => fail (* todo!!*)
      | tag_apply => xapp E (*todo: not needed?*)
      end
  | XspecArgs (>>> ?S) ?E => 
      match tag with
      | tag_let_trm =>  fail (* todo!!*)
      | tag_apply => xapp_spec S E (*todo: not needed?*)
      end 
  | Xlet ?S =>
     match tag with
     | tag_let_trm => xlet S; cont tt
     | tag_let_fun => xfun_noxbody S
     end
(*
   | Xlets ?S =>
     match tag with
     | tag_let_trm => xlets S; cont tt
     | tag_let_fun => xfun S
     end
*)
  | Xsimple => xmatch_simple; cont tt 
      (* todo : generalize
        | tag_case => xcases_real
        | tag_if => xif
        | tag_match ?n => xmatch
        *)
  end.

Ltac find_and_run_hint cont :=
  let a := ltac_get_label tt in
  let h := find_hint a in
  clear_hint a;
  first [ run_hint h cont | fail 1 ]. 

Tactic Notation "xhint" :=
  find_and_run_hint ltac:(fun _ => idtac).

Ltac xgo_core solver cont :=
  first [ find_and_run_hint cont
        | xgo_default solver cont ].

Ltac xgo_core_once solver :=
  xgo_core solver ltac:(fun _ => idtac).

Ltac xgo_core_repeat solver :=
  xgo_core solver ltac:(fun _ => instantiate; try solve [ solver tt ];
                          instantiate; try xgo_core_repeat solver).

Ltac xgo_pre tt :=
  first [ xcf; repeat progress(intros)
        | repeat progress(intros)
        | idtac ].

Ltac xgo_base solver :=
  xgo_pre tt; xgo_core_repeat solver.

Tactic Notation "xgo1" :=
  xgo_core_once ltac:(fun _ => idtac).

Tactic Notation "xgo" :=
  xgo_base ltac:(fun tt => idtac).
Tactic Notation "xgo" "~" := 
  xgo_base ltac:(fun tt => xauto~ ); instantiate; xauto~.
Tactic Notation "xgo" "*" := 
  xgo_base ltac:(fun tt => xauto* ); instantiate; xauto*. 

Tactic Notation "xgo" constr(a1) constr(h1) := 
  add_hint a1 h1; xgo.
Tactic Notation "xgo" constr(a1) constr(h1) "," constr(a2) constr(h2) := 
  add_hint a1 h1; add_hint a2 h2; xgo.
Tactic Notation "xgo" constr(a1) constr(h1) "," constr(a2) constr(h2) ","
  constr(a3) constr(h3) := 
  add_hint a1 h1; add_hint a2 h2; add_hint a3 h3; xgo.
Tactic Notation "xgo" constr(a1) constr(h1) "," constr(a2) constr(h2) ","
  constr(a3) constr(h3) "," constr(a4) constr(h4) := 
  add_hint a1 h1; add_hint a2 h2; add_hint a3 h3; add_hint a4 h4; xgo.

Tactic Notation "xgo" "~" constr(a1) constr(h1) := 
  add_hint a1 h1; xgo~.
Tactic Notation "xgo" "~" constr(a1) constr(h1) "," constr(a2) constr(h2) := 
  add_hint a1 h1; add_hint a2 h2; xgo~.
Tactic Notation "xgo" "~" constr(a1) constr(h1) "," constr(a2) constr(h2) ","
  constr(a3) constr(h3) := 
  add_hint a1 h1; add_hint a2 h2; add_hint a3 h3; xgo~.
Tactic Notation "xgo" "~" constr(a1) constr(h1) "," constr(a2) constr(h2) ","
  constr(a3) constr(h3) "," constr(a4) constr(h4) := 
  add_hint a1 h1; add_hint a2 h2; add_hint a3 h3; add_hint a4 h4; xgo~.



(*todo:remove*)
Ltac xapps_core spec args solver ::=
  let cont1 tt :=
    xapp_with spec args solver in
  let cont2 tt :=
    instantiate; xextract; try intro_subst in    
  match ltac_get_tag tt with
  | tag_let_trm => xlet; [ cont1 tt | cont2 tt ]
  | tag_seq =>     xseq; [ cont1 tt | cont2 tt ]
  end.


Ltac xinduct E := xinduction_heap E.

(* todo: remove*)
Tactic Notation "xapp_hyp" :=
  eapply local_weaken; 
    [ xlocal
    | let f := spec_goal_fun tt in let H := get_spec_hyp f in 
      apply (proj2 H) (* todo generalize to arities*)
    | hsimpl
    | hsimpl ].
