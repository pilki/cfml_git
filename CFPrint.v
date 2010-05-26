Set Implicit Arguments.
Require Import CFSpec.

(********************************************************************)
(* ** Notation for specifications *)

Open Local Scope func.

(*------------------------------------------------------------------*)
(* ** Printing abstract specifications *)

Notation "'Spec_1' f K" := (spec_1 K f) 
  (at level 69, f at level 0) : func.

Notation "'Spec_2' f K" := (spec_2 K f) 
  (at level 69, f at level 0) : func.

Notation "'Spec_3' f K" := (spec_3 K f) 
  (at level 69, f at level 0) : func.

Notation "'Spec_4' f K" := (spec_4 K f) 
  (at level 69, f at level 0) : func.

(*------------------------------------------------------------------*)
(* ** Printing general specifications *)

Notation "'Spec' f '()' | R >> H"
  := (Spec_1 f (fun (_:unit) R => H))
     (at level 69, f at level 0, 
      R ident, H at level 90,
      format "Spec  f  '()'  | R >>  '/'   '[v' H ']'") : func.
 
Notation "'Spec' f x1 | R >> H"
  := (Spec_1 f (fun x1 R => H))
     (at level 69, f at level 0, x1 ident, 
      R ident, H at level 90,
      format "Spec  f  x1  | R >>  '/'   '[v' H ']'") : func.

Notation "'Spec' f x1 x2 | R >> H"
  := (Spec_2 f (fun x1 x2 R => H))
     (at level 69, f at level 0, x1 ident, x2 ident, 
      R ident, H at level 90,
      format "Spec  f  x1  x2  | R >>  '/'   '[v' H ']'") : func.

Notation "'Spec' f x1 x2 x3 | R >> H"
  := (Spec_3 f (fun x1 x2 x3 R => H))
     (at level 69, f at level 0, x1 ident, x2 ident, x3 ident, 
      R ident, H at level 90,
      format "Spec  f  x1  x2  x3  | R >>  '/'   '[v' H ']'") : func.

Notation "'Spec' f x1 x2 x3 x4 | R >> H"
  := (Spec_4 f (fun x1 x2 x3 x4 R => H))
     (at level 69, f at level 0, x1 ident, x2 ident, x3 ident, x4 ident,
      R ident, H at level 90,
      format "Spec  f  x1  x2  x3  x4  | R >>  '/'   '[v' H ']'") : func.

Notation "'Spec' f ( x1 : A1 ) | R >> H"
  := (Spec_1 f (fun (x1:A1) R => H))
     (at level 69, f at level 0, x1 ident, 
      R ident, H at level 90,
      A1 at level 0, only parsing) : func.

Notation "'Spec' f ( x1 : A1 ) ( x2 : A2 ) | R >> H"
  := (Spec_2 f (fun (x1:A1) (x2:A2) R => H))
     (at level 69, f at level 0, x1 ident, x2 ident, 
      R ident, H at level 90,
      A1 at level 0, A2 at level 0, only parsing) : func.

Notation "'Spec' f ( x1 : A1 ) ( x2 : A2 ) ( x3 : A3 ) | R >> H"
  := (Spec_3 f (fun (x1:A1) (x2:A2) (x3:A3) R => H))
     (at level 69, f at level 0, x1 ident, x2 ident, x3 ident, 
      R ident, H at level 90,
      A1 at level 0, A2 at level 0, A3 at level 0, only parsing) : func.

Notation "'Spec' f ( x1 : A1 ) ( x2 : A2 ) ( x3 : A3 ) ( x4 : A4 ) | R >> H"
  := (Spec_4 f (fun (x1:A1) (x2:A2) (x3:A3) (x4:A4) R => H))
     (at level 69, f at level 0, x1 ident, x2 ident, x3 ident, x4 ident, 
      R ident, H at level 90,
      A1 at level 0, A2 at level 0, A3 at level 0, A4 at level 0, only parsing) : func.

(*------------------------------------------------------------------*)
(* ** Printing specifications without auxiliary variables *)

Notation "'Specs' f '()' >> H Q"
  := (Spec f () | R >> R H Q)
     (at level 69, f at level 0, H at level 0,
      format "Specs  f  ()  >>  '/'   '[v' H ']'  '[v' Q ']'") : func.

Notation "'Specs' f x1 >> H Q"
  := (Spec f x1 | R >> R H Q)
     (at level 69, f at level 0, x1 ident, H at level 0,
      format "Specs  f  x1  >>  '/'   '[v' H ']'  '[v' Q ']'") : func.

Notation "'Specs' f x1 x2 >> H Q"
  := (Spec f x1 x2 | R >> R H Q)
     (at level 69, f at level 0, x1 ident, x2 ident, H at level 0,
      format "Specs  f  x1  x2  >>  '/'   '[v' H ']'   '[v' Q ']'") : func.

Notation "'Specs' f x1 x2 x3 >> H Q"
  := (Spec f x1 x2 x3 | R >> R H Q)
     (at level 69, f at level 0, x1 ident, x2 ident, x3 ident, H at level 0,
      format "Specs  f  x1  x2  x3  >>  '/'   '[v' H ']'   '[v' Q ']'") : func.

Notation "'Specs' f x1 x2 x3 x4 >> H Q"
  := (Spec f x1 x2 x3 x4 | R >> R H Q)
     (at level 69, f at level 0, x1 ident, x2 ident, x3 ident, x4 ident, H at level 0,
      format "Specs  f  x1  x2  x3  x4  >>  '/'   '[v' H ']'   '[v' Q ']'") : func.

Notation "'Specs' f ( x1 : A1 ) >> H Q"
  := (Spec f (x1:A1) | R >> R H Q)
     (at level 69, f at level 0, x1 ident, H at level 0,  
      A1 at level 0, only parsing) : func.

Notation "'Specs' f ( x1 : A1 ) ( x2 : A2 ) >> H Q"
  := (Spec f (x1:A1) (x2:A2) | R >> R H Q)
     (at level 69, f at level 0, x1 ident, x2 ident, H at level 0,
      A1 at level 0, A2 at level 0, only parsing) : func.

Notation "'Specs' f ( x1 : A1 ) ( x2 : A2 ) ( x3 : A3 ) >> H Q"
  := (Spec f (x1:A1) (x2:A2) (x3:A3) | R >> R H Q)
     (at level 69, f at level 0, x1 ident, x2 ident, x3 ident, H at level 0,
      A1 at level 0, A2 at level 0, A3 at level 0, only parsing) : func.

Notation "'Specs' f ( x1 : A1 ) ( x2 : A2 ) ( x3 : A3 ) ( x4 : A4 ) >> H Q"
  := (Spec f (x1:A1) (x2:A2) (x3:A3) (x4:A4) | R >> R H Q)
     (at level 69, f at level 0, x1 ident, x2 ident, x3 ident, x4 ident, H at level 0,
      A1 at level 0, A2 at level 0, A3 at level 0, A4 at level 0, only parsing) : func.


(*------------------------------------------------------------------*)
(* ** Printing specifications without effects *)

Notation "'Pure' f x1 >> P"
  := (Spec f x1 |R>> pure R P)
     (at level 69, f at level 0, x1 ident,
      format "Pure  f  x1  >>  '/'   '[v' P ']'") : func.

Notation "'Pure' f x1 x2 >> P"
  := (Spec f x1 x2 |R>> pure R P)
     (at level 69, f at level 0, x1 ident, x2 ident,
      format "Pure  f  x1  x2  >>  '/'   '[v' P ']'") : func.

Notation "'Pure' f x1 x2 x3 >> P"
  := (Spec f x1 x2 x3 |R>> pure R P)
     (at level 69, f at level 0, x1 ident, x2 ident, x3 ident,
      format "Pure  f  x1  x2  x3  >>  '/'   '[v' P ']'") : func.

Notation "'Pure' f x1 x2 x3 x4 >> P"
  := (Spec f x1 x2 x3 x4 |R>> pure R P)
     (at level 69, f at level 0, x1 ident, x2 ident, x3 ident, x4 ident,
      format "Pure  f  x1  x2  x3  x4  >>  '/'   '[v' P ']'") : func.

Notation "'Pure' f x1 | y >> H"
  := (Pure f x1 >> (fun y => H))
     (at level 69, f at level 0, x1 ident, y ident, H at level 90,
      format "Pure  f  x1  | y >>  H") : func.

Notation "'Pure' f x1 x2 | y >> H"
  := (Pure f x1 x2 >> (fun y => H))
     (at level 69, f at level 0, x1 ident, x2 ident, 
      y ident, H at level 90,
      format "Pure  f  x1  x2  | y >>  H") : func.

Notation "'Pure' f x1 x2 x3 | y >> H"
  := (Pure f x1 x2 x3 >> (fun y => H))
     (at level 69, f at level 0, x1 ident, x2 ident, x3 ident, 
      y ident, H at level 90,
      format "Pure  f  x1  x2  x3  | y >>  H") : func.

Notation "'Pure' f x1 x2 x3 x4 | y >> H"
  := (Pure f x1 x2 x3 x4 >> (fun y => H))
     (at level 69, f at level 0, x1 ident, x2 ident, x3 ident, x4 ident, 
      y ident, H at level 90,
      format "Pure  f  x1  x2  x3  x4  | y >>  H") : func.

Notation "'Pure' f ( x1 : A1 ) >> P"
  := (Spec f (x1:A1) |R>> pure R P)
     (at level 69, f at level 0, x1 ident, 
      A1 at level 0, only parsing) : func.

Notation "'Pure' f ( x1 : A1 ) ( x2 : A2 ) >> P"
  := (Spec f (x1:A1) (x2:A2) |R>> pure R P)
     (at level 69, f at level 0, x1 ident, x2 ident,
      A1 at level 0, A2 at level 0, only parsing) : func.

Notation "'Pure' f ( x1 : A1 ) ( x2 : A2 ) ( x3 : A3 ) >> P"
  := (Spec f (x1:A1) (x2:A2) (x3:A3) |R>> pure R P)
     (at level 69, f at level 0, x1 ident, x2 ident, x3 ident,
      A1 at level 0, A2 at level 0, A3 at level 0, only parsing) : func.

Notation "'Pure' f ( x1 : A1 ) ( x2 : A2 ) ( x3 : A3 ) ( x4 : A4 ) >> P"
  := (Spec f (x1:A1) (x2:A2) (x3:A3) (x4:A4) |R>> pure R P)
     (at level 69, f at level 0, x1 ident, x2 ident, x3 ident, x4 ident,
      A1 at level 0, A2 at level 0, A3 at level 0, A4 at level 0, only parsing) : func.


(********************************************************************)
(* ** Notation for specifications through [rep] predicate -- TODO?? *)

(*------------------------------------------------------------------*)
(* ** Printing specifications without effects 

Notation "'RepSpec' f ( X1 ';' A1 )  | R >> H"
  := (Spec_1 f (fun (x1:A1) R => forall X1, rep x1 X1 -> H))
     (at level 69, f at level 0, X1 ident, 
      R ident, H at level 90,
      A1 at level 0) : func.

Notation "'RepSpec' f ( X1 ';' A1 ) ( X2 ';' A2 )  | R >> H"
  := (Spec_2 f (fun (x1:A1) (x2:A2) R => 
       forall X1 X2, rep x1 X1 -> rep x2 X2 -> H))
     (at level 69, f at level 0, X1 ident, X2 ident, 
      R ident, H at level 90,
      A1 at level 0, A2 at level 0) : func.

Notation "'RepSpec' f ( X1 ; A1 ) ( X2 ; A2 ) ( X3 ; A3 )  | R >> H"
  := (Spec_3 f (fun (x1:A1) (x2:A2) (x3:A3) R => 
       forall X1 X2 X3, rep x1 X1 -> rep x2 X2 -> rep x3 X3 -> H))
     (at level 69, f at level 0, X1 ident, X2 ident, X3 ident, 
      R ident, H at level 90,
      A1 at level 0, A2 at level 0, A3 at level 0) : func.

Notation "'RepSpec' f ( X1 ; A1 ) ( X2 ; A2 ) ( X3 ; A3 ) ( X4 ; A4 )  | R >> H"
  := (Spec_4 f (fun (x1:A1) (x2:A2) (x3:A3) (x4:A4) R => 
        forall X1 X2 X3 X4, rep x1 X1 -> rep x2 X2 -> rep x3 X3 -> rep x4 X4 -> H))
     (at level 69, f at level 0, X1 ident, X2 ident, X3 ident, X4 ident, 
      R ident, H at level 90,
      A1 at level 0, A2 at level 0, A3 at level 0, A4 at level 0) : func.
*)

(*------------------------------------------------------------------*)
(* ** Printing specifications without auxiliary variables 

Notation "'RepSpecs' f ( X1 ; A1 ) >> H Q"
  := (Spec f (x1:A1) | R >> 
       forall X1, rep x1 X1 -> R H Q)
     (at level 69, f at level 0, X1 ident, H at level 0, 
      A1 at level 0) : func.

Notation "'RepSpecs' f ( X1 ; A1 ) ( X2 ; A2 ) >> H Q"
  := (Spec f (x1:A1) (x2:A2) | R >> 
       forall X1 X2, rep x1 X1 -> rep x2 X2 -> R H Q)
     (at level 69, f at level 0, X1 ident, X2 ident, H at level 0,
      A1 at level 0, A2 at level 0) : func.

Notation "'RepSpecs' f ( X1 ; A1 ) ( X2 ; A2 ) ( X3 ; A3 ) >> H Q"
  := (Spec f (x1:A1) (x2:A2) (x3:A3) | R >> 
       forall X1 X2 X3, rep x1 X1 -> rep x2 X2 -> rep x3 X3 -> R H Q)
     (at level 69, f at level 0, X1 ident, X2 ident, X3 ident, H at level 0,
      A1 at level 0, A2 at level 0, A3 at level 0) : func.

Notation "'RepSpecs' f ( X1 ; A1 ) ( X2 ; A2 ) ( X3 ; A3 ) ( X4 ; A4 ) >> H Q"
  := (Spec f (x1:A1) (x2:A2) (x3:A3) (x4:A4) | R >> 
       forall X1 X2 X3 X4, rep x1 X1 -> rep x2 X2 -> rep x3 X3 -> rep x4 X4 -> R H Q)
     (at level 69, f at level 0, X1 ident, X2 ident, X3 ident, X4 ident, H at level 0,
      A1 at level 0, A2 at level 0, A3 at level 0, A4 at level 0) : func.
*)

(*------------------------------------------------------------------*)
(* ** Printing general specifications

Notation "'RepPure' f ( X1 ; A1 ) >> P"
  := (Spec f (x1:A1) | R >> 
       forall X1, rep x1 X1 -> pure R P)
     (at level 69, f at level 0, X1 ident, 
      A1 at level 0) : func.

Notation "'RepPure' f ( X1 ; A1 ) ( X2 ; A2 ) >> P"
  := (Spec f (x1:A1) (x2:A2) | R >> 
       forall X1 X2, rep x1 X1 -> rep x2 X2 -> pure R P)
     (at level 69, f at level 0, X1 ident, X2 ident,
      A1 at level 0, A2 at level 0) : func.

Notation "'RepPure' f ( X1 ; A1 ) ( X2 ; A2 ) ( X3 ; A3 ) >> P"
  := (Spec f (x1:A1) (x2:A2) (x3:A3) | R >> 
       forall X1 X2 X3, rep x1 X1 -> rep x2 X2 -> rep x3 X3 -> pure R P)
     (at level 69, f at level 0, X1 ident, X2 ident, X3 ident,
      A1 at level 0, A2 at level 0, A3 at level 0) : func.

Notation "'RepPure' f ( X1 ; A1 ) ( X2 ; A2 ) ( X3 ; A3 ) ( X4 ; A4 ) >> P"
  := (Spec f (x1:A1) (x2:A2) (x3:A3) (x4:A4) | R >> 
       forall X1 X2 X3 X4, rep x1 X1 -> rep x2 X2 -> rep x3 X3 -> rep x4 X4 -> pure R P)
     (at level 69, f at level 0, X1 ident, X2 ident, X3 ident, X4 ident,
      A1 at level 0, A2 at level 0, A3 at level 0, A4 at level 0) : func.
 *)


(*------------------------------------------------------------------*)
(* ** Specification of output modulo representation *)

Notation "X '.;' T" := (fun (x:T) => rep x X) (at level 68). 
Notation "P '.:' T" := (fun (x:T) => exists X, rep x X /\ P X) (at level 80). 


(********************************************************************)
(* Implementation of labels *)

Module Export AtomsEff. 

(** Variables are described as list of bits, e.g. [1::2::1::1::2::0].
    For efficiency, we do not use the type [list bool], but an ad-hoc
    predicate with three constructors. *)

Inductive atom : Set :=
  | atom_0 : atom
  | atom_1 : atom -> atom
  | atom_2 : atom -> atom.

Fixpoint beq (x y : atom) :=
  match x,y with
  | atom_0, atom_0 => true
  | atom_1 x', atom_1 y' => beq x' y'
  | atom_2 x', atom_2 y' => beq x' y'
  | _, _ => false
  end.

Lemma req : R_eq beq.
Proof.
  constructor; gen y;
  induction x; destruct y; unfold beq; simpl; intros;
  try solve [ auto | false 
            | rewrite* (@IHx y) | inversions* H ].
Qed.

Instance atom_inhabited : Inhab atom.
Proof. constructor. exact atom_0. Defined.

Instance atom_comparable : Eqb atom.
Proof. apply (Build_Eqb req). Defined.

(** Notation system *)

Notation "'`0'" := (atom_0) 
  (at level 50, format "`0") : atom_scope.
Notation "'`1' v" := (atom_1 v) 
  (at level 50, v at level 50, format "`1 v") : atom_scope.
Notation "'`2' v" := (atom_2 v) 
  (at level 50, v at level 50, format "`2 v") : atom_scope.
Open Scope atom_scope.
Bind Scope atom_scope with atom.
Delimit Scope atom_scope with atom.

End AtomsEff.


(********************************************************************)
(* ** Implementation of tags *)

Definition tag_name := atom.

Definition no_name := `0.

Notation "'?'" := (no_name).

Inductive tag_type : Type :=
  | tag_ret
  | tag_apply
  | tag_let_val
  | tag_let_fun
  | tag_let_trm
  | tag_body
  | tag_letrec
  | tag_case
  | tag_casewhen
  | tag_fail
  | tag_done
  | tag_if
  | tag_alias
  | tag_top_val
  | tag_top_fun
  | tag_top_trm
  | tag_match (n : nat)
  | tag_seq
  | tag_for
  | tag_while.

Definition tag (t:tag_type) (x:option tag_name) (A:Type) (P:A) := P.

Notation "'!B' P" := (tag tag_body None P)  
  (at level 95).
Notation "'!M' n P" := (tag (tag_match n) None P)
  (at level 95, n at level 0).
Notation "'!A' P" := (tag tag_apply None P)  
  (at level 95).
Notation "'!R' P" := (tag tag_ret None (local P))  
  (at level 69).
Notation "'!V' P" := (tag tag_let_val None (local P))  
  (at level 95).
Notation "'!F' P" := (tag tag_let_fun None (local P))  
  (at level 95).
Notation "'!T' P" := (tag tag_let_trm None (local P))  
  (at level 95).
Notation "'!C' P" := (tag tag_case None (local P))  
  (at level 95).
Notation "'!W' P" := (tag tag_casewhen None (local P))  
  (at level 95).
Notation "'!I' P" := (tag tag_if None (local P))  
  (at level 95).
Notation "'!E' P" := (tag tag_fail None (local P))  
  (at level 95).
Notation "'!S' P" := (tag tag_alias None (local P))  
  (at level 95).
Notation "'!D' P" := (tag tag_done None (local P))  
  (at level 95).
Notation "'!Seq' P" := (tag tag_seq None (local P))  
  (at level 95).
Notation "'!For' P" := (tag tag_for None (local P))  
  (at level 95).
Notation "'!While' P" := (tag tag_while None (local P))  
  (at level 95).
Notation "'!TV' P" := (tag tag_top_val None (local P))  
  (at level 95).
Notation "'!TF' P" := (tag tag_top_fun None (local P))  
  (at level 95).
Notation "'!TT' P" := (tag tag_top_trm None (local P))  
  (at level 95).

Notation "'!!B' x P" := (tag tag_body (Some x) P)
  (at level 95, x at level 0).
Notation "'!!M' x n P" := (tag (tag_match n) (Some x) P)
  (at level 95, x at level 0, n at level 0).
Notation "'!!A' x P" := (tag tag_apply (Some x) P)  
  (at level 95, x at level 0).
Notation "'!!R' x P" := (tag tag_ret (Some x) (local P))  
  (at level 69, x at level 0).
Notation "'!!V' x P" := (tag tag_let_val (Some x) (local P))  
  (at level 95, x at level 0).
Notation "'!!F' x P" := (tag tag_let_fun (Some x) (local P))  
  (at level 95, x at level 0).
Notation "'!!T' x P" := (tag tag_let_trm (Some x) (local P))  
  (at level 95, x at level 0).
Notation "'!!C' x P" := (tag tag_case (Some x) (local P))  
  (at level 95, x at level 0).
Notation "'!:W' x P" := (tag tag_casewhen (Some x) (local P))  
  (at level 95, x at level 0).
Notation "'!!I' x P" := (tag tag_if (Some x) (local P))  
  (at level 95, x at level 0).
Notation "'!!E' x P" := (tag tag_fail (Some x) (local P))  
  (at level 95, x at level 0).
Notation "'!!S' x P" := (tag tag_alias (Some x) (local P))  
  (at level 95, x at level 0).
Notation "'!!D' x P" := (tag tag_done (Some x) (local P))  
  (at level 95, x at level 0).
Notation "'!!Seq' x P" := (tag tag_seq (Some x) (local P))  
  (at level 95, x at level 0).
Notation "'!!For' x  P" := (tag tag_for (Some x) (local P))  
  (at level 95, x at level 0).
Notation "'!!While' x P" := (tag tag_while (Some x) (local P))  
  (at level 95, x at level 0).
Notation "'!!TV' x P" := (tag tag_top_val (Some x) (local P))  
  (at level 95, x at level 0).
Notation "'!!TF' x P" := (tag tag_top_fun (Some x) (local P))  
  (at level 95, x at level 0).
Notation "'!!TT' x P" := (tag tag_top_trm (Some x) (local P))  
  (at level 95, x at level 0).

Lemma add_tag : forall (T:Prop->Prop), (T = fun P:Prop => P) -> 
                forall (G:Prop), (T G) -> G. (* todo: was T'G *)
Proof. intros. subst. auto. Qed.

Ltac ltac_add_tag T :=
  apply (@add_tag T (refl_equal _)).

Ltac ltac_get_tag tt :=
  match goal with |- tag ?t _ _ _ _ => constr:(t) end.  

Ltac ltac_get_label tt :=
  match goal with |- tag _ (Some ?l) _ _ _ => constr:(l) end.  

Tactic Notation "xuntag" constr(t) :=
  match goal with |- tag t _ _ _ _ => unfold tag at 1 end.

Tactic Notation "xuntag" :=
  match goal with |- tag _ _ _ _ _ => unfold tag at 1 end.

Tactic Notation "xuntags" := unfold tag in *.


(********************************************************************)
(* ** Notation for characteristic formulae *)

Notation "'Ret' v" :=
  (!R (fun H Q => H heap_empty /\ Q v heap_empty))
  (at level 69) : charac.

Notation "'Fail'" :=
  (!E (fun _ _ => False))
  (at level 0) : charac.

Notation "'Done'" := 
  (!D (fun _ _ => True))
  (at level 0) : charac.

Notation "'App' f x1 ;" :=
  (!A (app_1 f x1))
  (at level 68, f at level 0, x1 at level 0) : charac.

Notation "'App' f x1 x2 ;" :=
  (!A (app_2 f x1 x2))
  (at level 68, f at level 0, x1 at level 0, 
   x2 at level 0) : charac.

Notation "'App' f x1 x2 x3 ;" :=
  (!A (app_3 f x1 x2 x3))
  (at level 68, f at level 0, x1 at level 0, x2 at level 0,
   x3 at level 0) : charac.

Notation "'App' f x1 x2 x3 x4 ;" :=
  (!A (app_3 f x1 x2 x3 x4))
  (at level 68, f at level 0, x1 at level 0, x2 at level 0,
   x3 at level 0, x4 at level 0) : charac.

Notation "'Body' f x1 '=>' Q" :=
  (!B (forall K, is_spec_1 K ->
                 (forall x1, K x1 Q) -> spec_1 K f))
  (at level 0, f at level 0, x1 ident) : charac.

Notation "'Body' f x1 x2 '=>' Q" :=
  (!B (forall K, is_spec_2 K -> 
                 (forall x1 x2, K x1 x2 Q) -> spec_2 K f))
  (at level 0, f at level 0, x1 ident, x2 ident) : charac.

Notation "'Body' f x1 x2 x3 '=>' Q" :=
  (!B (forall K, is_spec_3 K ->
                 (forall x1 x2 x3, K x1 x2 x3 Q) -> spec_3 K f))
  (at level 0, f at level 0, x1 ident, x2 ident, x3 ident) : charac.

Notation "'Body' f [ A1 ]  x1 '=>' Q" :=
  (!B (forall A1 K, is_spec_1 K ->
                 (forall x1, K x1 Q) -> spec_1 K f))
  (at level 0, f at level 0, x1 ident, A1 ident) : charac.

Notation "'Body' f [ A1 ]  x1 x2 '=>' Q" :=
  (!B (forall A1 K, is_spec_2 K ->
                 (forall x1 x2, K x1 x2 Q) -> spec_2 K f))
  (at level 0, f at level 0, x1 ident, x2 ident, A1 ident) : charac.

Notation "'Body' f [ A1 A2 ]  x1 '=>' Q" :=
  (!B (forall A1 A2 K, is_spec_1 K ->
                 (forall x1, K x1 Q) -> spec_1 K f))
  (at level 0, f at level 0, x1 ident, A1 ident, A2 ident) : charac.

Notation "'Body' f [ A1 A2 ]  x1 x2 '=>' Q" :=
  (!B (forall A1 A2 K, is_spec_2 K ->
                 (forall x1 x2, K x1 x2 Q) -> spec_2 K f))
  (at level 0, f at level 0, x1 ident, x2 ident, A1 ident, A2 ident) : charac.


Notation "'LetVal' : a x ':=' V 'in' F" :=
  (!!V a (fun H Q => forall x, x = V -> F H Q))
  (at level 69, a at level 0, x ident) : charac.

Notation "'Let' : a x ':=' F1 'in' F2" :=
  (!!T a (fun H Q => exists Q1, F1 H Q1 /\ forall x, F2 (Q1 x) Q))
  (at level 69, a at level 0, x ident) : charac.

      (* !L: fun H Q => exists Q1, F1 H Q1 /\ forall (x:T), F2 (Q1 x) Q *)

(* deprecated 

Notation "'LetVal' : a [ A1 ]  x1 ':=' Q1 'in' Q2" :=
  (!!L a (fun P => exists P1, (forall A1, Q1 P1)
                            /\ forall x1,P1 x1 -> Q2 P))
  (at level 69, a at level 0, x1 ident, A1 ident) : charac.

Notation "'LetVal' : a [ A1 A2 ]  x1 ':=' Q1 'in' Q2" :=
  (!!L a (fun P => exists P1, (forall A1 A2, Q1 P1)
                            /\ forall x1,P1 x1 -> Q2 P))
  (at level 69, a at level 0, x1 ident, A1 ident, A2 ident) : charac.
*)


(* deprecated

Notation "'LetVal' x1 ':=' Q1 'in' Q2" :=
  (!L (fun P => exists P1, Q1 P1 
                           /\ forall x1,P1 x1 -> Q2 P))
  (at level 69, x1 ident) : charac.

Notation "'LetVal' [ A1 ]  x1 ':=' Q1 'in' Q2" :=
  (!L (fun P => exists P1, (forall A1, Q1 P1)
                            /\ forall x1,P1 x1 -> Q2 P))
  (at level 69, x1 ident, A1 ident) : charac.

Notation "'LetVal' [ A1 A2 ]  x1 ':=' Q1 'in' Q2" :=
  (!L (fun P => exists P1, (forall A1 A2, Q1 P1)
                            /\ forall x1,P1 x1 -> Q2 P))
  (at level 69, x1 ident, A1 ident, A2 ident) : charac.
*)


Notation "'_If' x 'Then' Q1 'Else' Q2" :=
  (!I (fun H Q => (x = true -> Q1 H Q) /\ (x = false -> Q2 H Q)))
  (at level 69, x at level 0) : charac.

Notation "'Case' x '=' p 'Then' Q1 'Else' Q2" :=
  (!C (fun H Q => (x = p -> Q1 H Q) /\ (x <> p -> Q2 H Q)))
  (at level 69, x at level 0) : charac.

Notation "'Case' x '=' p [ x1 ]  'Then' Q1 'Else' Q2" :=
  (!C (fun H Q => (forall x1, x = p -> Q1 H Q) 
                /\ ((forall x1, x <> p) -> Q2 H Q)))
  (at level 69, x at level 0, x1 ident) : charac.

Notation "'Case' x '=' p [ x1 x2 ]  'Then' Q1 'Else' Q2" :=
  (!C (fun H Q => (forall x1 x2, x = p -> Q1 H Q) 
                /\ ((forall x1 x2, x <> p) -> Q2 H Q)))
  (at level 69, x at level 0, x1 ident, x2 ident) : charac.

Notation "'Case' x '=' p [ x1 x2 x3 ]  'Then' Q1 'Else' Q2" :=
  (!C (fun H Q => (forall x1 x2 x3, x = p -> Q1 H Q) 
                /\ ((forall x1 x2 x3, x <> p) -> Q2 H Q)))
  (at level 69, x at level 0, x1 ident, x2 ident,
   x3 ident) : charac.

Notation "'Case' x '=' p [ x1 x2 x3 x4 ]  'Then' Q1 'Else' Q2" :=
  (!C (fun H Q => (forall x1 x2 x3 x4, x = p -> Q1 H Q) 
                /\ ((forall x1 x2 x3 x4, x <> p) -> Q2 H Q)))
  (at level 69, x at level 0, x1 ident, x2 ident,
   x3 ident, x4 ident) : charac.

Notation "'Case' x '=' p [ x1 x2 x3 x4 x5 ]  'Then' Q1 'Else' Q2" :=
  (!C (fun H Q => (forall x1 x2 x3 x4 x5, x = p -> Q1 H Q) 
                /\ ((forall x1 x2 x3 x4 x5, x <> p) -> Q2 H Q)))
  (at level 69, x at level 0, x1 ident, x2 ident,
   x3 ident, x4 ident, x5 ident) : charac.

Notation "'Case' x '=' p [ x1 x2 x3 x4 x5 x6 ]  'Then' Q1 'Else' Q2" :=
  (!C (fun H Q => (forall x1 x2 x3 x4 x5 x6, x = p -> Q1 H Q) 
                /\ ((forall x1 x2 x3 x4 x5 x6, x <> p) -> Q2 H Q)))
  (at level 69, x at level 0, x1 ident, x2 ident,
   x3 ident, x4 ident, x5 ident, x6 ident) : charac.

Notation "'Case' x '=' p [ x1 x2 x3 x4 x5 x6 x7 ]  'Then' Q1 'Else' Q2" :=
  (!C (fun H Q => (forall x1 x2 x3 x4 x5 x6 x7, x = p -> Q1 H Q) 
                /\ ((forall x1 x2 x3 x4 x5 x6 x7, x <> p) -> Q2 H Q)))
  (at level 69, x at level 0, x1 ident, x2 ident,
   x3 ident, x4 ident, x5 ident, x6 ident, x7 ident) : charac.

Notation "'Case' x '=' p 'When' w 'Then' Q1 'Else' Q2" :=
  (!W (fun H Q => (x = p -> isTrue (w)%bool -> Q1 H Q) 
                /\ (x <> p \/ isTrue (!w) -> Q2 H Q)))
  (at level 69, x at level 0) : charac.

Notation "'Case' x '=' p [ x1 ]  'When' w 'Then' Q1 'Else' Q2" :=
  (!W (fun H Q => (forall x1, x = p -> isTrue w%bool -> Q1 H Q) 
                /\ ((forall x1, x <> p \/ isTrue (!w)) -> Q2 H Q)))
  (at level 69, x at level 0, x1 ident) : charac.

Notation "'Case' x '=' p [ x1 x2 ]  'When' w 'Then' Q1 'Else' Q2" :=
  (!W (fun H Q => (forall x1 x2, x = p -> isTrue w%bool -> Q1 H Q) 
                /\ ((forall x1 x2, x <> p \/ isTrue (!w)) -> Q2 H Q)))
  (at level 69, x at level 0, x1 ident, x2 ident) : charac.

Notation "'Case' x '=' p [ x1 x2 x3 ]  'When' w 'Then' Q1 'Else' Q2" :=
  (!W (fun H Q => (forall x1 x2 x3, x = p -> isTrue w%bool -> Q1 H Q) 
                /\ ((forall x1 x2 x3, x <> p \/ isTrue (!w)) -> Q2 H Q)))
  (at level 69, x at level 0, x1 ident, x2 ident,
   x3 ident) : charac.

Notation "'Case' x '=' p [ x1 x2 x3 x4 ]  'When' w 'Then' Q1 'Else' Q2" :=
  (!W (fun H Q => (forall x1 x2 x3 x4, x = p -> isTrue w%bool -> Q1 H Q) 
                /\ ((forall x1 x2 x3 x4, x <> p \/ isTrue (!w)) -> Q2 H Q)))
  (at level 69, x at level 0, x1 ident, x2 ident,
   x3 ident, x4 ident) : charac.

Notation "'Case' x '=' p [ x1 x2 x3 x4 x5 ]  'When' w 'Then' Q1 'Else' Q2" :=
  (!W (fun H Q => (forall x1 x2 x3 x4 x5, x = p -> isTrue w%bool -> Q1 H Q) 
                /\ ((forall x1 x2 x3 x4 x5, x <> p \/ isTrue (!w)) -> Q2 H Q)))
  (at level 69, x at level 0, x1 ident, x2 ident,
   x3 ident, x4 ident, x5 ident) : charac.

Notation "'Case' x '=' p [ x1 x2 x3 x4 x5 x6 ]  'When' w 'Then' Q1 'Else' Q2" :=
  (!W (fun H Q => (forall x1 x2 x3 x4 x5 x6, x = p -> isTrue w%bool -> Q1 H Q) 
                /\ ((forall x1 x2 x3 x4 x5 x6, x <> p \/ isTrue (!w)) -> Q2 H Q)))
  (at level 69, x at level 0, x1 ident, x2 ident,
   x3 ident, x4 ident, x5 ident, x6 ident) : charac.

Notation "'Case' x '=' p [ x1 x2 x3 x4 x5 x6 x7 ]  'When' w 'Then' Q1 'Else' Q2" :=
  (!W (fun H Q => (forall x1 x2 x3 x4 x5 x6 x7, x = p -> isTrue w%bool -> Q1 H Q) 
                /\ ((forall x1 x2 x3 x4 x5 x6 x7, x <> p \/ isTrue (!w)) -> Q2 H Q)))
  (at level 69, x at level 0, x1 ident, x2 ident,
   x3 ident, x4 ident, x5 ident, x6 ident, x7 ident) : charac.

Notation "'Match' n Q" :=
  (!M n Q)
  (at level 69, n at level 0) : charac.

Notation "'Match' x : n Q" :=
  (!!M x n Q)
  (at level 69, x ident, n at level 0) : charac.

Notation "'Alias' x ':=' v 'in' Q" :=
  (!S (fun H Q => forall x, x = v -> Q H Q))
  (at level 69, x ident) : charac.

Open Scope charac.

Notation "'LetFunc' a f1 ':=' Q1 'in' F" :=
  (!!F a fun H Q => forall f1, exists P1,
     (Q1 -> P1 f1) /\ (P1 f1 -> F H Q))
  (at level 69, a at level 0, f1 ident) : charac.

Notation "'LetFunc' a f1 ':=' Q1 'and' f2 ':=' Q2 'in' F" :=
  (!!F a fun H Q => forall f1 f2, exists P1 P2,
     (Q1 -> Q2 -> P1 f1 /\ P2 f2) /\ (P1 f1 -> P2 f2 -> F H Q))
  (at level 69, a at level 0, f1 ident, f2 ident) : charac.

Notation "'LetFunc' a f1 ':=' Q1 'and' f2 ':=' Q2 'and' f3 ':=' Q3 'in' F" :=
  (!!F a fun H Q => forall f1 f2 f3, exists P1 P2 P3,
     (Q1 -> Q2 -> Q3 -> P1 f1 /\ P2 f2 /\ P3 f3) /\ (P1 f1 -> P2 f2 -> P3 f3 -> F H Q))
  (at level 69, a at level 0, f1 ident, f2 ident, f3 ident) : charac.

Notation "'LetFunc' f1 ':=' Q1 'in' Q" :=
  (!F fun H Q => forall f1, exists P1,
     (Q1 -> P1 f1) /\ (P1 f1 -> Q H Q))
  (at level 69, f1 ident) : charac.

Notation "'LetFunc' f1 ':=' Q1 'and' f2 ':=' Q2 'in' F" :=
  (!F fun H Q => forall f1 f2, exists P1 P2,
     (Q1 -> Q2 -> P1 f1 /\ P2 f2) /\ (P1 f1 -> P2 f2 -> F H Q))
  (at level 69, f1 ident, f2 ident) : charac.

Notation "'LetFunc' f1 ':=' Q1 'and' f2 ':=' Q2 'and' f3 ':=' Q3 'in' F" :=
  (!F fun H Q => forall f1 f2 f3, exists P1 P2 P3,
     (Q1 -> Q2 -> Q3 -> P1 f1 /\ P2 f2 /\ P3 f3) /\ (P1 f1 -> P2 f2 -> P3 f3 -> F H Q))
  (at level 69, f1 ident, f2 ident, f3 ident) : charac.

Notation "Q1 ;; Q2" :=
  (!Seq fun H Q => exists Q', Q1 H Q' /\ Q2 (Q' tt) Q)
  (at level 68, right associativity) : charac.

Notation "'TopLet' x ':=' Q" :=
  (!TV (forall P, Q P -> P x))
  (at level 69, x at level 0, Q at level 200).

Notation "'TopLet' x ':=' Q" := (* todo: needed? *)
  (!TV (forall P:_->Prop, Q P -> P x))
  (at level 69, x at level 0, Q at level 200).

Notation "'TopLet' [ A1 ]  x ':=' Q" :=
  (!TV (forall A1 P, Q (P A1) -> (P A1) x))
  (at level 69, x at level 0, A1 ident, Q at level 200).

Notation "'TopLet' [ A1 A2 ]  x ':=' Q" :=
  (!TV (forall A1 A2 P, Q (P A1 A2) -> (P A1 A2) x))
  (at level 69, x at level 0, A1 ident, A2 ident, Q at level 200).

Notation "'TopLet' [ A1 A2 A3 ]  x ':=' Q" :=
  (!TV (forall A1 A2 A3 P, Q (P A1 A2 A3) -> (P A1 A2 A3) x))
  (at level 69, x at level 0, A1 ident, A2 ident, A3 ident, Q at level 200).

Notation "'TopLetFunc' ':=' H" :=
  (!TF H)
  (at level 69, Q at level 200).

Notation "'Func' f ':=' Q" := (* todo:needed?*)
  (!F (fun P => forall f, Q -> P f))
  (at level 69) : charac.


(********************************************************************)
(* ** Database of CF and of Spec *)

Definition database_cf := True.

Notation "'RegisterCf' T" := (Register database_cf T) 
  (at level 69).

Definition database_spec := True.

Notation "'RegisterSpec' T" := (Register database_spec T) 
  (at level 69).
