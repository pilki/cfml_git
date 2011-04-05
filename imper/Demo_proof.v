Set Implicit Arguments.
Require Import CFLib Demo_ml.


(*

(* [cell A] is equivalent to [loc] *)
Print cell.

(* [Cell] is the representation predicate, 
   so you can write [x ~> Cell T1 T2 V1 V2]. *)

Check Cell.

(* Focus and unfocus operations *)

Check Cell_focus.
Check Cell_unfocus.

(* Specification of creation and accessors for fields *)

Check _new_cell_spec.
Check _get_next_spec.
Check _set_next_spec.
Check _get_content_spec.
Check _set_content_spec.

*)

(* We can define our own representation on top of [Cell] *)

Fixpoint CList a A (T:A->a->hprop) (L:list A) (l:loc) : hprop :=
  match L with
  | nil => []
  | X::L' => l ~> Cell T (CList T) X L'
  end.

(* We can show that allocating a Cell extends a CList *)

Lemma CList_from_Cell : forall l a x q A (T:A->a->hprop) X Q,
  l ~> Cell Id Id x q \* x ~> T X \* q ~> CList T Q
  ==> l ~> CList T (X::Q).
Proof. intros. hchange (Cell_unfocus l). hsimpl. Qed.

Lemma CList_to_Cell : forall l a A (T:A->a->hprop) X Q,
  l ~> CList T (X::Q) ==> Hexists x q,
  l ~> Cell Id Id x q \* x ~> T X \* q ~> CList T Q.
Proof. intros. hdata_simpl CList. fold CList. hchange (Cell_focus l). hsimpl. Qed.

Implicit Arguments CList_from_Cell [a A].
Implicit Arguments CList_to_Cell [a A].
Opaque CList.

(** From there, we can prove the function [newx] *)

(*
let newx x q1 q2 = 
   let machin = {content = x; next = q1} in 
   machin.next <- q2 
*)

Lemma newx_spec : forall a,
  Spec newx (x:a) (q1:loc) (q2:loc) |R>>
    forall A (T:A->a->hprop) (X:A) (L1 L2 : list A),
    R (x ~> T X \* q1 ~> CList T L1 \* q2 ~> CList T L2) 
      (fun l => l ~> CList T (X::L2)).
Proof.
  xcf. (* apply the characteristic formula *)
  intros. (* introduces the arguments *)
  xapp. (* reason on application *)
  (* at this point we could call [xapp] directly, but let's
     first see how we can build a clean CList first *)
  xchange (CList_from_Cell machin). 
  (* at this point we cannot call [xapp] because 
     updating the record requires a [Cell] *)
  xchange (CList_to_Cell machin). xextract as y q.
  (* now we can continue *)
  xapp. (* reason on application *) 
  (* We could be tempted to conclude with [xret], but that
     would not work since we need to do some garbage collection *)
  xret_gc. (* conclude and create an existential for the discarded heap *)
  (* finally we need to rebuild the CList as earlier on *)
  hchange (CList_from_Cell machin). 
  hsimpl.
Qed.

(** A specification proof is always followed with a line of the 
    following form, for registering the specification so that it
    can be automatically used to reason about a call to the function *)

Hint Extern 1 (RegisterSpec newx) => Provide newx_spec.

