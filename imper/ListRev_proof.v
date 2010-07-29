Set Implicit Arguments.
Require Import LibCore CFPrim ListRev_ml MyLib_ml.

Parameter ml_is_null_spec : 
  Spec ml_is_null l |R>> R [] (\[ bool_of (l = null)]).

Hint Extern 1 (RegisterSpec ml_is_null) => Provide ml_is_null_spec.

Notation "'Hexists' x1 x2 , H" := (Hexists x1, Hexists x2, H)
  (at level 39, x1 ident, x2 ident, H at level 50) : heap_scope.
Notation "'Hexists' x1 x2 x3 , H" := (Hexists x1, Hexists x2, Hexists x3, H)
  (at level 39, x1 ident, x2 ident, x3 ident, H at level 50) : heap_scope.
Notation "'Hexists' x1 x2 x3 , H" := (Hexists x1, Hexists x2, Hexists x3, Hexists x4, H)
  (at level 39, x1 ident, x2 ident, x3 ident, x4 ident, H at level 50) : heap_scope.

Notation "'keep' R H Q" :=
  (R H (Q \*+ H)) (at level 25, R at level 0, H at level 0, Q at level 0).


(*****************)

Fixpoint List A a (T:A->a->hprop) (L:list A) (l:loc) : hprop :=
  match L with
  | nil => [True]
  | X::L' => Hexists x l', T X x \* l ~> RefOn (x,l') \* List T L' l'
  end.

Definition Pair A1 A2 a1 a2 (T1:A1->a1->hprop) (T2:A2->a2->hprop) P p :=
  let '(X1,X2) := P in let '(x1,x2) := p in T1 X1 x1 \* T2 X2 x2.

Fixpoint List' A a (T:A->a->hprop) (L:list A) (l:loc) : hprop :=
  match L with
  | nil => [True]
  | X::L' => l ~> Ref (Pair T (List' T)) (X,L')
  end.

Notation "'While' Q1 'Do' Q2 'Done'" :=
  (!While (fun H Q => exists A, exists I, exists R,
       wf R 
     /\ (exists x, H ==> I x)
     /\ (forall x, local (fun Hl Ql => exists Q', 
            Q1 Hl Q'
         /\ Q2 (Q' true) (# Hexists y, (I y) \* [R y x])
         /\ (Q' false ==> Ql tt)) (I x) Q)))
  (at level 69) : charac.
(*
Notation "'WWhile' r; p ; n 'Do' r  'Done'" :=
(!While (fun (H3 : hprop) (Q4 : unit -> hprop) =>
                 exists A0 I R,
                 wf R /\
                 (exists X, H3 ==> I X) /\
                 (forall X : A0,
                  local
                    (fun (H4 : hprop) (Q5 : unit -> hprop) =>
                     exists Q',
                     (Let  : '_x4 _x4 := r 
                      in (Let  : '_x3 _x3 := App ml_is_null _x4 ;
                          in (Ret !_x3))) H4 Q' /\
                     ((App ml_incr n ;);;
                      (Let  : '_x2 _x2 := App ml_get p ;
                       in (Let  : '_x1 _x1 := App ml_get _x2 ;
                           in App ml_set p (snd _x1) ;))) (Q' true)
                       (#Hexists Y : A0, I Y \* [R Y X]) /\
                     Q' false ==> Q5 tt) (I X) Q4)))
  (at level 69) : charac.
*)


Lemma mlength_spec : forall a,
  Spec mlength (l:mlist a) |R>> forall A (T:A->a->hprop) (L:list A),
     R (l ~> List T L) (\= (length L : int)).
Proof.
  xcf. unfold mlist. intros.
  xapp. xapp. xseq (Hexists l', n ~> @RefOn int (length L) \* p ~> RefOn l' \* l' ~> List T nil).
    (* todo : xseq automatic if xwhile *)
  xuntag. apply local_erase. exists (list A) (fun L' => Hexists k:int, Hexists l',
     n ~> RefOn k \* p ~> RefOn l' \* l' ~> List T L' \* [k + length L' = length L]) (@list_sub A).
  splits. prove_wf. exists L. hsimpl. math.
  intros L'. xextract. intros k l' E. apply local_erase. 
  skip.
  intros l'. xgc. xapp. xsimpl. auto. 
Qed.



  (*
   eapply (@xwhile_frame _ (fun L' => Hexists k l',
     n ~> RefOn k \* p ~> RefOn l' \* l' ~> List T L' \* [k + length L' = length L]) (@list_sub _)).

  xwhile_manual (fun L' => Hexists k l',
     n ~> RefOn k \* p ~> RefOn l' \* l' ~> List T L' \* [k + length L' = length L])
     (@list_sub A). L
  *)
















