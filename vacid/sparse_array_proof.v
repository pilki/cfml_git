Set Implicit Arguments.
Require Import LibCore.
Require Import CFPrim CFTactics. (* todo: group as CF *)
Require Import sparse_array_ml.

(* Require Import FuncTactics.*)

Notation "'Hexists' x1 x2 x3 x4 , H" := 
  (Hexists x1, Hexists x2, Hexists x3, Hexists x4, H)
  (at level 39, x1 ident, x2 ident, x3 ident, x4 ident, H at level 50) : heap_scope.
Notation "'Hexists' x1 x2 x3 x4 x5 , H" := 
  (Hexists x1, Hexists x2, Hexists x3, Hexists x4, Hexists x5, H)
  (at level 39, x1 ident, x2 ident, x3 ident, x4 ident, x5 ident, H at level 50) : heap_scope.


Class BagIndex T A := { index : T -> A -> Prop }.

Instance int_index : BagIndex int int.
Proof. intros. constructor. exact (fun n i => 0 <= i < n). Defined.

Lemma int_index_def : forall (n i : int),
  index n i = (0 <= i < n).
Proof. auto. Qed. 

Instance array_index : forall A, BagIndex (array A) int.
Proof. intros. constructor. exact (fun t i => index (length t) i). Defined.

Lemma array_index_def : forall A (t:array A) i,
  index t i = index (length t) i.
Proof. auto. Qed. 

Lemma array_index_bounds : forall A (t:array A) i,
  index t i = (0 <= i < length t).
Proof. auto. Qed. 

Opaque int_index array_index.

Notation "m \( x )" := (LibBag.read m x)
  (at level 29, format "m \( x )") : container_scope.
Notation "m \( x := v )" := (update m x v)
  (at level 29, format "m \( x := v )") : container_scope.


Parameter ml_array_get_spec : forall a,
  Spec ml_array_get (l:loc) (i:int) |R>> 
    forall `{Inhab a} (t:array a), index t i ->
    keep R (l ~> Array Id t) (\= t\(i)).

Parameter ml_array_set_spec : forall a,
  Spec ml_array_set (l:loc) (i:int) (v:a) |R>> 
    forall (t:array a), index t i -> 
    R (l ~> Array Id t) (# l ~> Array Id (t\(i:=v))).
      (* (# Hexists t', l ~> Array Id t' \* [t' = t\(i:=v)]).*)

Hint Extern 1 (RegisterSpec ml_array_get) => Provide @ml_array_get_spec.
Hint Extern 1 (RegisterSpec ml_array_set) => Provide @ml_array_set_spec.


Ltac xchange_debug L :=
  let K := fresh "TEMP" in
  forwards_nounfold K: L; eapply xchange_lemma; 
    [ clear K; try xlocal
    | apply K
    | clear K; instantiate 
    | clear K ].

Axiom isTrue_andb : forall b1 b2 : bool,
  isTrue (b1 && b2) = (isTrue b1 /\ isTrue b2).
Axiom isTrue_orb : forall b1 b2 : bool,
  isTrue (b1 || b2) = (isTrue b1 \/ isTrue b2).
Axiom isTrue_negb : forall b : bool,
  isTrue (! b) = (~ isTrue b).

Hint Rewrite isTrue_istrue isTrue_andb isTrue_orb isTrue_negb : rew_logicb.

Hint Rewrite not_True not_False not_not not_and not_or : rew_logic.

Tactic Notation "rew_logic" := 
  autorewrite with rew_logic.
Tactic Notation "rew_logic" "in" hyp(H) := 
  autorewrite with rew_logic in H.
Tactic Notation "rew_logic" "in" "*" := 
  autorewrite with rew_logic in *.

Tactic Notation "rew_logicb" := 
  autorewrite with rew_logicb.
Tactic Notation "rew_logicb" "in" hyp(H) := 
  autorewrite with rew_logicb in H.
Tactic Notation "rew_logicb" "in" "*" := 
  autorewrite with rew_logicb in *.

Tactic Notation "rew_logics" := 
  rew_logicb; rew_logic.
Tactic Notation "rew_logic" "in" hyp(H) := 
  rew_logicb in H; rew_logic in H.
Tactic Notation "rew_logic" "in" "*" := 
  rew_logicb in *; rew_logic in *.

Ltac check_noevar_in H :=
  let T := type of H in
  match type of H with T => idtac | _ => fail 1 end.

Ltac xif_post H ::=
   calc_partial_eq tt;
   try fold_bool; fold_prop;
   try fix_bool_of_known tt;
   try solve [ discriminate | false; congruence ];
   first [ subst_hyp H; try fold_bool; try rewriteb H 
         | rewriteb H
         | idtac ];
   try fix_bool_of_known tt;
   try (check_noevar_in H; rew_logicb in H; rew_logic in H).

Lemma array_index_prove : forall A (t:array A) i,
  0 <= i < length t -> index t i.
Proof. intros. rewrite~ array_index_def. Qed.
Hint Resolve array_index_prove.

Ltac auto_star ::= try solve [intuition eauto]. (* jauto => should splitt iff *)
Ltac auto_tilde := auto with maths.



(****************************************************)
(* Specification of the invariant *)

Definition tab := array int.

Notation "'L'" := maxlen.

Definition SarrayPacked :=
  @Sarray int (array int) (array int) (array int) Id (Array Id) (Array Id) (Array Id).

Definition SarrayUnpacked :=
  @Sarray int loc loc loc Id Id Id Id.

(*
Definition map_read A `{Inhabited B} := @read _ _ _ (@read_inst A B _).
Coercion map_read : map >-> Funclass.
*)

Require Import LibSet LibMap.

Instance map_index : forall A B, BagIndex (map A B) A.
Proof. intros. constructor. exact (fun m k => k \in (dom m : set A)). Defined.

Lemma map_index_def : forall A B (m:map A B) k,
  index m k = (k \in (dom m : set A)).
Proof. auto. Qed. 

Opaque map_index_def.


Definition good_sizes (Val Idx Back : tab) :=
  length Val = L /\ length Idx = L /\ length Back = L.

Definition Valid n (Idx Back : tab) i :=
  index L i /\ let k := Idx\(i) in 
  index n k /\ Back\(k) = i.

Definition SparseArray (m:map int int) (s:loc) :=
  Hexists (n:int) (Val:tab) (Idx:tab) (Back:tab),
     s ~> SarrayPacked n Val Idx Back
  \* [ good_sizes Val Idx Back
       /\ (forall i, index m i -> Valid n Idx Back i /\ Val\(i) = m\(i))
       /\ (forall k, index n k -> index L (Back\(k))) ].

(*
Lemma inbound_spec :
  Specs inbound i >> [] (\= istrue (index L i)).
Proof.
  xcf. intros. xret. hsimpl.
  extens. rew_logicb. rewrite* int_index_def.
Qed.

Hint Extern 1 (RegisterSpec inbound) => Provide inbound_spec.
*)


Lemma index_le : forall i n m : int,
  n <= m -> index n i -> index m i.
Proof. introv M. do 2 rewrite int_index_def. math. Qed.
Hint Resolve index_le.

Lemma index_array_length : forall A (t : array A) n i,
  index n i -> n = length t -> index t i.
Proof. intros. subst. rewrite~ array_index_def. Qed.
Hint Resolve index_array_length.

Lemma istrue_eq : forall (P Q : Prop),
  ((istrue P) = (istrue Q)) = (P <-> Q).
Proof.
  intros. extens. iff H.
  unfolds istrue. case_if; case_if; tryfalse; intuition.
  asserts_rewrite~ (P = Q). extens~.
Qed.

Hint Rewrite istrue_eq : rew_logicb.

Lemma Id_extract : forall A (x n : A),
  x ~> Id n ==> [x = n].
Proof. intros. unfold Id. hdata_simpl. xsimpl~. Qed.

Lemma valid_spec :
  Spec valid i s |R>> forall n Val Idx Back, 
    good_sizes Val Idx Back -> index L i -> n <= L ->
    keep R (s ~> SarrayPacked n Val Idx Back)
           (\= istrue (Valid n Idx Back i)).
Proof.
  xcf. introv (SVal&SIdx&SBack) Ii Le.
  unfold SarrayPacked. xchange (Sarray_focus s). xextract as n' val idx back.
Implicit Arguments Id_extract [A].
    (* temp *) xchange (Id_extract n'). xextract. intro_subst.
  xapps. xapps. eauto. xapps. xif. 
  (* case inbound *)
Ltac auto_tilde ::= auto with maths.
Tactic Notation "xapps" "~" := xapps; auto_tilde.
Tactic Notation "xapps" "*" := xapps; auto_star.
Lemma Id_import : forall A (x : A),
  [] ==> x ~> Id x.
Proof. intros. unfold Id. hdata_simpl. xsimpl~. Qed.
(* why not Axiom ? --> coqbug *)
  xapps. xapps~.
Implicit Arguments Id_import [A].
    (* temp: *) xchange (Id_import n).
  xchange (Sarray_unfocus s n val idx back). xret. 
    hsimpl. rew_logics. unfold Valid. intuition. 
    rewrite int_index_def. unfolds tab. math. (* todo: tab as notation -- omega should match up to conversion *)
  (* case outof bound *)
    (* temp *) xchange (Id_import n).
  xchange (Sarray_unfocus s n val idx back). xret. 
   hsimpl. rew_logics. fold_bool. fold_prop. unfold Valid.
   
  xapps. xapps. eauto. 
  xchange (Sarray_unfocus s n' val idx back). xret. 
   hsimpl. rew_logics. unfold Valid. intuition.
  (* ~ index L Idx[i] *)
  xchange (Sarray_unfocus s n' val idx back). xret. 
   hsimpl. asserts_rewrite (index L i = False).
rewrite (prop_eq_False_back C').

(*  xpost.*)
  xif.
  (* case in bound *)
  rew_reflect in C. rew_prop in C. 
  xapps. xapps. xapps. apply array_index_prove. rewrite~ SIdx.
  xapps. apply array_index_prove. 


  (* case not in bound *)
  xchange (Sarray_unfocus s n' val idx back).
  xret. hsimpl. xclean. rew_reflect in *.
    intros [H _]. apply C. rewrite int_index_def in H. 
    split; fold_prop; unfolds L; try math.

 (*--todo :sortir le n' ~> Id n *)
Qed.

let valid i s =
   0 <= i && i < maxlen && s.back.(s.idx.(i)) = i


Lemma get_spec :
  Spec get i s |R>> forall T, index T i -> 
    keep R (s ~> SparseArray T) (\= T\(i)).
Proof.
  xcf. introv Ii.
  xlet. 

Qed.

    
(*

lets M : @ml_array_get_spec.
eapply spec_elim_2_2.

evar (a:Type); let t := constr:(Inhab a) in
 let t' := eval unfold a in t in 
assert (x:t'); subst a; [  | pose (M _ x) ].
skip. apply s0.

forwards: M.
lets: (M Z _). apply H.
evar (a:Type); let t := constr:(Inhab a) in
 let t' := eval unfold a in t in 
evar (x:t');
eapply (M _ x).
evar (a:Type);
evar (x:Inhab a);
lets: (H a x); subst a x. 
Show Existentials.
 lets: (>>> Args H __ a).
*)





---------

Definition L := maxlen.

Definition idx_back_coherent n Back Idx :=
   forall k, index n k -> index L (Back\[k]) /\ Idx\[Back\[k]] = k.

Definition back_pointed n Back i :=
  exists k, index n k /\ i = Back\[k].

Definition repr_valid n Back Val T :=
  forall i, index L i -> 
    If (back_pointed n Back i) 
      then T\[i] = Val\[i] 
      else T\[i] = 0.

(* Definition of "l ~> Sarray T" *)

Definition Sarray (T:array int) (l:loc) : heap -> Prop :=
  hexists n (val idx back : loc) (Val Idx Back : array int),
    l ~> sparse_array_of n val idx back 
  * val ~> Array Pure Val
  * idx ~> Array Pure Idx
  * back ~> Array Pure Back
  * [ size Val = L /\ 
      size Idx = L /\
      size Back = L /\
      idx_back_coherent n Back Idx /\
      repr_valid n Back Val T ].


Lemma used_cell_test_correct : forall n Back Idx i, 
  index L i -> idx_back_coherent n Back Idx ->
  (back_pointed n Back i) <-> (index n (Idx\[i]) /\ Back\[Idx\[i]] = i).

Lemma create_spec :
  Spec create size |R>> (0 <= size <= L) -> 
    R [] (fun l => l ~> Sarray (CoqArray.make size default)).
  
  spec_1 create (fun size R => ...).

Lemma get_spec :
  Spec get i l |R>> forall T, index T i -> 
    R (l ~> Sarray T) (fun v => l ~> Sarray T * [v = T\[i]]).
    
    keep R (l ~> Sarray T) (= T\[i]).

Lemma set_spec :
  Spec set i v l |R>> forall T, index T i ->
    R (l ~> Sarray T) (# l ~> Sarray (T\[i:=v])



(* ---------
invariant:
   0 <= n < size <= maxlen
   forall i, 0 <= i < n -> 0 <= back[i] < sz /\ idx[back[i]] = i
*)

  (*back_pointed: index n (Idx\[i]) /\ Back\[Idx\[i]] = i *)