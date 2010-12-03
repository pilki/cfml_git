Set Implicit Arguments.
Require Import CFLib Dijkstra_ml.
Open Scope comp_scope.

(*
Module Type MLOrderedPairInt :=
  MLOrdered with Definition t := (int*int)%type.
Module MLNextNode' :  MLOrdered with Definition t := (int*int)%type.
*)

(*************************************************************)


(*-----------------------------------------------------------*)

Definition Min A (f:A->int) (P:A->Prop) :=  
  epsilon (fun n => (exists x, P x /\ n = f x)
                 /\ (forall x, P x -> n <= f x)).

Definition MinBar A (f:A->int) (P:A->Prop) :=  
  If (exists x, P x) then Finite(Min f P) else Infinite.

Lemma Min_eq : forall A x (f:A->int) (P:A->Prop),
  P x -> (forall y, P y -> f x <= f y) -> Min f P = f x.
Proof.
  intros. unfold Min.
  spec_epsilon* as y [(?&?&?) Sy]. clearbody y. subst y.
  forwards*: Sy x. forwards*: H0 x0. apply* le_antisym.
Qed.

Lemma Min_exists_nonneg : forall A (f:A->int) (P:A->Prop),
  (exists x, P x) -> 
  (forall x, P x -> f x >= 0) ->
  exists n, (exists x, P x /\ n = f x)
          /\ (forall x, P x -> n <= f x).
Proof.
(*
  introv [a Pa] Pos. 
  match goal with |- ?G' => set (G := G') end.
  cuts: (forall m:nat, G \/ (forall x, P x -> f x <= m -> False)).
    destruct (H (abs (f a))) as [?|M].
      auto.
      false~ (M a). rewrite~ abs_pos. apply le_refl.
  induction m.
  destruct (classic (exists x, P x /\ f x = 0)) as [(y&Py&Hy)|M].
    left. exists* 0.
    right. intros x Px Non. rew_classic in M. specializes M x.
     rew_classic in M. destruct M as [?|H]. false. apply H. 
      apply~ le_antisym. rewrite le_is_flip_ge. unfold flip. auto.
  destruct IHm as [?|N]. eauto. right. intros x Px Le.
    destruct (classic (exists x, P x /\ f x = m)) as [(y&Py&Hy)|M].
*)
Admitted.

Lemma Min_inv : forall A x (f:A->int) (P:A->Prop),
  (forall x, P x -> f x >= 0) ->
  P x -> 
  Min f P <= f x.
Proof.
(*
  unfold Min. introv H Px. 
  spec_epsilon as z Hz. exists (f x). 
*)
Admitted.

Lemma MinBar_Infinite : forall A (f:A->int) (P:A->Prop),
  (forall x, ~ P x) -> MinBar f P = Infinite.
Proof.
  intros. unfold MinBar. case_if~. destruct e as [x ?]. false*.
Qed.

Lemma MinBar_Finite : forall A x (f:A->int) (P:A->Prop),
  P x -> (forall y, P y -> f x <= f y) ->
  MinBar f P = Finite (f x).
Proof. 
  intros. unfold MinBar. case_if. 
  fequal. apply~ Min_eq. 
  rew_classic in n. false*.
Qed.

Lemma MinBar_Finite_inv : forall A n x (f:A->int) (P:A->Prop),
  MinBar f P = Finite n -> (forall x, P x -> f x >= 0) -> P x -> n <= f x.
Proof.
  unfold MinBar. introv H Pos Px. case_if.
  destruct e as [y ?]. invert H as M. apply~ Min_inv.
  false.
Qed.

Lemma MinBar_Infinite_inv : forall A x (f:A->int) (P:A->Prop),
  MinBar f P = Infinite -> ~ P x.
Proof. 
  unfold MinBar. introv H Px. case_if.
  false.
  rew_classic in n. false*.
Qed.

(*-----------------------------------------------------------*)

Parameter graph : Type -> Type.
Parameter nodes : forall A, graph A -> set int.
Parameter edges : forall A, graph A -> set (int*int*A).
  
Definition has_edge A (g:graph A) x y w :=
  (x,y,w) \in edges g.

Parameter edges_are_nodes : forall A (g : graph A) x y w,
  has_edge g x y w -> x \in nodes g /\ y \in nodes g.

Definition nonnegative_edges (g:graph int) :=
  forall x y w, has_edge g x y w -> w >= 0.

(*-----------------------------------------------------------*)

Definition path A := list (int*int*A).

Inductive is_path A (g:graph A) : int -> int -> path A -> Prop :=
  | is_path_nil : forall x, 
      is_path g x x nil
  | is_path_cons : forall x y z w p,
      is_path g x y p ->
      has_edge g y z w ->
      is_path g x z ((y,z,w)::p).

Definition weight (p:path int) :=
  nosimpl (fold_right (fun e acc => let '(_,_,w) := e in w+acc) 0 p).

Definition dist (g:graph int) x y :=  
  MinBar weight (is_path g x y).


Lemma weight_nil : 
  weight (nil : path int) = 0.
Proof. auto. Qed.

Lemma weight_cons : forall (p:path int) x y w, 
  weight ((x,y,w)::p) = w + weight p.
Proof. intros. unfold weight. rew_list~. Qed.

(*-----------------------------------------------------------*)

Parameter range : int -> int -> set int.

Definition GraphAdjList (G:graph int) (g:loc) :=
  Hexists N, g ~> Array Id N
         \* [nodes G = range 0 (LibArray.length N)]
         \* [forall_ x \in (nodes G), forall y w, 
               Mem (y,w) (N\(x)) = has_edge G x y w].


(*************************************************************)

Module Type OrderedSigSpec.

Declare Module O : MLOrdered.
Import O.
Parameter T : Type.
Parameter S : htype T t.

Global Instance le_inst : Le T.
Global Instance le_order : Le_total_order.

Parameter le_spec : Spec le (x:t) (y:t) |R>> forall X Y,  
  keep R (x ~> S X \* y ~> S Y) (\= istrue (LibOrder.le X Y)).

Hint Extern 1 (RegisterSpec le) => Provide le_spec.

End OrderedSigSpec.


(*************************************************************)

(** Definition of the minimum of a multiset *)

Definition is_min_of `{Le A} (E:multiset A) (X:A) := 
  X \in E /\ forall_ Y \in E, X <= Y.

(*************************************************************)

Module Type HeapSigSpec.

Declare Module H : MLHeapSig.
Declare Module OS : OrderedSigSpec with Module O := H.MLElement.
Import H MLElement OS. 

Parameter Heap : htype T t -> htype (multiset T) heap.

Parameter create_spec :
  Spec create () |R>> 
    R [] (~> Heap S \{}).

Parameter is_empty_spec : 
  Spec is_empty (h:heap) |R>> forall E,
    keep R (h ~> Heap S E) (\= istrue (E = \{})).

Parameter push_spec : 
  Spec push (x:t) (h:heap) |R>> forall E X,
    R (h ~> Heap S E \* x ~> S X) (# h ~> Heap S (\{X} \u E)).

Parameter pop_spec : 
  Spec pop (h:heap) |R>> forall E,
    R (h ~> Heap S E) (fun x => Hexists X F, 
      [is_min_of E X] \* [E = \{X} \u F] \* x ~> S X \* h ~> Heap S F).

Hint Extern 1 (RegisterSpec create) => Provide create_spec.
Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.
Hint Extern 1 (RegisterSpec push) => Provide push_spec.
Hint Extern 1 (RegisterSpec pop) => Provide pop_spec.
End HeapSigSpec.


(*************************************************************)

Module NextNodeSpec <: OrderedSigSpec with Module O := MLNextNode.
Module O := MLNextNode.
Import O.
Definition T : Type := (int*int)%type.
Definition S : htype T t := Id.

Global Instance le_inst : Le T.
Proof.
  constructor.
  exact (fun (p1 p2 : int*int) => snd p1 <= snd p2).
Defined.
  
Global Instance le_order : Le_total_order.
Admitted. (* todo :order prod *)

Lemma le_spec : Spec le (x:t) (y:t) |R>> forall X Y, 
  keep R (x ~> S X \* y ~> S Y) (\= istrue (LibOrder.le X Y)).
Proof.
  xcf. unfold S. intros x y X Y. xextract. intros. subst. xgo~.
Qed.

Hint Extern 1 (RegisterSpec le) => Provide le_spec.

End NextNodeSpec.

(*************************************************************)

Global Instance len_inhab : Inhab len.
Proof. constructor. exact Infinite. Qed.


(*************************************************************)
Require Import LibArray LibMap.

Module DijkstraSpec.
Declare Module MLHeap : MLHeapSig with Module MLElement := MLNextNode.
Import NextNodeSpec.
Module Dijkstra := MLDijkstra MLHeap.
Import Dijkstra.



(*-----------------------------------------------------------*)

Hint Constructors Mem.

Hint Extern 1 (index _ _) => skip.

Axiom bool_test' : forall b,
  b = true \/ b = false.

Hint Constructors is_path.

Tactic Notation "rew_array" "~" :=
  rew_array; auto_tilde.
Tactic Notation "rew_array" "~" "in" hyp(H) :=
  rew_array in H; auto_tilde.


(*-----------------------------------------------------------*)

Implicit Types V : array bool.
Implicit Types B : array len.
Implicit Types H : multiset (int*int).
Implicit Types p : path int.

Section Invariants.
Variables (G:graph int) (s:int).

(*-----------------------------------------------------------*)

Record inv V B H reach : Prop :=
  { source_ok     : B\(s) = Finite 0;
    treated_ok    : forall z, V\(z) = true -> B\(z) = dist G s z;
    untreated_ok  : forall z, V\(z) = false -> z <> s -> 
                      B\(z) = MinBar weight (reach z);
    heap_correct  : forall z d, V\(z) = false -> z <> s -> (z,d) \in H -> 
                      exists p, reach z p /\ weight p = d;
    heap_complete : forall z p, reach z p -> 
                      exists d, (z,d) \in H /\ d <= weight p }.  

Definition from_out V z p :=
  is_path G s z p /\ V\(z) = false.

Definition enters V z p :=
  from_out V z p /\ (exists q y w, p = (y,z,w)::q /\ V\(y) = true).

Definition enters_via x L V z p :=
  from_out V z p /\ exists q w, p = (x,z,w)::q /\ Mem (z,w) L.

Definition new_enters x L V z p :=
  enters V z p \/ enters_via x L V z p.


(*-----------------------------------------------------------*)

Lemma new_enters_grows : forall x L V z p y w,
  new_enters x L V z p -> new_enters x ((y,w)::L) V z p.
Proof. introv [H|(q&w'&?&?&M)]. left~. right. split~. exists___*. Qed.

Lemma new_enters_inv : forall x L V z p y w,
  new_enters x ((y,w)::L) V z p -> 
      new_enters x L V z p 
   \/ (from_out V z p /\ exists q, p = (x,y,w)::q).
Proof.
  introv [H|(P&(q&w'&E&M))]. left. left~.
  inverts M. right*. left; right; split*.
Qed.

Lemma from_out_update : forall x V z p, z <> x ->
  from_out (V\(x:=true)) z p = from_out V z p.
Proof. intros. unfold from_out. rew_array~. Qed.

Lemma enters_step : forall L V x z p, V\(x) = false -> z <> x ->
  (forall y w, Mem (y,w) L = has_edge G x y w) ->
  enters (V\(x:=true)) z p = new_enters x L V z p.
Proof.
  introv Vx Nvx EQ. extens. iff H. hnf in H.
  destruct H as (F&(q&y&w&E&Vy)).
   rewrite~ from_out_update in F. tests (y = x).
    right. split~. exists q w. split~. rewrite EQ. 
     lets: (proj1 F). subst p. inverts* H.
    left. rew_array~ in Vy. splits*.
  destruct H as [(F&(q&y&w&E&Vy))|(P&(q&w&E&M))];
   (split; [ rewrite~ from_out_update | ]).
     exists q y w. split~. rew_array~. intro_subst; false.
     exists q x w. split~. rew_array~.
Qed.

Lemma enters_shorter : forall V z p, 
  V\(s) = true -> nonnegative_edges G ->
  is_path G s z p -> V\(z) = false -> 
  exists x q, enters V x q /\ weight q <= weight p.
Proof.
  introv Vs NG P. set_eq s': s in P. set_eq G': G in P. 
  induction P; intros; subst. false. destruct (bool_test' (V\(y))).
    exists z ((y,z,w)::p). split. 
      split. split~.
      exists p y w. split~. apply le_refl.
    forwards~ (x&q&E&L): IHP. exists x q. split~.
     rewrite weight_cons. forwards: NG H. math.    
Qed.

Lemma enters_best : forall V x p,
  V\(s) = true -> nonnegative_edges G ->
  V\(x) = false -> enters V x p ->
  (forall y q, enters V y q -> weight p <= weight q) ->
  dist G s x = Finite (weight p).
Proof.
  introv Vs NG Vx E BE.
  unfold dist.
  lets ((?&_)&_): E. applys~ (@MinBar_Finite (path int)) p.
  intros p' P'. forwards~ (y&q&E'&L): enters_shorter V P'.
   forwards: BE E'. math.
Qed.

Lemma nonnegative_path : forall p x y, 
  nonnegative_edges G -> is_path G x y p -> 0 <= weight p.
Proof.
  introv NG H. induction H. 
  rewrite weight_nil. apply le_refl.
  rewrite weight_cons. forwards: NG H0. math.
Qed.

Implicit Arguments eq_trans' [A].

Lemma inv_heap_empty_correct : forall e V B,
  nonnegative_edges G -> 
  inv V B \{} (enters V) -> B\(e) = dist G s e.
Proof.
  introv [Sok Tok Uok Hcorr Hcomp].
  destruct (bool_test' (V\(e))) as [E|E].
  apply~ Tok.
  unfold dist. tests (e = s).
    rewrite Sok. rewrite~ (MinBar_Finite (nil:path int)).
     intros. applys* nonnegative_path.
    rewrite~ Uok. apply (eq_trans' Infinite); 
     rewrite~ MinBar_Infinite; intros p P.
     
enters_shorter : forall V z p, 
  V\(s) = true -> nonnegative_edges G ->
  is_path G s z p -> V\(z) = false -> 
  exists x q, enters V x q /\ weight q <= weight p.


(*-----------------------------------------------------------*)

End Invariants.

Import MLHeap.

Parameter Heap : htype (multiset (int*int)) heap.

Parameter create_spec :
  Spec create () |R>> 
    R [] (~> Heap \{}).

Parameter is_empty_spec : 
  Spec is_empty (h:heap) |R>> forall E,
    keep R (h ~> Heap E) (\= istrue (E = \{})).

Parameter push_spec : 
  Spec push (x:int*int) (h:heap) |R>> forall E X,
    R (h ~> Heap E \* x ~> S X) (# h ~> Heap (\{X} \u E)).

Parameter pop_spec : 
  Spec pop (h:heap) |R>> forall E,
    R (h ~> Heap E) (fun x => Hexists X F, 
      [is_min_of E X] \* [E = \{X} \u F] \* x ~> Id X \* h ~> Heap F).

Hint Extern 1 (RegisterSpec create) => Provide create_spec.
Hint Extern 1 (RegisterSpec is_empty) => Provide is_empty_spec.
Hint Extern 1 (RegisterSpec push) => Provide push_spec.
Hint Extern 1 (RegisterSpec pop) => Provide pop_spec.


(*-----------------------------------------------------------*)


Ltac xwhile_inv_core W I :=
  match type of W with
  | wf _ => eapply (@while_loop_cf_to_inv _ I _ W)
  | _ -> nat => eapply (@while_loop_cf_to_inv _ I (measure W))
  | _ => eapply (@while_loop_cf_to_inv _ I W)
  end.


Tactic Notation "xwhile_inv" constr(W) constr(I) :=
  xwhile_pre ltac:(fun _ => xwhile_inv_core W I).

Axiom array_make_read : forall `{Inhab A} (i n:int) (v:A),
  index n i -> (make n v)\(i) = v.

Hint Rewrite @array_make_read : rew_array.



Ltac multiset_in_inv_base H M ::=
  match type of H with
  | _ \in \{} => false; apply (@in_empty_inv _ _ H)  
  | _ \in \{_} => 
    generalize (in_single_inv H); try clear H; try intro_subst_hyp
  | _ \in _ \u _ => 
    let H' := fresh "TEMP" in
    destruct (in_union_inv H) as [H'|H']; 
    try clear H; multiset_in_inv_base H' M
  | _ => rename H into M
  end.


Lemma shortest_path_spec :
  Spec shortest_path g a b |R>> forall G,
    nonnegative_edges G ->
    a \in nodes G ->
    b \in nodes G ->
    keep R (g ~> GraphAdjList G) (\= dist G a b).
Proof.
  xcf. introv Pos Ds De. unfold GraphAdjList at 1. hdata_simpl.
  xextract as N NG Adj. xapps. xapps. xapps. xapps. xapps~. xapps.
  set (data := fun B V H =>
    g ~> Array Id N \* v ~> Array Id V \* b ~> Array Id B \* h ~> Heap H).
  set (hinv := fun H:multiset(int*int) => 
    Hexists B V, data B V H \* [inv G s V B H (enters G s V)]).
  xseq (# hinv \{}). xwhile_inv (fun H:multiset(int*int) => 0%nat) hinv. 
    skip. (* todo: termination *)
    (* -- initial state satisfies invariant -- *)
    esplit. unfold hinv,data. hsimpl. constructor.
      rew_array~.
      introv Mz. rew_array~ in Mz. false.
      introv Mz Ns. rew_array~. rewrite~ MinBar_Infinite.
       intros p (_&(q&y&w&_&E)). rew_array~ in E. (* false *)
      introv _ Ns E. multiset_in E. intros E. inverts E. false.
      introv (_&(q&y&w&_&E)). rew_array~ in E. false.  
    (* -- verification of the loop body -- *) 
    intros H. unfold hinv. xextract as B V [Sok Tok Uok Hcorr Hcomp]. 
     apply local_erase. esplit. splits.
    (* ---- loop condition -- *) 
    unfold data. xapps. xret.
    (* ---- loop body -- *) 
    xextract as HN. xapp. skip.
    (* ---- loop post-condition -- *) 
    hextract as He. fold_bool. rew_logic in He. subst H.
     unfold data. xsimpl. constructor~.
  (* ---- return value -- *) 
  unfold hinv, data. xextract as B V Inv. 
  xapp~. intros l. hdata_simpl GraphAdjList. xsimpl~.
  subst l. apply* inv_heap_empty_correct.
Qed.






Definition from_out V z p :=
  is_path G s z p /\ V\(z) = false.

Definition enters V z p :=
  from_out V z p /\ (exists q y w, p = (y,z,w)::q /\ V\(y) = true).


Record inv V B H reach : Prop :=
  { source_ok     : B\(s) = Finite 0;
    treated_ok    : forall z, V\(z) = true -> B\(z) = dist G s z;
    untreated_ok  : forall z, V\(z) = false -> z <> s -> 
                      B\(z) = MinBar weight (reach z);
    heap_correct  : forall z d, V\(z) = false -> z <> s -> (z,d) \in H -> 
                      exists p, reach z p /\ weight p = d;
    heap_complete : forall z p, reach z p -> 
                      exists d, (z,d) \in H /\ d <= weight p }.  



(*-----------------------------------------------------------*)

End DijkstraSpec. 
