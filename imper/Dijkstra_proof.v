Set Implicit Arguments.
Require Import CFLib Dijkstra_ml.
Open Scope comp_scope.

Tactic Notation "exists" := 
  exists___.
Tactic Notation "exists" "~" := 
  exists; auto_tilde.
Tactic Notation "exists" "*" := 
  exists; auto_star.


Ltac subst_hyp_base H ::=
  match type of H with 
  | (_,_,_,_) = (_,_,_,_) => injection H; clear H; do 3 intro_subst_hyp
  | (_,_,_) = (_,_,_) => injection H; clear H; do 3 intro_subst_hyp
  | (_,_) = (_,_) => injection H; clear H; do 2 intro_subst_hyp
  | ?x = ?y => first [ subst x | subst y ] 
  end.

Lemma subst_hyp_demo : forall x y x' y' z z' : nat, forall P:nat->Prop, 
  (x,y,z) = (x',y',z') -> P x -> P x' -> P y -> P y' -> P z -> P z' -> z = z'.
Proof.
  introv H. intros. 
  subst_hyp_base H. auto.
Qed.
 
(* todo: __ in introv means "intros" *)



Axiom bool_test' : forall b,
  b = true \/ b = false.

Axiom bool_neq_true_eq_false : forall b,
  b <> true -> b = false.
Hint Resolve bool_neq_true_eq_false.

Hint Resolve istrue_True.


Hint Rewrite @array_update_read_eq : rew_arr.

Tactic Notation "rew_arr" := 
  autorewrite with rew_arr.
Tactic Notation "rew_arr" "in" hyp(H) := 
  autorewrite with rew_arr in H.
Tactic Notation "rew_arr" "in" "*" := 
  autorewrite with rew_arr in *.

Tactic Notation "rew_arr" "~" :=
  rew_arr; auto_tilde.
Tactic Notation "rew_arr" "*" :=
  rew_arr; auto_star.
Tactic Notation "rew_arr" "~" "in" hyp(H) :=
  rew_arr in H; auto_tilde.
Tactic Notation "rew_arr" "*" "in" hyp(H) :=
  rew_arr in H; auto_star.


Axiom make_index : forall `{Inhab A} n i (v:A),
  index n i -> index (make n v) i.
Hint Resolve @make_index.

Lemma pred_ext_elim_l_0 : forall A (P Q:A->Prop),
  (forall x, P x = Q x) -> (forall x, P x -> Q x).
Proof. introv H. intros. rewrite~ <- H. Qed.
Implicit Arguments pred_ext_elim_l_0 [A P Q].

Axiom index_update : forall `{Inhab A} (T:array A) n i j (v:A),
  index n i -> index (T\(j:=v)) i.
Hint Resolve @index_update.

Require Import LibArray.
Axiom index_array_length : forall A (t : array A) i,
  index (length t) i -> index t i.

Hint Resolve index_array_length.

Hint Resolve bool_inhab.

Lemma conj_dup_r : forall P Q : Prop,
  Q -> (Q -> P) -> P /\ Q.
Proof. auto*. Qed.


(*
Module Type MLOrderedPairInt :=
  MLOrdered with Definition t := (int*int)%type.
Module MLNextNode' :  MLOrdered with Definition t := (int*int)%type.
*)


Lemma not_True_to_False : ~ True -> False.
Proof. intros. rew_logic in *. auto. Qed.
Hint Immediate not_True_to_False.



Ltac testsd_base E H1 H2 :=
  destruct E as [H1|H2].

Ltac testsp_base E H1 H2 :=
  testsd_base (classicT E) H1 H2.

Ltac testsb_base E H1 H2 :=
  testsp_base (isTrue E) H1 H2.

Ltac tests_dispatch E H1 H2 :=
  match type of E with
  | bool => testsb_base E H1 H2
  | Prop => testsp_base E H1 H2
  | {_}+{_} => testsd_base E H1 H2
  end.

Ltac tests_post H I :=
  tryfalse; rew_logic in H; revert H; 
  first [ intro_subst_hyp | intros I ]; tryfalse.

Ltac tests_base E I1 I2 :=
  let H1 := fresh "TEMP" in
  let H2 := fresh "TEMP" in
  tests_dispatch E H1 H2; [ tests_post H1 I1 | tests_post H2 I2 ].

Tactic Notation "tests" constr(E) "as" simple_intropattern(I1) simple_intropattern(I2) := 
  tests_base E I1 I2.

Tactic Notation "tests" constr(E) "as" simple_intropattern(I) :=
  tests E as I I.

Tactic Notation "tests" constr(E) :=
  let H := fresh "C" in tests E as H.



(*************************************************************)


Definition value_nonneg A (f:A->int) (P:A->Prop) :=
  forall x, P x -> f x >= 0.  

(*-----------------------------------------------------------*)

Definition min A (f:A->int) (P:A->Prop) :=  
  epsilon (fun n => (exists x, P x /\ n = f x)
                 /\ (forall x, P x -> n <= f x)).

Lemma min_eq : forall A x (f:A->int) (P:A->Prop),
  P x -> (forall y, P y -> f x <= f y) -> min f P = f x.
Proof.
  intros. unfold min.
  spec_epsilon* as y [(?&?&?) Sy]. clearbody y. subst y.
  forwards*: Sy x. forwards*: H0 x0. apply* le_antisym.
Qed.

Lemma min_exists_nonneg : forall A (f:A->int) (P:A->Prop),
  (exists x, P x) -> 
  value_nonneg f P ->
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

Lemma min_inv : forall A (f:A->int) (P:A->Prop),
  (exists x, P x) -> value_nonneg f P -> 
  exists x, P x /\ min f P = f x /\ (forall y, P y -> f x <= f y).
Proof.
  intros. forwards* (n&(y&Py&Ey)&My): min_exists_nonneg.
  unfold min. spec_epsilon* as z' ((z&Pz&Ez)&Hz). rewrite* Ez in Hz.
Qed.

Lemma min_elim : forall A x (f:A->int) (P:A->Prop),
  value_nonneg f P ->
  P x -> 
  min f P <= f x.
Proof. intros. forwards* (y&Py&Ey&My): min_inv. rewrite~ Ey. Qed.


(*-----------------------------------------------------------*)

Definition mininf A (f:A->int) (P:A->Prop) :=  
  If (exists x, P x) then Finite(min f P) else Infinite.

Lemma mininf_infinite : forall A (f:A->int) (P:A->Prop),
  (forall x, ~ P x) -> mininf f P = Infinite.
Proof.
  intros. unfold mininf. case_if~. destruct e as [x ?]. false*.
Qed.

Lemma mininf_finite : forall A x (f:A->int) (P:A->Prop),
  P x -> (forall y, P y -> f x <= f y) -> mininf f P = Finite (f x).
Proof. 
  intros. unfold mininf. case_if. 
  fequal. apply~ min_eq. 
  rew_classic in n. false*.
Qed.

Lemma mininf_finite_inv : forall A n (f:A->int) (P:A->Prop),
  mininf f P = Finite n -> value_nonneg f P ->
   exists x, P x /\ f x = n /\ (forall y, P y -> n <= f y).
Proof.
  introv E N. unfold mininf in E. case_If. inverts E. 
  forwards* (x&Px&Ex&Mx): min_inv. rewrite* <- Ex in Mx.
Qed.

Lemma mininf_finite_elim : forall A n x (f:A->int) (P:A->Prop),
  mininf f P = Finite n -> value_nonneg f P -> P x -> n <= f x.
Proof.
  unfold mininf. introv H Pos Px. case_if.
  destruct e as [y ?]. invert H as M. apply~ min_elim.
  false.
Qed.

Lemma mininf_infinite_inv: forall A (f:A->int) (P:A->Prop),
  mininf f P = Infinite -> (forall x, ~ P x).
Proof. 
  unfold mininf. introv H Px. case_if.
  false.
  rew_classic in n. false*.
Qed.

Lemma mininf_infinite_elim : forall A x (f:A->int) (P:A->Prop),
  mininf f P = Infinite -> ~ P x.
Proof. intros. apply* mininf_infinite_inv. Qed.

(*-----------------------------------------------------------*)

Definition len_gt l d :=
  match l with Finite d' => d < d' | Infinite => True end.

Lemma mininf_len_gt : forall d A (f:A->int) (P:A->Prop),
  len_gt (mininf f P) d ->
  value_nonneg f P ->
  forall x, P x -> d < f x.
Proof.
  unfold len_gt. introv H NE. sets_eq l:(mininf f P).  (* todo: case_eq*)
  intros. destruct l.
    forwards*: (@mininf_finite_elim A). math.
    forwards*: (@mininf_infinite_elim A) x.
Qed.

Lemma mininf_len_gt_not : forall d A (f:A->int) (P:A->Prop),
  ~ (len_gt (mininf f P) d) ->
  value_nonneg f P ->
  exists d', mininf f P = Finite d' /\ d' <= d.
Proof. 
  unfold len_gt. introv H N. cases (mininf f P); tryfalse~.
  forwards* (x&Px&Ex&Mx): mininf_finite_inv. eauto with maths.
Qed.
Lemma mininf_len_gt_not_elim : forall d A (f:A->int) (P:A->Prop),
  ~ (len_gt (mininf f P) d) ->
  value_nonneg f P ->
  exists x, P x /\ f x <= d.
Proof.
  introv H N. forwards~ (d'&E&L): mininf_len_gt_not H.
  forwards~ (x&Px&Lx&_): mininf_finite_inv E. eauto with maths.
Qed.

(*-----------------------------------------------------------*)

Parameter graph : Type -> Type.
Parameter nodes : forall A, graph A -> set int.
Parameter edges : forall A, graph A -> set (int*int*A).
  
Definition has_edge A (g:graph A) x y w :=
  (x,y,w) \in edges g.

Parameter has_edge_nodes : forall A (g : graph A) x y w,
  has_edge g x y w -> x \in nodes g /\ y \in nodes g.

Lemma has_edge_in_nodes_l : forall A (g : graph A) x y w,
  has_edge g x y w -> x \in nodes g.
Proof. intros. forwards*: has_edge_nodes. Qed.

Lemma has_edge_in_nodes_r : forall A (g : graph A) x y w,
  has_edge g x y w -> y \in nodes g.
Proof. intros. forwards*: has_edge_nodes. Qed.

Definition nonneg_edges (g:graph int) :=
  forall x y w, has_edge g x y w -> w >= 0.
  (* forall x y, value_nonneg id (has_edge g x y) *)

(*-----------------------------------------------------------*)

Definition path A := list (int*int*A).

Inductive is_path A (g:graph A) : int -> int -> path A -> Prop :=
  | is_path_nil : forall x, 
      x \in nodes g ->
      is_path g x x nil
  | is_path_cons : forall x y z w p,
      is_path g x y p ->
      has_edge g y z w ->
      is_path g x z ((y,z,w)::p).

Definition weight (p:path int) :=
  nosimpl (fold_right (fun e acc => let '(_,_,w) := e in w+acc) 0 p).

Definition dist (g:graph int) x y :=  
  mininf weight (is_path g x y).

Lemma weight_nil : 
  weight (nil : path int) = 0.
Proof. auto. Qed.

Lemma weight_cons : forall (p:path int) x y w, 
  weight ((x,y,w)::p) = w + weight p.
Proof. intros. unfold weight. rew_list~. Qed.

Lemma nonneg_edges_to_path : forall g x y, 
  nonneg_edges g ->
  value_nonneg weight (is_path g x y).
Proof.
  introv NG H. induction H. 
  rewrite weight_nil. math. 
  rewrite weight_cons. forwards: NG H0. math.
Qed.

Lemma is_path_cons_has_edge : forall A (g:graph A) x y z w p,
  is_path g x z ((y,z,w)::p) -> has_edge g y z w.
Proof. introv H. inverts~ H. Qed.

Lemma is_path_in_nodes_l : forall A (g:graph A) x y p,
  is_path g x y p -> x \in nodes g.
Proof. introv H. induction~ H. Qed.

Lemma is_path_in_nodes_r : forall A (g:graph A) x y p,
  is_path g x y p -> y \in nodes g.
Proof. introv H. inverts~ H. apply* has_edge_in_nodes_r. Qed. 
     
Parameter edges_are_nodes : forall A (g : graph A) x y w,
  has_edge g x y w -> x \in nodes g /\ y \in nodes g.



(*-----------------------------------------------------------*)

Parameter range : int -> int -> set int.

Definition GraphAdjList (G:graph int) (g:loc) :=
  Hexists N, g ~> Array Id N
   \* [forall x, x \in nodes G = index (LibArray.length N) x]
   \* [forall x y w, x \in nodes G ->
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
Hint Resolve len_inhab.

(*************************************************************)
Require Import LibArray LibMap.

Module DijkstraSpec.
Declare Module MLHeap : MLHeapSig with Module MLElement := MLNextNode.
Import NextNodeSpec.
Module Dijkstra := MLDijkstra MLHeap.
Import Dijkstra.

Import MLHeap.

(*-----------------------------------------------------------*)
(* todo : fix *)

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

Hint Constructors Mem is_path.Ltac auto_star ::= try solve [ auto | jauto ]. 

(*
Hint Extern 3 (_ \in _) => in_union_extract.
Hint Extern 3 (_ \in _ \u _) => in_union_get.
*)


Lemma multiset_in_union_single_eq_l : forall A (x:A) E F,
  E = \{x} \u F -> x \in E.
Proof. intros. subst. multiset_in. Qed.

Lemma multiset_in_union_single_eq_r : forall A (x y:A) E F,
  E = \{x} \u F -> y \in F-> y \in E.
Proof. introv M N. subst. multiset_in. Qed.

Hint Resolve multiset_in_union_single_eq_l multiset_in_union_single_eq_r.


(*-----------------------------------------------------------*)

Implicit Types V : array bool.
Implicit Types B : array len.
Implicit Types Q : multiset (int*int).
Implicit Types p : path int.

Section Invariants.
Variables (G:graph int) (s:int).

(*-----------------------------------------------------------*)

Definition size_ok `{Inhab A} (T:array A) :=
  forall x, x \in nodes G -> index T x.

Hint Unfold size_ok.

Require Import LibArray.
Require Import LibSet.

(*-----------------------------------------------------------*)

Record inv_of z V B Q reach : Prop := {
  Bdist: z \in nodes G -> isTrue (V\(z)) -> B\(z) = dist G s z;
  Bbest: z \in nodes G -> ~ isTrue (V\(z)) -> B\(z) = mininf weight (reach z); 
  Hcorr: forall d, (z,d) \in Q -> z \in nodes G /\
           (~ isTrue (V\(z)) -> exists p, reach z p /\ weight p = d);
  Hcomp: forall p, z \in nodes G -> reach z p -> exists d, (z,d) \in Q /\ d <= weight p }.

Record inv V B Q reach : Prop := {
  Invof: forall z, inv_of z V B Q reach;
  SizeV: size_ok V;
  SizeB: size_ok B }.

Definition from_out V z p :=
  is_path G s z p /\ V\(z) = false.

Definition crossing V z p :=
  from_out V z p /\ (p = nil \/ exists q y w, p = (y,z,w)::q /\ V\(y) = true).

Definition crossing_via x L V z p :=
  from_out V z p /\ exists q w, p = (x,z,w)::q /\ Mem (z,w) L.

Definition new_crossing x L V z p :=
  z <> x /\ (crossing V z p \/ crossing_via x L V z p).

Definition outgoing_edges x L :=
  forall y w, Mem (y,w) L = has_edge G x y w.

(*-----------------------------------------------------------*)

Section NewEnters.
Hint Unfold new_crossing crossing_via.

Lemma new_crossing_nil : forall x V z, z <> x -> 
  new_crossing x nil V z = crossing V z.
Proof.
  intros. extens. intros p. unfold new_crossing.
  iff (?&[?|((P&Vz)&(q&w&E&M))]) ?; auto*. inverts M.
Qed.
Lemma new_crossing_not : forall x L V z y w, y <> z ->
  new_crossing x ((y,w)::L) V z = new_crossing x L V z.
Proof.
  intros. extens. intros p. iff (?&[?|(?&(q&w'&?&M))]).
   eauto 10. inverts M. false. eauto 10. eauto 10. eauto 10.
Qed.

Lemma new_crossing_grows : forall x L V z p y w,
  new_crossing x L V z p -> new_crossing x ((y,w)::L) V z p.
Proof. introv (N&[H|(q&w'&?&?&M)]); eauto 10. Qed.

Lemma new_crossing_inv : forall x L V z p y w,
  new_crossing x ((y,w)::L) V z p -> 
      new_crossing x L V z p 
   \/ (z <> x /\ from_out V z p /\ exists q, p = (x,y,w)::q).
Proof. introv (N&[H|(P&(q&w'&E&M))]). eauto. inverts M; eauto 10. Qed.

End NewEnters.

(*-----------------------------------------------------------*)


Variables (NG:nonneg_edges G) (Ns:s \in nodes G).

Lemma value_nonneg_new_crossing : forall x L V y,
  value_nonneg weight (new_crossing x L V y).
Proof. introv [_ [((F&_)&_)|((F&_)&_)]]; apply* nonneg_edges_to_path. Qed.

Hint Resolve value_nonneg_new_crossing.
Hint Resolve nonneg_edges_to_path. (* todo try remove *)

Lemma from_out_in_nodes : forall V z p,
  from_out V z p -> z \in nodes G.
Proof. introv [F _]. apply* is_path_in_nodes_r. Qed.

Lemma from_out_cons_in_nodes : forall V z p y w q, 
  from_out V z p -> p = (y,z,w)::q -> y \in nodes G.
Proof. introv [F _] E. subst. inverts F. apply* is_path_in_nodes_r. Qed.

Lemma crossing_in_nodes : forall V z p, 
  crossing V z p -> z \in nodes G.
Proof. introv [F _]. apply* from_out_in_nodes. Qed.

Hint Resolve from_out_in_nodes from_out_cons_in_nodes crossing_in_nodes.

(*-----------------------------------------------------------*)

Lemma dist_source : dist G s s = Finite 0.
Proof.
  applys~ (mininf_finite (nil:path int)).
  intros. apply* nonneg_edges_to_path.
Qed.

Lemma crossing_step : forall L V x, 
  V\(x) = false -> size_ok V -> x \in nodes G ->
  outgoing_edges x L ->
  new_crossing x L V = crossing (V\(x:=true)).
Proof.
  introv Vx SV Nx EQ. extens. intros z p. 
  asserts EF: (z \in nodes G -> z <> x -> from_out (V\(x:=true)) z p = from_out V z p).
    intros. unfold from_out. rew_array~.
  iff (Nzx&H) H.
   hnf in H. destruct H as [(F&[N|(q&y&w&E&Vy)])|(P&(q&w&E&M))];
    (split; [ rewrite* EF | ]).
     auto.
     right. exists q y w. split~. rew_array*. auto_false.
     right. exists q x w. rew_arr~.     
   asserts: (z <> x).
     intro_subst. lets ((_&E)&_): H. rew_arr~ in E. false.
    destruct H as (F&[N|(q&y&w&E&Vy)]).
      rewrite* EF in F. subst. split~. left. split~.
      rewrite* EF in F. tests (y = x); split~.
        right. split~. exists q w. split~. rewrite EQ. 
         subst p. applys* is_path_cons_has_edge (proj1 F).
        left. subst p. rew_array* in Vy. splits~. right*.
Qed.

Lemma crossing_shorter : forall V z p, 
  is_path G s z p -> V\(z) = false -> 
  exists x q, crossing V x q /\ weight q <= weight p.
Proof.
  introv P. set_eq s': s in P. set_eq G': G in P. 
  induction P; intros; subst. 
  exists s (nil:path int). splits_all~. apply le_refl.
  destruct (bool_test' (V\(y))).
    exists z ((y,z,w)::p). split. 
      split. split~.
      right. exists p y w. split~. math.
    forwards~ (x&q&E&L): IHP. exists x q. split~.
     rewrite weight_cons. forwards: NG H. math.    
Qed.

Lemma crossing_best : forall V x p,
  V\(x) = false -> crossing V x p -> 
  (forall y q, crossing V y q -> weight p <= weight q) ->
  dist G s x = Finite (weight p).
Proof.
  introv Vx En BE. unfold dist.
  lets ((?&_)&_): En. applys~ (@mininf_finite (path int)) p.
  intros p' P'. forwards~ (y&q&E'&L): crossing_shorter V P'.
   forwards: BE E'. math.
Qed.


(*-----------------------------------------------------------*)


Hint Extern 1 (_ \in _ \u _) => multiset_in.
Hint Extern 1 (_ \in \{_}) => multiset_in.

Lemma inv_start : forall n, 
  (forall x, x \in nodes G -> index n x) ->
  inv (make n false) (make n Infinite\(s:=Finite 0)) 
      ('{(s, 0)}) (crossing (make n false)).
Proof.
  introv EQ.
  asserts Es: (crossing (make n false) s nil).  splits~. splits~. rew_array~.
  constructors~; [| skip (*todo: size_ok*)].
  intros z. constructors~.
  introv Nz Vi. rew_array~ in Vi. false.
  introv Nz Vi. tests (z = s).
    rew_arr~. rewrite~ (mininf_finite (nil:path int)).    
     intros p ((?&?)&?). apply* nonneg_edges_to_path.
    rew_array~. rewrite~ mininf_infinite.
     intros p (P&[Pn|(q&y&w&Py&Ey)]).
       subst. destruct P as [P _]. inverts P. false.
       rew_array* in Ey.
  introv E. multiset_in E. splits~. exists~ (nil:path int).
  introv Nz (P&[Pn|(q&y&w&Py&Ey)]). 
    exists 0. subst p. destruct P as [P _]. inverts P.
     split~. rewrite weight_nil. math.
    rew_array* in Ey. false. 
Qed.

Axiom boolneg : forall b, !b -> b = false.
Hint Resolve boolneg.


Lemma inv_end_elim : forall x V B,
  inv V B \{} (crossing V) -> 
  x \in nodes G ->
  B\(x) = dist G s x.
Proof.
  introv [Inv SB SV] Nx.
  tests (V\(x)). applys* (Bdist (Inv x)).
  rewrite~ (Bbest (Inv x)). unfold dist.
  asserts Ne: (forall z p, z \in nodes G -> ~ crossing V z p).
    introv Nz P. forwards* (d&N&_): (Hcomp (Inv z)). multiset_in N.
  apply (eq_trans' Infinite); rewrite~ mininf_infinite.
  intros p P. forwards* (z&q&Q'&?): crossing_shorter P. 
Qed.

Lemma size_ok_elim : forall `{Inhab A} (T:array A) x,
  size_ok T -> x \in nodes G -> index T x.
Proof. unfolds~ size_ok. Qed.
Hint Extern 1 (index _ _) => apply size_ok_elim.


Lemma inv_begin_loop : forall x d V B Q Q',
  Q = '{(x,d)} \u Q' -> 
  is_min_of Q (x,d) ->
  x \in nodes G ->
  ~ isTrue (V\(x)) ->
  inv V B Q (crossing V) ->
     inv (V\(x:=true)) B Q' (new_crossing x nil V)
  /\ Finite d = dist G s x.
Proof.
  introv EQ [In Mi] Nx Vx [Inv SB SV]. 
  asserts: (forall y q, crossing V y q -> d <= weight q). 
    introv Ey. lets ((_&?)&_): Ey. specializes~ Inv y.  
    forwards* (d'&In'&?): (Hcomp Inv) Ey.
    lets Sy: Mi In'. skip: (d <= d'). math. (* todo with modules *)
  forwards* (_&p&En&W): Hcorr (Inv x).
  apply conj_dup_r. subst d. rewrite~ (@crossing_best V x p).
  introv Dx. constructors~. intros z. forwards [Bd Bb Hc Hk]: Inv z.
  tests (z = x). constructors; rew_arr~.
    intros _ _. rewrite~ Bb. subst d. rewrite* (mininf_finite p).
    auto_false.
    introv In'. split~. auto_false~.
    introv _ En'. false~ (proj1 En').
  constructors.
    introv Nz Vi. rew_array~ in Vi.
    introv Nz Vi. rew_array~ in Vi. rewrite~ new_crossing_nil.
    intros d' Iz. forwards [Nz Hcz]: Hc d'. eauto. split~.
     introv Vz. rew_array~ in Vz. rewrite~ new_crossing_nil.  
    introv Nz En'. lets: (proj1 En'). rewrite~ new_crossing_nil in En'.
     forwards~ (dz&Hz&?): Hk En'. exists~ dz.
     subst Q. multiset_in Hz; intros; tryfalse. split~.
Qed.

Lemma inv_end_loop : forall V x Q B L,
  outgoing_edges x L ->
  x \in nodes G ->
  ~ isTrue (V\(x)) ->
  inv (V\(x:=true)) B Q (new_crossing x L V) ->
  inv (V\(x:=true)) B Q (crossing (V\(x:=true))).
Proof.
  introv EL Nx Vx [Inv SB SV]. constructors~.
  intros z. lets [Bd Bb Hc Hk]: Inv z. tests (x = z).
  constructors.
    auto.
    rew_arr~; auto_false.
    introv Hd. forwards [? ?]: Hc Hd. split~. rew_arr~; auto_false.
    introv Nz En. lets ((_&N)&_): En. rew_arr~ in N. false.
  constructors.
    auto.
    rewrite~ crossing_step in Bb.
    introv Hzd. forwards~ [? M]: Hc Hzd. rewrite~ crossing_step in M.
    introv Nz En. apply~ Hk. rewrite~ crossing_step.
Qed.



Lemma inv_update_le : forall L V B Q x y w dx dy,
  x \in nodes G ->
  has_edge G x y w ->
  dy = dx + w ->
  Finite dx = dist G s x ->
  inv (V\(x:=true)) B Q (new_crossing x L V) -> 
  If len_gt (B\(y)) dy 
    then inv (V\(x:=true)) (B\(y:=Finite dy)) (\{(y, dy)} \u Q) (new_crossing x ((y,w)::L) V)
    else inv (V\(x:=true)) B Q (new_crossing x ((y, w)::L) V).
Proof.
  introv Nx Ed Dy Eq [Inv SB SV]. sets_eq V': (V\(x:=true)).
  cuts K: (forall z, 
    If len_gt (B\(y)) dy 
    then inv_of z V' (B\(y:=Finite dy)) ('{(y, dy)} \u Q) (new_crossing x ((y,w)::L) V)
    else inv_of z V' B Q (new_crossing x ((y, w)::L) V)).
    case_If; constructors~.
  intros z. lets [Bd Bb Hc Hk]: Inv z. tests (z = y).
  (* case z = y *)
  forwards~ (px&Px&Wx&Mx): (@mininf_finite_inv (path int)) (eq_sym Eq).
  lets Ny: (has_edge_in_nodes_r Ed).
  sets p: ((x,y,w)::px). 
  asserts W: (weight p = dy). subst p. rewrite weight_cons. math. 
  tests (V'\(y)) as C; case_If as Nlt.
  (* subcase y visisted, distance improved *)
  false. rewrite~ Bd in Nlt. forwards M: mininf_len_gt Nlt p; subst p; auto.
    rewrite weight_cons in M. math.
  (* subcase y visisted, distance not improved *)
  constructors; auto_false. 
  introv In. forwards [? ?]: Hc In. split~. auto_false.
  intros py _ Ey. lets [E|(Nxy&(P'&Vy')&(p'&Ep))]: (new_crossing_inv Ey).
    forwards~ (d&D'&In'): Hcomp E.
    subst V'. rew_array~ in C. auto_false.
  (* subcase y not visisted, distance improved *)
  asserts P: (new_crossing x ((y, w) :: L) V y p).
    subst p. split. intro_subst. subst V'. rew_arr~ in C.
    right. split. split. auto.
    subst V'. tests (x = y). rew_arr~ in C. rew_array~ in C. exists___~. 
  constructors.
    auto_false.
    introv Vi. rew_arr~. rewrite~ (mininf_finite p). rewrite~ W.
     intros q Enq. lets [E|(Nxy&(P'&Vy')&(p'&Ep))]: (new_crossing_inv Enq).
       rewrite~ Bb in Nlt. forwards~: mininf_len_gt Nlt E. math.
       subst q. rewrite weight_cons. inverts P' as Q' _. forwards: Mx Q'. math.
    introv Iy. split~. multiset_in Iy.
      introv E. inverts E. introv Vi. exists~ p.
      introv Vi. lets~ (_&p'&P'&Wp'): Hc H.
       exists p'. split~. apply~ new_crossing_grows.   
    intros py _ Ey. lets [E|(Nxy&(P'&Vy')&(p'&Ep))]: (new_crossing_inv Ey).
      forwards~ (d&D'&In'): Hcomp E. exists~ d.
      subst py. inverts P' as P' W. rewrite weight_cons. exists dy. split~.
       forwards~ M: (@mininf_finite_elim (path int)) p' (eq_sym Eq). math.
  (* subcase y not visisted, distance not improved *)
  constructors.
    auto_false.
    intros Vi. rewrite~ Bb in Nlt. forwards~ (d&Md&Ld): mininf_len_gt_not Nlt.
     forwards~ (p'&P'&Wq&Mq): (@mininf_finite_inv (path int)) Md.
     rewrite~ Bb. rewrite Md. rewrite~ (mininf_finite p').
      rewrite~ Wq. apply~ new_crossing_grows.
      intros p0 Ep0. rewrite Wq. lets~ [E|(Nxy&(Py&Vy')&(p''&Ep''))]: (new_crossing_inv Ep0).
        subst p0. inverts Py as Py W. rewrite weight_cons. 
         forwards~ M: (@mininf_finite_elim (path int)) p'' (eq_sym Eq). 
         math.
    introv Iy. forwards~ (_&p'&P'&Wp'): Hc Iy. split~. introv Vi. exists p'. split~.
     apply~ new_crossing_grows.   
    intros py _ Ey. lets [E|(Nxy&(Py&Vy')&(p'&Ep))]: (new_crossing_inv Ey).
      applys~ Hk E.
      subst py. inverts Py as Py W. rewrite weight_cons.
       forwards~ M: (@mininf_finite_elim (path int)) p' (eq_sym Eq). 
        rewrite~ Bb in Nlt. forwards~ (p''&Q''&Wq''): mininf_len_gt_not_elim Nlt.
        lets~ (dy'&Iy&Wy): Hk Q''. exists dy'. split~. math.    
  (* case z <> y *)
  case_If.
  constructors.
    intros. rew_array~.
    intros. rew_array~. rewrite~ new_crossing_not. 
    introv In. multiset_in In. intros; false. rewrite~ new_crossing_not.
    introv Nz En. rewrite~ new_crossing_not in En. 
     forwards~ (dz&Hz&?): Hk En. exists~ dz.
  constructors; try solve [ auto | rewrite~ new_crossing_not ].
Qed.

Lemma inv_no_update : forall V' B H x d,
  V'\(x) = true ->
  inv V' B ('{(x,d)}\u H) (crossing V') ->
  inv V' B H (crossing V').
Proof.
  introv Vx [Inv SB SV]. constructors~. intros z.
  lets [Bd Bb Hc Hk]: Inv z. constructors~.
    introv Nz En. forwards~ (d'&In&?): Hk En. lets~ ((_&?)&?): En.
     exists d'. split~. multiset_in In; auto_false.
Qed.

End Invariants.

(*-----------------------------------------------------------*)

Definition ex_intro' A (x:A) (P:A->Prop) (H:P x) := @ex_intro A P x H.
Implicit Arguments ex_intro' [A [P] [H]].

Hint Unfold size_ok.

Lemma count_bounds : forall `{Inhab A} (t:array A) (f:A->Prop),
  0 <= count f t <= length t.
Admitted.

Lemma Mem_last : forall A (L:list A) x,
  Mem x (L & x).
Proof. intros. apply~ Mem_app_or. Qed.
Lemma Mem_rev : forall A (L:list A) x,
  Mem x L -> Mem x (rev L).
Proof. introv H. induction H; rew_rev; apply~ Mem_app_or. Qed.
Lemma Mem_rev_eq : forall A (L:list A) x,
  Mem x L = Mem x (rev L).
Proof. extens. iff M. apply~ Mem_rev. rewrite <- rev_rev. apply~ Mem_rev. Qed.

Lemma xgen_lemma : forall A (J:A->hprop) (E:A),
  J E ==> heap_is_pack J.
Proof. intros. hsimpl*. Qed.

Ltac xgen_abstract H E :=
  let Jx := eval pattern E in H in
  match Jx with ?J _ => constr:(J) end.

Ltac xgen_nosimpl E :=
  match goal with |- ?H ==> _ =>
    let J := xgen_abstract H E in 
    eapply pred_le_trans; [ apply (@xgen_lemma _ J E) | ] end.


Ltac xgen_base E := 
  xgen_nosimpl E.    

Tactic Notation "xgen" constr(E1) :=
  xgen_base E1.
Tactic Notation "xgen" constr(E1) constr(E2) :=
  xgen_base E1; xgen_base E2.


Lemma xgen_demo : forall (x E y F:int) H1 R,
  (forall H2, x ~> R E \* y ~> R F \* H1 ==> H2 -> H2 = H2 -> True) -> True.
Proof.
  introv H. dup.
  eapply H. xgen E. xgen F. xok. auto.
  eapply H. xgen E F. xok. auto.
Qed.

Hint Extern 1 (wf ?R) => unfold R : wf.



Lemma shortest_path_spec :
  Spec shortest_path g a b |R>> forall G,
    nonneg_edges G ->
    a \in nodes G ->
    b \in nodes G ->
    keep R (g ~> GraphAdjList G) (\= dist G a b).
Proof.
  xcf. introv Pos Ds De. unfold GraphAdjList at 1. hdata_simpl.
  xextract as N NG Adj. lets NG': (pred_ext_elim_l_0 NG).
  xapps. xapps. xapps. xapps. xapps*. xapps.
  set (data := fun B V Q =>
    g ~> Array Id N \* v ~> Array Id V \* b ~> Array Id B \* q ~> Heap Q).
  set (hinv := fun VQ => let '(V,Q) := VQ in
    Hexists B, data B V Q \* [inv G s V B Q (crossing G s V)]).
  xseq. (* (# Hexists V, hinv (V,\{})).  *) 
  set (termin := lexico2 (binary_map (count (=true)) (upto (length N)))
                       (binary_map (fun Q:multiset(int*int) => card Q:int) (downto 0))).
  xwhile_inv termin hinv. prove_wf. (* todo: automate *)
    (* -- initial state satisfies invariant -- *)
    refine (ex_intro' (_,_)). unfold hinv,data. hsimpl. 
     applys_eq~ inv_start 2. permut_simpl. (* todo: rename *)
    (* -- verification of the loop body -- *) 
    intros [V Q]. unfold hinv. xextract as B Inv.  (* todo: lost notation *)
     apply local_erase. esplit. splits. (* todo :tactic *)
    (* ---- loop condition -- *) 
    unfold data. xapps. xret.
    (* ---- loop body -- *) 
    xextract as HN. xapp. intros [x d] H' Mi HE. intro_subst.
    lets [Inv' SB SV]: Inv.
    asserts: (x \in nodes G). 
      lets [_ _ Hc _]: Inv' x. forwards~ [? _]: Hc d.
       subst Q. multiset_in. (* todo: auto*)
    xmatch. xapps~. xif; [ skip: (V\(x) = false) | ]. (* todo: cleanup *)
    (* ------ node treated -- *) 
    forwards~ [Inv'' Dx]: inv_begin_loop HE Inv.
    xapps~. xfun. xapps~.
    sets V': (V\(x:=true)).
    sets I: (fun L => Hexists L', Hexists B Q, data B V' Q (* todo bug when writing Hexists *)
        \* [inv G s V' B Q (new_crossing G s x L' V) ] \* [N\(x) = rev(L')++L]).
    xapp_manual. xapply (KR I); clear KR; match goal with |- context [update] => idtac | _ => clears update end.
    (* -------- verification of update -- *) 
    apply Supdate. xisspec. clears update. clear hinv. (* todo tactic *)
    unfold I at 1. hide I. unfold data. hide data. clears B Q.  
    intros [y w] L. xextract as L' B Q Inv EQ. sort.
    xmatch.
    lets [_ _ SV]: Inv. 
    asserts Ew: (has_edge G x y w). rewrite~ <- Adj. rewrite EQ. applys* Mem_app_or.
    asserts Ny: (y \in nodes G). applys~ has_edge_in_nodes_r x w.
    xlet. xret. xextract as Dy. (* todo xret does xlet *)
    xapps~. xlet.
    xframe - []. xpost (\= istrue (len_gt (B\(y)) dy)). (* todo automate *)
    destruct (B\(y)); xgo~. 
    xok. xextracts. rewrite app_last in EQ. rewrite <- rev_cons in EQ.
    show_all. unfold I, data. 
    forwards~ K: inv_update_le s Ew Dy Inv. xif; case_If. 
      xapps~. xapps~. hsimpl;eauto.
      xret. hsimpl;eauto. 
    (* -------- iter pre-condition -- *) 
    unfold I. unfold data. hsimpl~ (nil:list (int*int)). xok.
    (* -------- iter post-condition -- *) 
    clears update. subst I.
    hextract as L B' Q'' I' Leq. hsimpl~ (V',Q'') B'.
    left. hnf. subst V'. 
  (* todo :swapped SB and SV *)
  (* todo : changer sizer_ok pour avoir length B = n *) 
  (* todo: garder n = length N *)
  skip LenV: (length V = length N).

  split.
    rewrite <- LenV. forwards K: (count_bounds (V\(x:=true)) (=true)).
     rewrite length_update in K. math.
    lets M: (@count_update bool _). rewrite M. clear M. (* bug coq -> rewrites (rm) *)
     do 2 case_If. math.
    rew_app in Leq. applys~ inv_end_loop I'.
      hnf. intros. rewrite~ <- Adj. rewrite Leq.

  apply Mem_rev_eq.
    (* ------ node ignored -- *) 
    xret. unfold data. hsimpl (V,H'). (* todo improve pair *) (* todo: rename H' *)
      right. split~. hnf. subst Q. rewrite card_union. rewrite card_single. math.
  (* todo: name card_int as a function *)
      skip: (V\(x) = true) . (* cleanup*)
    subst Q. apply* inv_no_update. 
    (* ---- loop post-condition -- *) 
    hextract as He. fold_bool. rew_logic in He. subst Q. unfold data.
    xsimpl~.
  (* ---- return value -- *) 
  intros V B Inv. unfold hinv, data. lets [_ _ ?]: Inv.
  xapp~. intros l. hdata_simpl GraphAdjList. xsimpl~.
  subst l. apply* inv_end_elim.
Qed.


(*-----------------------------------------------------------*)

(* todo: rename Q into H *)
(* todo: cleanup the boolean equalities *)
(* todo: prettyprint for  "let (x,y) =" and "fun (x,y) ="
(* todo: automate multiset_in *)
(* todo: try intro_subst_hyp should deal with tuples *)


(*-----------------------------------------------------------*)

End DijkstraSpec. 


